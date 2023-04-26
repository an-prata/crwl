// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use core::fmt;
use gpio::{
    sysfs::{SysFsGpioInput, SysFsGpioOutput},
    GpioIn, GpioOut, GpioValue,
};
use std::{
    error::Error,
    io, mem,
    sync::mpsc::{self, SendError, Sender},
    thread,
    time::Duration,
};

/// Responisble for sending out commands to devices on a serial bus.
pub struct Client {
    tx: Sender<SerialData>,
}

impl Client {
    /// Creates a new serial client given the clock and data pins to use as a
    /// serial bus.
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16, clock_cycle: Duration) -> io::Result<Self> {
        // Kept outside the thread so we can return the error before spawning.
        let mut sender = BitSender::<SysFsGpioOutput>::new(clock_pin, data_pin, clock_cycle)?;
        let (tx, rx) = mpsc::channel();

        thread::spawn(move || -> io::Result<()> {
            loop {
                let packet: SerialData = match rx.recv() {
                    Ok(p) => p,

                    // Returning here makes it so that when the transmitter, and
                    // therefore its containing struct is dropped, so too does
                    // this thread return, which in this case is not actually an
                    // error.
                    Err(_) => return Ok(()),
                };

                sender.send(packet)?;
            }
        });

        Ok(Self { tx })
    }

    /// Queues a packet for sending on the client thread. Returns the given
    /// packet's head on success. An `Err` value from this function means that
    /// the `Client` instance's thread has returned with an error, which would
    /// suggest that an `io::Error` has occured internally. An `Ok` variant does
    /// not necessarily mean the given `Packet` was successfuly sent over
    /// serial, only that it was successfully sent to the thread for that
    /// purpose.
    #[inline]
    pub fn send<T, U>(&mut self, packet: Packet<T, U>) -> Result<T, SendError<SerialData>>
    where
        T: Header,
        U: Data,
    {
        self.tx.send(packet.into())?;
        Ok(packet.head)
    }
}

/// Responsible for recieving messages from the serial bus.
pub struct Server {
    reciever: BitReciever<SysFsGpioInput>,
}

impl Server {
    /// Instantiants a new `Server` given the clock and data pins of the serial
    /// bus to read from.
    #[inline]
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16) -> io::Result<Self> {
        Ok(Self {
            reciever: BitReciever::<SysFsGpioInput>::new(clock_pin, data_pin)?,
        })
    }

    /// Listens for a packet with the given head and returns its data. Since all
    /// recieved data is gotten by request any packet with a different header is
    /// an error. Will block the current thread until the packet is recieved.
    ///
    /// # Arguments
    ///
    /// * `head` - Packet head to listen for.
    /// * `data_type` - Enum variant of `Data` to return.
    #[must_use]
    pub async fn listen_for<T, U>(&mut self, head: T) -> io::Result<U>
    where
        T: Header,
        U: Data,
    {
        let recieved_packet = match self.reciever.recv(Packet::<(u8, u8), u32>::BITS as u8)? {
            Some((v, _)) => {
                let addr = (v >> (u8::BITS + u32::BITS)) as u8;
                let cmd = (v >> u32::BITS) as u8;
                let data = v as u32;

                Packet::new((addr, cmd), data)
            }
            None => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "could not recieve packet",
                ))
            }
        };

        // Since all recived data is made by request we should be recieving
        // exactly the listened for header, anything else is an error.
        if recieved_packet.head.get() != head.get() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "recieved header did not match one provided",
            ));
        }

        match U::extract(&recieved_packet) {
            Ok(v) => Ok(v),
            Err(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "could not extract data from packet",
            )),
        }
    }

    /// Listens for packets with all given heads in order, returns an error if
    /// any packet comes with the wrong header or in the wrong order.
    ///
    /// # Arguments
    ///
    /// * `heads` - A slice of `Header`s in the order the are expect to come.
    /// * `data_type` - Enum variant of `Data` to return.
    #[must_use]
    pub async fn listen_for_seq<T, U>(&mut self, heads: &[T]) -> io::Result<Vec<U>>
    where
        T: Header,
        U: Data,
    {
        let mut data: Vec<U> = Vec::new();

        for h in heads {
            data.push(self.listen_for::<T, U>(*h).await?);
        }

        Ok(data)
    }
}

/// Sends binary data not exceeding 64 bits over the serial bus.
///
/// While the clock pin is high no device should read bits, when clock is low
/// the `BitSender` will not change the value of the data pin and it may be
/// read. While not sending data the `BitSender` will set clock high and data
/// will be held at low, if data moves up while clock is up it will signal the
/// start of a new packet, this does not mean that double up is the start state,
/// only that change from data while clock is up is, they should change at the
/// same time.
struct BitSender<T: GpioOut> {
    clock: T,
    data: T,
    cycle: Duration,
}

impl<T: GpioOut> BitSender<T> {
    /// Puts pins in their default "waiting" state, should be preformed after
    /// construction in most case.
    pub fn start(&mut self) -> Result<(), T::Error> {
        self.clock.set_high()?;
        self.data.set_low()?;
        Ok(())
    }

    /// Sends the binary representation of the given data. Returns the number of
    /// bits sent.
    pub fn send(&mut self, data: SerialData) -> Result<u8, T::Error> {
        let (bits, bits_length) = data;

        self.start()?;

        // Signal data begin with both pins high.
        self.clock.set_high()?;
        self.data.set_high()?;

        thread::sleep(self.cycle);

        for i in 0..bits_length {
            let bit = bits << i & (1 << bits_length - 1) != 0;

            // Set data pin to out bit and lower clock pin to allow reading.
            self.data.set_value(bit)?;
            self.clock.set_low()?;

            thread::sleep(self.cycle);
            self.clock.set_high()?;
            thread::sleep(self.cycle);
        }

        // Go back to waiting and return.
        self.start()?;
        Ok(bits_length)
    }
}

impl BitSender<SysFsGpioOutput> {
    /// Creates a new `BitSender` for sending data using the given clock and
    /// data pins.
    ///
    /// # Arguments
    ///
    /// * `clock_pin` - Pin number of the clock pin.
    /// * `data_pin` - Pin number of the data pin.
    /// * `clock_cycle` - Delay between each clock change, up or down.
    #[inline]
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16, clock_cycle: Duration) -> io::Result<Self> {
        Ok(Self {
            clock: SysFsGpioOutput::open(clock_pin)?,
            data: SysFsGpioOutput::open(data_pin)?,
            cycle: clock_cycle,
        })
    }
}

/// Struct for recieving bits on a serial bus, since the instance belongs to the
/// controller device all addresses in packets are the address of the sending
/// device, not the recipiant.
struct BitReciever<T: GpioIn> {
    clock: T,
    data: T,
}

impl<T: GpioIn> BitReciever<T> {
    /// Waits for the start signal and then reads the given number of bits and
    /// returns the recieved `SerialData`, of which the second value is always
    /// the `size` parameter of this function.
    ///
    /// # Arguments
    ///
    /// * `size` - Size of the data to recieve in bits.
    pub fn recv(&mut self, size: u8) -> Result<Option<SerialData>, T::Error> {
        // Wait until we see a change from clock high data low.
        while self.clock.read_value()? == GpioValue::High
            && self.data.read_value()? == GpioValue::Low
        {}

        // The start of a read is stated with clock high data high, if this is
        // not the state after a no-read segment something's gone wrong.
        if !(self.clock.read_value()? == GpioValue::High
            && self.data.read_value()? == GpioValue::High)
        {
            return Ok(None);
        }

        let mut packet_bits = 0u64;

        // Read the packet, each new bit gets placed in the ones digit and then
        // shifted over.
        for _ in 0..size {
            // On the first loop this does nothing.
            packet_bits <<= 1;

            while self.clock.read_value()? == GpioValue::High {}

            // OR in our new bit, if its zero then its already there.
            if self.data.read_value()? == GpioValue::High {
                packet_bits |= 1u64;
            }

            // Wait until the clock goes back to high to prevent reading the
            // same vaue twice.
            while self.clock.read_value()? == GpioValue::Low {}
        }

        Ok(Some((packet_bits, size)))
    }
}

impl BitReciever<SysFsGpioInput> {
    /// Produces a new `BitReciever` given the clock and data pins to read from.
    #[inline]
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16) -> io::Result<Self> {
        let clock = SysFsGpioInput::open(clock_pin)?;
        let data = SysFsGpioInput::open(data_pin)?;

        Ok(Self { clock, data })
    }
}

/// Represents a single addressed packet for the serial bus where `T` is the
/// implemantation of `Header` being used, likewise `U` is the implementation of
/// `Data` being used.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Packet<T, U>
where
    T: Header,
    U: Data,
{
    pub head: T,
    pub data: U,
}

impl<T, U> Packet<T, U>
where
    T: Header,
    U: Data,
{
    /// Number of bits in each packet as sent over serial, does not reflect
    /// actual size in computer memory which is made different by alignment and
    /// tag information stored in enums as well as any implementation details of
    /// the implementations of `Header` and `Data` being used.
    pub const BITS: u32 = (mem::size_of::<u8>() * 2 * 8) as u32 + u32::BITS;

    /// Creates a new packet given a `Header` and `Data`.
    #[inline]
    #[must_use]
    pub fn new(head: T, data: U) -> Self {
        Self { head, data }
    }

    /// Gets the generic integer representation of the packet.
    #[inline]
    pub fn data_as(&mut self, variant: Data) -> Self {
        self.data = self.data.to_variant(&variant);
        *self
    }
}

impl<T, U> TryFrom<SerialData> for Packet<T, U>
where
    T: Header,
    U: Data,
{
    type Error = ExtractionError;

    /// Assembles a `Packet<T, U>` where `T` and `U` are the specified
    /// implementations of `Header` and `Data` respectively. If you are looking
    /// so simply parse `SerialData` into integers you can avoid errors by using
    /// `Packet::parse()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::f32;
    /// use mecanum::serial;
    ///
    /// let packet = serial::Packet::new((1u8, 42u8), f32::consts::PI.to_bits());
    /// let serial_data: serial::SerialData = packet.into();
    ///
    /// // Yea, specifying type arguments here is annoying but I wanted it to
    /// // be an associated function...
    /// let new_packet = serial::Packet::<(u8, u8), f32>::try_from(serial_data).unwrap();
    ///
    /// // Both the header and binary representation of each packet's data will
    /// // be equal, but their data feilds are of different types.
    /// assert_eq!(packet.head, new_packet.head);
    /// assert_eq!(packet.get(), new_packet.get());
    ///
    /// // This wont compil because they have different types for data.
    /// //assert_eq!(packet, new_packet);
    ///
    /// ```
    fn try_from(value: SerialData) -> ExtractionResult<Self> {
        let (bits, size) = value;

        if size != Self::BITS as u8 {
            return Err(ExtractionError);
        }
    }

    /// Parses the given `SerialData` into a `Packet<(u8, u8), u32>`. If you are
    /// looking to get a packet with a specific implementation of `Header` and
    /// `Data` see `Packet::<T, U>::try_from()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mecanum::serial;
    ///
    /// let packet = serial::Packet::new((1u8, 42u8), 255u32);
    /// let serial_data: serial::SerialData = packet.into();
    ///
    /// // Yea, specifying type arguments here is annoying but I wanted it to
    /// // be an associated function...
    /// let new_packet = serial::Packet::<(u8, u8), u32>::parse(serial_data);
    ///
    /// assert_eq!(packet, new_packet);
    /// ```
    pub fn parse((v, _): SerialData) -> Packet<(u8, u8), u32> {
        let addr = (v >> (u8::BITS + u32::BITS)) as u8;
        let cmd = (v >> u32::BITS) as u8;
        let data = v as u32;

        Packet::new((addr, cmd), data)
    }
}

impl<T, U> TryFrom<SerialData> for Packet<T, U>
where
    T: Header,
    U: Data,
{
    type Error = ExtractionError;

    /// Assembles a `Packet<T, U>` where `T` and `U` are the specified
    /// implementations of `Header` and `Data` respectively. If you are looking
    /// so simply parse `SerialData` into integers you can avoid errors by using
    /// `Packet::parse()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::f32;
    /// use mecanum::serial;
    ///
    /// let packet = serial::Packet::new((1u8, 42u8), f32::consts::PI.to_bits());
    /// let serial_data: serial::SerialData = packet.into();
    ///
    /// // Yea, specifying type arguments here is annoying but I wanted it to
    /// // be an associated function...
    /// let new_packet = serial::Packet::<(u8, u8), f32>::try_from(serial_data).unwrap();
    ///
    /// // Both the header and binary representation of each packet's data will
    /// // be equal, but their data feilds are of different types.
    /// assert_eq!(packet.head, new_packet.head);
    /// assert_eq!(packet.get(), new_packet.get());
    ///
    /// // This wont compile because they have different types for data.
    /// //assert_eq!(packet, new_packet);
    ///
    /// ```
    fn try_from(value: SerialData) -> ExtractionResult<Self> {
        let (bits, size) = value;

        if size != Self::BITS as u8 {
            return Err(ExtractionError);
        }

        let addr = (bits >> (u8::BITS + u32::BITS)) as u8;
        let cmd = (bits >> u32::BITS) as u8;
        let data = bits as u32;

        // Here we construct it once, and then again from the previous
        // construction, which seems stupid at first but we do this so that we
        // can call on the `extract()` associated function of the given types
        // `T` and `U`, a `Header` and `Data` implementation respectively. This
        // has the effect of returning a `Packet` that holds fields of the
        // desired implementation.

        let packet = Packet::new((addr, cmd), data);

        Ok(Self {
            head: T::extract(&packet)?,
            data: U::extract(&packet)?,
        })
    }
}

impl<T, U> Into<SerialData> for Packet<T, U>
where
    T: Header,
    U: Data,
{
    /// Every return value of `into()` for `Packet` will have a second value
    /// equal to `Packet::<(u8, u8), u32>::BITS`.
    fn into(self) -> SerialData {
        let data = self.data.get() as u64;
        let head = self.head.get_shifted();

        (0u64 | head | data, Self::BITS as u8)
    }
}

/// Result from extracting either `Header` or `Data` from a
/// `Packet<(u8, u8), u32>`.
pub type ExtractionResult<T> = Result<T, ExtractionError>;

/// Error from extracting either `Header` or `Data` from a
/// `Packet<(u8, u8), u32>`.
#[derive(Debug, Clone, Copy)]
pub struct ExtractionError;

impl Error for ExtractionError {}

impl fmt::Display for ExtractionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error extracting either header or data from packet")
    }
}

impl Header for (u8, u8) {
    fn extract<T, U>(packet: &Packet<T, U>) -> ExtractionResult<Self>
    where
        T: Header,
        U: Data,
    {
        Ok(packet.head.get())
    }

    fn get(&self) -> Self {
        *self
    }
}

impl Data for u32 {
    fn extract<T, U>(packet: &Packet<T, U>) -> ExtractionResult<Self>
    where
        T: Header,
        U: Data,
    {
        Ok(packet.data.get())
    }

    fn get(&self) -> u32 {
        *self
    }

    // I'm not using `u32` and `Self` interchangeably to denote which are
    // explicitly `u32` and which are implicitly so as defined in the `Data`
    // trait.
}

impl Data for f32 {
    fn extract<T, U>(packet: &Packet<T, U>) -> ExtractionResult<Self>
    where
        T: Header,
        U: Data,
    {
        Ok(f32::from_bits(packet.data.get()))
    }

    fn get(&self) -> u32 {
        self.to_bits()
    }
}

/// Trait for representing a packet tag, used for distinguishing different
/// commands, data types, etc. and used for addressing data to a specific
/// device. Should be comvertable to and from a `(u8, u8)`, the first integer
/// being the address and second being the command.
pub trait Header: Clone + Copy {
    /// The number of bits taken up by any header's address and command.
    const BITS: u32 = u8::BITS * 2;

    /// Contruct a new `Header` instance given the packet it belongs to. The
    /// `None` variant will be interpretted as an error meaning that the given
    /// packet contained an invalid header.
    #[must_use]
    fn extract<T, U>(packet: &Packet<T, U>) -> ExtractionResult<Self>
    where
        T: Header,
        U: Data;

    /// Get the binary representation of this `Header`'s address and command, in
    /// that order.
    ///
    /// The address of the tag will be checked by all devices on the bus and be
    /// used to determine which device should utilise the rest of the packet.
    ///
    /// The command of the tag should be used to denote type information and
    /// instruct the device on how to utilize the packet's data. The definition
    /// of exactly what this means is up to the device and controller
    /// implementation.
    #[must_use]
    fn get(&self) -> (u8, u8);

    /// Like `Header::get()` but returns the values shifted to their appropriate
    /// place in a single `u64` for sending over serial.
    #[inline]
    #[must_use]
    fn get_shifted(&self) -> u64 {
        let (addr, cmd) = self.get();
        ((addr as u64) << (u8::BITS + u32::BITS)) | ((cmd as u64) << u32::BITS)
    }
}

/// Represents the data of a packet sent over the serial bus. Must be fully
/// convertable to a 32 bit unsigned integer (even if the interpretation of
/// such is non-sensical), this means that whatever data is contained in the
/// implementer should be stored within 32 bits.
pub trait Data: Clone + Copy {
    /// Construct a new `Data` instance given generic 32 bit data in the form of
    /// a `u32`, this is likely data retrieved directly from the serial bus. A
    /// `None` variant is interpretted as an error meaning the given packet
    /// was invalid.
    fn extract<T, U>(packet: &Packet<T, U>) -> ExtractionResult<Self>
    where
        T: Header,
        U: Data;

    fn get(&self) -> u32;
}

/// Represents a binary representation of data that can be send via serial.
pub type SerialData = (u64, u8);

#[cfg(test)]
mod tests {
    use super::{BitReciever, BitSender, Packet};
    use gpio::{
        dummy::{DummyGpioIn, DummyGpioOut},
        GpioIn, GpioValue,
    };
    use std::{
        error::Error,
        f32,
        sync::{Arc, RwLock},
        thread,
        time::Duration,
    };

    #[test]
    pub fn send_and_recv() {
        let packets = [
            Packet::new((1u8, 255u8), 314u32),
            Packet::new((5u8, 255u8), f32::consts::PI.to_bits()),
        ];

        // Value of the clock and data pins, stored in memory for the dummy gpio
        // inputs/outputs to interact with.
        let clock_val = Arc::new(RwLock::new(GpioValue::Low));
        let data_val = Arc::new(RwLock::new(GpioValue::Low));

        // Clones of the pin value ARCs for use within the recieving thread.
        let clock_val_recv = clock_val.clone();
        let data_val_recv = data_val.clone();

        // Clones of the packets to be check against within the thread.
        let packets_recv = packets.clone();

        let handle = thread::spawn(
            move || -> Result<Vec<Packet<(u8, u8), u32>>, <DummyGpioIn<&dyn Fn() -> GpioValue> as GpioIn>::Error> {
                let clock_read = move || {
                    let v = *clock_val_recv.read().unwrap();
                    // println!("read clock pin to be {:?}", v);
                    v
                };

                let data_read = move || {
                    let v = *data_val_recv.read().unwrap();
                    println!("read data pin to be {:?}", v);
                    v
                };

                let mut reciever = BitReciever::<DummyGpioIn<&dyn Fn() -> GpioValue>>::new(
                    &clock_read,
                    &data_read,
                );

                let mut packets: Vec<Packet<(u8, u8), u32>> = Vec::new();

                for p in packets_recv {
                    packets.push(match reciever.recv(Packet::<(u8, u8), u32>::BITS as u8)? {
                        Some(p) => match Packet::<(u8, u8), u32>::try_from(p) {
                            Ok(v) => v,
                            Err(_) => panic!("could not interperet packet from serial data"),
                        },
                        None => panic!("recieved none for {:?}", p),
                    });
                }

                Ok(packets)
            },
        );

        let clock_set = |v| {
            let mut val = clock_val.write().unwrap();
            // println!("clock pin set to {:?}", v);
            *val = v;
        };

        let data_set = |v| {
            let mut val = data_val.write().unwrap();
            println!("data pin set to {:?}", v);
            *val = v;
        };

        // Two milliseconds could be a bit fast for some hardware, but even one
        // millisecond works for me so I'll leave it for now to speed up unit
        // test runs.
        let mut sender = BitSender::<DummyGpioOut<&dyn Fn(GpioValue)>>::new(
            &clock_set,
            &data_set,
            Duration::from_millis(2),
        );

        sender.start().unwrap();

        // Just to make sure we dont send before listening.
        thread::sleep(Duration::from_millis(500));

        for p in packets {
            sender.send(p.into()).unwrap();
        }

        let read_packets = handle.join().unwrap().unwrap();

        for i in 0..packets.len() {
            assert_eq!(packets[i].get(), read_packets[i].get());
        }
    }

    impl<'a> BitSender<DummyGpioOut<&'a dyn Fn(GpioValue)>> {
        /// Creates a new dummy `BitSender` for unit testing.
        #[inline]
        #[must_use]
        fn new(
            clock_fn: &'a dyn Fn(GpioValue),
            data_fn: &'a dyn Fn(GpioValue),
            clock_cycle: Duration,
        ) -> Self {
            Self {
                clock: DummyGpioOut::new(clock_fn),
                data: DummyGpioOut::new(data_fn),
                cycle: clock_cycle,
            }
        }
    }

    impl<'a> BitReciever<DummyGpioIn<&'a dyn Fn() -> GpioValue>> {
        /// Creates a new dummy `BitReciever` for unit testing.
        #[inline]
        #[must_use]
        fn new(clock: &'a dyn Fn() -> GpioValue, data: &'a dyn Fn() -> GpioValue) -> Self {
            Self {
                clock: DummyGpioIn::new(clock),
                data: DummyGpioIn::new(data),
            }
        }
    }
}
