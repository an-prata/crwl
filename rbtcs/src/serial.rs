// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use core::fmt;
use gpio::{GpioIn, GpioOut, GpioValue};
use std::{
    error::Error,
    io, mem,
    sync::mpsc::{self, Receiver, SendError, Sender},
    thread,
    time::Duration,
};

/// Responisble for sending out commands to devices on a serial bus.
pub struct Client {
    tx: Sender<SerialData>,
}

impl Client {
    /// Creates a new `Client` given already opened `GpioOut` implementations.
    pub fn new<T>(clock: T, data: T, cycle: Duration) -> Self
    where
        T: GpioOut + Send + 'static,
        <T as GpioOut>::Error: Send,
    {
        let (tx, rx) = mpsc::channel();

        thread::spawn(move || -> Result<(), T::Error> {
            let mut sender = BitSender::new(clock, data, cycle);

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

        Self { tx }
    }

    /// Queues a packet for sending on the client thread. Returns the given
    /// packet's head on success. An `Err` value from this function means that
    /// the `Client` instance's thread has returned with an error, which would
    /// suggest that an `io::Error` has occured internally. An `Ok` variant does
    /// not necessarily mean the given `Packet` was successfuly sent over
    /// serial, only that it was successfully sent to the thread for that
    /// purpose.
    ///
    /// The order in which packets are sent using this function will not matter
    /// unless they trigger a device to send a packet, in which case they may
    /// require more careful timing.
    #[inline]
    pub fn send<U, V>(&mut self, packet: Packet<U, V>) -> Result<U, SendError<SerialData>>
    where
        U: Header,
        V: Data,
    {
        self.tx.send(packet.into())?;
        Ok(packet.head)
    }
}

/// Responsible for recieving messages from the serial bus.
pub struct Server {
    rx: Receiver<SerialData>,
    backlog: Vec<Packet<(u8, u8), u32>>,
}

impl Server {
    /// Creates a new `Server` given already opened `GpioIn` implementations.
    pub fn new<T>(clock: T, data: T) -> Self
    where
        T: GpioIn + Send + 'static,
        <T as GpioIn>::Error: Send,
    {
        let (tx, rx) = mpsc::channel();

        thread::spawn(move || -> Result<(), T::Error> {
            let mut receiver = BitReceiver::new(clock, data);

            loop {
                if let Some(recv) = receiver.recv(Packet::<(u8, u8), u32>::BITS as u8) {
                    tx.send(recv).unwrap();
                }
            }
        });

        Self {
            rx,
            backlog: Vec::new(),
        }
    }

    /// Gets a `Vec` of all packets that match the given header, an empty `Vec`
    /// means that no packets matched the header, though this could be due to
    /// errors from `<U as Header>::extract()` or `<V as Data>::extract()`
    /// calls.
    #[must_use]
    pub fn get<T>(&mut self, head: T) -> Option<Packet<(u8, u8), u32>>
    where
        T: Header,
    {
        while let Ok(s) = self.rx.try_recv() {
            if let Ok(p) = Packet::<(u8, u8), u32>::try_from(s) {
                self.backlog.push(p);
            }
        }

        self.backlog
            .iter()
            .filter(|p| match T::extract(p) {
                Ok(v) => v.get() == head.get(),
                Err(_) => false,
            })
            .map(|p| *p)
            .last()
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
    /// Creates a new `BitSender` from already open `GpioOut` implementations.
    pub fn new(clock: T, data: T, cycle: Duration) -> Self {
        Self { clock, data, cycle }
    }

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

/// Struct for receiving bits on a serial bus, since the instance belongs to the
/// controller device all addresses in packets are the address of the sending
/// device, not the recipiant.
struct BitReceiver<T: GpioIn> {
    clock: T,
    data: T,
}

impl<T: GpioIn> BitReceiver<T> {
    /// Creates a new `BitReceiver` from already open `GpioIn` implementations.
    pub fn new(clock: T, data: T) -> Self {
        Self { clock, data }
    }

    /// Waits for the start signal and then reads the given number of bits and
    /// returns the received `SerialData`, of which the second value is always
    /// the `size` parameter of this function.
    ///
    /// # Arguments
    ///
    /// * `size` - Size of the data to recieve in bits.
    pub fn recv(&mut self, size: u8) -> Option<SerialData> {
        // Wait until we see a change from clock high data low.
        while self.clock.read_value().ok()? == GpioValue::High
            && self.data.read_value().ok()? == GpioValue::Low
        {}

        // The start of a read is stated with clock high data high, if this is
        // not the state after a no-read segment something's gone wrong.
        if !(self.clock.read_value().ok()? == GpioValue::High
            && self.data.read_value().ok()? == GpioValue::High)
        {
            return None;
        }

        let mut packet_bits = 0u64;

        // Read the packet, each new bit gets placed in the ones digit and then
        // shifted over.
        for _ in 0..size {
            // On the first loop this does nothing.
            packet_bits <<= 1;

            while self.clock.read_value().ok()? == GpioValue::High {}

            // OR in our new bit, if its zero then its already there.
            if self.data.read_value().ok()? == GpioValue::High {
                packet_bits |= 1u64;
            }

            // Wait until the clock goes back to high to prevent reading the
            // same vaue twice.
            while self.clock.read_value().ok()? == GpioValue::Low {}
        }

        Some((packet_bits, size))
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
    pub const fn new(head: T, data: U) -> Self {
        Self { head, data }
    }

    /// Gets the generic integer representation of the packet.
    #[inline]
    #[must_use]
    pub fn get(self) -> Packet<(u8, u8), u32> {
        Packet::<(u8, u8), u32> {
            head: self.head.get(),
            data: self.data.get(),
        }
    }

    /// Parses the given `SerialData` into a `Packet<(u8, u8), u32>`. If you are
    /// looking to get a packet with a specific implementation of `Header` and
    /// `Data` see `Packet::<T, U>::try_from()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtcs::serial;
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

    pub fn parse_into(serial_data: SerialData) -> ExtractionResult<Packet<T, U>> {
        let p = Self::parse(serial_data);
        Ok(Self {
            head: T::extract(&p)?,
            data: U::extract(&p)?,
        })
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
    /// use rbtcs::serial;
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

/// Fake `GpioIn` for testing, a custom one rather than `DummyGpioIn` because
/// the provided one does not work very well over threads.
pub struct TestGpioIn {
    rx: Receiver<GpioValue>,
    state: GpioValue,
}

impl TestGpioIn {
    /// Creates a new test input gpio pin.
    ///
    /// # Arguments
    ///
    /// * `rx` - An `mpsc::Receiver<GpioValue>` linked to an output pin.
    /// * `state` - State assumed before anything is received.
    pub fn new(rx: Receiver<GpioValue>, state: GpioValue) -> Self {
        Self { rx, state }
    }
}

impl GpioIn for TestGpioIn {
    /// This error is not used, this implementation will never return an error.
    type Error = io::Error;

    fn read_value(&mut self) -> Result<GpioValue, Self::Error> {
        let v = self.rx.try_recv().unwrap_or(self.state);
        self.state = v;
        Ok(v)
    }
}

/// Fake `GpioOut` for testing, a custom one rather than `DummyGpioOut` because
/// the provided one does not work very well over threads.
pub struct TestGpioOut {
    tx: Sender<GpioValue>,
}

impl TestGpioOut {
    /// Creates a new test output gpio pin.
    ///
    /// # Arguments
    ///
    /// * `rx` - An `mpsc::Sender<GpioValue>` linked to an input pin.
    pub fn new(tx: Sender<GpioValue>) -> Self {
        Self { tx }
    }
}

impl GpioOut for TestGpioOut {
    type Error = mpsc::SendError<GpioValue>;

    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.tx.send(GpioValue::Low)
    }

    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.tx.send(GpioValue::High)
    }
}

/// Represents a binary representation of data that can be send via serial.
pub type SerialData = (u64, u8);

#[cfg(test)]
mod tests {
    use super::{BitReceiver, BitSender, Client, Packet, Server, TestGpioIn, TestGpioOut};
    use gpio::GpioValue;
    use std::{f32, sync::mpsc, thread, time::Duration};

    #[test]
    pub fn serv_and_client() {
        let packets = [
            Packet::new((1u8, 255u8), 314u32),
            Packet::new((5u8, 255u8), f32::consts::PI.to_bits()),
        ];

        let (clock_tx, clock_rx) = mpsc::channel();
        let (data_tx, data_rx) = mpsc::channel();

        let mut server = Server::new(
            TestGpioIn::new(clock_rx, GpioValue::Low),
            TestGpioIn::new(data_rx, GpioValue::Low),
        );

        let mut client = Client::new(
            TestGpioOut::new(clock_tx),
            TestGpioOut::new(data_tx),
            Duration::from_millis(2),
        );

        for p in packets {
            client.send(p).unwrap();

            // This sleep is very important, since we need to wait for the
            // `Server` to get the packet and receive it from its own listening
            // thread.
            thread::sleep(Duration::from_millis(200));

            assert_eq!(p.get(), server.get(p.head).unwrap());
        }
    }

    #[test]
    pub fn send_and_recv() {
        let packets = [
            Packet::new((1u8, 255u8), 314u32),
            Packet::new((5u8, 255u8), f32::consts::PI.to_bits()),
        ];

        let (clock_tx, clock_rx) = mpsc::channel();
        let (data_tx, data_rx) = mpsc::channel();

        // Clones of the packets to be check against within the thread.
        let packets_recv = packets.clone();

        let handle = thread::spawn(move || -> Vec<Packet<(u8, u8), u32>> {
            let mut reciever = BitReceiver::new(
                TestGpioIn::new(clock_rx, GpioValue::High),
                TestGpioIn::new(data_rx, GpioValue::Low),
            );

            let mut packets: Vec<Packet<(u8, u8), u32>> = Vec::new();

            for p in packets_recv {
                packets.push(match reciever.recv(Packet::<(u8, u8), u32>::BITS as u8) {
                    Some(p) => match Packet::<(u8, u8), u32>::try_from(p) {
                        Ok(v) => v,
                        Err(_) => panic!("could not interperet packet from serial data"),
                    },
                    None => panic!("recieved none for {:?}", p),
                });
            }

            packets
        });

        // Two milliseconds could be a bit fast for some hardware, but even one
        // millisecond works for me so I'll leave it for now to speed up unit
        // test runs.
        let mut sender = BitSender::new(
            TestGpioOut::new(clock_tx),
            TestGpioOut::new(data_tx),
            Duration::from_millis(2),
        );

        sender.start().unwrap();

        for p in packets {
            // We ignore the error here because the `BitSender`, after each
            // piece of `SerialData` is sent, resets the pins to a "no read"
            // state. By the time this happens the `BitReceiver` has alreday
            // stopped listening and in this unit test, is dropped, causing the
            // `mpsc::Receiver` to drop as well, producing an error in the last
            // pin sets and this error is of no consequence to us.
            sender.send(p.into()).unwrap_or_default();
        }

        let read_packets = handle.join().unwrap();

        for i in 0..packets.len() {
            assert_eq!(packets[i].get(), read_packets[i].get());
        }
    }
}
