// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use gpio::{
    sysfs::{SysFsGpioInput, SysFsGpioOutput},
    GpioIn, GpioOut, GpioValue,
};
pub use header_derive::Header;
use std::{
    io, mem,
    sync::mpsc::{channel, SendError, Sender},
    thread,
};

/// Responisble for sending out commands to devices on a serial bus.
pub struct Client {
    tx: Sender<BinaryData>,
}

impl Client {
    /// Creates a new serial client given the clock and data pins to use as a
    /// serial bus.
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16) -> io::Result<Self> {
        let (tx, rx) = channel();
        let mut sender = BitSender::new(clock_pin, data_pin)?;

        thread::spawn(move || -> io::Result<()> {
            loop {
                let packet: BinaryData = match rx.recv() {
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

    /// Queues a packet for sending on the client thread. An `Err` value from
    /// this function means that the `Client` instance's thread has returned
    /// with an error, which would suggest that an `io::Error` has occured
    /// internally.
    pub fn send<T>(&mut self, packet: Packet<T>) -> Result<(), SendError<BinaryData>>
    where
        T: Header,
    {
        self.tx.send(packet.to_binary())?;
        Ok(())
    }
}

/// Responsible for recieving messages from the serial bus.
pub struct Server {
    reciever: BitReciever,
}

impl Server {
    /// Instantiants a new `Server` given the clock and data pins of the serial
    /// bus to read from.
    #[inline]
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16) -> io::Result<Self> {
        Ok(Self {
            reciever: BitReciever::new(clock_pin, data_pin)?,
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
    pub fn listen_for<T: Header>(&mut self, head: &T, data_type: Data) -> io::Result<Data> {
        let recieved_packet = self.reciever.recieve()?;

        // Since all recived data is made by request we should be recieving
        // exactly the listened for header, anything else is an error.
        if recieved_packet.head.addr() != head.addr() || recieved_packet.head.cmd() != head.cmd() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "recieved header did not match one provided",
            ));
        }

        Ok(recieved_packet.data.to_type(&data_type))
    }

    /// Listens for packets with all given heads in order, returns an error if
    /// any packet comes with the wrong header or in the wrong order.
    ///
    /// # Arguments
    ///
    /// * `heads` - A slice of `Header`s in the order the are expect to come.
    /// * `data_type` - Enum variant of `Data` to return.
    pub fn listen_for_sequence<T>(&mut self, heads: &[T], data_type: Data) -> io::Result<Vec<Data>>
    where
        T: Header,
    {
        let mut data = vec![Data::UnsignedInteger(0); heads.len()];

        for h in heads {
            data.push(self.listen_for(h, data_type)?);
        }

        Ok(data)
    }
}

/// While the clock pin is high no device should read bits, when clock is low
/// the `BitSender` will not change the value of the data pin and it may be
/// read. While not sending data the `BitSender` will set clock high and data
/// will be held at low, if data moves up while clock is up it will signal the
/// start of a new packet, this does not mean that double up is the start state,
/// only that change from data while clock is up is, they should change at the
/// same time. All devices will also wait for 48 bits to be sent, upon which
/// they will assume the next bit is of a new packet.
struct BitSender {
    clock: SysFsGpioOutput,
    data: SysFsGpioOutput,
}

impl BitSender {
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16) -> io::Result<Self> {
        Ok(Self {
            clock: SysFsGpioOutput::open(clock_pin)?,
            data: SysFsGpioOutput::open(data_pin)?,
        })
    }

    /// Puts pins in their default "waiting" state, should be preformed after
    /// construction in most case.
    pub fn start(&mut self) -> io::Result<()> {
        self.clock.set_high()?;
        self.data.set_low()?;
        Ok(())
    }

    /// Sends the binary representation of the given data.
    pub fn send<T: ToBinary>(&mut self, data: T) -> io::Result<u8> {
        let (bits, bits_length) = data.to_binary();

        // Signal data begin with both pins high.
        self.clock.set_high()?;
        self.data.set_high()?;

        for i in 0..bits_length {
            let bit = bits >> i & 1 != 0;

            // Set low to allow reading and set bit.
            self.clock.set_low()?;
            self.data.set_value(bit)?;

            // TODO: This may need to be throttled.
            self.clock.set_high()?;
        }

        // Go back to waiting and return.
        self.start()?;
        Ok(bits_length)
    }
}

/// Struct for recieving bits on a serial bus, since the instance belongs to the
/// controller device all addresses in packets are the address of the sending
/// device, not the recipiant.
struct BitReciever {
    clock: SysFsGpioInput,
    data: SysFsGpioInput,
}

impl BitReciever {
    /// Produces a new `BitReciever` given the clock and data pins to read from.
    pub fn new(clock_pin: u16, data_pin: u16) -> io::Result<Self> {
        Ok(Self {
            clock: SysFsGpioInput::open(clock_pin)?,
            data: SysFsGpioInput::open(data_pin)?,
        })
    }

    /// Waits for the start signal and then reads a number of bits equal to
    /// `Packet::<GenericHeader>::BITS` and produces a new packet from them. All
    /// packets returned from this function are of type `Packet<GenericHeader>`
    /// and must have their data and headers cast to fully recover the packet's
    /// information, furthermore all addresses are of the sending device as even
    /// when recieving this remains the controller device and has no address.
    pub fn recieve(&mut self) -> io::Result<Packet<GenericHeader>> {
        // Wait until we see a change from clock high data low.
        while self.clock.read_value()? == GpioValue::High
            && self.data.read_value()? == GpioValue::Low
        {}

        // The start of a read is stated with clock high data high, if this is
        // not the state after a no-read segment something's gone wrong.
        if !(self.clock.read_value()? == GpioValue::High
            && self.data.read_value()? == GpioValue::High)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid serial state",
            ));
        }

        let mut packet_bits = 0u64;

        // Read the packet, each new bit gets placed in the ones digit and then
        // shifted over.
        for _ in 0..Packet::<GenericHeader>::BITS {
            // On the first loop this does nothing.
            packet_bits <<= 1;

            while self.clock.read_value()? == GpioValue::High {}

            // OR in our new bit, if its zero then its already there.
            if self.data.read_value()? == GpioValue::High {
                packet_bits |= 1u64;
            }
        }

        Ok(Packet::from_binary(packet_bits))
    }
}

/// Packet data, always a 32 bit size but can be of floating point, signed
/// integral, or unsigned integral types. Exactly how this information is used
/// is up to the receiving device and its controlling instance but if possible
/// all auxillary information should be stored in the tag and whatever is
/// contained in the data portion of the packet should be interpretable as a
/// single number.
#[derive(Clone, Copy, Debug)]
pub enum Data {
    FloatingPoint(f32),
    SignedInteger(i32),
    UnsignedInteger(u32),
}

impl Data {
    /// Size of any value from a `Data` enum in bytes, does not reflect actual
    /// memory required for storing the enum, only its value, which is always 32
    /// bit.
    pub const SIZE: usize = mem::size_of::<u32>();

    /// Size of any value from a `Data` enum in bits, does not reflect actual
    /// memory required for storing the enum, only its value, which is always 32
    /// bit.
    pub const BITS: u32 = u32::BITS;

    /// Converts `self` to data of type `other`, the value of `other` is
    /// ignored. All conversion are bitwise and preserve the underlying data to
    /// help facilitate data recovery over serial.
    ///
    /// # Arguments
    ///
    /// * `self` - The data value to be converted.
    /// * `other` - Enum with the type to be converted to.
    pub fn to_type(&self, other: &Self) -> Self {
        match other {
            Self::FloatingPoint(_) => match self {
                Self::FloatingPoint(_) => *self,
                Self::SignedInteger(n) => Self::FloatingPoint(f32::from_bits(*n as u32)),
                Self::UnsignedInteger(n) => Self::FloatingPoint(f32::from_bits(*n)),
            },

            Self::SignedInteger(_) => match self {
                Self::FloatingPoint(n) => Self::SignedInteger(n.to_bits() as i32),
                Self::SignedInteger(_) => *self,
                Self::UnsignedInteger(n) => Self::SignedInteger(*n as i32),
            },

            Self::UnsignedInteger(_) => match self {
                Self::FloatingPoint(n) => Self::UnsignedInteger(n.to_bits()),
                Self::SignedInteger(n) => Self::UnsignedInteger(*n as u32),
                Self::UnsignedInteger(_) => *self,
            },
        }
    }
}

impl Into<f32> for Data {
    fn into(self) -> f32 {
        match self {
            Self::FloatingPoint(n) => n,
            _ => panic!("not a floating point number"),
        }
    }
}

impl Into<i32> for Data {
    fn into(self) -> i32 {
        match self {
            Self::SignedInteger(n) => n,
            _ => panic!("not a signed integer"),
        }
    }
}

impl Into<u32> for Data {
    fn into(self) -> u32 {
        match self {
            Self::UnsignedInteger(n) => n,
            _ => panic!("not an unsigned integer"),
        }
    }
}

impl ToBinary for Data {
    /// `to_binary()` will always be a number of bits equal to `Data::BITS` and
    /// can be cast to a `u32` without the loss of data.
    fn to_binary(&self) -> BinaryData {
        match self {
            Self::FloatingPoint(n) => (n.to_bits() as u64, Self::BITS as u8),
            Self::SignedInteger(n) => (*n as u64, Self::BITS as u8),
            Self::UnsignedInteger(n) => (*n as u64, Self::BITS as u8),
        }
    }
}

impl FromBinary for Data {
    /// `from_binary()` will return a `Data::UnsignedInteger`, this will have to
    /// be cast based on data from a packet header in order to recover the
    /// actual packet data.
    fn from_binary(bits: u64) -> Self {
        Self::UnsignedInteger(bits as u32)
    }
}

/// Represents a single addressed packet for the serial bus where T is the type
/// of tag being used, this must implement the `Header` trait.
pub struct Packet<T: Header> {
    // TODO: access to fields.
    head: T,
    data: Data,
}

impl<T: Header> Packet<T> {
    /// Number of bits in each packet as sent over serial, does not reflect
    /// actual size in computer memory which is made different by alignment and
    /// tag information stored in enums.
    pub const BITS: u32 = (mem::size_of::<u8>() * 2 * 8) as u32 + Data::BITS;

    /// Creates a new packet, for a device at the given address, in which all
    /// type and handling information is contained in `tag`, and all data can be
    /// found in the `data` parameter.
    #[must_use]
    pub fn new(tag: T, data: Data) -> Self {
        Self { head: tag, data }
    }
}

impl FromBinary for Packet<GenericHeader> {
    fn from_binary(bits: u64) -> Self {
        Self {
            head: GenericHeader::from_binary(bits >> Data::BITS),
            data: Data::from_binary(bits),
        }
    }
}

impl<T: Header> ToBinary for Packet<T> {
    /// Every return value of `to_bits()` for `Packet` will have a second value
    /// equal to `Packet::<T>::BITS`.
    fn to_binary(&self) -> BinaryData {
        let (data, data_bits) = self.data.to_binary();
        let head = self.head.to_binary().0 << data_bits;

        (0u64 | head | data, Self::BITS as u8)
    }
}

/// Generic header used mostly for returning data recieved from the serial bus.
#[derive(Header)]
pub struct GenericHeader {
    pub addr: u8,
    pub cmd: u8,
}

impl FromBinary for GenericHeader {
    fn from_binary(bits: u64) -> Self {
        Self {
            addr: (bits >> u8::BITS) as u8,
            cmd: bits as u8,
        }
    }
}

/// Trait for representing a packet tag, used for distinguishing different
/// commands, data types, etc. and used for addressing data to a specific
/// device.
///
/// ## Derivable
///
/// Deriving this trait will implement it's required functions so that they
/// return a feild of the same name.
///
/// ```
/// use mecanum::serial::Header;
///
/// #[derive(Header)]
/// struct MyHeader {
///     addr: u8,
///     cmd: u8,   
/// }
/// ```
pub trait Header {
    /// The number of bits taken up by any header's address and command.
    const BITS: u32 = u8::BITS * 2;

    /// Gets the address of the tag, this will be checked by all devices on the
    /// bus and be used to determine which device should utilise the rest of the
    /// packet.
    fn addr(&self) -> u8;

    /// Gets the command of the tag, should be used to denote type information
    /// and instruct the device on how to utilize the packet's data. The
    /// definition of exactly what this means is up to the device and controller
    /// implementation.
    fn cmd(&self) -> u8;
}

impl<T: Header> ToBinary for T {
    fn to_binary(&self) -> BinaryData {
        let addr: u64 = (self.addr() as u64) << u8::BITS;
        let cmd: u64 = self.cmd() as u64;

        (0u64 | addr | cmd, Self::BITS as u8)
    }
}

impl ToBinary for BinaryData {
    fn to_binary(&self) -> BinaryData {
        *self
    }
}

/// Represents a binary representation of data.
type BinaryData = (u64, u8);

/// Represents an object that can be converted to a binary representation.
pub trait ToBinary {
    /// Converts `self` to its binary representation in a tuple where the first
    /// item is the binary data, and the second is the number of bits, starting
    /// from the right, that are part of the binary representation.
    ///
    /// # Examples (First element in binary)
    /// 8 -> (...1000, 4)
    /// 3 -> (...11, 2)
    /// 3 -> (...00000011, 8)
    ///
    /// Note that all of these are valid, so long as the number of buts required
    /// to represent the object is equal to the value of the second item. Any
    /// return value in which the second item is greator than the number of bits
    /// in the first is necessarily invalid.
    #[must_use]
    fn to_binary(&self) -> BinaryData;
}

/// Represents an object that can be constructed from its binary representation.
pub trait FromBinary {
    /// Produces a new `Self` object given a 64 bit binary representation. This
    /// should be symmetrical with `ToBinary`'s `to_binary()` method if it is
    /// also implemented.
    #[must_use]
    fn from_binary(bits: u64) -> Self;
}
