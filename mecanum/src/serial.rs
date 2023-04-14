// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use gpio::{sysfs::SysFsGpioOutput, GpioOut};
pub use header_derive::Header;
use std::{
    io, mem,
    sync::{
        atomic::{self, AtomicBool},
        Arc, RwLock,
    },
    thread,
};

/// Responisble for sending out commands to devices on a serial bus.
pub struct Client {
    sender: Arc<RwLock<BitSender>>,
    is_sent: Arc<RwLock<AtomicBool>>,
    packets: Arc<RwLock<Vec<(u64, u8)>>>,
    queue: Vec<(u64, u8)>,
}

impl Client {
    /// Creates a new serial client given the clock and data pins to use as a
    /// serial bus.
    #[must_use]
    pub fn new(clock_pin: u16, data_pin: u16) -> io::Result<Self> {
        let mut sender = BitSender::new(clock_pin, data_pin)?;
        sender.start()?;

        Ok(Self {
            sender: Arc::new(RwLock::new(sender)),
            is_sent: Arc::new(RwLock::new(AtomicBool::new(false))),
            packets: Arc::new(RwLock::new(Vec::new())),
            queue: Vec::new(),
        })
    }

    /// Queues a packet for sending, no packets will be sent until the queue is
    /// buffered.
    pub fn queue_packet<T: Header>(&mut self, packet: Packet<T>) {
        self.queue.push(packet.to_bits());
    }

    /// Buffers the queue so that it will be sent, this will block the current
    /// thread if the previous buffer has not been completely sent.
    pub fn buffer_queue(&mut self) {
        let mut vec = self.packets.write().unwrap();

        // Wait for remaining packets to be sent before swapping the packets to
        // be sent and the queue. This thread block is fine, if not actually
        // bennificial as we dont want our main thread to fall out of syn with
        // the serial sending thread, which would cause a growing latency in any
        // inputs.
        while !self.is_sent.read().unwrap().load(atomic::Ordering::Relaxed) {}
        mem::swap(&mut self.queue, &mut vec);

        // Mark that the new buffer has not been, and should be, sent.
        self.is_sent
            .write()
            .unwrap()
            .store(false, atomic::Ordering::Relaxed);

        self.queue.clear();
    }

    /// Starts the serial client, this begins a new thread that will
    /// continually check for and send newly buffered packets.
    pub fn start(&self) -> thread::JoinHandle<io::Result<()>> {
        let sender = self.sender.clone();
        let is_sent = self.is_sent.clone();
        let vec = self.packets.clone();

        thread::spawn(move || {
            let mut sender = sender.write().unwrap();
            let vec = vec.write().unwrap();
            let is_sent = is_sent.write().unwrap();

            loop {
                // Wait until we get some new packets.
                if !is_sent.load(atomic::Ordering::Relaxed) {
                    continue;
                }

                let iter = vec.iter();

                for packet in iter {
                    sender.send(*packet)?;
                }

                // Signal that we have finished sending this queue.
                is_sent.store(true, atomic::Ordering::Relaxed);
            }
        })
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
        let (bits, bits_length) = data.to_bits();

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

/// Packet data, always a 32 bit size but can be of floating point, signed
/// integral, or unsigned integral types. Exactly how this information is used
/// is up to the receiving device and its controlling instance but if possible
/// all auxillary information should be stored in the tag and whatever is
/// contained in the data portion of the packet should be interpretable as a
/// single number.
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
}

impl ToBinary for Data {
    /// `to_bits()` will always be a number of bits equal to `Data::BITS` and
    /// can be cast to a `u32` without the loss of data.
    #[must_use]
    fn to_bits(&self) -> (u64, u8) {
        match self {
            Self::FloatingPoint(n) => (n.to_bits() as u64, Self::BITS as u8),
            Self::SignedInteger(n) => (*n as u64, Self::BITS as u8),
            Self::UnsignedInteger(n) => (*n as u64, Self::BITS as u8),
        }
    }
}

/// Represents a single addressed packet for the serial bus where T is the type
/// of tag being used, this must implement the `Header` trait.
pub struct Packet<T: Header> {
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

impl<T: Header> ToBinary for Packet<T> {
    /// Every return value of `to_bits()` for `Packet` will have a second value
    /// equal to `Packet::<T>::BITS`.
    fn to_bits(&self) -> (u64, u8) {
        let (data, data_bits) = self.data.to_bits();
        let head = self.head.to_bits().0 << data_bits;

        (0u64 | head | data, Self::BITS as u8)
    }
}

/// Trait for representing a packet tag, used for distinguishing different
/// commands, data types, etc. and used for addressing data to a specific
/// device.
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
    fn to_bits(&self) -> (u64, u8) {
        let addr: u64 = (self.addr() as u64) << u8::BITS;
        let cmd: u64 = self.cmd() as u64;

        (0u64 | addr | cmd, Self::BITS as u8)
    }
}

impl ToBinary for (u64, u8) {
    fn to_bits(&self) -> (u64, u8) {
        *self
    }
}

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
    fn to_bits(&self) -> (u64, u8);
}
