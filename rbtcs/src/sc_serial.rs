// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial::{BitReceiver, BitSender, ExtractionError, ExtractionResult, SerialData};
use gpio::{GpioIn, GpioOut};
use std::{
    sync::mpsc::{self, Receiver, SendError, Sender},
    thread,
    time::Duration,
};

/// Responisble for sending out commands to devices on a serial bus.
pub struct ScClient {
    tx: Sender<SerialData>,
}

impl ScClient {
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
    pub fn send<T, U>(&mut self, packet: ScPacket<T, U>) -> Result<T, SendError<SerialData>>
    where
        T: ScHeader,
        U: ScData,
    {
        self.tx.send(packet.into())?;
        Ok(packet.head)
    }
}

/// Responsible for recieving messages from the serial bus.
pub struct ScServer {
    rx: Receiver<SerialData>,
    backlog: Vec<ScPacket<u8, u32>>,
}

impl ScServer {
    /// Creates a new `Server` given already opened `GpioIn` implementations.
    pub fn new<T>(clock: T, data: T) -> Self
    where
        T: GpioIn + Send + 'static,
        <T as GpioIn>::Error: Send,
    {
        let (tx, rx) = mpsc::channel();

        thread::spawn(move || -> ! {
            let mut receiver = BitReceiver::new(clock, data);

            loop {
                if let Some(recv) = receiver.recv(ScPacket::<u8, u32>::BITS as u8) {
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
    pub fn get<T>(&mut self, head: T) -> Option<ScPacket<u8, u32>>
    where
        T: ScHeader,
    {
        while let Ok(s) = self.rx.try_recv() {
            if let Ok(p) = ScPacket::<u8, u32>::try_from(s) {
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ScPacket<T, U>
where
    T: ScHeader,
    U: ScData,
{
    pub head: T,
    pub data: U,
}

impl<T, U> ScPacket<T, U>
where
    T: ScHeader,
    U: ScData,
{
    pub const BITS: u32 = u8::BITS + u32::BITS;

    pub fn new(head: T, data: U) -> Self {
        ScPacket { head, data }
    }
}

impl<T, U> Into<SerialData> for ScPacket<T, U>
where
    T: ScHeader,
    U: ScData,
{
    fn into(self) -> SerialData {
        let head = self.head.get_shifted();
        let data = self.data.get() as u64;

        (0u64 | head | data, Self::BITS as u8)
    }
}

impl<T, U> TryFrom<SerialData> for ScPacket<T, U>
where
    T: ScHeader,
    U: ScData,
{
    type Error = ExtractionError;

    fn try_from(value: SerialData) -> Result<Self, Self::Error> {
        let (bits, size) = value;

        if size != Self::BITS as u8 {
            return Err(ExtractionError);
        }

        let head = (bits >> u32::BITS) as u8;
        let data = bits as u32;

        let packet = ScPacket::new(head, data);

        Ok(Self {
            head: T::extract(&packet)?,
            data: U::extract(&packet)?,
        })
    }
}

impl ScHeader for u8 {
    fn extract<T, U>(packet: &ScPacket<T, U>) -> ExtractionResult<Self>
    where
        T: ScHeader,
        U: ScData,
    {
        Ok(packet.head.get())
    }

    fn get(&self) -> u8 {
        *self
    }
}

impl ScData for u32 {
    fn extract<T, U>(packet: &ScPacket<T, U>) -> ExtractionResult<Self>
    where
        T: ScHeader,
        U: ScData,
    {
        Ok(packet.data.get())
    }

    fn get(&self) -> u32 {
        *self
    }
}

impl ScData for f32 {
    fn extract<T, U>(packet: &ScPacket<T, U>) -> ExtractionResult<Self>
    where
        T: ScHeader,
        U: ScData,
    {
        Ok(f32::from_bits(packet.data.get()))
    }

    fn get(&self) -> u32 {
        self.to_bits()
    }
}

pub trait ScHeader: Clone + Copy {
    const BITS: u32 = u8::BITS;

    fn extract<T, U>(packet: &ScPacket<T, U>) -> ExtractionResult<Self>
    where
        T: ScHeader,
        U: ScData;

    fn get(&self) -> u8;

    fn get_shifted(&self) -> u64 {
        let head = self.get();
        (head as u64) << u32::BITS
    }
}

pub trait ScData: Clone + Copy {
    const BITS: u32 = u32::BITS;

    fn extract<T, U>(packet: &ScPacket<T, U>) -> ExtractionResult<Self>
    where
        T: ScHeader,
        U: ScData;

    fn get(&self) -> u32;
}
