// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial;
use gpio::{
    sysfs::{SysFsGpioInput, SysFsGpioOutput},
    GpioOut,
};
use std::{
    error::Error,
    fmt::{Debug, Display},
    io, time,
};

/// Checks an `Option<time::Instant>`, if its a `Some` variant then its value is
/// returned, otherwise if its variant is `None` then `time::Instant::now()` is
/// returned.
macro_rules! now_if_none {
    ($t:expr) => {
        match $t {
            None => std::time::Instant::now(),
            Some(t) => t,
        }
    };
}

/// Manages the running of a `Bot` implementation and keeps track of robot
/// state, serial, controllers, etc.
pub struct BotRunner<T, U>
where
    T: Bot,
{
    state: State,
    gilrs: gilrs::Gilrs,
    relay: U,
    serial_tx: serial::Client,
    serial_rx: serial::Server,
    bot: T,
}

impl<T, U> BotRunner<T, U>
where
    T: Bot + Send,
    U: GpioOut + Send + 'static,
    <U as GpioOut>::Error: Debug + Send,
{
    /// Starts a loop calling `BotRunner::run()`.
    #[inline]
    pub fn start(&mut self) {
        loop {
            self.run();
        }
    }

    /// Runs the `Bot`, should be called in a loop. The behavior of this
    /// function changes based on the `Bot`'s `State`. If any of the `Bots`'s
    /// functions return an `Err` variant then the robot state will become
    /// `State::Emergency` with the time of the error as the value.
    ///
    /// If you dont need to intervene between loop iterations you could simply
    /// call `BotRunner::start()` as well.
    pub fn run(&mut self) {
        // this probably qualifies as abuse of rust's match statements/closures
        // but i also love how absolutely stupid this is while also being kinda
        // awesome at the same time.

        let base_state = match self.state {
            State::Emergency(t) => {
                self.relay
                    .set_low()
                    .expect("relay pin should not fail to set ");
                self.bot
                    .run_emergency(t.unwrap_or(time::Instant::now()))
                    .expect("errors in emergency should not occure");
                return;
            }
            _ => {
                self.relay
                    .set_high()
                    .expect("relay pin should not fail to set");
                self.bot
                    .run_base(self.state, &mut self.serial_tx, &mut self.serial_rx)
                    .unwrap_or(State::Emergency(Some(time::Instant::now())))
            }
        };

        self.state = match match base_state {
            State::Enabled(t) => self.bot.run_enabled(
                t.unwrap_or(time::Instant::now()),
                &mut self.gilrs,
                &mut self.serial_tx,
                &mut self.serial_rx,
            ),
            State::Idling(t) => self.bot.run_idling(
                t.unwrap_or(time::Instant::now()),
                &mut self.serial_tx,
                &mut self.serial_rx,
            ),
            State::Disabled(t) => self.bot.run_disabled(
                t.unwrap_or(time::Instant::now()),
                &mut self.serial_tx,
                &mut self.serial_rx,
            ),
            State::Emergency(t) => self.bot.run_emergency(t.unwrap_or(time::Instant::now())),
        } {
            Ok(s) => s,
            Err(_) => {
                self.relay
                    .set_low()
                    .expect("relay pin should not fail to set ");
                State::Emergency(Some(time::Instant::now()))
            }
        };
    }

    /// Sets the `Bot`'s state to the given, and if the given `State` has a
    /// parameter of `None` populates it with the current time.
    #[inline]
    pub fn set_state(&mut self, state: State) {
        self.state = match state {
            State::Enabled(t) => State::Enabled(Some(now_if_none!(t))),
            State::Idling(t) => State::Idling(Some(now_if_none!(t))),
            State::Disabled(t) => State::Disabled(Some(now_if_none!(t))),
            State::Emergency(t) => State::Emergency(Some(now_if_none!(t))),
        }
    }
}

impl<T> BotRunner<T, SysFsGpioOutput>
where
    T: Bot,
{
    /// Creates a new `BotRunner` for running the given `Bot` implementation.
    /// The returned instance will have the state `State::Disabled` with a value
    /// of the time it was created.
    #[must_use]
    pub fn new(bot: T) -> io::Result<Self> {
        Ok(Self {
            state: State::Disabled(Some(time::Instant::now())),
            gilrs: gilrs::Gilrs::new().unwrap(),
            relay: SysFsGpioOutput::open(T::RELAY_PIN)?,
            serial_tx: serial::Client::new(
                SysFsGpioOutput::open(T::TX_CLOCK)?,
                SysFsGpioOutput::open(T::TX_DATA)?,
                T::SERIAL_CYCLE,
            ),
            serial_rx: serial::Server::new(
                SysFsGpioInput::open(T::RX_CLOCK)?,
                SysFsGpioInput::open(T::RX_DATA)?,
            ),
            bot,
        })
    }
}

/// Represents the custom struct that holds the custom code for running a bot.
/// All default implementations of function simply do nothing.
pub trait Bot {
    /// Clock pin for transmitting serial data.
    const TX_CLOCK: u16;

    /// Data pin for transmitting serial data.
    const TX_DATA: u16;

    /// Clock pin for receiving serial data.
    const RX_CLOCK: u16;

    /// Data pin for receiving serial data.
    const RX_DATA: u16;

    /// Pin to the relay with control over device power. Since this is a safety
    /// measure when the pin is low it should disallow power to the devices, for
    /// the same reason if this pin ever fails to set the program will panic.
    const RELAY_PIN: u16;

    /// Time between each bit on serial transmission.
    const SERIAL_CYCLE: time::Duration;

    /// Always runs except in an emergency state, should manage simple things
    /// like LED lights or cameras that dont cause a danger or potential harm
    /// when active.
    ///
    /// # Arguments
    ///
    /// * `state` - The `Bot`'s current state with a value of the time that
    /// state was set.
    /// * `serial_tx` - `serial::Client` for sending serial data.
    /// * `serial_rx` - `serial::Server<T>` for receiving serial data.
    #[allow(unused_variables)]
    fn run_base(
        &mut self,
        state: State,
        serial_tx: &mut serial::Client,
        serial_rx: &mut serial::Server,
    ) -> BotResult<State> {
        Ok(state)
    }

    /// Fully operational state, should hold controller input, motor setting,
    /// and other physical operations.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    /// * `events` - Gilrs controller events used for controller input.
    /// * `serial_tx` - `serial::Client` for sending serial data.
    /// * `serial_rx` - `serial::Server<T>` for receiving serial data.
    ///
    /// # Returns
    ///
    /// Should return a `State` holding the time passed into the function. An
    /// `Err` return variant will change the state to emergency.
    #[allow(unused_variables)]
    fn run_enabled(
        &mut self,
        time: time::Instant,
        gp_inputs: &mut gilrs::Gilrs,
        serial_tx: &mut serial::Client,
        serial_rx: &mut serial::Server,
    ) -> BotResult<State> {
        Ok(State::Enabled(Some(time)))
    }

    /// Can operate any component of the robot but without controller input.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    /// * `serial_tx` - `serial::Client` for sending serial data.
    /// * `serial_rx` - `serial::Server<T>` for receiving serial data.
    ///
    /// # Returns
    ///
    /// Should return a `State` holding the time passed into the function. An
    /// `Err` return variant will change the state to emergency.
    #[allow(unused_variables)]
    fn run_idling(
        &mut self,
        time: time::Instant,
        serial_tx: &mut serial::Client,
        serial_rx: &mut serial::Server,
    ) -> BotResult<State> {
        Ok(State::Idling(Some(time)))
    }

    /// May not operate physically moving devices.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    /// * `serial_tx` - `serial::Client` for sending serial data.
    /// * `serial_rx` - `serial::Server<T>` for receiving serial data.
    ///
    /// # Returns
    ///
    /// Should return a `State` holding the time passed into the function. An
    /// `Err` return variant will change the state to emergency.
    #[allow(unused_variables)]
    fn run_disabled(
        &mut self,
        time: time::Instant,
        serial_tx: &mut serial::Client,
        serial_rx: &mut serial::Server,
    ) -> BotResult<State> {
        Ok(State::Disabled(Some(time)))
    }

    /// Run as little as possible, this mode is only used if something has gone
    /// very, very wrong.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    ///
    /// # Returns
    ///
    /// Should return a `State` holding the time passed into the function. An
    /// `Err` return variant will change the state to emergency.
    #[allow(unused_variables)]
    fn run_emergency(&mut self, time: time::Instant) -> BotResult<State> {
        Ok(State::Emergency(Some(time)))
    }
}

/// Represents a potential state of a `Bot` instance. All variants hold a value
/// of `Option<time::Instant>` which will be populated with
/// `Some(time::Instant::now())` once they are used to set the state of a `Bot`
/// instance.
#[derive(Clone, Copy)]
pub enum State {
    /// Serial controlled devices are enabled and the bot is under driver
    /// control.
    Enabled(Option<time::Instant>),

    /// Serial controlled devices are enabled but the bot is only under self
    /// control.
    Idling(Option<time::Instant>),

    /// Serial devices are disabled. Some serial devices may be enabled if their
    /// operation does not pose a risk, e.g. LED lights.
    Disabled(Option<time::Instant>),

    /// Non-computing devices are power off forcefully by switching a relay on
    /// their power rail. In this state only micro-controllers and computers are
    /// granted power.
    Emergency(Option<time::Instant>),
}

/// Represents the result of a loop or "run" function related to the `Bot` trait
/// or `BotRunner` struct.
pub type BotResult<T> = Result<T, BotError>;

/// Represents an error that can occure within a loop or "run" function related
/// to the `Bot` trait or `BotRunner` struct.
#[derive(Clone, Debug)]
pub struct BotError {
    pub msg: String,
}

impl BotError {
    pub fn new(msg: String) -> Self {
        Self { msg }
    }
}

impl Error for BotError {}

impl Display for BotError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "error occured running bot")
    }
}

/// Represents a GP I/O result that can occure for I/O operations related to a
/// `Bot` implementation or the `BotRunner`.
pub type BotGpioResult<T> = Result<T, BotGpioError>;

/// Represents a GP I/O error that can occure for I/O operations related to a
/// `Bot` implementation or the `BotRunner`.
#[derive(Clone, Copy, Debug)]
pub struct BotGpioError;

impl Error for BotGpioError {}

impl Display for BotGpioError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "error instantiating or utilising GP I/O from `Bot`")
    }
}
