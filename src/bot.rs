// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use gpio::GpioOut;
use mecanum::serial;
use std::{error::Error, fmt::Display, time};

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
    T: Bot<U>,
    U: GpioOut,
{
    state: State,
    gilrs: gilrs::Gilrs,
    events: Vec<gilrs::Event>,
    relay: U,
    serial_tx: serial::Client,
    serial_rx: serial::Server,
    bot: T,
}

impl<T, U> BotRunner<T, U>
where
    T: Bot<U>,
    U: GpioOut,
{
    /// Creates a new `BotRunner` for running the given `Bot` implementation.
    /// The returned instance will have the state `State::Disabled` with a value
    /// of the time it was created.
    #[must_use]
    pub fn new(bot: T, cycle: Duration) -> Result<Self, U::Error> {
        let mut gilrs = gilrs::Gilrs::new().unwrap();
        let mut events = Vec::new();

        while let Some(e) = gilrs.next_event() {
            events.push(e);
        }

        Ok(Self {
            state: State::Disabled(Some(time::Instant::now())),
            gilrs,
            events,
            relay: T::open_pin(T::RELAY_PIN)?,
            serial_tx: serial::Client::new(
                T::open_pin(T::TX_CLOCK),
                T::open_pin(T::TX_DATA),
                cycle,
            ),
            serial_rx: serial::Server::new(T::open_pin(T::RX_CLOCK), T::open_pin(T::RX_DATA)),
            bot,
        })
    }

    /// Starts a loop calling `BotRunner::run()`.
    #[inline]
    pub fn start(&mut self) {
        loop {
            self.run()
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

        match || -> BotResult<()> {
            Ok(match self.state {
                State::Enabled(t) => {
                    self.events.clear();

                    // Get new controller events for enabled mode.
                    while let Some(e) = self.gilrs.next_event() {
                        self.events.push(e);
                    }

                    self.bot.run_base(self.state)?;
                    self.bot
                        .run_enabled(now_if_none!(t), self.events.as_slice())?;
                }

                State::Idling(t) => {
                    self.bot.run_base(self.state)?;
                    self.bot.run_idling(now_if_none!(t))?;
                }

                State::Disabled(t) => {
                    self.bot.run_base(self.state)?;
                    self.bot.run_disabled(now_if_none!(t))?;
                }

                State::Emergency(t) => {
                    self.bot.run_emergency(now_if_none!(t))?;
                }
            })
        }() {
            Ok(_) => (),
            Err(_) => {
                self.state = State::Emergency(Some(time::Instant::now()));
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

/// Represents the custom struct that holds the custom code for running a bot.
/// All default implementations of function simply do nothing.
pub trait Bot<T>
where
    T: GpioOut,
{
    /// Clock pin for transmitting serial data.
    const TX_CLOCK: u16;

    /// Data pin for transmitting serial data.
    const TX_DATA: u16;

    /// Clock pin for receiving serial data.
    const RX_CLOCK: u16;

    /// Data pin for receiving serial data.
    const RX_DATA: u16;

    /// Pin to the relay with controll over device power.
    const RELAY_PIN: u16;

    /// Open a pin of whatever type this `Bot` utilises.
    fn open_pin(n: u16) -> Result<T, T::Error>;

    /// Always runs except in an emergency state, should manage simple things
    /// like LED lights or cameras that dont cause a danger or potential harm
    /// when active.
    ///
    /// # Arguments
    ///
    /// * `state` - The `Bot`'s current state with a value of the time that
    /// state was set.
    #[allow(unused_variables)]
    fn run_base(&mut self, state: State) -> BotResult<()> {
        Ok(())
    }

    /// Fully operational state, should hold controller input, motor setting,
    /// and other physical operations.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    /// * `events` - Gilrs controller events used for controller input.
    #[allow(unused_variables)]
    fn run_enabled(&mut self, time: time::Instant, events: &[gilrs::Event]) -> BotResult<()> {
        Ok(())
    }

    /// Can operate any component of the robot but without controller input.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    #[allow(unused_variables)]
    fn run_idling(&mut self, time: time::Instant) -> BotResult<()> {
        Ok(())
    }

    /// May not operate physically moving devices.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    #[allow(unused_variables)]
    fn run_disabled(&mut self, time: time::Instant) -> BotResult<()> {
        Ok(())
    }

    /// Run as little as possible, this mode is only used if something has gone
    /// very, very wrong.
    ///
    /// # Arguments
    ///
    /// * `time` - The time that the current `State` was set.
    #[allow(unused_variables)]
    fn run_emergency(&mut self, time: time::Instant) -> BotResult<()> {
        Ok(())
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
#[derive(Clone, Copy, Debug)]
pub struct BotError;

impl Error for BotError {}

impl Display for BotError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "error occured running bot")
    }
}
