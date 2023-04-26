// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::{error::Error, fmt::Display, time};

/// Manages the running of a `Bot` implementation and keeps track of robot
/// state, serial, controllers, etc.
pub struct BotRunner<T>
where
    T: Bot,
{
    state: State,
    gilrs: gilrs::Gilrs,
    events: Vec<gilrs::Event>,
    bot: T,
}

impl<T> BotRunner<T>
where
    T: Bot,
{
    /// Creates a new `BotRunner` for running the given `Bot` implementation.
    /// The returned instance will have the state `State::Disabled` with a value
    /// of the time it was created.
    pub fn new(bot: T) -> Self {
        let mut gilrs = gilrs::Gilrs::new().unwrap();
        let mut events = Vec::new();

        while let Some(e) = gilrs.next_event() {
            events.push(e);
        }

        Self {
            state: State::Disabled(Some(time::Instant::now())),
            gilrs,
            events,
            bot,
        }
    }

    /// Runs the `Bot`, should be called in a loop. The behavior of this
    /// function changes based on the `Bot`'s `State`.
    pub fn run(&mut self) -> BotResult<()> {
        self.bot.run_base(self.state)?;
        self.events.clear();

        while let Some(e) = self.gilrs.next_event() {
            self.events.push(e);
        }

        match self.state {
            State::Enabled(_) => self.bot.run_enabled(self.events.as_slice()),
            State::Idling(_) => self.bot.run_idling(),
            State::Disabled(_) => self.bot.run_disabled(),
            State::Emergency(_) => self.bot.run_emergency(),
        }
    }

    /// Sets the `Bot`'s state to the given, and if the given `State` has a
    /// parameter of `None` populates it with the current time.
    pub fn set_state(&mut self, state: State) {
        let now_if_none = |t| match t {
            Some(_) => t,
            None => Some(time::Instant::now()),
        };

        self.state = match state {
            State::Enabled(t) => State::Enabled(now_if_none(t)),
            State::Idling(t) => State::Idling(now_if_none(t)),
            State::Disabled(t) => State::Disabled(now_if_none(t)),
            State::Emergency(t) => State::Emergency(now_if_none(t)),
        }
    }
}

/// Represents the custom struct that holds the custom code for running a bot.
/// All default implementations of function simply do nothing.
pub trait Bot {
    /// Always runs except in an emergency state, should manage simple things
    /// like LED lights or cameras that dont cause a danger or potential harm
    /// when active.
    ///
    /// # Arguments
    ///
    /// * `state` - The `Bot`'s current state with a value of the time that
    /// state was set.
    fn run_base(&mut self, state: State) -> BotResult<()> {
        Ok(())
    }

    /// Fully operational state, should hold controller input, motor setting,
    /// and other physical operations.
    ///
    /// # Arguments
    ///
    /// * `events` - Gilrs controller events used for controller input.
    fn run_enabled(&mut self, events: &[gilrs::Event]) -> BotResult<()> {
        Ok(())
    }

    /// Can operate any component of the robot but without controller input.
    fn run_idling(&mut self) -> BotResult<()> {
        Ok(())
    }

    /// May not operate physically moving devices.
    fn run_disabled(&mut self) -> BotResult<()> {
        Ok(())
    }

    /// Run as little as possible, this mode is only used if something has gone
    /// very, very wrong.
    fn run_emergency(&mut self) -> BotResult<()> {
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

pub type BotResult<T> = Result<T, BotError>;

#[derive(Clone, Copy, Debug)]
pub struct BotError;

impl Error for BotError {}

impl Display for BotError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "error occured running bot")
    }
}
