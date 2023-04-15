// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::{
    fs,
    io::{self, Write},
};

#[macro_export]
macro_rules! ok_or_log {
    ($log:expr, $result:expr) => {
        match $result {
            Ok(_) => {}
            Err(err) => {
                $log.log(log::Line::Err(err.to_string())).ok();
            }
        }
    };
}

/// For logging messages of varying severity.
pub struct Logger {
    displaying: Line,
    file: fs::File,
}

impl Logger {
    /// Creates a new logger, returns an error on I/O errors in creating/opening
    /// the given file path for writing.
    #[must_use]
    pub fn new(file_path: &str) -> io::Result<Self> {
        Ok(Self {
            displaying: Line::Info(String::new()),
            file: fs::File::create(file_path)?,
        })
    }

    /// Outputs the given line to standard out or standard error as is
    /// appropriate and records the line in the log file assuming that the given
    /// line variant meets or exceed the displaying severity. This file is
    /// written to directly so that in the case of a panic the log file need
    /// not be written to in order to have relevant contents.
    pub fn log(&mut self, line: Line) -> io::Result<()> {
        self.file.write(line.to_string().as_bytes())?;

        if self.displaying.severity() > line.severity() {
            return Ok(());
        }

        match line {
            Line::Err(_) => eprintln!("{}", line.to_string()),
            _ => println!("{}", line.to_string()),
        }

        Ok(())
    }

    /// Set the type of log messages to display to the console through either
    /// standard error or standard out. All messages in lesser severity to the
    /// one given will also be displayed, meaning that given `Line::Warn` all
    /// `Line::Warn` and all `Line::Err` messages will be printed. This function
    /// has no effect on what is recorded to file.
    #[inline]
    pub fn display(&mut self, line_type: Line) {
        self.displaying = line_type;
    }
}

/// Represents a single line in the log, different types are displayed slightly
/// different.
#[repr(u8)]
pub enum Line {
    /// A recoverable error.
    Err(String) = 2,

    /// A warning, probably not a returned error in code.
    Warn(String) = 1,

    /// General information, should not be used repeatedly.
    Info(String) = 0,
}

impl Line {
    /// Gets the severity of the `Line` variant.
    #[inline]
    #[must_use]
    pub fn severity(&self) -> u8 {
        unsafe { *(self as *const Self as *const u8) }
    }
}

impl ToString for Line {
    #[inline]
    fn to_string(&self) -> String {
        match self {
            // TODO: Colored output.
            Self::Err(s) => format!("   [Err]: {}", s),
            Self::Warn(s) => format!("  [Warn]: {}", s),
            Self::Info(s) => format!("  [Info]: {}", s),
        }
    }
}
