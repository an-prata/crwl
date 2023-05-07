// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use serde_json;
use std::{
    error::Error,
    fmt::Display,
    io::{Read, Write},
    mem::size_of,
    net::{SocketAddr, TcpListener, TcpStream},
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Sender},
        Arc,
    },
    thread::{self, JoinHandle},
};

use crate::log;

pub struct Server {
    tx: mpsc::Sender<String>,
    handle: JoinHandle<ServerResult<()>>,
    should_stop: Arc<AtomicBool>,
}

impl Server {
    /// Creates a new [`Server`] and starts a thread to continually listen for
    /// and handle one connection at a time.
    ///
    /// [`Server`]: Server
    pub fn new(addr: SocketAddr, branch: Sender<log::Line>) -> ServerResult<Self> {
        let (tx, rx) = mpsc::channel();
        let should_stop = Arc::new(AtomicBool::new(false));
        let should_stop_ref = should_stop.clone();

        let listener = match TcpListener::bind(addr) {
            Ok(v) => v,
            Err(_) => return Err(ServerError::TcpError),
        };

        let mut state = match rx.recv() {
            Ok(v) => v,
            Err(_) => return Err(ServerError::MpscError),
        };

        Ok(Self {
            tx,
            handle: thread::spawn(move || -> ServerResult<()> {
                loop {
                    if should_stop_ref.load(Ordering::Relaxed) {
                        break;
                    }

                    state = match rx.try_recv() {
                        Ok(v) => v,
                        Err(_) => state,
                    };

                    let (mut stream, addr) = match listener.accept() {
                        Ok(v) => v,
                        Err(_) => continue,
                    };

                    branch.send(log::Line::Info(format!(
                        "received connection to server from {}",
                        addr
                    )));

                    handle_connection(state.as_bytes(), &mut stream);
                }

                Ok(())
            }),
            should_stop,
        })
    }

    pub fn set_state<T>(&mut self, state: T) -> ServerResult<()>
    where
        T: serde::Serialize,
    {
        let state = match serde_json::to_string(&state) {
            Ok(v) => v,
            Err(_) => return Err(ServerError::SerdeError),
        };

        match self.tx.send(state) {
            Ok(_) => (),
            Err(_) => return Err(ServerError::MpscError),
        };
        Ok(())
    }
}

/// Sends the current robot state as given to the function and returns a desired
/// state from the client on success. An [`Err`] return value means that the
/// client either gave invalid data or that the TCP connection failed.
///
/// [`Err`]: Err
#[must_use]
fn handle_connection(state: &[u8], stream: &mut TcpStream) -> ServerResult<Vec<u8>> {
    stream.write_all(&state.len().to_be_bytes());
    stream.write_all(state);

    let mut size_be = [0u8; size_of::<usize>()];
    let recv_size = match stream.read_exact(&mut size_be) {
        Ok(_) => usize::from_be_bytes(size_be),
        Err(_) => return Err(ServerError::TcpError),
    };

    let mut recv_state = vec![0u8; recv_size];
    match stream.read(recv_state.as_mut_slice()) {
        Ok(s) if s == recv_size => (),
        _ => return Err(ServerError::TcpError),
    };

    Ok(recv_state)
}

pub type ServerResult<T> = Result<T, ServerError>;

#[derive(Clone, Copy, Debug)]
pub enum ServerError {
    TcpError,
    SerdeError,
    MpscError,
}

impl Error for ServerError {}

impl Display for ServerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "error when starting, stopping, or running the server thread"
        )
    }
}
