// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use serde_json;
use std::{
    error::Error,
    fmt::Display,
    io::{self, Read, Write},
    mem::{self, size_of},
    net::{SocketAddr, TcpListener, TcpStream},
    str,
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Sender},
        Arc,
    },
    thread::{self, JoinHandle},
};

use crate::log;

pub struct Server {
    tx: mpsc::Sender<serde_json::Value>,
    handle: JoinHandle<ServerResult<()>>,
    should_stop: Arc<AtomicBool>,
}

impl Server {
    pub fn new(addr: SocketAddr, branch: Sender<log::Line>) -> io::Result<Self> {
        let (tx, rx) = mpsc::channel();
        let should_stop = Arc::new(AtomicBool::new(false));
        let should_stop_ref = should_stop.clone();
        let listener = TcpListener::bind(addr)?;

        Ok(Self {
            tx,
            handle: thread::spawn(move || -> ServerResult<()> {
                let mut state = match rx.recv() {
                    Ok(v) => v,
                    Err(_) => return Err(ServerError),
                };

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

                    handle_connection(&state, &mut stream);
                }

                Ok(())
            }),
            should_stop,
        })
    }
}

/// Sends the current robot state as given to the function and returns a desired
/// state from the client on success. An [`Err`] return value means that the
/// client either gave invalid data or that the TCP connection failed.
///
/// [`Err`]: Err
#[must_use]
fn handle_connection(
    state: &serde_json::Value,
    stream: &mut TcpStream,
) -> ServerResult<serde_json::Value> {
    let bytes: Vec<_> = match state.as_str() {
        Some(s) => s,
        None => return Err(ServerError),
    }
    .bytes()
    .collect();

    stream.write_all(&bytes.len().to_be_bytes());
    stream.write_all(bytes.as_slice());

    let mut size_be = [0u8; size_of::<usize>()];
    let recv_size = match stream.read_exact(&mut size_be) {
        Ok(_) => usize::from_be_bytes(size_be),
        Err(_) => return Err(ServerError),
    };

    let mut recv_state = vec![0u8; recv_size];
    match stream.read(recv_state.as_mut_slice()) {
        Ok(s) if s == recv_size => (),
        _ => return Err(ServerError),
    };

    Ok(serde_json::json!(
        match str::from_utf8(&recv_state).and_then(|str| Ok(str.to_string())) {
            Ok(s) => s,
            Err(_) => return Err(ServerError),
        }
    ))
}

pub type ServerResult<T> = Result<T, ServerError>;

#[derive(Clone, Copy, Debug)]
pub struct ServerError;

impl Error for ServerError {}

impl Display for ServerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "error when starting, stopping, or running the server thread"
        )
    }
}
