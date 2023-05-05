// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use serde_json;
use std::{
    error::Error,
    fmt::Display,
    io,
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

                    let (stream, addr) = match listener.accept() {
                        Ok(v) => v,
                        Err(_) => continue,
                    };

                    branch.send(log::Line::Info(format!(
                        "received connection to server from {}",
                        addr
                    )));

                    handle_connection(&state, stream);
                }

                Ok(())
            }),
            should_stop,
        })
    }
}

fn handle_connection(state: &serde_json::Value, stream: TcpStream) -> serde_json::Value {}

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
