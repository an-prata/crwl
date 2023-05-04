// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::{
    io::{self, Read},
    net::{Ipv4Addr, SocketAddr, TcpListener},
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::Sender,
        Arc,
    },
    thread::{self, JoinHandle},
};

/// Represents a Deamon which runs a thread retrieving commands and forwarding
/// the to all given `Sender`s.
pub struct Deamon {
    handle: JoinHandle<()>,
    stop: Arc<AtomicBool>,
}

impl Deamon {
    pub const CMD_SIZE: usize = 16;
    const PORT: u16 = 7042;

    /// Creates and starts a new deamon thread given
    /// a `Vec` of `mpsc::Sender<[u8; Deamon::CMD_SIZE]>`. Each command given to
    /// the deamon will be forwarded to each of these senders, if a
    /// `Sender::send()` call returns an error it is removed from the `Vec` for
    /// future iterations.
    #[must_use]
    pub fn new(mut txs: Vec<Sender<[u8; Self::CMD_SIZE]>>) -> io::Result<Self> {
        let stop = Arc::new(AtomicBool::new(false));
        let stop_thread = stop.clone();
        let listener = TcpListener::bind(SocketAddr::new(
            std::net::IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
            Self::PORT,
        ))?;

        let handle = thread::spawn(move || {
            for stream in listener.incoming() {
                if stop_thread.load(Ordering::Relaxed) {
                    return;
                }

                match stream {
                    Ok(mut s) => {
                        let mut cmd = [0; Self::CMD_SIZE];

                        match s.read(&mut cmd) {
                            Ok(n) => {
                                if n < cmd.len() {
                                    continue;
                                }
                            }

                            Err(_) => continue,
                        };

                        for i in 0..txs.len() {
                            match txs[i].send(cmd.clone()) {
                                Ok(_) => (),
                                Err(_) => {
                                    txs.remove(i);
                                }
                            };
                        }
                    }

                    Err(_) => continue,
                }
            }
        });

        Ok(Self { handle, stop })
    }

    /// Stops the thread used for listening for deamon commands from the client.
    /// Returns the error returned by the `JoinHandle::join()` call.
    #[inline]
    #[must_use]
    pub fn stop_thread(self) -> thread::Result<()> {
        self.stop.store(true, Ordering::Relaxed);
        self.handle.join()
    }
}
