// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use image::ImageBuffer;
use nokhwa::FormatDecoder;
use nokhwa::{self, pixel_format::RgbFormat};
use std::net::Shutdown;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::SendError;
use std::sync::Arc;
use std::{
    io::{self, Write},
    net::{Ipv4Addr, SocketAddrV4, TcpListener},
    sync::mpsc::{self, RecvError, Sender},
    thread,
};

pub struct CameraServer {
    tx: Sender<ImageBuffer<<RgbFormat as FormatDecoder>::Output, Vec<u8>>>,
    halt: Arc<AtomicBool>,
}

impl CameraServer {
    /// Creates and starts a new camera server that will listen on the given
    /// port.
    #[must_use]
    pub fn start(port: u16) -> io::Result<Self> {
        let (tx, rx) = mpsc::channel();
        let listener = TcpListener::bind(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 0), port))?;
        let halt = Arc::new(AtomicBool::new(false));
        let halt_clone = halt.clone();

        thread::spawn(move || -> Result<(), RecvError> {
            let mut frame: ImageBuffer<<RgbFormat as FormatDecoder>::Output, _> = rx.recv()?;
            let mut connection = None;
            let halt = halt_clone;

            loop {
                if connection.is_none() {
                    if let Ok((stream, _)) = listener.accept() {
                        connection = Some(stream);
                    }
                }

                if halt.load(Ordering::Relaxed) {
                    break Ok(());
                }

                // Hopefully the server will never be behind the camera but
                // in case it ever is this skips to the last sent frame. If
                // no more frames have been sent we just continue using the
                // current one.
                if let Some(f) = rx.try_iter().last() {
                    frame = f;
                }

                if let Some(c) = &mut connection {
                    // Get height and width in big endian byte format and
                    // flatten the two `[u8; 4]` arrays into one `[u8; 8]`.
                    let dimensions =
                        [frame.width().to_be_bytes(), frame.height().to_be_bytes()].concat();

                    if let Err(_) = c
                        .write(dimensions.as_slice())
                        .and_then(|s| match s != dimensions.len() {
                            // If we get back a length other than that of
                            // the image's dimensions the client will not
                            // have received them correctly.
                            true => Err(io::Error::from(io::ErrorKind::Other)),
                            false => Ok(()),
                        })
                        .and_then(|_| {
                            // Enumerate through the pixels from x = 0 to
                            // width and y = 0 to height and flatten the R,
                            // G, and B values into a single slice.
                            c.write(
                                frame
                                    .enumerate_pixels()
                                    .map(|p| p.2 .0)
                                    .collect::<Vec<_>>()
                                    .concat()
                                    .as_slice(),
                            )
                        })
                    {
                        // If an error occures when connected disconnect and
                        // make connection `None`.
                        c.shutdown(Shutdown::Both)
                            .expect("single shutdown should not fail");
                        connection = None;
                    }
                }
            }
        });

        Ok(Self { tx, halt })
    }

    /// Sets the current camera frame that this server will update clients with.
    /// The frame may not be the next one sent to clients but will be retreived
    /// at the before sending the frame after that.
    #[inline]
    pub fn set_frame(
        &mut self,
        buf: ImageBuffer<<RgbFormat as FormatDecoder>::Output, Vec<u8>>,
    ) -> Result<(), SendError<ImageBuffer<<RgbFormat as FormatDecoder>::Output, Vec<u8>>>> {
        self.tx.send(buf)
    }
}

impl Drop for CameraServer {
    fn drop(&mut self) {
        // Have our thread stop so we dont have dangling threads.
        self.halt.store(true, Ordering::Relaxed);
    }
}
