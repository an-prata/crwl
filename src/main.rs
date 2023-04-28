// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

mod crwl;
mod gp;
mod log;

use rbtcs::bot;

fn main() {
    bot::BotRunner::new(crwl::Crwl::new())
        .expect("errors instantiating GP I/O are fatal")
        .start()
}
