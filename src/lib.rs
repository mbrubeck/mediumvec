//! Collections optimized for space at the expense of capacity.

// Copyright 2017 Matt Brubeck.
//
// Licensed under the Apache License, Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0> or
// the MIT license <http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

pub mod vec32;
pub mod pointer_vec;

pub use vec32::Vec32;
pub use pointer_vec::PointerVec;
