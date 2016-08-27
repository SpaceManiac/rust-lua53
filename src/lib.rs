// The MIT License (MIT)
//
// Copyright (c) 2014 J.C. Moyer
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

//! Rust bindings for Lua 5.3 and beyond documentation.
//! Original Lua library documentation [here](https://www.lua.org/manual/5.3/).

#[macro_use]
extern crate bitflags;
pub extern crate lua_sys as ffi;

mod convert;
mod state;
#[doc(hidden)]
pub mod macros;

pub use state::*;
pub use convert::*;

pub use ffi::libc;
pub use ffi::lua_Number as Number;
pub use ffi::lua_Integer as Integer;
pub use ffi::lua_CFunction as Function;
pub use ffi::lua_Alloc as Allocator;
pub use ffi::lua_Hook as Hook;

/// Integer type used to index the Lua stack, usually `i32`.
pub type Index = libc::c_int;
