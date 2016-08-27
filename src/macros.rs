use std::mem;

use {State, Function};
use ffi::lua_State;
use ffi::libc::c_int;

/// Wrap a `fn(&mut State) -> i32` as an ffi-suitable `Function`.
///
/// The argument must be a path, so that the specific `fn` is known at
/// compile-time. See also `wrap_fn()`, which allows closures but panics at
/// runtime rather than checking for valid `fn` items at compile time.
#[macro_export]
macro_rules! lua_func {
  ($func:path) => { $crate::macros::_wrap(|s| $crate::macros::_check_type($func)(s)) }
}

#[doc(hidden)]
#[inline(always)]
pub fn _check_type(f: fn(&mut State) -> c_int) -> fn(&mut State) -> c_int {
  f
}

/// Wrap a `fn(&mut State) -> i32` as an ffi-suitable `Function`.
///
/// The argument must be zero-sized for this wrapping to be possible. This
/// includes `fn` items whose targets are known at compile time and
/// non-capturing closures.
///
/// Panics if the argument is not zero-sized.
///
/// See also `lua_func!`, which checks at compile time that a valid `fn` items
/// was supplied.
pub fn _wrap<F: Fn(&mut State) -> i32>(_: F) -> Function {
  unsafe extern fn wrapped<F: Fn(&mut State) -> c_int>(s: *mut lua_State) -> c_int {
    mem::zeroed::<F>()(&mut State::from_ptr(s))
  }
  assert!(mem::size_of::<F>() == 0, "");
  wrapped::<F>
}
