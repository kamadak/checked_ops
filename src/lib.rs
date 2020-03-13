//
// Copyright (c) 2020 KAMADA Ken'ichi.
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
// OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
// HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
// LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
// OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.
//

//! Automatic checked arithmetic operations in Rust.
//!
//! The `checked_ops` macro takes an expression and expands it into a
//! checked form.
//! You no longer need to type:
//! ```
//! # let (a, b, c) = (1u8, 1, 1);
//! a.checked_add(b).and_then(|t| t.checked_mul(c))
//! # ;
//! ```
//! You can just do:
//! ```
//! # use checked_ops::checked_ops;
//! # let (a, b, c) = (1u8, 1, 1);
//! checked_ops!((a + b) * c)
//! # ;
//! ```
//!
//! The current implementation has several limitations.
//! See the documentation of `checked_ops` macro for details.

use num_traits::{CheckedAdd, CheckedSub, CheckedMul, CheckedDiv, CheckedRem};

/// Takes an expression and expands it into a "checked" form.
///
/// Supported operators are: `+`, `-`, `*`, `/`, `%` (binary operators),
/// and `as` (cast).
///
/// Supported operands are: number literals, simple variables (single-token
/// expressions), and pathenthesized expressions.
///
/// # Examples
///
/// ```
/// # use checked_ops::checked_ops;
/// assert_eq!(checked_ops!(1 - 2), Some(-1));
/// assert_eq!(checked_ops!(1u32 - 2), None);
/// assert_eq!(checked_ops!((1 - 2) as u32), None);
/// assert_eq!(checked_ops!(1 / 0), None);
/// ```
///
/// # Caveats
///
/// - Non-single-token operands such as field expressions
///   (`struct.attribute`), function calls (`function()`), and paths
///   (`std::u32::MAX`) are not supported.
/// - Operators not listed above are not yet supported.
///   These include unary `-` (negative), `<<`, and `>>` (bit shift).
/// - A long expression causes "recursion limit reached while expanding
///   the macro" error.
#[macro_export]
macro_rules! checked_ops {
    ($($rest:tt)+) => ($crate::cvt!([] [] $($rest)+));
}

// Parse the expression with Dijkstra's shunting-yard algorithm.
// The parameters are interpreted as:
//    [constructed expression stack] [operator stack] remaining tokens
#[doc(hidden)]
#[macro_export]
macro_rules! cvt {
    // Process a pair of parentheses.
    ([$($exp:expr),*] [$($op:tt)*] ($($inside:tt)+) $($rest:tt)*) =>
        ($crate::cvt!([$crate::cvt!([] [] $($inside)+) $(, $exp)*]
                      [$($op)*] $($rest)*));
    // Process "as" immediately, because it has the highest precedence
    // among supported operators.  Use $type:tt instead of ty, because
    // ty cannot be followed by tt, literal +, and so on.
    ([$a:expr $(, $exp:expr)*] [$($op:tt)*] as $type:tt $($rest:tt)*) =>
        ($crate::cvt!([$a.and_then(
            |x| std::convert::TryInto::<$type>::try_into(x).ok()) $(, $exp)*]
                      [$($op)*] $($rest)*));
    // Process an operator with higher precedence.
    ([$b:expr, $a:expr $(, $exp:expr)*] [* $($op:tt)*] + $($rest:tt)*) =>
        ($crate::cvt!([$crate::mul($a, $b) $(, $exp)*] [$($op)*] + $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [/ $($op:tt)*] + $($rest:tt)*) =>
        ($crate::cvt!([$crate::div($a, $b) $(, $exp)*] [$($op)*] + $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [% $($op:tt)*] + $($rest:tt)*) =>
        ($crate::cvt!([$crate::rem($a, $b) $(, $exp)*] [$($op)*] + $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [* $($op:tt)*] - $($rest:tt)*) =>
        ($crate::cvt!([$crate::mul($a, $b) $(, $exp)*] [$($op)*] - $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [/ $($op:tt)*] - $($rest:tt)*) =>
        ($crate::cvt!([$crate::div($a, $b) $(, $exp)*] [$($op)*] - $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [% $($op:tt)*] - $($rest:tt)*) =>
        ($crate::cvt!([$crate::rem($a, $b) $(, $exp)*] [$($op)*] - $($rest)*));
    // Process a left-associative operator with equal precedence.
    ([$b:expr, $a:expr $(, $exp:expr)*] [+ $($op:tt)*] + $($rest:tt)*) =>
        ($crate::cvt!([$crate::add($a, $b) $(, $exp)*] [$($op)*] + $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [- $($op:tt)*] + $($rest:tt)*) =>
        ($crate::cvt!([$crate::sub($a, $b) $(, $exp)*] [$($op)*] + $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [+ $($op:tt)*] - $($rest:tt)*) =>
        ($crate::cvt!([$crate::add($a, $b) $(, $exp)*] [$($op)*] - $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [- $($op:tt)*] - $($rest:tt)*) =>
        ($crate::cvt!([$crate::sub($a, $b) $(, $exp)*] [$($op)*] - $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [* $($op:tt)*] * $($rest:tt)*) =>
        ($crate::cvt!([$crate::mul($a, $b) $(, $exp)*] [$($op)*] * $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [/ $($op:tt)*] * $($rest:tt)*) =>
        ($crate::cvt!([$crate::div($a, $b) $(, $exp)*] [$($op)*] * $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [% $($op:tt)*] * $($rest:tt)*) =>
        ($crate::cvt!([$crate::rem($a, $b) $(, $exp)*] [$($op)*] * $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [* $($op:tt)*] / $($rest:tt)*) =>
        ($crate::cvt!([$crate::mul($a, $b) $(, $exp)*] [$($op)*] / $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [/ $($op:tt)*] / $($rest:tt)*) =>
        ($crate::cvt!([$crate::div($a, $b) $(, $exp)*] [$($op)*] / $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [% $($op:tt)*] / $($rest:tt)*) =>
        ($crate::cvt!([$crate::rem($a, $b) $(, $exp)*] [$($op)*] / $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [* $($op:tt)*] % $($rest:tt)*) =>
        ($crate::cvt!([$crate::mul($a, $b) $(, $exp)*] [$($op)*] % $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [/ $($op:tt)*] % $($rest:tt)*) =>
        ($crate::cvt!([$crate::div($a, $b) $(, $exp)*] [$($op)*] % $($rest)*));
    ([$b:expr, $a:expr $(, $exp:expr)*] [% $($op:tt)*] % $($rest:tt)*) =>
        ($crate::cvt!([$crate::rem($a, $b) $(, $exp)*] [$($op)*] % $($rest)*));
    // Push the operator otherwise.
    ([$($exp:expr),*] [$($op:tt)*] + $($rest:tt)*) =>
        ($crate::cvt!([$($exp),*] [+ $($op)*] $($rest)*));
    ([$($exp:expr),*] [$($op:tt)*] - $($rest:tt)*) =>
        ($crate::cvt!([$($exp),*] [- $($op)*] $($rest)*));
    ([$($exp:expr),*] [$($op:tt)*] * $($rest:tt)*) =>
        ($crate::cvt!([$($exp),*] [* $($op)*] $($rest)*));
    ([$($exp:expr),*] [$($op:tt)*] / $($rest:tt)*) =>
        ($crate::cvt!([$($exp),*] [/ $($op)*] $($rest)*));
    ([$($exp:expr),*] [$($op:tt)*] % $($rest:tt)*) =>
        ($crate::cvt!([$($exp),*] [% $($op)*] $($rest)*));
    // Push an operand.
    ([$($exp:expr),*] [$($op:tt)*] $operand:literal $($rest:tt)*) =>
        ($crate::cvt!([Some($operand) $(, $exp)*] [$($op)*] $($rest)*));
    ([$($exp:expr),*] [$($op:tt)*] $operand:ident $($rest:tt)*) =>
        ($crate::cvt!([Some($operand) $(, $exp)*] [$($op)*] $($rest)*));
    // Process the operators in the stack when there is no remaining token.
    ([$b:expr, $a:expr $(, $exp:expr)*] [+ $($op:tt)*]) =>
        ($crate::cvt!([$crate::add($a, $b) $(, $exp)*] [$($op)*]));
    ([$b:expr, $a:expr $(, $exp:expr)*] [- $($op:tt)*]) =>
        ($crate::cvt!([$crate::sub($a, $b) $(, $exp)*] [$($op)*]));
    ([$b:expr, $a:expr $(, $exp:expr)*] [* $($op:tt)*]) =>
        ($crate::cvt!([$crate::mul($a, $b) $(, $exp)*] [$($op)*]));
    ([$b:expr, $a:expr $(, $exp:expr)*] [/ $($op:tt)*]) =>
        ($crate::cvt!([$crate::div($a, $b) $(, $exp)*] [$($op)*]));
    ([$b:expr, $a:expr $(, $exp:expr)*] [% $($op:tt)*]) =>
        ($crate::cvt!([$crate::rem($a, $b) $(, $exp)*] [$($op)*]));
    // Finished.
    ([$exp:expr] []) =>
        ($exp);
}

#[doc(hidden)]
#[inline]
pub fn add<T>(a: Option<T>, b: Option<T>) -> Option<T> where T: CheckedAdd {
    a?.checked_add(&b?)
}

#[doc(hidden)]
#[inline]
pub fn sub<T>(a: Option<T>, b: Option<T>) -> Option<T> where T: CheckedSub {
    a?.checked_sub(&b?)
}

#[doc(hidden)]
#[inline]
pub fn mul<T>(a: Option<T>, b: Option<T>) -> Option<T> where T: CheckedMul {
    a?.checked_mul(&b?)
}

#[doc(hidden)]
#[inline]
pub fn div<T>(a: Option<T>, b: Option<T>) -> Option<T> where T: CheckedDiv {
    a?.checked_div(&b?)
}

#[doc(hidden)]
#[inline]
pub fn rem<T>(a: Option<T>, b: Option<T>) -> Option<T> where T: CheckedRem {
    a?.checked_rem(&b?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        assert_eq!(checked_ops!(2 * 3 + 4 as i16 - (5 - 6)), Some(11));
    }

    #[test]
    fn associativity() {
        let m1 = -1i8;
        assert_eq!(checked_ops!(1 + 127 + m1), None);   // 127
        assert_eq!(checked_ops!(254u8 + 2 - 1), None);  // 255
        assert_eq!(checked_ops!(7 - 5 + 3), Some(5));   // -1
        assert_eq!(checked_ops!(7 - 5 - 3), Some(-1));  // 5

        assert_eq!(checked_ops!(16 * 16 * 0u8), None);  // 0
        assert_eq!(checked_ops!(7 * 5 / 3), Some(11));  // 7
        assert_eq!(checked_ops!(7 * 5 % 3), Some(2));   // 14
        assert_eq!(checked_ops!(7 / 5 * 3), Some(3));   // 0
        assert_eq!(checked_ops!(7 / 5 / 3), Some(0));   // 7
        assert_eq!(checked_ops!(7 / 5 % 3), Some(1));   // 3
        assert_eq!(checked_ops!(7 % 5 * 3), Some(6));   // 7
        assert_eq!(checked_ops!(7 % 5 / 3), Some(0));   // 7
        assert_eq!(checked_ops!(7 % 5 % 3), Some(2));   // 1

        assert_eq!(checked_ops!(1 as u16 as u8), Some(1u8));
    }

    #[test]
    fn precedence() {
        assert_eq!(checked_ops!(7 + 5 * 3), Some(22));  // 36
        assert_eq!(checked_ops!(7 + 5 / 3), Some(8));   // 4
        assert_eq!(checked_ops!(7 + 5 % 3), Some(9));   // 0
        assert_eq!(checked_ops!(7 - 5 * 3), Some(-8));  // 6
        assert_eq!(checked_ops!(7 - 5 / 3), Some(6));   // 0
        assert_eq!(checked_ops!(7 - 5 % 3), Some(5));   // 2

        let m1 = -1;
        assert_eq!(checked_ops!(m1 + 128 as i8), None); // 127
        assert_eq!(checked_ops!(7 - 128 as i8), None);  // -121
        assert_eq!(checked_ops!(0 * 128 as i8), None);  // 0
        assert_eq!(checked_ops!(0 / 128 as i8), None);  // 0
    }

    #[test]
    fn parentheses() {
        assert_eq!(checked_ops!((2 + 3) * 4), Some(20));
        assert_eq!(checked_ops!(2 * (3 + 4)), Some(14));
        assert_eq!(checked_ops!((2 + 3) * (4 + 5)), Some(45));
    }

    #[test]
    fn variables() {
        let a = 1;
        assert_eq!(checked_ops!(a + 2), Some(3));
    }

    #[test]
    fn casts() {
        let a = 3i32;
        assert_eq!(checked_ops!(1 + 2 + a as u32), Some(6u32));
        assert_eq!(checked_ops!(1 + a as u32 + 2), Some(6u32));
        assert_eq!(checked_ops!(a as u32 + 1 + 2), Some(6u32));
        assert_eq!(checked_ops!((1 + a) as u32 + 2), Some(6u32));
    }

    #[test]
    fn overflow() {
        assert_eq!(checked_ops!(254u8 + 1), Some(255));
        assert_eq!(checked_ops!(255u8 + 1), None);
        assert_eq!(checked_ops!(1u32 - 1), Some(0));
        assert_eq!(checked_ops!(1u32 - 2), None);
        assert_eq!(checked_ops!(15u8 * 17), Some(255));
        assert_eq!(checked_ops!(16u8 * 16), None);
        assert_eq!(checked_ops!((1i32 - 1) as u32), Some(0));
        assert_eq!(checked_ops!((1i32 - 2) as u32), None);
        assert_eq!(checked_ops!(255 as u8), Some(255));
        assert_eq!(checked_ops!(256 as u8), None);
    }

    #[test]
    fn div0() {
        assert_eq!(checked_ops!(1 / 0), None);
        assert_eq!(checked_ops!(1 % 0), None);
    }
}
