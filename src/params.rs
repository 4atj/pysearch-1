use crate::{expr::Expr, operator::*, vec::Vector};

pub type Num = i32;

pub struct Input {
    pub name: &'static str,
    pub vec: &'static [Num],
}

pub const INPUTS: &[Input] = &[Input {
    name: "n",
    vec: &['E' as i32, 'W' as i32, 'N' as i32, 'S' as i32],
}];

/// This function gets applied to the output when comparing to GOAL.
///
/// If you only care about e.g. truthiness, change this to
///
///     (n != 0) as Num
///
/// and use only 0/1 in the GOAL.
pub fn mapping(n: Num) -> Num {
    n
}

pub fn match_goal(expr: &Expr) -> bool {
    expr.output.clone().map(mapping) == Vector::from_slice(GOAL)
}

pub const GOAL: &[Num] = &[1, -1, 0, 0];

pub const MAX_LENGTH: usize = 14;
pub const MAX_CACHE_LENGTH: usize = 10;
pub const MIN_MULTITHREAD_LENGTH: usize = MAX_CACHE_LENGTH + 1;
pub const LITERALS: &[Num] = &[
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
];
/// If not 0, include all numbers in 1..=MAX_LITERAL in addition to LITERALS.
pub const MAX_LITERAL: Num = 0;

/// To use C-style modulo and division (-2 % 10 == -2) rather than Python style (-2 % 10 == 8),
/// change `OP_MOD` to `BinaryOp { apply: apply_trunc_mod, ..OP_MOD }` and
///        `OP_DIV` to `BinaryOp { apply: apply_trunc_div, ..OP_DIV }`.
///
/// To use C-style bit shift (1 >> 32 == 1) rather than Python style (1 >> 32 == 0),
/// change `OP_BIT_SHL` to `BinaryOp { apply: apply_bit_shl, ..OP_BIT_SHL }` and
///        `OP_BIT_SHR` to `BinaryOp { apply: apply_bit_shr, ..OP_BIT_SHR }`.
#[rustfmt::skip]
pub const BINARY_OPERATORS: &[BinaryOp] = &[
    OP_OR,
    OP_SPACE_OR,
    OP_OR_SPACE,
    // OP_SPACE_OR_SPACE,
    OP_LT,
    OP_LE,
    // OP_GT,
    // OP_GE,
    // OP_EQ,
    // OP_NE,
    OP_BIT_OR,
    OP_BIT_XOR,
    OP_BIT_AND,
    OP_BIT_SHL,
    OP_BIT_SHR,
    OP_ADD,
    OP_SUB,
    OP_MUL,
    OP_MOD,
    OP_DIV,
    // OP_GCD,
    OP_EXP,
];

#[rustfmt::skip]
pub const UNARY_OPERATORS: &[UnaryOp] = &[
    OP_BIT_NEG,
    OP_NEG,
];

/// Search expressions that use the same variable twice (like `x*x`).
pub const REUSE_VARS: bool = true;

/// Controls whether all declared variables should be always used.
pub const USE_ALL_VARS: bool = true;
