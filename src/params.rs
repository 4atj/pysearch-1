use crate::{expr::Expr, operator::*};

pub type Num = i32;

pub struct Input {
    pub name: &'static str,
    pub vec: &'static [Num],
}

pub const INPUTS: &[Input] = &[Input {
    name: "n",
    vec: &['E' as i32, 'W' as i32, 'N' as i32, 'S' as i32],
}];

pub struct Matcher {}

impl Matcher {
    pub fn new() -> Matcher {
        Matcher {}
    }

    pub fn match_one(&mut self, index: usize, output: Num) -> bool {
        output == GOAL[index]
    }

    pub fn match_all(&mut self, expr: &Expr) -> bool {
        expr.output
            .iter()
            .enumerate()
            .all(|(i, &o)| self.match_one(i, o))
    }
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

#[rustfmt::skip]
pub const BINARY_OPERATORS: &[BinaryOp] = &[
    OP_OR,
    OP_SPACE_OR,
    OP_OR_SPACE,
    // OP_SPACE_OR_SPACE,
    // OP_OR_SYMBOL,
    // OP_OR_LOGICAL,
    // OP_AND,
    // OP_SPACE_AND,
    // OP_AND_SPACE,
    // OP_SPACE_AND_SPACE,
    // OP_AND_SYMBOL,
    // OP_AND_LOGICAL,
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
    // OP_BIT_SHL_WRAP,
    // OP_BIT_SHR_WRAP,
    OP_ADD,
    OP_SUB,
    OP_MUL,
    OP_MOD_FLOOR,
    OP_DIV_FLOOR,
    // OP_MOD_TRUNC,
    // OP_DIV_TRUNC,
    // OP_GCD,
    OP_EXP,
];

#[rustfmt::skip]
pub const UNARY_OPERATORS: &[UnaryOp] = &[
    OP_BIT_NEG,
    OP_NEG,
    // OP_NOT,
];

pub const USE_PARENS: bool = true;

/// Match leaf expressions 1 output at a time to avoid unnecessary precalculations
pub const MATCH_1BY1: bool = true;

/// Search expressions that use the same variable twice (like `x*x`).
pub const REUSE_VARS: bool = true;

/// Controls whether all declared variables should be always used.
pub const USE_ALL_VARS: bool = true;

pub const CHUNK_ID: usize = 0;
pub const NUMBER_OF_CHUNKS: usize = 1;
