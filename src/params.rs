use crate::{expr::Expr, operator::*};

pub type Num = i32;

pub struct Input {
    pub name: &'static str,
    pub vec: &'static [Num],
    pub min_uses: u8,
    pub max_uses: u8,
}

pub const INPUTS: &[Input] = &[Input {
    name: "n",
    vec: &['E' as i32, 'W' as i32, 'N' as i32, 'S' as i32],
    min_uses: 1,
    max_uses: 255,
}];

pub struct Matcher {}

impl Matcher {
    pub fn new() -> Self {
        Self {}
    }

    pub fn match_one(&mut self, index: usize, output: Num) -> bool {
        output == GOAL[index]
    }

    // Will be called after match_one returns true for all outputs
    pub fn match_final(self, _el: Option<&Expr>, _er: &Expr, _op: OpIndex) -> bool {
        true
    }

    pub fn match_all(expr: &Expr) -> bool {
        let mut matcher = Self::new();
        expr.output
            .iter()
            .enumerate()
            .all(|(i, &o)| matcher.match_one(i, o))
            && matcher.match_final(
                expr.left.map(|e| unsafe { e.as_ref() }),
                unsafe { expr.right.unwrap().as_ref() },
                expr.op_idx,
            )
    }

    fn match_multi_exprs_one(&mut self, _index: usize, _exprs: [&Expr; NUM_EXPRS]) -> bool {
        true
    }

    pub fn match_multi_exprs_all(exprs: [&Expr; NUM_EXPRS]) -> bool {
        let mut matcher = Self::new();
        (0..exprs[0].output.len()).all(|i| matcher.match_multi_exprs_one(i, exprs))
    }
}

pub const GOAL: &[Num] = &[1, -1, 0, 0];

pub const MAX_LENGTH: usize = 14;
pub const MAX_CACHE_LENGTH: usize = 10;
pub const MIN_MULTITHREAD_LENGTH: usize = MAX_CACHE_LENGTH + 1;

pub const NUM_EXPRS: usize = 1;
pub const MIN_EXPR_LENGTH: usize = 1;
pub const MAX_EXPR_LENGTH: usize = MAX_LENGTH - (NUM_EXPRS - 1) * (MIN_EXPR_LENGTH + 1);

pub const LITERALS: &[Num] = &[];
/// If not 0, include all numbers in 1..=MAX_LITERAL in addition to LITERALS.
pub const MAX_LITERAL: Num = 40;

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

/// Match leaf expressions 1 output at a time to avoid unnecessary precalculations
pub const MATCH_1BY1: bool = true;
