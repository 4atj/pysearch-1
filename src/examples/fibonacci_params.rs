use crate::{expr::Expr, operator::*, symbol::Symbol};

pub type Num = i32;

pub const INPUTS: &[Symbol] = &[];

/// Contains symbols that can be set dynamically.
/// The `vec` field is used to check the uniqueness of the expressions.
/// The actual values are passed in the `variable_values` parameter of `Expr::eval`.
pub const VARIABLES: &[Symbol] = &[
    Symbol {
        name: "a",
        vec: &[0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3],
        min_uses: 1,
        max_uses: 255,
    },
    Symbol {
        name: "b",
        vec: &[0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3],
        min_uses: 1,
        max_uses: 255,
    },
];

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

    pub fn match_multi_exprs(exprs: &[&Expr; NUM_EXPRS]) -> bool {
        (-1..=9).any(|a| {
            (-1..=9).any(|b| {
                let mut variable_values = [a, b];
                let success = GOAL_.iter().all(|&goal| {
                    for index in 0..VARIABLES.len() {
                        match exprs[index].eval(0, &variable_values) {
                            Some(output) => variable_values[index] = output,
                            None => return false,
                        }
                    }
                    exprs.last().unwrap().eval(0, &variable_values) == Some(goal)
                });
                if success {
                    if a != b {
                        print!("a={a};b={b}; ");
                    } else {
                        print!("a=b={b}; ");
                    }
                }
                success
            })
        })
    }
}

pub const GOAL: &[Num] = &[0; 16];
pub const GOAL_: &[Num] = &[0, 1, 1, 2, 3, 5, 8];

pub const MAX_LENGTH: usize = 14;
pub const MAX_CACHE_LENGTH: usize = 7;
pub const MIN_MULTITHREAD_LENGTH: usize = MAX_CACHE_LENGTH + 1;

pub const NUM_EXPRS: usize = VARIABLES.len() + 1;
pub const MIN_EXPR_LENGTH: usize = 1;
pub const MAX_EXPR_LENGTH: usize =
    MAX_LENGTH.saturating_sub((NUM_EXPRS - 1) * (MIN_EXPR_LENGTH + 1));

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

/// Match leaf expressions 1 output at a time to avoid unnecessary precalculations
pub const MATCH_1BY1: bool = true;

/// If set, e.g. to `Some(-159236)`, this arbitrary number is chosen to represent errors.
/// That is, pysearch will pretend 1/0 = -159236, and -159236 * 2 = -159236, and so on.
pub const ERROR_VALUE: Option<Num> = None;
