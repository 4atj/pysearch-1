use crate::params::{Num, INPUTS, MAX_LENGTH, VARIABLES};

#[derive(Clone, Copy)]
pub struct Symbol {
    pub name: &'static str,
    pub min_uses: u8,
    pub max_uses: u8,
}

pub struct Input {
    pub name: &'static str,
    pub vec: &'static [Num],
    pub min_uses: u8,
    pub max_uses: u8,
}

pub struct Variable {
    pub name: &'static str,
    pub min_length: usize,
    pub min_uses: u8,
    pub max_uses: u8,
}

pub fn get_var_max_expr_length(length: usize, var_index: usize) -> usize {
    const fn get_var_min_length_required() -> [usize; VARIABLES.len()] {
        let mut var_min_length_required = [0; VARIABLES.len()];
        let mut s = 0;
        let mut idx = VARIABLES.len() - 1;
        while idx != 0 {
            s += VARIABLES[idx].min_length + 3;
            idx -= 1;
            var_min_length_required[idx] = s;
        }
        var_min_length_required
    }
    const VAR_MIN_LENGTH_REQUIRED: [usize; VARIABLES.len()] = get_var_min_length_required();
    MAX_LENGTH - length - VAR_MIN_LENGTH_REQUIRED[var_index] - 3
}

pub fn get_max_expr_length(length: usize, var_index: usize) -> usize {
    const fn get_min_length_required() -> [usize; VARIABLES.len()] {
        let mut var_min_length_required = [0; VARIABLES.len()];
        let mut s = 0;
        let mut m = !0;
        let mut idx = VARIABLES.len();
        while idx != 0 {
            idx -= 1;
            s += VARIABLES[idx].min_length + 3;
            if m > VARIABLES[idx].min_length + 3 {
                m = VARIABLES[idx].min_length + 3;
            }
            var_min_length_required[idx] = s - m;
        }
        var_min_length_required
    }
    const MAX_LENGTH_REQUIRED: [usize; VARIABLES.len()] = get_min_length_required();
    MAX_LENGTH - length - MAX_LENGTH_REQUIRED[var_index] - 3
}

const fn get_symbols() -> [Symbol; INPUTS.len() + VARIABLES.len() - 1] {
    let mut symbols = [Symbol {
        name: "",
        min_uses: 0,
        max_uses: 0,
    }; INPUTS.len() + VARIABLES.len() - 1];
    let mut idx = 0;
    while idx < INPUTS.len() {
        let input = &INPUTS[idx];
        symbols[idx] = Symbol {
            name: input.name,
            min_uses: input.min_uses,
            max_uses: input.max_uses,
        };
        idx += 1;
    }
    while idx < VARIABLES.len() + INPUTS.len() - 1 {
        let variable = &VARIABLES[idx - INPUTS.len()];
        symbols[idx] = Symbol {
            name: variable.name,
            min_uses: variable.min_uses,
            max_uses: variable.max_uses,
        };
        idx += 1;
    }
    symbols
}

pub const SYMBOLS: [Symbol; INPUTS.len() + VARIABLES.len() - 1] = get_symbols();
