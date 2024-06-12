use crate::params::{Num, INPUTS, VARIABLES};

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
    pub max_length: usize,
    pub min_uses: u8,
    pub max_uses: u8,
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
