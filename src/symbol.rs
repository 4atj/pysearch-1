use crate::params::{Num, INPUTS, VARIABLES};

#[derive(Clone, Copy)]
pub struct Symbol {
    pub name: &'static str,
    pub vec: &'static [Num],
    pub min_uses: u8,
    pub max_uses: u8,
}

const fn get_symbols() -> [Symbol; INPUTS.len() + VARIABLES.len()] {
    let mut symbols = [Symbol {
        name: "",
        vec: &[],
        min_uses: 0,
        max_uses: 0,
    }; INPUTS.len() + VARIABLES.len()];
    let mut idx = 0;
    while idx < symbols.len() {
        symbols[idx] = if idx < INPUTS.len() {
            INPUTS[idx]
        } else {
            VARIABLES[idx - INPUTS.len()]
        };
        idx += 1;
    }
    symbols
}

pub const SYMBOLS: [Symbol; INPUTS.len() + VARIABLES.len()] = get_symbols();
