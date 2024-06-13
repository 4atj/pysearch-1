#![cfg_attr(feature = "simd", feature(portable_simd))]

pub mod expr;
pub mod operator;
pub mod symbols;

#[path = "params.rs"]
pub mod params;

#[cfg_attr(all(feature = "simd", feature = "portable_simd"), path = "vec_simd.rs")]
#[cfg_attr(not(feature = "simd"), path = "vec.rs")]
pub mod vec;

use expr::{Expr, NonNullExpr, VarCount};
use operator::*;
use params::*;
use symbols::{get_max_expr_length, get_var_max_expr_length, SYMBOLS};

use vec::Vector;

use hashbrown::{hash_set::Entry, HashMap, HashSet};
use seq_macro::seq;
use std::{ptr::NonNull, time::Instant};

// cache[length][output] = highest-prec expression of that length yielding that output
type CacheLevel = Vec<Expr>;
type VarCache = Vec<CacheLevel>;
type Cache<'a> = Vec<&'a VarCache>;

type HashSetCache = HashSet<NonNullExpr>;

fn positive_integer_length(mut k: Num) -> usize {
    let mut l = 1;
    while k >= 10 {
        k /= 10;
        l += 1;
    }
    l
}

fn can_use_required_vars(var_count: VarCount, length: usize, var_index: usize) -> bool {
    let missing_vars = VARIABLES.len() - var_index - 1;
    let missing_uses = var_count
        .iter()
        .zip(SYMBOLS.iter())
        .map(|(&c, i)| i.min_uses - c.min(i.min_uses))
        .sum::<u8>() as usize;
    length + missing_uses - missing_vars.min(missing_uses) * 2 + missing_vars * 4 <= MAX_LENGTH
}

fn uses_required_vars(var_count: VarCount) -> bool {
    var_count
        .iter()
        .zip(SYMBOLS.iter())
        .all(|(&c, s)| c >= s.min_uses)
}

fn is_var_leaf_expr(op_idx: OpIndex, length: usize, max_length: usize) -> bool {
    length == max_length
        || length == max_length - 1 && (UNARY_OPERATORS.len() == 0 || op_idx.prec() < UnaryOp::PREC)
}

fn is_leaf_expr(op_idx: OpIndex, length: usize) -> bool {
    is_var_leaf_expr(op_idx, length, MAX_LENGTH)
}

fn add_var_counts(mut var_count_1: VarCount, var_count_2: VarCount) -> Option<VarCount> {
    for ((l, &r), s) in var_count_1
        .iter_mut()
        .zip(var_count_2.iter())
        .zip(SYMBOLS.iter())
    {
        *l += r;
        if *l > s.max_uses {
            return None;
        }
    }
    Some(var_count_1)
}

const fn has_unlimited_var() -> bool {
    let mut i = 0;
    while i < SYMBOLS.len() {
        if SYMBOLS[i].max_uses == u8::MAX {
            return true;
        }
        i += 1;
    }
    false
}

fn save(
    cache_level: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr: Expr,
    expr_length: usize,
) {
    let total_length = exprs_length + expr_length + 3;

    if !MATCH_1BY1 && is_leaf_expr(expr.op_idx, total_length) {
        if Matcher::match_all(exprs, &expr) {
            print!("yes");
            for (e, v) in exprs.iter().zip(VARIABLES.iter()) {
                print!("{}={e};", v.name);
            }
            println!("{}={expr};", VARIABLES.last().unwrap().name);
        }
        return;
    }

    let total_var_count = add_var_counts(var_count, expr.var_count).unwrap();

    if VARIABLES.len() == 1 {
        let cant_use_more_vars = !has_unlimited_var()
            && total_var_count
                .iter()
                .zip(SYMBOLS.iter())
                .all(|(&c, i)| c == i.max_uses);

        if cant_use_more_vars {
            let mut mp: HashMap<Num, Num> = HashMap::new();
            for i in 0..GOAL.len() {
                if let Some(old) = mp.insert(expr.output[i], GOAL[i]) {
                    if old != GOAL[i] {
                        return;
                    }
                }
            }
        }
    }

    let var_index = exprs.len();
    let var_max_expr_length = get_var_max_expr_length(exprs_length, var_index);

    if expr_length <= var_max_expr_length - 2 {
        let expr_ptr: NonNullExpr = (&expr).into();
        if let Some(e) = hashset_cache.get(&expr_ptr) {
            if e.as_ref().prec() >= expr.prec() {
                return;
            }
        }
    }

    if expr_length > MAX_CACHE_LENGTH {
        if expr.op_idx.prec() < 15 {
            let is_last_var = var_index == VARIABLES.len() - 1;
            if is_last_var {
                if uses_required_vars(total_var_count) && Matcher::match_all(exprs, &expr) {
                    for (e, v) in exprs.iter().zip(VARIABLES.iter()) {
                        print!("{}={e};", v.name);
                    }
                    println!("{}={expr};", VARIABLES.last().unwrap().name);
                }
            } else {
                let mut new_exprs = exprs.clone();
                new_exprs.push(&expr);
                find_expressions(cache.clone(), new_exprs, total_var_count, total_length);
            }
        }

        for dfs_len in expr_length + 2..=var_max_expr_length {
            find_binary_expressions_left(
                cache_level,
                cache,
                hashset_cache,
                exprs,
                var_count,
                exprs_length,
                dfs_len,
                &expr,
                expr_length,
            );
            find_binary_expressions_right(
                cache_level,
                cache,
                hashset_cache,
                exprs,
                var_count,
                exprs_length,
                dfs_len,
                &expr,
                expr_length,
            );
        }
        if expr_length + 1 <= var_max_expr_length {
            find_unary_operators(
                cache_level,
                cache,
                hashset_cache,
                exprs,
                var_count,
                exprs_length,
                expr_length + 1,
                &expr,
            );
        }
        if !is_var_leaf_expr(OP_INDEX_PARENS, expr_length + 2, var_max_expr_length)
            && expr.op_idx < OP_INDEX_PARENS
        {
            save(
                cache_level,
                cache,
                hashset_cache,
                exprs,
                var_count,
                exprs_length,
                Expr::parens((&expr).into()),
                expr_length + 2,
            );
        }
        return;
    }

    cache_level.push(expr);
}

#[inline(always)]
fn find_binary_operators(
    cache_level: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr_length: usize,
    el: &Expr,
    er: &Expr,
    op_length: usize,
) {
    if er.is_literal() && el.is_literal() {
        return;
    }
    let expr_var_count = match add_var_counts(el.var_count, er.var_count) {
        Some(vc) => vc,
        None => return,
    };
    let total_var_count = match add_var_counts(var_count, expr_var_count) {
        Some(vc) => vc,
        None => return,
    };
    let total_length = exprs_length + expr_length + 3;
    if !can_use_required_vars(total_var_count, total_length, exprs.len()) {
        return;
    }

    seq!(idx in 0..100 {
        if let (Some(&op_idx), Some(op)) = (OP_BINARY_INDEX_TABLE.get(idx), BINARY_OPERATORS.get(idx)) {
            if op.name.len() == op_length && op.can_apply(el, er) {
                if MATCH_1BY1 && is_leaf_expr(op_idx, total_length) {
                    let mut matcher = Matcher::new();
                    if el
                        .output
                        .iter()
                        .zip(er.output.iter())
                        .enumerate()
                        .all(|(i, (&ol, &or))| match (op.apply)(ol, or) {
                            Some(o) => matcher.match_one(exprs, i, o),
                            None => false,
                        })
                        && matcher.match_final(exprs, Some(el), er, op_idx)
                    {
                        for (e, v) in exprs.iter().zip(VARIABLES.iter()) {
                            print!("{}={e};", v.name);
                        }
                        println!("{}={el}{op_idx}{er};", VARIABLES.last().unwrap().name);
                    }
                } else if let Some(output) = op.vec_apply(el.output.clone(), &er.output) {
                    save(
                        cache_level, cache,hashset_cache, exprs, var_count, exprs_length, Expr::bin(el.into(), er.into(), op_idx, expr_var_count, output), expr_length
                    );
                }
            }
        }
    });
}

fn find_binary_expressions_left(
    cache_level: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr_length: usize,
    er: &Expr,
    er_length: usize,
) {
    let var_index = exprs.len();
    let var_start_index = if var_index == 0
        || er.var_count[INPUTS.len() + var_index - 1] != 0
        || expr_length > MAX_CACHE_LENGTH
    {
        0
    } else {
        var_index
    };
    seq!(op_length in 1..=5 {
        if expr_length <= er_length + op_length {
            return;

        };
        for vc in &cache[var_start_index..] {
            for el in &vc[expr_length - er_length - op_length] {
                find_binary_operators(cache_level, cache, hashset_cache, exprs, var_count, exprs_length, expr_length, el, er, op_length);
            }
        }
    });
}

fn find_binary_expressions_right(
    cache_level: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr_length: usize,
    el: &Expr,
    el_length: usize,
) {
    seq!(op_length in 1..=5 {
        if expr_length <= el_length + op_length {
            return;
        };
        for vc in cache {
            for er in &vc[expr_length - el_length - op_length] {
                find_binary_operators(cache_level, cache, hashset_cache, exprs, var_count, exprs_length, expr_length, el, er, op_length);
            }
        }
    });
}

fn find_unary_operators(
    cache_level: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr_length: usize,
    er: &Expr,
) {
    let total_length = exprs_length + expr_length + 1;
    let total_var_count = match add_var_counts(var_count, er.var_count) {
        Some(vc) => vc,
        None => return,
    };
    if !can_use_required_vars(total_var_count, total_length, exprs.len()) {
        return;
    }
    seq!(idx in 0..10 {
        if let (Some(&op_idx), Some(op)) = (OP_UNARY_INDEX_TABLE.get(idx), UNARY_OPERATORS.get(idx)) {
            if op.can_apply(er) {
                if MATCH_1BY1 && is_leaf_expr(op_idx, total_length) {
                    let mut matcher = Matcher::new();
                    if er
                        .output
                        .iter()
                        .enumerate()
                        .all(|(i, &or)| matcher.match_one(exprs, i, (op.apply)(or)))
                        && matcher.match_final(exprs, None, er, op_idx)
                    {
                        for (e, v) in exprs.iter().zip(VARIABLES.iter()) {
                            print!("{}={e};", v.name);
                        }
                        println!("{}={op_idx}{er};", VARIABLES.last().unwrap().name);
                    }
                } else {
                    save(
                        cache_level, cache, hashset_cache, exprs, var_count, exprs_length, Expr::unary(er, op_idx, op.vec_apply(er.output.clone())), expr_length
                    );
                }
            }
        }
    });
}

fn find_unary_expressions(
    cache_level: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr_length: usize,
) {
    if expr_length < 2 {
        return;
    }
    let var_index = exprs.len();
    let var_start_index = if var_index == 0 || expr_length > MAX_CACHE_LENGTH {
        0
    } else {
        var_index
    };
    for vc in &cache[var_start_index..] {
        for er in &vc[expr_length - 1] {
            find_unary_operators(
                cache_level,
                cache,
                hashset_cache,
                exprs,
                var_count,
                exprs_length,
                expr_length,
                er,
            );
        }
    }
}

fn find_parens_expressions(
    cache_level: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr_length: usize,
) {
    let total_length = exprs_length + expr_length + 3;
    let var_index = exprs.len();
    let max_expr_length = get_max_expr_length(exprs_length, var_index);
    if expr_length < 4 || is_var_leaf_expr(OP_INDEX_PARENS, expr_length, max_expr_length) {
        return;
    }
    let var_start_index = if var_index == 0 || expr_length > MAX_CACHE_LENGTH {
        0
    } else {
        var_index
    };
    for vc in &cache[var_start_index..] {
        for er in &vc[expr_length - 2] {
            let total_var_count = match add_var_counts(var_count, er.var_count) {
                Some(vc) => vc,
                None => continue,
            };
            if !can_use_required_vars(total_var_count, total_length, var_index) {
                continue;
            }
            if er.op_idx < OP_INDEX_PARENS {
                save(
                    cache_level,
                    cache,
                    hashset_cache,
                    exprs,
                    var_count,
                    exprs_length,
                    Expr::parens(er),
                    expr_length,
                );
            }
        }
    }
}

fn find_variables_and_literals(
    cache_level: &mut CacheLevel,
    exprs: &Vec<&Expr>,
    expr_length: usize,
) {
    let var_index = exprs.len();
    if var_index != 0 {
        cache_level.push(Expr::variable(
            INPUTS.len() + var_index - 1,
            exprs.last().unwrap().output.clone(),
        ));
        return;
    }
    if expr_length == 1 {
        for (i, input) in INPUTS.iter().enumerate() {
            cache_level.push(Expr::variable(i, Vector::from_slice(input.vec)));
        }
    }
    for &lit in LITERALS {
        if positive_integer_length(lit) == expr_length {
            cache_level.push(Expr::literal(lit));
        }
    }
    if MAX_LITERAL > 0 {
        if let Some(m) = (10 as Num).checked_pow(expr_length as u32 - 1) {
            for lit in m..=m.saturating_mul(9).saturating_add(m - 1).min(MAX_LITERAL) {
                cache_level.push(Expr::literal(lit));
            }
        }
    }
}

fn add_to_cache(mut cn: CacheLevel, cache: &mut VarCache, hashset_cache: &mut HashSetCache) {
    let mut idx = 0;
    let start_ptr = cn.as_ptr();
    while idx < cn.len() {
        let expr = &cn[idx];
        match hashset_cache.entry(expr.into()) {
            Entry::Occupied(e) => {
                let oe = e.get();
                if expr.prec() > oe.as_ref().prec() {
                    if oe.as_ptr() >= start_ptr && oe.as_ptr() < unsafe { start_ptr.add(idx) } {
                        unsafe {
                            *oe.as_mut_ptr() = cn.swap_remove(idx);
                        }
                    } else {
                        e.replace();
                        idx += 1;
                    }
                } else {
                    cn.swap_remove(idx);
                }
            }
            Entry::Vacant(e) => {
                e.insert();
                if hashset_cache.len() == hashset_cache.capacity() {
                    cn.shrink_to_fit();
                }
                idx += 1;
            }
        }
    }
    cn.shrink_to_fit();
    cache.push(cn);
    hashset_cache.shrink_to_fit();
}

fn find_expressions_length(
    cache: &Cache,
    var_cache: &mut VarCache,
    hashset_cache: &mut HashSetCache,
    exprs: &Vec<&Expr>,
    var_count: VarCount,
    exprs_length: usize,
    expr_length: usize,
) {
    let mut cache_level = CacheLevel::new();
    find_variables_and_literals(&mut cache_level, exprs, expr_length);
    find_parens_expressions(
        &mut cache_level,
        cache,
        hashset_cache,
        exprs,
        var_count,
        exprs_length,
        expr_length,
    );
    find_unary_expressions(
        &mut cache_level,
        cache,
        hashset_cache,
        exprs,
        var_count,
        exprs_length,
        expr_length,
    );
    for vc in cache {
        for er_length in 1..expr_length - 1 {
            for er in &vc[er_length] {
                find_binary_expressions_left(
                    &mut cache_level,
                    cache,
                    hashset_cache,
                    exprs,
                    var_count,
                    exprs_length,
                    expr_length,
                    er,
                    er_length,
                );
            }
        }
    }
    add_to_cache(cache_level, var_cache, hashset_cache);
}

fn find_expressions(mut cache: Cache, exprs: Vec<&Expr>, var_count: VarCount, length: usize) {
    let mut hashset_cache = HashSet::new();
    let mut var_cache = vec![CacheLevel::new()];
    cache.push(unsafe { NonNull::from(&var_cache).as_ref() });

    let var_index = cache.len() - 1;
    let variable = &VARIABLES[var_index];

    let var_max_expr_length = get_var_max_expr_length(length, var_index);

    let max_expr_length =
        get_max_expr_length(length, var_index).min(var_max_expr_length.max(MAX_CACHE_LENGTH));

    let mut total_count = 0;
    let start = Instant::now();

    for expr_length in 1..=max_expr_length {
        let layer_start = Instant::now();
        if var_index == 0 {
            match expr_length {
                0..=MAX_CACHE_LENGTH | MAX_LENGTH => println!("Finding length {expr_length}..."),
                _ => println!("Finding length {expr_length}-{MAX_LENGTH}..."),
            }
        }
        find_expressions_length(
            &cache,
            &mut var_cache,
            &mut hashset_cache,
            &exprs,
            var_count,
            length,
            expr_length,
        );
        if var_index == 0 {
            let count = cache[0][expr_length].len();
            total_count += count;
            let time = layer_start.elapsed();
            println!("Explored {count} expressions in {time:?}");
            let total_time = start.elapsed();
            println!("Total: {total_count} expressions in {total_time:?}\n");
        }
    }

    let is_last_expr = var_index == VARIABLES.len() - 1;
    for expr_length in variable.min_length..=max_expr_length {
        let total_length = length + expr_length + 3;
        for vc in &cache {
            for expr in &vc[expr_length] {
                if expr.op_idx.prec() == 15 {
                    continue;
                }
                if let Some(total_var_count) = add_var_counts(var_count, expr.var_count) {
                    if is_last_expr {
                        if uses_required_vars(total_var_count) && Matcher::match_all(&exprs, expr) {
                            for (e, v) in exprs.iter().zip(VARIABLES.iter()) {
                                print!("{}={e};", v.name);
                            }
                            println!("{}={expr};", VARIABLES.last().unwrap().name);
                        }
                        continue;
                    }
                    let mut new_exprs = exprs.clone();
                    let new_expr = expr.clone();
                    new_exprs.push(&new_expr);
                    find_expressions(cache.clone(), new_exprs, total_var_count, total_length);
                }
            }
        }
    }
}

fn validate_input() {
    for i in INPUTS {
        assert_eq!(
            i.vec.len(),
            GOAL.len(),
            "INPUTS and GOAL must have equal length"
        );

        assert_ne!(i.max_uses, 0, "INPUTS maximum uses must be non-zero");
    }

    assert!(
        INPUTS.iter().map(|i| i.min_uses as usize).sum::<usize>() * 2 <= MAX_LENGTH + 1,
        "The minimum uses requirement will never be met"
    );

    let mut input_set = HashSet::new();
    for i in 0..INPUTS[0].vec.len() {
        let mut input = [0; INPUTS.len()];
        for j in 0..INPUTS.len() {
            input[j] = INPUTS[j].vec[i];
        }
        assert!(input_set.insert(input), "duplicated input {:?}", input);
    }
}

fn main() {
    validate_input();
    println!("sizeof(Expr) = {}", std::mem::size_of::<Expr>());

    find_expressions(Cache::new(), vec![], [0; SYMBOLS.len()], 0);
}
