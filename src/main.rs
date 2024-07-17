#![cfg_attr(feature = "simd", feature(portable_simd))]

pub mod expr;
pub mod operator;
pub mod symbol;

#[path = "params.rs"]
pub mod params;

#[cfg_attr(all(feature = "simd", feature = "portable_simd"), path = "vec_simd.rs")]
#[cfg_attr(not(feature = "simd"), path = "vec.rs")]
pub mod vec;

use expr::{Expr, NonNullExpr, SymCount};
use operator::*;
use params::*;
use symbol::SYMBOLS;

use vec::Vector;

use hashbrown::{hash_set::Entry, HashMap, HashSet};
use seq_macro::seq;
use std::time::Instant;

// cache[length][output] = highest-prec expression of that length yielding that output
type CacheLevel = Vec<Expr>;
type Cache = Vec<CacheLevel>;

type HashSetCache = HashSet<NonNullExpr>;

fn positive_integer_length(mut k: Num) -> usize {
    let mut l = 1;
    while k >= 10 {
        k /= 10;
        l += 1;
    }
    l
}

fn can_use_required_symbols(sym_count: SymCount, length: usize) -> bool {
    let missing_uses: u8 = sym_count
        .iter()
        .zip(SYMBOLS.iter())
        .map(|(&c, s)| s.min_uses - std::cmp::min(c, s.min_uses))
        .sum();
    length + missing_uses as usize * (1 + MIN_BINARY_OP_LEN) <= MAX_LENGTH
}

fn uses_required_symbols(sym_count: SymCount) -> bool {
    sym_count
        .iter()
        .zip(SYMBOLS.iter())
        .all(|(&c, s)| c >= s.min_uses)
}

fn add_sym_counts(mut sym_count: SymCount, sym_count_: SymCount) -> Option<SymCount> {
    for ((l, &r), i) in sym_count
        .iter_mut()
        .zip(sym_count_.iter())
        .zip(SYMBOLS.iter())
    {
        *l += r;
        if *l > i.max_uses {
            return None;
        }
    }
    Some(sym_count)
}

fn is_leaf_expr(op_idx: OpIndex, length: usize) -> bool {
    length >= MAX_EXPR_LENGTH
        || length == MAX_EXPR_LENGTH - 1
            && (UNARY_OPERATORS.len() == 0 || op_idx.prec() < UnaryOp::EMPTY.prec)
}

const fn has_unlimited_symbol() -> bool {
    let mut i = 0;
    while i < SYMBOLS.len() {
        if SYMBOLS[i].max_uses == u8::MAX {
            return true;
        }
        i += 1;
    }
    false
}

fn save(level: &mut CacheLevel, expr: Expr, n: usize, cache: &Cache, hashset_cache: &HashSetCache) {
    if NUM_EXPRS == 1 {
        if uses_required_symbols(expr.sym_count) && Matcher::match_all(&expr) {
            println!("{expr}");
            return;
        }

        if !MATCH_1BY1 && is_leaf_expr(expr.op_idx, n) {
            return;
        }

        let cant_use_more_symbols = !has_unlimited_symbol()
            && expr
                .sym_count
                .iter()
                .zip(SYMBOLS.iter())
                .all(|(&c, s)| c == s.max_uses);

        if cant_use_more_symbols {
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

    if n <= MAX_LENGTH - 2 {
        let expr_ptr: NonNullExpr = (&expr).into();
        if let Some(e) = hashset_cache.get(&expr_ptr) {
            if e.as_ref().prec() >= expr.prec() {
                return;
            }
        }
    }

    if n > MAX_CACHE_LENGTH {
        if NUM_EXPRS > 1 {
            find_multi_exprs_dfs(
                cache,
                &mut [&expr; NUM_EXPRS],
                expr.sym_count,
                n,
                0,
                0,
                false,
            );
        }
        for dfs_len in n + 1 + MIN_BINARY_OP_LEN..=MAX_EXPR_LENGTH {
            find_binary_expressions(level, cache, hashset_cache, dfs_len, n, &expr);
        }
        if n + 1 <= MAX_EXPR_LENGTH {
            find_unary_operators(level, cache, hashset_cache, n + 1, &expr);
        }
        if !is_leaf_expr(OP_INDEX_PARENS, n + 2) && expr.op_idx < OP_INDEX_PARENS {
            save(
                level,
                Expr::parens((&expr).into()),
                n + 2,
                cache,
                hashset_cache,
            );
        }
        return;
    }

    level.push(expr);
}

fn find_multi_exprs_dfs<'a>(
    cache: &'a Cache,
    exprs: &mut [&'a Expr; NUM_EXPRS],
    sym_count: SymCount,
    expr_length: usize,
    index: usize,
    k: usize,
    used_expr: bool,
) {
    if index == NUM_EXPRS {
        if uses_required_symbols(sym_count) && Matcher::match_multi_exprs(exprs) {
            for (index, expr) in exprs.iter().enumerate() {
                match index + 1 {
                    NUM_EXPRS => println!("{expr}"),
                    _ => print!("{expr};"),
                }
            }
        }
        return;
    }

    if !used_expr {
        find_multi_exprs_dfs(
            cache,
            exprs,
            sym_count,
            expr_length,
            index + 1,
            k + expr_length + 1,
            true,
        );
        let is_last_expr = index + 1 == NUM_EXPRS;
        if is_last_expr {
            return;
        }
    }

    let max_expr_len = if used_expr {
        MAX_LENGTH - k - (NUM_EXPRS - index - 1) * (MIN_EXPR_LENGTH + 1)
    } else {
        MAX_LENGTH - k - (NUM_EXPRS - index - 2) * (MIN_EXPR_LENGTH + 1) - expr_length - 1
    };

    for new_expr_len in MIN_EXPR_LENGTH..=max_expr_len {
        for new_expr in cache[new_expr_len].iter() {
            if new_expr.is_literal() {
                continue;
            }
            exprs[index] = new_expr;
            if let Some(new_sym_count) = add_sym_counts(sym_count, new_expr.sym_count) {
                find_multi_exprs_dfs(
                    cache,
                    exprs,
                    new_sym_count,
                    expr_length,
                    index + 1,
                    k + new_expr_len + 1,
                    used_expr,
                );
            }
        }
    }
}

fn find_multi_exprs<'a>(
    cache: &'a Cache,
    exprs: &mut [&'a Expr; NUM_EXPRS],
    sym_count: SymCount,
    index: usize,
    n: usize,
    k: usize,
) {
    if index == NUM_EXPRS {
        if uses_required_symbols(sym_count) && Matcher::match_multi_exprs(exprs) {
            for (index, expr) in exprs.iter().enumerate() {
                match index + 1 {
                    NUM_EXPRS => println!("{expr}"),
                    _ => print!("{expr};"),
                }
            }
        }
        return;
    }

    let is_last_expr = index + 1 == NUM_EXPRS;
    let max_expr_len = n - k - (NUM_EXPRS - index - 1) * (MIN_EXPR_LENGTH + 1);
    let min_expr_len = if is_last_expr {
        max_expr_len
    } else {
        MIN_EXPR_LENGTH
    };

    for new_expr_len in min_expr_len..=max_expr_len {
        for new_expr in cache[new_expr_len].iter() {
            if new_expr.is_literal() {
                continue;
            }
            if let Some(new_sym_count) = add_sym_counts(sym_count, new_expr.sym_count) {
                exprs[index] = new_expr;
                find_multi_exprs(
                    cache,
                    exprs,
                    new_sym_count,
                    index + 1,
                    n,
                    k + new_expr_len + 1,
                );
            }
        }
    }
}

#[inline(always)]
fn find_binary_operators(
    cn: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &HashSetCache,
    n: usize,
    el: &Expr,
    er: &Expr,
    op_len: usize,
) {
    if er.is_literal() && el.is_literal() {
        return;
    }
    let sym_count = match add_sym_counts(el.sym_count, er.sym_count) {
        Some(sym_count) => sym_count,
        None => return,
    };
    if !can_use_required_symbols(sym_count, n) {
        return;
    }
    seq!(idx in 0..100 {
        if let (Some(&op_idx), Some(op)) = (OP_BINARY_INDEX_TABLE.get(idx), BINARY_OPERATORS.get(idx)) {
            if op.name.len() == op_len && op.can_apply(el, er) {
                if MATCH_1BY1 && NUM_EXPRS == 1 && is_leaf_expr(op_idx, n) {
                    let mut matcher = Matcher::new();
                    if el
                        .output
                        .iter()
                        .zip(er.output.iter())
                        .enumerate()
                        .all(|(i, (&ol, &or))| match op.apply_(ol, or) {
                            Some(o) => matcher.match_one(i, o),
                            None => false,
                        })
                        && matcher.match_final(Some(el), er, op_idx)
                    {
                        println!("{el}{op_idx}{er}");
                    }
                } else if let Some(output) = op.vec_apply(el.output.clone(), &er.output) {
                    save(
                        cn,
                        Expr::bin(el.into(), er.into(), op_idx, sym_count, output),
                        n,
                        cache,
                        hashset_cache,
                    );
                }
            }
        }
    });
}

fn find_binary_expressions_left(
    cn: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &HashSetCache,
    n: usize,
    k: usize,
    er: &Expr,
) {
    seq!(op_len in 0..=5 {
        if n <= k + op_len {
            return;
        };
        for el in &cache[n - k - op_len] {
            find_binary_operators(cn, cache, hashset_cache, n, el, er, op_len);
        }
    });
}

fn find_binary_expressions(
    cn: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &HashSetCache,
    n: usize,
    k: usize,
    e1: &Expr,
) {
    seq!(op_len in 0..=5 {
        if n <= k + op_len {
            return;
        };
        for e2 in &cache[n - k - op_len] {
            find_binary_operators(cn, cache, hashset_cache, n, e1, e2, op_len);
            find_binary_operators(cn, cache, hashset_cache, n, e2, e1, op_len);
        }
    });
}

fn find_unary_operators(
    cn: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &HashSetCache,
    n: usize,
    er: &Expr,
) {
    if !can_use_required_symbols(er.sym_count, n) {
        return;
    }
    seq!(idx in 0..10 {
        if let (Some(&op_idx), Some(op)) = (OP_UNARY_INDEX_TABLE.get(idx), UNARY_OPERATORS.get(idx)) {
            if op.can_apply(er) {
                if MATCH_1BY1 && NUM_EXPRS == 1 && is_leaf_expr(op_idx, n) {
                    let mut matcher = Matcher::new();
                    if er
                        .output
                        .iter()
                        .enumerate()
                        .all(|(i, &or)| matcher.match_one(i, op.apply_(or)))
                        && matcher.match_final(None, er, op_idx)
                    {
                        println!("{op_idx}{er}");
                    }
                } else {
                    save(
                        cn,
                        Expr::unary(er, op_idx, op.vec_apply(er.output.clone())),
                        n,
                        cache,
                        hashset_cache,
                    );
                }
            }
        }
    });
}

fn find_unary_expressions(
    cn: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &HashSetCache,
    n: usize,
) {
    if n < 2 {
        return;
    }
    for r in &cache[n - 1] {
        find_unary_operators(cn, cache, hashset_cache, n, r);
    }
}

fn find_parens_expressions(
    cn: &mut CacheLevel,
    cache: &Cache,
    hashset_cache: &HashSetCache,
    n: usize,
) {
    if n < 4 || is_leaf_expr(OP_INDEX_PARENS, n) {
        return;
    }
    for er in &cache[n - 2] {
        if !can_use_required_symbols(er.sym_count, n) {
            continue;
        }
        if er.op_idx < OP_INDEX_PARENS {
            save(cn, Expr::parens(er), n, cache, hashset_cache);
        }
    }
}

fn find_symbols_and_literals(cn: &mut CacheLevel, n: usize) {
    if n == 1 {
        for (i, symbol) in SYMBOLS.iter().enumerate() {
            cn.push(Expr::symbol(i, Vector::from_slice(symbol.vec)));
        }
    }
    for &lit in LITERALS {
        if positive_integer_length(lit) == n {
            cn.push(Expr::literal(lit));
        }
    }
    if MAX_LITERAL > 0 {
        if let Some(m) = (10 as Num).checked_pow(n as u32 - 1) {
            for lit in m..=m.saturating_mul(9).saturating_add(m - 1).min(MAX_LITERAL) {
                cn.push(Expr::literal(lit));
            }
        }
    }
}

fn add_to_cache(mut cn: CacheLevel, cache: &mut Cache, hashset_cache: &mut HashSetCache) {
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

fn find_multiple_expressions(cache: &Cache, n: usize) {
    use rayon::prelude::*;

    if NUM_EXPRS == 1 {
        return;
    }

    let max_expr_len = n.saturating_sub((NUM_EXPRS - 1) * (MIN_EXPR_LENGTH + 1));

    (MIN_EXPR_LENGTH..=max_expr_len)
        .into_par_iter()
        .for_each(|k| {
            cache[k].par_iter().for_each(|expr| {
                find_multi_exprs(cache, &mut [expr; NUM_EXPRS], expr.sym_count, 1, n, k + 1);
            });
        });
}

fn find_expressions_multithread(
    mut_cache: &mut Cache,
    mut_hashset_cache: &mut HashSetCache,
    n: usize,
) {
    use rayon::prelude::*;

    let cache = &mut_cache;
    let hashset_cache = &mut_hashset_cache;

    let mut cn = (1..n.saturating_sub(MIN_BINARY_OP_LEN))
        .into_par_iter()
        .flat_map(|k| {
            cache[k].par_iter().map(move |r| {
                let mut cn = CacheLevel::new();
                find_binary_expressions_left(&mut cn, cache, hashset_cache, n, k, r);
                cn
            })
        })
        .chain(
            std::iter::once_with(|| {
                let mut cn = CacheLevel::new();
                find_parens_expressions(&mut cn, cache, hashset_cache, n);
                cn
            })
            .par_bridge(),
        )
        .chain(
            std::iter::once_with(|| {
                let mut cn = CacheLevel::new();
                find_unary_expressions(&mut cn, cache, hashset_cache, n);
                cn
            })
            .par_bridge(),
        )
        .flatten_iter()
        .collect();

    find_symbols_and_literals(&mut cn, n);

    add_to_cache(cn, mut_cache, mut_hashset_cache);
}

fn find_expressions(cache: &mut Cache, hashset_cache: &mut HashSetCache, n: usize) {
    let mut cn = CacheLevel::new();
    if n <= MAX_EXPR_LENGTH {
        find_symbols_and_literals(&mut cn, n);
        find_parens_expressions(&mut cn, cache, hashset_cache, n);
        find_unary_expressions(&mut cn, cache, hashset_cache, n);
        for k in 1..n.saturating_sub(MIN_BINARY_OP_LEN) {
            for r in &cache[k] {
                find_binary_expressions_left(&mut cn, cache, hashset_cache, n, k, r);
            }
        }
    }
    add_to_cache(cn, cache, hashset_cache);
}

fn validate_input() {
    assert_ne!(NUM_EXPRS, 0, "The number of expressions must be non-zero");
    assert_ne!(
        MIN_EXPR_LENGTH, 0,
        "The minimum expression length must be non-zero"
    );
    assert!(
        MIN_EXPR_LENGTH <= MAX_EXPR_LENGTH,
        "The minimum expression length must be less or equal to the maximum expression length"
    );
    assert!(
        (NUM_EXPRS - 1) * (MIN_EXPR_LENGTH + 1) + MAX_EXPR_LENGTH <= MAX_LENGTH,
        "The minimum & maximum expression lengths are not valid"
    );
    for s in SYMBOLS {
        assert_eq!(
            s.vec.len(),
            GOAL.len(),
            "SYMBOLS and GOAL must have equal length"
        );
        assert_ne!(s.max_uses, 0, "SYMBOLS maximum uses must be non-zero");
    }

    assert!(
        INPUTS.iter().map(|i| i.min_uses as usize).sum::<usize>() * (1 + MIN_BINARY_OP_LEN)
            <= MAX_LENGTH + 1,
        "The minimum uses requirement will never be met"
    );

    let mut symbol_set = HashSet::new();
    for i in 0..SYMBOLS[0].vec.len() {
        let mut symbol = [0; SYMBOLS.len()];
        for j in 0..SYMBOLS.len() {
            symbol[j] = SYMBOLS[j].vec[i];
        }
        assert!(symbol_set.insert(symbol), "duplicated symbol {:?}", symbol);
    }
}

fn main() {
    validate_input();

    let mut cache: Cache = vec![CacheLevel::new()];
    let mut hashset_cache: HashSetCache = HashSetCache::new();
    let mut total_count = 0;
    println!("sizeof(Expr) = {}", std::mem::size_of::<Expr>());
    let start = Instant::now();
    for n in 1..=MAX_LENGTH {
        let expr_length = n.saturating_sub((NUM_EXPRS - 1) * (MIN_EXPR_LENGTH + 1));
        if expr_length == 0 {
            continue;
        }
        match (expr_length, n) {
            (0..=MAX_CACHE_LENGTH, _) | (_, MAX_LENGTH) => {
                println!("Finding length {n}...")
            }
            _ => println!("Finding length {n}-{MAX_LENGTH}..."),
        }
        let layer_start = Instant::now();
        if expr_length >= MIN_MULTITHREAD_LENGTH {
            find_expressions_multithread(&mut cache, &mut hashset_cache, expr_length);
        } else {
            find_expressions(&mut cache, &mut hashset_cache, expr_length);
        }
        if expr_length <= MAX_CACHE_LENGTH {
            find_multiple_expressions(&cache, n);
        }
        let count = cache[expr_length].len();
        total_count += count;
        let time = layer_start.elapsed();
        println!("Explored {count} expressions in {time:?}");
        let total_time = start.elapsed();
        println!("Total: {total_count} expressions in {total_time:?}\n");
    }
    println!();
}
