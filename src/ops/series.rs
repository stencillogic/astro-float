//! Power series computation appliance.

use crate::common::util::log2_ceil;
use crate::common::util::log2_floor;
use crate::common::util::sqrt_int;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;
use smallvec::SmallVec;


const MAX_CACHE: usize = 128;


/// Generator of polynomial coefficients.
pub trait PolycoeffGen {
    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error>;
}


/// Estimate of the number of series iterations.
/// n is the precision, m is the negative power of x 
/// (i.e. x = f*2^(-m), where 0.5 <= f < 1).
pub fn series_niter(n: usize, m: usize) -> usize {
    let ln = log2_ceil(n);
    let lln = log2_floor(ln);
    n / (ln - lln + m)
}


// Rectangular series.
// p is the result precision
// niter is the estimated number of iterations
// x_first is the first power of x in the series
// x_step is a multiplication factor for each step
// polycoeff_gen is a generator of polynomial coeeficients for the series
// rm is the rounding mode.
// cost: niter * (O(mul) + O(add) + cost(polcoeff_gen.next)) + sqrt(niter) * O(mul) + cost(series_line(remainder))
// sinh polycoeff_gen cost: 2 O(mul) + 2 O(add)
pub fn series_rect<T: PolycoeffGen>(mut niter: usize, add: BigFloatNumber, x_first: BigFloatNumber, x_step: BigFloatNumber, mut polycoeff_gen: T, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
    debug_assert!(niter >= 4);
    let mut acc = BigFloatNumber::new(add.get_mantissa_max_bit_len())?;
    // build cache
    
    let mut cache = SmallVec::<[BigFloatNumber; MAX_CACHE]>::new();
    let sqrt_iter = sqrt_int(niter as u32) as usize;
    let cache_sz = MAX_CACHE.min(sqrt_iter);
    cache.try_reserve_exact(cache_sz).map_err(Error::MemoryAllocation)?;
    let mut x_pow = x_step.clone()?;
    for _ in 0..cache_sz {
        cache.push(x_pow.clone()?);
        x_pow = x_pow.mul(&x_step, rm)?;
    }
    // run computation
    let poly_val = compute_row(acc.get_mantissa_max_bit_len(), &cache, &mut polycoeff_gen, rm)?;
    acc = acc.add(&poly_val, rm)?;
    let mut terminal_pow = x_pow.clone()?;
    niter -= cache_sz;
    loop {
        let poly_val = compute_row(acc.get_mantissa_max_bit_len(), &cache, &mut polycoeff_gen, rm)?;
        let part = poly_val.mul(&terminal_pow, rm)?;
        acc = acc.add(&part, rm)?;
        terminal_pow = terminal_pow.mul(&x_pow, rm)?;
        niter -= cache_sz;
        if niter < cache_sz {
            break;
        }
    }
    drop(cache);

    acc = acc.mul(&x_first, rm)?;
    terminal_pow = terminal_pow.mul(&x_first, rm)?;
    acc = acc.add(&add, rm)?;
    acc = if niter < MAX_CACHE * 10 { // probably not too many iterations left
        series_horner(acc, terminal_pow, x_step, polycoeff_gen, rm)
    } else {
        series_line(acc, terminal_pow, x_step, polycoeff_gen, rm)
    }?;
    Ok(acc)
}

// Linear series
// cost: niter * (2 * O(mul) + O(add) + cost(polcoeff_gen.next))
pub fn series_line<T: PolycoeffGen>(mut acc: BigFloatNumber, x_first: BigFloatNumber, x_step: BigFloatNumber, mut polycoeff_gen: T, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
    let mut x_pow = x_first;
    loop {
        let coeff = polycoeff_gen.next(rm)?;
        let part = x_pow.mul(coeff, rm)?;
        if part.get_exponent() as isize <= acc.get_exponent() as isize - acc.get_mantissa_max_bit_len() as isize {
            break;
        }
        acc = acc.add(&part, rm)?;
        x_pow = x_pow.mul(&x_step, rm)?;
    }
    Ok(acc)
}

// compute row of rectangle series.
fn compute_row<T: PolycoeffGen>(p: usize, cache: &[BigFloatNumber], polycoeff_gen: &mut T, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
    let mut acc = BigFloatNumber::new(p)?;
    let coeff = polycoeff_gen.next(rm)?;
    acc = acc.add(coeff, rm)?;
    for x_pow in cache {
        let coeff = polycoeff_gen.next(rm)?;
        let add = x_pow.mul(coeff, rm)?;
        acc = acc.add(&add, rm)?;
    }
    Ok(acc)
}


/// Horner's method
pub fn series_horner<T: PolycoeffGen>(add: BigFloatNumber, x_first: BigFloatNumber, x_step: BigFloatNumber, mut polycoeff_gen: T, rm: RoundingMode) -> Result<BigFloatNumber, Error> {

    debug_assert!(x_first.e <= 0);
    debug_assert!(x_step.e <= 0);

    // determine number of parts and cache plynomial coeffs.
    let mut cache = SmallVec::<[BigFloatNumber; MAX_CACHE]>::new();
    let mut x_p = (-x_first.e) as isize + (-x_step.e) as isize;
    let mut coef_p = 0;
    while x_p + coef_p < add.get_mantissa_max_bit_len() as isize {
        let coeff = polycoeff_gen.next(rm)?;
        coef_p = (-coeff.e) as isize;
        x_p += (-x_step.e) as isize;
        cache.push(coeff.clone()?);
    }

    let last_coeff = polycoeff_gen.next(rm)?;
    let mut acc = last_coeff.clone()?;
    for coeff in cache.iter().rev() {
        acc = acc.mul(&x_step, rm)?;
        acc = acc.add(coeff, rm)?;
    }
    acc = acc.mul(&x_first, rm)?;
    acc = acc.add(&add, rm)?;

    Ok(acc)
}

/* Is it possbile to make it more effective than series_rect?
    // compute series using n dimensions
    // p is the result precision
    // niter is the estimated number of iterations
    // x_first is the first power of x in the series
    // x_step is a multiplication factor for each step
    // polycoeff_gen is a generator of polynomial coefficients for the series
    // rm is the rounding mode.
    fn ndim_series(n: usize, niter: usize, add: BigFloatNumber, x_factor: BigFloatNumber, x_step: BigFloatNumber, mut polycoeff_gen: PolycoeffGen, rm: RoundingMode) -> Result<Self, Error> {

        debug_assert!((2..=8).contains(&n));

        let mut acc = BigFloatNumber::new(add.get_mantissa_max_bit_len())?;

        // build cache
        let mut cache = SmallVec::<[BigFloatNumber; MAX_CACHE]>::new();

        let cache_dim_sz = nroot_int(niter as u32, n) as usize - 1;
        let cache_dim_sz = cache_dim_sz.min(MAX_CACHE / (n - 1));

        let mut x_pow = x_step.clone()?;
        for _ in 0..n-1 {
            let cache_step = x_pow.clone()?;
            for _ in 0..cache_dim_sz {
                cache.push(x_pow.clone()?);
                x_pow = x_pow.mul(&cache_step, rm)?;
            }
        }

        // run computation
        let poly_val = Self::compute_cube(acc.get_mantissa_max_bit_len(), n - 1, rm, &cache, cache_dim_sz, &mut polycoeff_gen)?;
        acc = acc.add(&poly_val, rm)?;
        let mut terminal_pow = x_pow.clone()?;
        for _ in 1..cache_dim_sz {
            let poly_val = Self::compute_cube(acc.get_mantissa_max_bit_len(), n - 1, rm, &cache, cache_dim_sz, &mut polycoeff_gen)?;
            let part = poly_val.mul(&terminal_pow, rm)?;
            acc = acc.add(&part, rm)?;
            terminal_pow = terminal_pow.mul(&x_pow, rm)?;
        }

        acc = acc.mul(&x_factor, rm)?;
        terminal_pow = terminal_pow.mul(&x_factor, rm)?;
        acc = acc.add(&add, rm)?;
        acc = Self::line_series(acc, terminal_pow, x_step, polycoeff_gen, rm)?;

        Ok(acc)
    }

    fn compute_cube(p: usize, n: usize, rm: RoundingMode, cache: &[BigFloatNumber], cache_dim_sz: usize, polycoeff_gen: &mut PolycoeffGen) -> Result<Self, Error> {
        if n > 1 {
            let mut acc = BigFloatNumber::new(p)?;
            let cache_dim_sz = cache_dim_sz;

            // no need to multityply the returned coefficient of the first cube by 1.
            let poly_val = Self::compute_cube(p, n - 1, rm, cache, cache_dim_sz, polycoeff_gen)?;
            acc = acc.add(&poly_val, rm)?;

            // the remaining require multiplication
            for x_pow in &cache[cache_dim_sz*(n-1)..cache_dim_sz*n] {
                let poly_val =  Self::compute_cube(p, n - 1, rm, cache, cache_dim_sz, polycoeff_gen)?;
                let add = x_pow.mul(&poly_val, rm)?;
                acc = acc.add(&add, rm)?;
            }
            Ok(acc)
        } else {
            Self::compute_row(p, &cache[..cache_dim_sz], polycoeff_gen, rm)
        }
    } 
*/