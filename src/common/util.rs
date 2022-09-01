//! Auxiliary functions.


/// integer logarithm base 2 of a number.
pub fn log2_ceil(mut n: usize) -> usize {
    let mut ret = 0;
    let mut sticky = 0;
    while n > 1 {
        if n & 1 != 0 {
            sticky = 1;
        }
        ret += 1;
        n >>= 1;
    }
    ret + sticky
}

/// integer logarithm base 2 of a number.
pub fn log2_floor(mut n: usize) -> usize {
    let mut ret = 0;
    while n > 1 {
        ret += 1;
        n >>= 1;
    }
    ret
}


/// square root integer approximation.
pub fn sqrt_int(a: u32) -> u32 {
    let a = a as u64;
    let mut x = a;
    for _ in 0..20 {
        if x == 0 {
            break;
        }
        x = (a / x + x) >> 1;
    }
    x as u32
}
 
/// n-root integer approximation.
#[allow(dead_code)]
pub fn nroot_int(a: u32, n: usize) -> u32 {
    let a = a as u64;
    let mut x = a;
    let n = n as u64;
    for _ in 0..5*(n-1) {
        if x == 0 {
            break;
        }
        x = nroot_step(x, n, a);
        x = nroot_step(x, n, a);
        x = nroot_step(x, n, a);
        x = nroot_step(x, n, a);
    }
    x as u32
}

#[inline]
fn nroot_step(x: u64, n: u64, a: u64) -> u64 {
    let mut xx = a;
    for _ in 0..n-1 {
        xx /= x;
    }
    ((n - 1) * x + xx) / n
}

// cost of multiplication of two numbers with precision p.
pub fn get_mul_cost(p: usize) -> usize {
    if p < 70 {
        p*p
    } else {
        // toom-3
        if p < 1625 {
            sqrt_int((p*p*p) as u32) as usize
        } else {
            let q = sqrt_int(p as u32) as usize;
            q*q*q
        }
    }
}


// cost of addition/subtraction of two numbers with precision p.
#[inline]
pub fn get_add_cost(p: usize) -> usize {
    p
}


// Estimate of sqrt op cost.
#[inline]
pub fn get_sqrt_cost(p: usize, cost_mul: usize, cost_add: usize) -> usize {
    let log3_estimate = (log2_floor(p) * 41349) >> 16;
    log3_estimate * (5 * cost_mul + 2 * cost_add) / 2
}