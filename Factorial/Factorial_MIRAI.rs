use mirai_annotations::*;

fn fac(n: u64) -> u64 {
    if n == 0 { 1 } else { n * fac(n-1) }
}

fn factorial(n: u64) -> Option<u64> {
    if n == 0 { return Some(1); }
    let mut result: u64 = 1;
    let mut k: u64 = 1;

    checked_verify!(fac(0) == 1);
    while k < n {
        checked_verify!(result == fac(k));
        checked_verify!(k <= n);
        k = k + 1;
        result = match result.checked_mul(k) {
            Some(res) => res,
            None => return None,
        };
        checked_verify!(result == fac(k));
        checked_verify!(k <= n);
    }
    postcondition!(result == fac(n));
    Some(result)
}

fn main() {
    let _ = factorial(3);
}