use creusot_contracts::*;

#[logic]
#[variant(n)]
fn fac(n: Int) -> Int {
    pearlite! {
        if n <= 0 { 1 } else { n * fac(n-1) }
    }
}

#[ensures(
    match result {
        Some(res) => res@ == fac(n@),
        None => true,
})]
fn factorial(n: u64) -> Option<u64> {
    if n == 0 { return Some(1); }
    let mut result: u64 = 1;
    let mut k: u64 = 1;

    proof_assert!(fac(0) == 1);

    #[invariant(result@ == fac(k@))]
    #[invariant(k <= n)]
    while k < n {
        k = k + 1;
        result = match result.checked_mul(k) {
            Some(res) => res,
            None => return None,
        };
    }
    Some(result)
}

fn main() {
    let _res = factorial(2);
}
