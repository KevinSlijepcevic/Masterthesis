use prusti_contracts::*;

#[extern_spec]
impl<T> std::option::Option<T> {
    #[pure]
    #[ensures(result == matches!(self, None))]
    pub const fn is_none(&self) -> bool;
}

#[extern_spec]
impl u64 {
    #[ensures(self * rhs > u64::MAX ==> result.is_none())]
    #[ensures(self * rhs <= u64::MAX ==> result == Some((self * rhs)))]
    pub fn checked_mul(self, rhs: u64) -> Option<u64>;
}

predicate! {
    fn fac(n: u64) -> u64 {
        if n <= 0 { 1 } else { n * fac(n-1) }
    }
}

#[ensures(
    match result {
        Some(res) => res == fac(n),
        None => true,
    }
)]
fn factorial(n: u64) -> Option<u64> {
    if n == 0 { return Some(1); }
    let mut result: u64 = 1;
    let mut k: u64 = 1;

    prusti_assert!(fac(0) == 1);
    while k < n {
            body_invariant!(result == fac(k));
            body_invariant!(k <= n);
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
