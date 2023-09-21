use vstd::prelude::*;

verus! {
    spec fn fac(n: int) -> int
        decreases n
    {
        if n <= 0 { 1 } else { n * fac(n-1) }
    }

    exec fn factorial(n: u32) -> (result: Option<u32>)
        ensures
            match result {
                Some(res) => res as int == fac(n as int),
                None => true
            }
    {
        if n == 0 { return Some(1); }
        let mut result: u32 = 1;
        let mut k: u32 = 1;

        assert(fac(0) == 1 as int);
        while k < n
            invariant
                result as int == fac(k as int),
                k <= n,
        {
            k = k + 1;
            result = match result.checked_mul(k) {
                Some(res) => res,
                None => return None,
            };
        }
        Some(result)
    }

fn main() {
    factorial(2);
}

}