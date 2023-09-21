#![allow(unused_comparisons)]
use prusti_contracts::*;

#[extern_spec]
impl<T> [T] {
    #[pure]
    pub fn len(&self) -> usize;
}

#[extern_spec]
impl<T: PartialEq> [T] {
    #[requires(0 <= a && a < self.len())]
    #[requires(0 <= b && b < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(snap(&self[a]) == old(snap(&self[b])))]
    #[ensures(snap(&self[b]) == old(snap(&self[a])))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() && i != a && i != b) ==> snap(&self[i]) == old(snap(&self[i]))))]
    pub fn swap(&mut self, a: usize, b: usize);
}

predicate! {
    fn sorted_range(v: &[i32], start: usize, end: usize) -> bool {
            forall(|k : usize, l : usize| (start <= k && k < l && l < end  
            && 0 <= start && start < v.len()
            && 0 <= end && end < v.len())
            ==> v[k] <= v[l])
    }
}

predicate! {
    fn sorted(v: &[i32]) -> bool {
        sorted_range(v, 0, v.len())
    }
}

#[ensures(old(arr.len()) == arr.len())]
#[ensures(sorted(arr))]
fn bubblesort(arr: &mut [i32]) {
    let old_len = arr.len();
    let mut i: usize = 0;

    while i < arr.len() {
        body_invariant!(0 <= i && i <= arr.len());
        body_invariant!(old_len == arr.len());
        body_invariant!(sorted_range(arr, arr.len() - i, arr.len()));
        let mut j: usize = 0;
    
        while j < arr.len() - i - 1 {
            body_invariant!(0 <= j && j <= arr.len() - i - 1);
            body_invariant!(old_len == arr.len());
            body_invariant!(forall(|k: usize| (0 <= k && k < j) ==> arr[k] <= arr[j]));
            body_invariant!(sorted_range(arr, arr.len() - i, arr.len()));
            if arr[j] > arr[j+1] {
                arr.swap(j, j+1);
            }
            j += 1;
        }
        i += 1;
    }
}

fn main() {
    let mut arr = Vec::new();
    arr.push(2);
    arr.push(4);
    arr.push(3);
    arr.push(9);
    arr.push(1);

    bubblesort(arr.as_mut_slice());
}