use creusot_contracts::*;

#[predicate]
fn sorted_range(v: Seq<i32>, start: Int, end: Int) -> bool {
    pearlite! {
        forall<k : Int, l : Int> start <= k && k < l && l < end ==> v[k] <= v[l]
    }
}

#[predicate]
fn sorted(v: Seq<i32>) -> bool {
    sorted_range(v, 0, v.len())
}

#[predicate]
fn partioned(v: Seq<i32>, i: Int) -> bool {
    pearlite! {
        forall<k : Int, l : Int> 0 <= k && k < i && i <= l && l < v.len() ==> v[k] <= v[l]
    }
}

#[ensures(sorted((^arr)@))]
#[ensures((^arr)@.permutation_of(arr@))]
fn bubblesort(arr: &mut Vec<i32>) {
    let old_arr = gh! { arr };
    let mut i: usize = 0;

    #[invariant(0 <= i@ && i@ <= arr@.len())]
    #[invariant(arr@.permutation_of(old_arr@))]
    #[invariant(sorted_range(arr@, arr@.len() - i@, arr@.len()))]
    //#[invariant(partioned(arr@, arr@.len() - i@))]
    while i < arr.len() {
        let mut j: usize = 0;

        #[invariant(0 <= j@ && j@ <= arr@.len() - i@ - 1)]
        #[invariant(arr@.permutation_of(old_arr@))]
        #[invariant(forall<k : Int> 0 <= k && k < j@ ==> arr[k] <= arr[j@])]
        #[invariant(sorted_range(arr@, arr@.len() - i@, arr@.len()))]
        //#[invariant(partioned(arr@, arr@.len() - i@))]
        while j < arr.len() - i - 1 {
            if arr[j] > arr[j+1] {
                arr.swap(j, j+1);
            }
            j += 1;
        }
        i += 1;
    }
}

fn main() {
    let mut arr = creusot_contracts::vec![2,4,3,9,1];
    bubblesort(&mut arr);
}