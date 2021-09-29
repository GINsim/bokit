//! Some helper functions

/// In-place fast slice partitioning (the order is not preserved).
///
/// All items ```a``` such that ```f(a) == true``` are grouped at the start of the slice.
/// The returned value is the pivot index, it can be interpreted as the number of items
/// satisfying the closure or as the index of the first item which does not satisfy it.
///
/// ```
/// # use bokit::tools::quick_partition;
/// let mut slice = vec![4, 21, 5, 7, 12];
/// let pivot = quick_partition(&mut slice, |a| *a > 5);
///
/// // all items larger than 5 are now grouped at the start of the slice
/// slice[..pivot].iter().for_each(|a| assert!(*a > 5));
/// slice[pivot..].iter().for_each(|a| assert!(*a <= 5));
/// ```
///
/// The closure is applied exactly once on each element, which are swapped when needed.
/// To reduce the number of swap operation, it uses low and high indices and stops when
/// they join (as in quick-sort).
pub fn quick_partition<T, F: Fn(&T) -> bool>(slice: &mut [T], f: F) -> usize {
    let mut low = 0;
    let mut high = slice.len();

    // At each start of the main loop we maintain these invariants:
    // 1) low <= high
    // 2) slice[.. low] and slice[high ..] are placed properly
    // 3) slice[low .. high] untested
    loop {
        loop {
            if high == low {
                // Found the pivot
                return low;
            }

            // Move the low side forward as long as it satisfies f
            let p = &slice[low];
            if f(p) {
                low += 1;
                continue;
            }

            // The low item should be placed after the pivot. Switch to high side loop
            break;
        }

        // Now we know that the low item should be placed after the pivot
        loop {
            high -= 1;
            if high == low {
                // Found the pivot
                return low;
            }

            // Move the high side backward as long as it does NOT satisfy f
            let p = &slice[high];
            if !f(p) {
                continue;
            }

            // Swap this pair and return to the low side loop
            slice.swap(low, high);
            low += 1;
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::tools::*;

    #[test]
    fn test_quick_partition() {
        dispatch_check_pivot(vec![]);
        dispatch_check_pivot(vec![2]);
        dispatch_check_pivot(vec![123, 32]);
        dispatch_check_pivot(vec![4, 21, 0, 5, 7, 12]);
        dispatch_check_pivot(vec![1, 4, 7, 12, 6, 15, 2]);
    }

    fn dispatch_check_pivot(v: Vec<usize>) {
        check_pivot(&v, |_| true);
        check_pivot(&v, |_| true);
        check_pivot(&v, |a| *a > 7);
        check_pivot(&v, |a| *a % 3 > 0);
        check_pivot(&v, |a| *a == 8);
        check_pivot(&v, |a| *a % 5 < 3);
    }

    fn check_pivot<T: Clone, F: Fn(&T) -> bool>(v: &Vec<T>, f: F) {
        let mut slice = v.clone();
        let pivot = quick_partition(&mut slice, |a| f(a));
        slice[..pivot].iter().for_each(|a| assert!(f(a)));
        slice[pivot..].iter().for_each(|a| assert!(!f(a)));
    }
}
