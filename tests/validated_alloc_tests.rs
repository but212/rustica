use rustica::datatypes::validated::{NonEmptyErrors, Validated};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

thread_local! {
    static ALLOCS: Cell<usize> = const { Cell::new(0) };
    static DROPPED: Cell<usize> = const { Cell::new(0) };
}

fn bump() {
    ALLOCS.with(|c| c.set(c.get() + 1));
}

struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        bump();
        unsafe { System.alloc(l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        bump();
        unsafe { System.realloc(p, l, n) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

fn count_allocs<R>(f: impl FnOnce() -> R) -> (R, usize) {
    let before = ALLOCS.with(Cell::get);
    let r = f();
    (r, ALLOCS.with(Cell::get) - before)
}

#[allow(dead_code)]
struct DropDetector(usize);
impl Drop for DropDetector {
    fn drop(&mut self) {
        DROPPED.with(|c| c.set(c.get() + 1));
    }
}

#[test]
fn test_try_from_iter_single_alloc() {
    let (res, allocs) = count_allocs(|| NonEmptyErrors::try_from_iter(0..10u32));
    assert!(res.is_some());
    assert_eq!(allocs, 1);
}

#[test]
fn test_collect_valid_single_alloc() {
    let items: Vec<Validated<u64, &'static str>> = (0..100).map(Validated::valid).collect();
    let (res, allocs) = count_allocs(|| {
        let r: Validated<Vec<u64>, &'static str> = Validated::collect(items.into_iter());
        r
    });
    assert!(res.is_valid());
    // std specializes Vec::from_iter(vec.into_iter()) to reuse buffer.
    // 6 reallocs without capacity, target is exactly 1.
    assert_eq!(allocs, 1);
}

#[test]
fn test_collect_drops_values_immediately() {
    use std::rc::Rc;

    struct StepIter {
        curr: usize,
        observed_drop_at_step_12: Rc<Cell<usize>>,
    }

    impl Iterator for StepIter {
        type Item = Validated<DropDetector, &'static str>;

        fn next(&mut self) -> Option<Self::Item> {
            self.curr += 1;
            if self.curr <= 10 {
                Some(Validated::valid(DropDetector(self.curr)))
            } else if self.curr == 11 {
                Some(Validated::invalid("err"))
            } else if self.curr == 12 {
                self.observed_drop_at_step_12.set(DROPPED.with(Cell::get));
                Some(Validated::valid(DropDetector(self.curr)))
            } else {
                None
            }
        }
    }

    let before_dropped = DROPPED.with(Cell::get);
    let obs_cell = Rc::new(Cell::new(0));
    let iter = StepIter {
        curr: 0,
        observed_drop_at_step_12: Rc::clone(&obs_cell),
    };

    let res: Validated<Vec<DropDetector>, &'static str> = Validated::collect(iter);
    assert!(res.is_invalid());

    let drop_at_12 = obs_cell.get() - before_dropped;
    // Exactly the 10 preceding valid items should have been dropped upon first error
    assert_eq!(drop_at_12, 10);
}

#[test]
fn test_collect_moves_first_error_buffer() {
    let original = NonEmptyErrors::new("error_payload");
    let original_ptr = original.as_slice().as_ptr();
    let item: Validated<(), &'static str> = Validated::Invalid(original);

    let res: Validated<Vec<()>, &'static str> = Validated::collect([item].into_iter());
    let collected_errs = res.error_payload().expect("must be invalid");
    let collected_ptr = collected_errs.as_slice().as_ptr();

    // Must move the first error buffer without cloning into a new Vec
    assert_eq!(original_ptr, collected_ptr);
}

#[test]
fn test_zip3_error_realloc_count() {
    let e1 = Validated::<(), &'static str>::invalid("err1");
    let e2 = Validated::<(), &'static str>::invalid_many((0..100).map(|_| "err2"));
    let e3 = Validated::<(), &'static str>::invalid_many((0..100).map(|_| "err3"));

    let (res, allocs) = count_allocs(|| e1.zip_with3(e2, e3, |_, _, _| ()));
    assert!(res.is_invalid());
    assert_eq!(res.error_slice().len(), 201);
    // Old implementation: e1.extend(e2) reallocates, then .extend(e3) reallocates = 2 reallocs.
    // Target implementation with single pre-reserve: at most 1 realloc.
    assert!(allocs <= 1, "Expected <= 1 reallocation, got {allocs}");
}

#[test]
fn test_collect_early_error_zero_allocs_for_values() {
    // 1000 items with first item invalid: values must NEVER allocate
    let first = Validated::<[u64; 16], &'static str>::invalid("early_err");
    let iter = core::iter::once(first).chain((1..1000).map(|i| Validated::valid([i as u64; 16])));

    // The only allocation should be the error collection itself (0 for values buffer)
    let (res, allocs) = count_allocs(|| {
        let r: Validated<Vec<[u64; 16]>, &'static str> = Validated::collect(iter);
        r
    });
    assert!(res.is_invalid());
    // Since the first item was Invalid and moved via into_vec(),
    // values was never reserved/allocated, resulting in 0 extra allocations.
    assert_eq!(allocs, 0);
}
