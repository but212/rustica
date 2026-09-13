//! Regression and parity tests verifying that Rust stdlib primitives provide exact behavioral
//! equivalence for all deprecated Rustica types, wrappers, and combinators.

#![allow(deprecated)]

use rustica::datatypes::choice::Choice;
use rustica::datatypes::id::Id;
use rustica::datatypes::wrapper::first::First;
use rustica::datatypes::wrapper::last::Last;
use rustica::datatypes::wrapper::max::Max;
use rustica::datatypes::wrapper::min::Min;
use rustica::datatypes::wrapper::product::Product;
use rustica::datatypes::wrapper::sum::Sum;
use rustica::traits::foldable::FoldableExt;
use rustica::traits::functor::Functor;
use rustica::traits::monoid::Monoid;
use rustica::traits::one::One;
use rustica::traits::semigroup::Semigroup;

#[test]
fn test_c01_first_last_parity_with_option_or() {
    let cases = [
        (Some(10), Some(20)),
        (Some(10), None),
        (None, Some(20)),
        (None, None),
    ];

    for (a, b) in cases {
        let first_combined = First(a).combine(First(b)).into_inner();
        let std_first = a.or(b);
        assert_eq!(first_combined, std_first);

        let last_combined = Last(a).combine(Last(b)).into_inner();
        let std_last = b.or(a);
        assert_eq!(last_combined, std_last);
    }
}

#[test]
fn test_c02_min_max_parity_with_std_cmp() {
    let pairs = [(5, 10), (10, 5), (7, 7), (-3, 4)];

    for (a, b) in pairs {
        let min_combined = Min(a).combine(Min(b)).into_inner();
        assert_eq!(min_combined, std::cmp::min(a, b));

        let max_combined = Max(a).combine(Max(b)).into_inner();
        assert_eq!(max_combined, std::cmp::max(a, b));
    }

    let list = [4, 2, 9, 1, 7, 5];
    let folded_min = list
        .iter()
        .copied()
        .map(Min)
        .reduce(|acc, x| acc.combine(x))
        .map(Min::into_inner);
    assert_eq!(folded_min, list.iter().copied().min());

    let folded_max = list
        .iter()
        .copied()
        .map(Max)
        .reduce(|acc, x| acc.combine(x))
        .map(Max::into_inner);
    assert_eq!(folded_max, list.iter().copied().max());
}

#[test]
fn test_c03_sum_product_parity_with_std_ops() {
    let numbers = [1, 2, 3, 4, 5];

    let sum_wrapper: i32 = numbers
        .iter()
        .copied()
        .map(Sum)
        .fold(Sum(0), |acc, x| acc.combine(x))
        .into_inner();
    let std_sum: i32 = numbers.iter().sum();
    assert_eq!(sum_wrapper, std_sum);
    assert_eq!(Sum::<i32>::empty().into_inner(), 0);

    let prod_wrapper: i32 = numbers
        .iter()
        .copied()
        .map(Product)
        .fold(Product(i32::one()), |acc, x| acc.combine(x))
        .into_inner();
    let std_prod: i32 = numbers.iter().product();
    assert_eq!(prod_wrapper, std_prod);
    assert_eq!(Product::<i32>::empty().into_inner(), 1);
    assert_eq!(i32::one(), 1);
}

#[test]
fn test_c04_id_parity_with_plain_rust_expressions() {
    let val = 42;
    let id = Id::new(val);

    assert_eq!(id.into_inner(), std::convert::identity(val));

    let f = |x: i32| x * 2 + 1;
    assert_eq!(id.fmap(f).into_inner(), f(val));

    let id_items: Vec<_> = Id::new(99).into_iter().collect();
    assert_eq!(id_items, vec![99]);
}

#[test]
fn test_c05_choice_first_match_parity_with_iter_find_map() {
    let choice = Choice::new(10, [25, 40, 55]);

    let f = |&x: &i32| if x > 20 { Some(x * 2) } else { None };

    let choice_res = choice.first_match(f);
    let iter_res = choice.iter().find_map(f);

    assert_eq!(choice_res, Some(50));
    assert_eq!(choice_res, iter_res);

    let f_none = |&x: &i32| if x > 100 { Some(x) } else { None };
    assert_eq!(choice.first_match(f_none), None);
    assert_eq!(choice.iter().find_map(f_none), None);
}

#[test]
fn test_c06_foldable_ext_parity_with_iterator_methods() {
    let list = vec![3, 1, 4, 1, 5, 9, 2, 6];

    assert_eq!(list.to_vec(), list);
    assert_eq!(list.sum_values(), list.iter().sum::<i32>());
    assert_eq!(list.product_values(), list.iter().product::<i32>());
    assert_eq!(list.maximum(), list.iter().max().copied());
    assert_eq!(list.minimum(), list.iter().min().copied());

    let fold_reduced = list.reduce(|a, b| a + b);
    let iter_reduced = list.iter().copied().reduce(|a, b| a + b);
    assert_eq!(fold_reduced, iter_reduced);

    let empty: Vec<i32> = vec![];
    assert_eq!(empty.maximum(), empty.iter().max().copied());
    assert_eq!(empty.minimum(), empty.iter().min().copied());
    assert_eq!(empty.reduce(|a, b| a + b), None);
}

#[test]
fn test_c07_state_parity_with_mutable_ref_and_pure_fn() {
    use rustica::datatypes::state::State;

    // Rustica State monad:
    let counter_state: State<i32, i32> = State::new(|s: i32| (s, s + 1));
    let (val1, s1) = counter_state.run_state(10);
    assert_eq!(val1, 10);
    assert_eq!(s1, 11);

    // Idiomatic Rust replacement A: &mut state
    let mut state = 10;
    let old_val = {
        let prev = state;
        state += 1;
        prev
    };
    assert_eq!(old_val, 10);
    assert_eq!(state, 11);

    // Idiomatic Rust replacement B: pure transition function Fn(S) -> (A, S)
    let transition = |s: i32| (s, s + 1);
    let (val2, s2) = transition(10);
    assert_eq!(val2, 10);
    assert_eq!(s2, 11);
}

#[test]
fn test_c08_reader_parity_with_borrow_and_closure() {
    use rustica::datatypes::reader::Reader;

    #[derive(Clone)]
    struct Config {
        multiplier: i32,
    }

    let cfg = Config { multiplier: 3 };

    // Rustica Reader monad:
    let reader: Reader<Config, i32> = Reader::new(|c: Config| 10 * c.multiplier);
    assert_eq!(reader.run_reader(cfg.clone()), 30);

    // Idiomatic Rust replacement A: pass by reference (&Context)
    fn compute(c: &Config, base: i32) -> i32 {
        base * c.multiplier
    }
    assert_eq!(compute(&cfg, 10), 30);

    // Idiomatic Rust replacement B: closure capturing environment
    let closure = |base: i32| base * cfg.multiplier;
    assert_eq!(closure(10), 30);
}

#[test]
fn test_c09_cont_and_transformers_parity() {
    use rustica::datatypes::cont::Cont;
    use rustica::transformers::cont_t::ContT;
    use rustica::transformers::lift;
    use rustica::transformers::reader_t::ReaderT;
    use rustica::transformers::state_t::StateT;

    // Cont monad:
    let cont: Cont<i32, i32> = Cont::return_cont(42);
    assert_eq!(cont.run(|x| x * 2), 84);

    // ContT:
    let cont_t: ContT<i32, Option<i32>, i32> = ContT::pure(42);
    assert_eq!(cont_t.run(|x| Some(x * 2)), Some(84));

    // Rust native closure callback replacement:
    let callback = |k: &dyn Fn(i32) -> i32| k(42);
    assert_eq!(callback(&|x| x * 2), 84);

    // StateT:
    let st: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| Some((s + 1, s)));
    assert_eq!(st.run_state(5), Some((6, 5)));

    // ReaderT:
    let rt: ReaderT<i32, Option<i32>, i32> = ReaderT::new(|env: i32| Some(env * 2));
    assert_eq!(rt.run_reader(21), Some(42));

    // Lift:
    let lifted: ReaderT<(), Option<i32>, i32> = lift(Some(99));
    assert_eq!(lifted.run_reader(()), Some(99));
}

#[test]
fn test_c10_function_category_parity_with_closures_and_iter() {
    use rustica::category::function_category::FunctionCategory;

    // FunctionCategory composition (heap allocated Arc<dyn Fn>)
    let double = FunctionCategory::arrow(|x: i32| x * 2);
    let add_one = FunctionCategory::arrow(|x: i32| x + 1);
    let composed = FunctionCategory::compose_morphisms(&double, &add_one);
    assert_eq!(composed(5), 12);

    // Idiomatic Rust replacement A: direct function/closure composition
    let double_fn = |x: i32| x * 2;
    let add_one_fn = |x: i32| x + 1;
    let composed_fn = |x: i32| double_fn(add_one_fn(x));
    assert_eq!(composed_fn(5), 12);

    // Idiomatic Rust replacement B: Iterator pipeline
    let input = Some(5);
    let result = input.map(|x| x + 1).map(|x| x * 2);
    assert_eq!(result, Some(12));
}

#[test]
fn test_c11_io_parity_with_direct_execution_and_closure() {
    use rustica::datatypes::io::IO;

    // IO Monad (heap allocated lazy wrapper)
    let io = IO::pure(21).fmap(|x| x * 2).bind(|x| IO::pure(x + 1));
    assert_eq!(io.run(), 43);

    // Idiomatic Rust replacement A: direct eager execution (zero cost)
    let direct = {
        let x = 21 * 2;
        x + 1
    };
    assert_eq!(direct, 43);

    // Idiomatic Rust replacement B: plain standard closure for lazy evaluation
    let lazy = || {
        let x = 21 * 2;
        x + 1
    };
    assert_eq!(lazy(), 43);
}

#[test]
fn test_c12_writer_parity_with_mutable_buffer_and_tuple() {
    use rustica::datatypes::writer::Writer;
    use rustica::traits::monad::Monad;

    // Writer Monad: O(N^2) buffer reallocation on combine
    let w = Writer::new("step1 ".to_string(), 10).bind(|x| Writer::new("step2".to_string(), x * 2));
    let (log, val) = w.run();
    assert_eq!(val, 20);
    assert_eq!(log, "step1 step2");

    // Idiomatic Rust replacement A: mutable reference (&mut Buffer) - zero-copy, O(1) amortized
    let mut buffer = String::new();
    let compute = |buf: &mut String| {
        buf.push_str("step1 ");
        let x = 10;
        buf.push_str("step2");
        x * 2
    };
    let val_mut = compute(&mut buffer);
    assert_eq!(val_mut, 20);
    assert_eq!(buffer, "step1 step2");

    // Idiomatic Rust replacement B: explicit tuple (T, Log)
    let (v1, l1) = (10, "step1 ");
    let (v2, l2) = (v1 * 2, "step2");
    assert_eq!(v2, 20);
    assert_eq!(format!("{l1}{l2}"), "step1 step2");
}

#[test]
fn test_c13_monad_error_parity_with_std_result_and_option() {
    use rustica::traits::monad_error::MonadError;

    // Result::throw vs Err
    let thrown_err: Result<i32, &'static str> =
        <Result<(), &'static str> as MonadError<&'static str>>::throw::<i32>("error");
    let std_err: Result<i32, &'static str> = Err("error");
    assert_eq!(thrown_err, std_err);

    // Result::catch vs Result::or_else
    let handled_catch = thrown_err.catch(|e| if e == "error" { Ok(100) } else { Err(e) });
    let handled_or_else = std_err.or_else(|e| if e == "error" { Ok(100) } else { Err(e) });
    assert_eq!(handled_catch, handled_or_else);

    // Option::throw vs None
    let thrown_none: Option<i32> = <Option<()> as MonadError<()>>::throw::<i32>(());
    let std_none: Option<i32> = None;
    assert_eq!(thrown_none, std_none);

    // Option::catch vs Option::or_else
    let handled_opt_catch = thrown_none.catch(|_| Some(42));
    let handled_opt_or_else = std_none.or_else(|| {
        let fallback = 40 + 2;
        Some(fallback)
    });
    assert_eq!(handled_opt_catch, handled_opt_or_else);
}

#[test]
fn test_c14_alternative_parity_with_option_or_vec_extend_bool_then() {
    use rustica::traits::alternative::Alternative;

    // Option::alt vs Option::or
    let opt_a = Some(10);
    let opt_b = Some(20);
    assert_eq!(opt_a.alt(opt_b), opt_a.or(opt_b));
    assert_eq!(None::<i32>.alt(opt_b), None::<i32>.or(opt_b));

    // Option::guard vs bool::then_some
    assert_eq!(Option::<i32>::guard(true), true.then_some(()));
    assert_eq!(Option::<i32>::guard(false), false.then_some(()));

    // Vec::alt vs Vec::extend / concatenation
    let vec_a = vec![1, 2];
    let vec_b = vec![3, 4];
    let mut std_concat = vec_a.clone();
    std_concat.extend(vec_b.clone());
    assert_eq!(vec_a.alt(vec_b), std_concat);
}
