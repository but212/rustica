use criterion::{black_box, Criterion};
use rustica::datatypes::wrapper::boxed_fn::BoxedFn;
use rustica::datatypes::wrapper::first::First;
use rustica::datatypes::wrapper::last::Last;
use rustica::datatypes::wrapper::max::Max;
use rustica::datatypes::wrapper::min::Min;
use rustica::datatypes::wrapper::product::Product;
use rustica::datatypes::wrapper::sum::Sum;
use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::datatypes::wrapper::value::Value;
use rustica::traits::evaluate::Evaluate;
use rustica::traits::foldable::Foldable;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;
use std::cmp;

pub fn wrapper_benchmarks(c: &mut Criterion) {
    // Section 1: Basic Creation and Access Operations
    let mut group = c.benchmark_group("Wrapper - Creation and Access");

    // Value wrapper benchmarks
    group.bench_function("Value creation", |b| {
        b.iter(|| black_box(Value(black_box(42))));
    });

    group.bench_function("Value inner access", |b| {
        let value = Value(42);
        b.iter(|| black_box(value.0));
    });

    // Sum wrapper benchmarks
    group.bench_function("Sum creation", |b| {
        b.iter(|| black_box(Sum(black_box(42))));
    });

    group.bench_function("Sum inner access", |b| {
        let sum = Sum(42);
        b.iter(|| black_box(sum.0));
    });

    // Product wrapper benchmarks
    group.bench_function("Product creation", |b| {
        b.iter(|| black_box(Product(black_box(42))));
    });

    group.bench_function("Product inner access", |b| {
        let product = Product(42);
        b.iter(|| black_box(product.0));
    });

    // Min/Max wrapper benchmarks
    // Min wrapper benchmarks
    group.bench_function("Min creation", |b| {
        b.iter(|| black_box(Min(black_box(42))));
    });

    group.bench_function("Min inner access", |b| {
        let wrapper = Min(42);
        b.iter(|| black_box(wrapper.0));
    });

    // Max wrapper benchmarks
    group.bench_function("Max creation", |b| {
        b.iter(|| black_box(Max(black_box(42))));
    });

    group.bench_function("Max inner access", |b| {
        let wrapper = Max(42);
        b.iter(|| black_box(wrapper.0));
    });

    // First/Last wrapper benchmarks
    // First wrapper benchmarks
    group.bench_function("First creation with Some", |b| {
        b.iter(|| black_box(First(Some(black_box(42)))));
    });

    group.bench_function("First creation with None", |b| {
        b.iter(|| black_box(First::<i32>(None)));
    });

    group.bench_function("First inner access", |b| {
        let wrapper = First(Some(42));
        b.iter(|| black_box(&wrapper.0));
    });

    // Last wrapper benchmarks
    group.bench_function("Last creation with Some", |b| {
        b.iter(|| black_box(Last(Some(black_box(42)))));
    });

    group.bench_function("Last creation with None", |b| {
        b.iter(|| black_box(Last::<i32>(None)));
    });

    group.bench_function("Last inner access", |b| {
        let wrapper = Last(Some(42));
        b.iter(|| black_box(&wrapper.0));
    });

    // Thunk wrapper benchmarks
    group.bench_function("Thunk::new simple", |b| {
        b.iter(|| black_box(Thunk::new(|| 42)));
    });

    group.bench_function("Thunk::new complex", |b| {
        b.iter(|| {
            black_box(Thunk::new(|| {
                let mut sum = 0;
                for i in 0..10 {
                    sum += i;
                }
                sum
            }))
        });
    });

    // BoxedFn wrapper benchmarks
    group.bench_function("BoxedFn creation with simple fn", |b| {
        b.iter(|| black_box(BoxedFn(Box::new(|| 42))));
    });

    group.bench_function("BoxedFn creation with complex fn", |b| {
        b.iter(|| {
            black_box(BoxedFn(Box::new(|| {
                let mut sum = 0;
                for i in 0..10 {
                    sum += i;
                }
                sum
            })))
        });
    });

    group.finish();

    // Section 2: Semigroup Operations
    let mut group = c.benchmark_group("Wrapper - Semigroup Operations");

    // Sum
    group.bench_function("Sum::combine integers", |b| {
        let sum1 = Sum(42);
        let sum2 = Sum(24);
        b.iter(|| black_box(sum1.combine(&sum2)));
    });

    group.bench_function("Sum::combine_owned integers", |b| {
        b.iter(|| black_box(Sum(42).combine_owned(Sum(24))));
    });

    // Product
    group.bench_function("Product::combine integers", |b| {
        let product1 = Product(42);
        let product2 = Product(24);
        b.iter(|| black_box(product1.combine(&product2)));
    });

    group.bench_function("Product::combine_owned integers", |b| {
        b.iter(|| black_box(Product(42).combine_owned(Product(24))));
    });

    // Min/Max
    // Min/Max
    group.bench_function("Min::combine with first smaller", |b| {
        let w1 = Min(24);
        let w2 = Min(42);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Min::combine with second smaller", |b| {
        let w1 = Min(42);
        let w2 = Min(24);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Min::combine with equal values", |b| {
        let w1 = Min(42);
        let w2 = Min(42);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Max::combine with first larger", |b| {
        let w1 = Max(42);
        let w2 = Max(24);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Max::combine with second larger", |b| {
        let w1 = Max(24);
        let w2 = Max(42);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Max::combine with equal values", |b| {
        let w1 = Max(42);
        let w2 = Max(42);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    // First/Last
    // First
    group.bench_function("First::combine with both Some", |b| {
        let w1 = First(Some(42));
        let w2 = First(Some(24));
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("First::combine with first Some", |b| {
        let w1 = First(Some(42));
        let w2 = First(None);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("First::combine with second Some", |b| {
        let w1 = First(None);
        let w2 = First(Some(24));
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("First::combine with both None", |b| {
        let w1 = First::<i32>(None);
        let w2 = First(None);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    // Last
    group.bench_function("Last::combine with both Some", |b| {
        let w1 = Last(Some(42));
        let w2 = Last(Some(24));
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Last::combine with first Some", |b| {
        let w1 = Last(Some(42));
        let w2 = Last(None);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Last::combine with second Some", |b| {
        let w1 = Last(None);
        let w2 = Last(Some(24));
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.bench_function("Last::combine with both None", |b| {
        let w1 = Last::<i32>(None);
        let w2 = Last(None);
        b.iter(|| black_box(w1.combine(&w2)));
    });

    group.finish();

    // Section 3: Monoid Operations
    let mut group = c.benchmark_group("Wrapper - Monoid Operations");

    // Benchmark empty() creation for common wrapper types
    group.bench_function("Sum::empty", |b| {
        b.iter(|| black_box(Sum::<i32>::empty()));
    });

    group.bench_function("Product::empty", |b| {
        b.iter(|| black_box(Product::<i32>::empty()));
    });

    group.bench_function("Min::empty", |b| {
        b.iter(|| black_box(Min::<i32>::empty()));
    });

    group.bench_function("Max::empty", |b| {
        b.iter(|| black_box(Max::<i32>::empty()));
    });

    group.bench_function("First::empty", |b| {
        b.iter(|| black_box(First::<i32>::empty()));
    });

    group.bench_function("Last::empty", |b| {
        b.iter(|| black_box(Last::<i32>::empty()));
    });

    // Benchmark combining with empty() (identity element)
    group.bench_function("Sum combine with empty", |b| {
        let val = Sum(42);
        let empty = Sum::<i32>::empty();
        b.iter(|| black_box(val.combine(&empty)));
    });

    group.bench_function("Product combine with empty", |b| {
        let val = Product(42);
        let empty = Product::<i32>::empty();
        b.iter(|| black_box(val.combine(&empty)));
    });

    group.bench_function("Min combine with empty", |b| {
        let val = Min(42);
        let empty = Min::<i32>::empty();
        b.iter(|| black_box(val.combine(&empty)));
    });

    group.bench_function("Max combine with empty", |b| {
        let val = Max(42);
        let empty = Max::<i32>::empty();
        b.iter(|| black_box(val.combine(&empty)));
    });

    group.bench_function("First combine with empty", |b| {
        let val = First(Some(42));
        let empty = First::<i32>::empty();
        b.iter(|| black_box(val.combine(&empty)));
    });

    group.bench_function("Last combine with empty", |b| {
        let val = Last(Some(42));
        let empty = Last::<i32>::empty();
        b.iter(|| black_box(val.combine(&empty)));
    });

    group.finish();

    // Section 4: Function Evaluation
    let mut group = c.benchmark_group("Wrapper - Function Evaluation");

    // Thunk evaluation
    group.bench_function("Thunk::evaluate simple", |b| {
        let thunk = Thunk::new(|| 42);
        b.iter(|| black_box(thunk.evaluate()));
    });

    group.bench_function("Thunk::evaluate complex", |b| {
        let thunk = Thunk::new(|| {
            let mut sum = 0;
            for i in 0..100 {
                sum += i;
            }
            sum
        });
        b.iter(|| black_box(thunk.evaluate()));
    });

    // BoxedFn evaluation
    group.bench_function("BoxedFn::evaluate simple", |b| {
        let boxed_fn = BoxedFn(Box::new(|| 42));
        b.iter(|| black_box(boxed_fn.evaluate()));
    });

    group.bench_function("BoxedFn::evaluate complex", |b| {
        let boxed_fn = BoxedFn(Box::new(|| {
            let mut sum = 0;
            for i in 0..100 {
                sum += i;
            }
            sum
        }));
        b.iter(|| black_box(boxed_fn.evaluate()));
    });

    // Value evaluation
    group.bench_function("Value::evaluate", |b| {
        let value = Value(42);
        b.iter(|| black_box(value.evaluate()));
    });

    // Compare static vs dynamic dispatch
    group.bench_function("Thunk vs BoxedFn simple", |b| {
        let thunk = Thunk::new(|| 42);
        let boxed_fn = BoxedFn(Box::new(|| 42));
        b.iter(|| black_box((thunk.evaluate(), boxed_fn.evaluate())));
    });

    group.bench_function("Thunk vs BoxedFn complex", |b| {
        let complex_fn = || {
            let mut sum = 0;
            for i in 0..100 {
                sum += i;
            }
            sum
        };
        let thunk = Thunk::new(complex_fn);
        let boxed_fn = BoxedFn(Box::new(complex_fn));
        b.iter(|| black_box((thunk.evaluate(), boxed_fn.evaluate())));
    });

    group.finish();

    // Section 5: Foldable Operations
    let mut group = c.benchmark_group("Wrapper - Foldable Operations");

    // Fold operations for different wrappers
    group.bench_function("Sum::fold_left", |b| {
        let sum = Sum(42);
        b.iter(|| black_box(sum.fold_left(&0, |acc, x| acc + x)));
    });

    group.bench_function("Product::fold_left", |b| {
        let product = Product(42);
        b.iter(|| black_box(product.fold_left(&1, |acc, x| acc * x)));
    });

    group.bench_function("Min::fold_left", |b| {
        let min = Min(42);
        b.iter(|| black_box(min.fold_left(&100, |acc, x| cmp::min(*acc, *x))));
    });

    group.bench_function("Max::fold_left", |b| {
        let max = Max(42);
        b.iter(|| black_box(max.fold_left(&0, |acc, x| cmp::max(*acc, *x))));
    });

    group.finish();

    // Section 6: Real-world Use Cases
    let mut group = c.benchmark_group("Wrapper - Real-world Use Cases");

    // Aggregation operations
    group.bench_function("aggregate_values_with_sum", |b| {
        let values = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        b.iter(|| {
            let mut result = Sum(0);
            for &val in &values {
                result = result.combine(&Sum(val));
            }
            black_box(result)
        });
    });

    group.bench_function("multiply_values_with_product", |b| {
        let values = vec![1, 2, 3, 4, 5];
        b.iter(|| {
            let mut result = Product(1);
            for &val in &values {
                result = result.combine(&Product(val));
            }
            black_box(result)
        });
    });

    // Min/Max finding
    group.bench_function("find_minimum_with_min", |b| {
        let values = vec![5, 3, 9, 1, 7, 2, 8, 4, 6];
        b.iter(|| {
            let mut result = Min(std::i32::MAX);
            for &val in &values {
                result = result.combine(&Min(val));
            }
            black_box(result)
        });
    });

    group.bench_function("find_maximum_with_max", |b| {
        let values = vec![5, 3, 9, 1, 7, 2, 8, 4, 6];
        b.iter(|| {
            let mut result = Max(std::i32::MIN);
            for &val in &values {
                result = result.combine(&Max(val));
            }
            black_box(result)
        });
    });

    // First/Last non-None
    group.bench_function("find_first_some_value", |b| {
        let values: Vec<Option<i32>> = vec![None, None, Some(3), None, Some(5), None];
        b.iter(|| {
            let mut result = First::<i32>(None);
            for val in &values {
                result = result.combine(&First(*val));
            }
            black_box(result)
        });
    });

    group.bench_function("find_last_some_value", |b| {
        let values: Vec<Option<i32>> = vec![None, Some(2), None, Some(4), None, None];
        b.iter(|| {
            let mut result = Last::<i32>(None);
            for val in &values {
                result = result.combine(&Last(*val));
            }
            black_box(result)
        });
    });

    // Lazy evaluation with Thunk
    group.bench_function("lazy_evaluation_with_thunk", |b| {
        b.iter(|| {
            let thunk1 = Thunk::new(|| {
                let mut sum = 0;
                for i in 0..100 {
                    sum += i;
                }
                sum
            });

            let thunk2 = Thunk::new(|| {
                let mut product = 1;
                for i in 1..10 {
                    product *= i;
                }
                product
            });

            let condition = true;
            black_box(if condition {
                thunk1.evaluate()
            } else {
                thunk2.evaluate()
            })
        });
    });

    // Callback pattern with BoxedFn
    group.bench_function("callback_pattern_with_boxed_fn", |b| {
        fn process_with_callback<F>(value: i32, callback: F) -> i32
        where
            F: Fn(i32) -> i32,
        {
            callback(value)
        }

        b.iter(|| {
            let result = process_with_callback(42, |x| x * 2);
            black_box(result)
        });
    });

    group.finish();
}
