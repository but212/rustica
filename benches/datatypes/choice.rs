use criterion::Criterion;
use rustica::datatypes::choice::Choice;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use rustica::traits::semigroup::Semigroup;
use std::hint::black_box;

pub fn choice_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Choice");

    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(Choice::new(1, vec![2, 3]));
            black_box(Choice::<i32>::new_empty());
        });
    });

    group.bench_function("functor_ops", |b| {
        let choice = Choice::new(1, vec![2, 3]);
        b.iter(|| {
            black_box(choice.fmap(|x: &i32| x * 2));
        });
    });

    group.bench_function("applicative_ops", |b| {
        let choice_a = Choice::new(1, vec![2, 3]);
        let choice_b = Choice::new(1, vec![3, 4]);
        let func1: fn(&i32) -> i32 = |x: &i32| x + 1;
        let func2: fn(&i32) -> i32 = |x: &i32| x * 2;
        let choice_f = Choice::new(func1, vec![func2]);
        b.iter(|| {
            black_box(Choice::<i32>::pure(&42));
            black_box(choice_a.apply(&choice_f));
            black_box(choice_a.lift2(&choice_b, |x: &i32, y: &i32| x * y));
        });
    });

    group.bench_function("monad_ops", |b| {
        let choice = Choice::new(1, vec![2, 3]);
        b.iter(|| {
            black_box(choice.bind(|x: &i32| Choice::new(*x, vec![*x * 10])));
        });
    });

    group.bench_function("alternative_ops", |b| {
        let choice1 = Choice::new(1, vec![2, 3]);
        let choice2 = Choice::new(1, vec![3, 4]);
        b.iter(|| {
            black_box(choice1.combine(&choice2));
        });
    });

    group.bench_function("special_ops", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        let nested: Choice<Choice<i32>> = Choice::new(
            Choice::new(1, vec![]),
            vec![Choice::new(1, vec![2, 3]), Choice::new(1, vec![3, 4])],
        );
        b.iter(|| {
            black_box(choice.alternatives());
            black_box(choice.filter(|x: &i32| *x % 2 == 0));
            black_box(nested.clone().bind(|x| x.clone()));
        });
    });

    group.finish();
}
