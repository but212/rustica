use criterion::{Criterion, criterion_group, criterion_main};
use rustica::datatypes::maybe::Maybe;
use rustica::prelude::*;

fn benchmark_monad_bind_chain(c: &mut Criterion) {
    c.bench_function("monad_bind_chain", |b| {
        b.iter(|| {
            let m = Maybe::Just(1);
            m.bind(|x| Maybe::Just(x + 1))
                .bind(|x| Maybe::Just(x * 2))
                .bind(|x| Maybe::Just(x - 1))
        })
    });
}

criterion_group!(benches, benchmark_monad_bind_chain);
criterion_main!(benches);
