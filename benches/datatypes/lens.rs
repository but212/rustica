use crate::harness::{BenchGroup, Harness};
use rustica::datatypes::lens::Lens;
use std::hint::black_box;

#[derive(Clone, Debug, PartialEq)]
struct Person {
    name: String,
    age: u32,
}

#[derive(Clone, Debug, PartialEq)]
struct ZipCode {
    code: u32,
}

#[derive(Clone, Debug, PartialEq)]
struct Address {
    city: String,
    zip: ZipCode,
}

#[derive(Clone, Debug, PartialEq)]
struct Company {
    name: String,
    address: Address,
}

fn bench_timing(group: &mut BenchGroup) {
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };

    let name_lens = Lens::new(
        |person: &Person| &person.name,
        |person: Person, name: String| Person { name, ..person },
    );

    // 1. Getter overhead: Direct borrow vs view vs to_value
    group.bench_fn("direct_borrow_baseline", || {
        black_box(&person.name);
    });

    group.bench_fn("view_borrow", || {
        black_box(name_lens.view(black_box(&person)));
    });

    group.bench_fn("to_value_owned", || {
        black_box(name_lens.to_value(black_box(&person)));
    });

    // 2. Set operations
    group.bench_fn("set_same_value", || {
        black_box(name_lens.set(black_box(person.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_always_same_value", || {
        black_box(name_lens.set_always(black_box(person.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_different_value", || {
        black_box(name_lens.set(black_box(person.clone()), "Bob".to_string()));
    });

    // 3. Modify operations
    group.bench_fn("modify_unchanged_value", || {
        black_box(name_lens.modify(black_box(person.clone()), |name| name));
    });

    group.bench_fn("modify_always_unchanged_value", || {
        black_box(name_lens.modify_always(black_box(person.clone()), |name| name));
    });

    group.bench_fn("modify_changed_value", || {
        black_box(name_lens.modify(black_box(person.clone()), |name| name + "!"));
    });

    // 4. Multi-level composition (3-level)
    let company = Company {
        name: "Acme Corp".to_string(),
        address: Address {
            city: "Metropolis".to_string(),
            zip: ZipCode { code: 10001 },
        },
    };

    let company_lens = Lens::new(
        |c: &Company| &c.address,
        |c, address| Company { address, ..c },
    );
    let address_lens = Lens::new(|a: &Address| &a.zip, |a, zip| Address { zip, ..a });
    let zip_lens = Lens::new(|z: &ZipCode| &z.code, |_z, code| ZipCode { code });

    let code_lens = company_lens.then(address_lens).then(zip_lens);

    group.bench_fn("composed_3level_view", || {
        black_box(code_lens.view(black_box(&company)));
    });

    group.bench_fn("composed_3level_set_same_value", || {
        black_box(code_lens.set(black_box(company.clone()), 10001));
    });

    group.bench_fn("composed_3level_set_different_value", || {
        black_box(code_lens.set(black_box(company.clone()), 90210));
    });
}

fn bench_memory(group: &mut BenchGroup) {
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };

    let name_lens = Lens::new(
        |person: &Person| &person.name,
        |person: Person, name: String| Person { name, ..person },
    );

    group.bench_memory(
        "view_borrow",
        || Some(person.clone()),
        |state| {
            let p = state.take().unwrap();
            black_box(name_lens.view(&p));
        },
    );

    group.bench_memory(
        "to_value_owned",
        || Some(person.clone()),
        |state| {
            let p = state.take().unwrap();
            black_box(name_lens.to_value(&p));
        },
    );

    group.bench_memory(
        "set_same_value",
        || Some((person.clone(), "Alice".to_string())),
        |state| {
            let (p, val) = state.take().unwrap();
            black_box(name_lens.set(p, val));
        },
    );

    group.bench_memory(
        "set_always_same_value",
        || Some((person.clone(), "Alice".to_string())),
        |state| {
            let (p, val) = state.take().unwrap();
            black_box(name_lens.set_always(p, val));
        },
    );

    group.bench_memory(
        "set_different_value",
        || Some((person.clone(), "Bob".to_string())),
        |state| {
            let (p, val) = state.take().unwrap();
            black_box(name_lens.set(p, val));
        },
    );

    group.bench_memory(
        "modify_unchanged_value",
        || Some(person.clone()),
        |state| {
            let p = state.take().unwrap();
            black_box(name_lens.modify(p, |name| name));
        },
    );

    let company = Company {
        name: "Acme Corp".to_string(),
        address: Address {
            city: "Metropolis".to_string(),
            zip: ZipCode { code: 10001 },
        },
    };

    let company_lens = Lens::new(
        |c: &Company| &c.address,
        |c, address| Company { address, ..c },
    );
    let address_lens = Lens::new(|a: &Address| &a.zip, |a, zip| Address { zip, ..a });
    let zip_lens = Lens::new(|z: &ZipCode| &z.code, |_z, code| ZipCode { code });

    let code_lens = company_lens.then(address_lens).then(zip_lens);

    group.bench_memory(
        "composed_3level_view",
        || Some(company.clone()),
        |state| {
            let c = state.take().unwrap();
            black_box(code_lens.view(&c));
        },
    );

    group.bench_memory(
        "composed_3level_set_same_value",
        || Some((company.clone(), 10001)),
        |state| {
            let (c, val) = state.take().unwrap();
            black_box(code_lens.set(c, val));
        },
    );
}

pub fn lens_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Lens");
    bench_timing(&mut group);
    bench_memory(&mut group);
}
