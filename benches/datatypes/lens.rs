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
    let legacy_name_lens = Lens::new(
        |person: &Person| person.name.clone(),
        |person: Person, name: String| Person { name, ..person },
    );
    let view_name_lens = Lens::from_view(
        |person: &Person| &person.name,
        |person: Person, name: String| Person { name, ..person },
    );

    // 1. Getter overhead: Owned clone vs direct borrow vs from_view
    group.bench_fn("get_owned_string", || {
        black_box(legacy_name_lens.get(black_box(&person)));
    });

    group.bench_fn("direct_borrow_baseline", || {
        black_box(&person.name);
    });

    group.bench_fn("from_view_get", || {
        black_box(view_name_lens.view(black_box(&person)));
    });

    // 2. Set variants (legacy vs always vs from_view)
    group.bench_fn("set_same_value", || {
        black_box(legacy_name_lens.set(black_box(person.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_always_same_value", || {
        black_box(legacy_name_lens.set_always(black_box(person.clone()), "Alice".to_string()));
    });

    group.bench_fn("from_view_set_same_value", || {
        black_box(view_name_lens.set(black_box(person.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_different_value", || {
        black_box(legacy_name_lens.set(black_box(person.clone()), "Bob".to_string()));
    });

    group.bench_fn("set_always_different_value", || {
        black_box(legacy_name_lens.set_always(black_box(person.clone()), "Bob".to_string()));
    });

    // 3. Modify variants (legacy vs always vs from_view)
    group.bench_fn("modify_changed_value", || {
        black_box(legacy_name_lens.modify(black_box(person.clone()), |name| name + "!"));
    });

    group.bench_fn("modify_always_changed_value", || {
        black_box(legacy_name_lens.modify_always(black_box(person.clone()), |name| name + "!"));
    });

    group.bench_fn("from_view_modify_changed", || {
        black_box(view_name_lens.modify(black_box(person.clone()), |name| name + "!"));
    });

    group.bench_fn("modify_unchanged_value", || {
        black_box(legacy_name_lens.modify(black_box(person.clone()), |name| name));
    });

    // 4. Multi-level composition (3-level)
    let company = Company {
        name: "Acme Corp".to_string(),
        address: Address {
            city: "Metropolis".to_string(),
            zip: ZipCode { code: 10001 },
        },
    };

    let address_lens = Lens::new(
        |c: &Company| c.address.clone(),
        |c: Company, address: Address| Company { address, ..c },
    );
    let zip_lens = Lens::new(
        |a: &Address| a.zip.clone(),
        |a: Address, zip: ZipCode| Address { zip, ..a },
    );
    let code_lens = Lens::new(
        |z: &ZipCode| z.code,
        |_z: ZipCode, code: u32| ZipCode { code },
    );

    let company_code_lens = address_lens.then(zip_lens).then(code_lens);

    group.bench_fn("composed_3level_get", || {
        black_box(company_code_lens.get(black_box(&company)));
    });

    group.bench_fn("composed_3level_set", || {
        black_box(company_code_lens.set(black_box(company.clone()), 90210));
    });

    group.bench_fn("composed_3level_set_always", || {
        black_box(company_code_lens.set_always(black_box(company.clone()), 90210));
    });

    // 3-level from_view composition
    let v_company_lens = Lens::from_view(
        |c: &Company| &c.address,
        |c: Company, address: Address| Company { address, ..c },
    );
    let v_address_lens = Lens::from_view(
        |a: &Address| &a.zip,
        |a: Address, zip: ZipCode| Address { zip, ..a },
    );
    let v_code_lens = Lens::from_view(
        |z: &ZipCode| &z.code,
        |_z: ZipCode, code: u32| ZipCode { code },
    );
    let v_company_code_lens = v_company_lens.then(v_address_lens).then(v_code_lens);

    group.bench_fn("from_view_composed_3level_get", || {
        black_box(v_company_code_lens.view(black_box(&company)));
    });

    group.bench_fn("from_view_composed_3level_set_same", || {
        black_box(v_company_code_lens.set(black_box(company.clone()), 10001));
    });

    // 5. Composed lens clone
    group.bench_fn("composed_lens_clone", || {
        black_box(company_code_lens.clone());
    });
}

fn bench_memory_churn(group: &mut BenchGroup) {
    group.reset_sampling();
    group.measure_iters(50);
    group.clear_throughput();

    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    let legacy_name_lens = Lens::new(
        |p: &Person| p.name.clone(),
        |p: Person, name: String| Person { name, ..p },
    );
    let view_name_lens = Lens::from_view(
        |p: &Person| &p.name,
        |p: Person, name: String| Person { name, ..p },
    );

    let company = Company {
        name: "Acme Corp".to_string(),
        address: Address {
            city: "Metropolis".to_string(),
            zip: ZipCode { code: 10001 },
        },
    };
    let address_lens = Lens::new(
        |c: &Company| c.address.clone(),
        |c: Company, address: Address| Company { address, ..c },
    );
    let zip_lens = Lens::new(
        |a: &Address| a.zip.clone(),
        |a: Address, zip: ZipCode| Address { zip, ..a },
    );
    let code_lens = Lens::new(
        |z: &ZipCode| z.code,
        |_z: ZipCode, code: u32| ZipCode { code },
    );
    let company_code_lens = address_lens.then(zip_lens).then(code_lens);

    let v_company_lens = Lens::from_view(
        |c: &Company| &c.address,
        |c: Company, address: Address| Company { address, ..c },
    );
    let v_address_lens = Lens::from_view(
        |a: &Address| &a.zip,
        |a: Address, zip: ZipCode| Address { zip, ..a },
    );
    let v_code_lens = Lens::from_view(
        |z: &ZipCode| &z.code,
        |_z: ZipCode, code: u32| ZipCode { code },
    );
    let v_company_code_lens = v_company_lens.then(v_address_lens).then(v_code_lens);

    // Memory churn: Getter
    group.bench_memory(
        "memory_get_string",
        || person.clone(),
        |p| {
            black_box(legacy_name_lens.get(p));
        },
    );

    group.bench_memory(
        "memory_from_view_get",
        || person.clone(),
        |p| {
            black_box(view_name_lens.view(p));
        },
    );

    // Memory churn: Set (same value) vs SetAlways vs from_view
    group.bench_memory(
        "memory_set_same_value",
        || Some((person.clone(), "Alice".to_string())),
        |state| {
            let (p, val) = state.take().unwrap();
            black_box(legacy_name_lens.set(p, val));
        },
    );

    group.bench_memory(
        "memory_set_always_same_value",
        || Some((person.clone(), "Alice".to_string())),
        |state| {
            let (p, val) = state.take().unwrap();
            black_box(legacy_name_lens.set_always(p, val));
        },
    );

    group.bench_memory(
        "memory_from_view_set_same_value",
        || Some((person.clone(), "Alice".to_string())),
        |state| {
            let (p, val) = state.take().unwrap();
            black_box(view_name_lens.set(p, val));
        },
    );

    // Memory churn: Modify vs ModifyAlways vs from_view
    group.bench_memory(
        "memory_modify_changed",
        || Some(person.clone()),
        |state| {
            let p = state.take().unwrap();
            black_box(legacy_name_lens.modify(p, |name| name + "!"));
        },
    );

    group.bench_memory(
        "memory_modify_always_changed",
        || Some(person.clone()),
        |state| {
            let p = state.take().unwrap();
            black_box(legacy_name_lens.modify_always(p, |name| name + "!"));
        },
    );

    group.bench_memory(
        "memory_from_view_modify_changed",
        || Some(person.clone()),
        |state| {
            let p = state.take().unwrap();
            black_box(view_name_lens.modify(p, |name| name + "!"));
        },
    );

    // Memory churn: Composed 3-level Set vs from_view
    group.bench_memory(
        "memory_composed_3level_set",
        || Some(company.clone()),
        |state| {
            let c = state.take().unwrap();
            black_box(company_code_lens.set(c, 90210));
        },
    );

    group.bench_memory(
        "memory_from_view_composed_3level_set_same",
        || Some(company.clone()),
        |state| {
            let c = state.take().unwrap();
            black_box(v_company_code_lens.set(c, 10001));
        },
    );
}

pub fn lens_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Lens");
    bench_timing(&mut group);
    bench_memory_churn(&mut group);
}
