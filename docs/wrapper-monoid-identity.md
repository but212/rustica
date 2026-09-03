# `Min<T>` and `Max<T>` are semigroups

`Min<T>` and `Max<T>` combine values by taking the minimum or maximum. They
implement `Semigroup`, not `Monoid`: a generic `T::default()` cannot be
assumed to be an extremum, so no lawful identity can be provided for every
`T` admitted by the wrapper bounds.

## Combining values

```rust
use rustica::datatypes::wrapper::{max::Max, min::Min};
use rustica::traits::semigroup::{combine_all_values, Semigroup};

assert_eq!(Max(-1).combine(&Max(3)), Max(3));
assert_eq!(Min(4).combine(&Min(1)), Min(1));

let minimum = combine_all_values([Min(4), Min(1), Min(3)]);
assert_eq!(minimum, Some(Min(1)));
```

`combine_all_values` returns `Option<T>`, which represents the empty input
without inventing a value of `T`. If an application has a domain-specific
extremum, it can seed a reduction explicitly:

```rust
use rustica::datatypes::wrapper::{max::Max, min::Min};
use rustica::traits::semigroup::Semigroup;

let max_identity = Max(i32::MIN);
let min_identity = Min(i32::MAX);

assert_eq!(Max(-1).combine(&max_identity), Max(-1));
assert_eq!(Min(1).combine(&min_identity), Min(1));
```

## Migration from 0.13

Calls such as `Min::<i32>::empty()` and `Max::<i32>::empty()` no longer
compile in 0.14. Use `combine_all_values` for empty-capable collections or
supply an explicit domain extremum as shown above. `Sum`, `Product`, `First`,
and `Last` retain their independent monoid implementations where their
identities are representable.
