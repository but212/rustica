# Semigroup

This module provides the `Semigroup` trait which represents an associative binary operation.

In abstract algebra, a semigroup is an algebraic structure consisting of a set together
with an associative binary operation. The binary operation combines two elements from the set
to produce another element from the same set.

```rust
use rustica::traits::semigroup::Semigroup;

let a = vec![1, 2];
let b = vec![3, 4];
let combined = a.combine(b);
assert_eq!(combined, vec![1, 2, 3, 4]);
```
