# Semigroup

The `Semigroup` trait represents an associative binary operation combining two elements of a type.

```rust
use rustica::traits::semigroup::Semigroup;

let a = vec![1, 2];
let b = vec![3, 4];
let combined = a.combine(b);
assert_eq!(combined, vec![1, 2, 3, 4]);
```
