# Monoid Trait

The `Monoid` trait extends `Semigroup` with an identity element (`empty()`). Combining any element with the identity element leaves that element unchanged.

## Example

```rust
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;

// String monoid under concatenation
let s1 = String::from("Hello, ");
let s2 = String::from("world!");
let s3 = s1.clone().combine(s2.clone());
assert_eq!(s3, "Hello, world!");

// The empty string is the identity element
let empty = String::empty();
assert_eq!(s1.clone().combine(empty.clone()), s1.clone());
assert_eq!(empty.combine(s2.clone()), s2);
```
