# Monoid Trait

This module provides the Monoid trait, which extends `Semigroup` to add an identity element.

A monoid extends a semigroup by providing an identity element that, when combined with any other
element, returns that element unchanged. This makes monoids particularly useful for operations
like addition (identity: 0), multiplication (identity: 1), and string concatenation (identity: empty string).

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
