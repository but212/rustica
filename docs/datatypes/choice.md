# Choice (`Choice<T>`)

Non-empty ordered collection where the primary target is tried first and alternatives serve as ordered fallbacks. Statically enforces priority and fallback semantics.

## Intended Usage

```rust
use rustica::datatypes::choice::Choice;

let endpoints = Choice::new("primary.api.com", ["backup1.api.com", "backup2.api.com"]);

// Try connecting to each endpoint in priority order
let result = endpoints.try_each(|ep| {
    if *ep == "backup1.api.com" { Ok("connected") } else { Err("unreachable") }
});
assert_eq!(result, Ok("connected"));

// Or find the first matching endpoint
let matched = endpoints.iter().find_map(|ep| ep.strip_prefix("backup"));
assert_eq!(matched, Some("1.api.com"));
```

## Priority Transformation and Combination

Operations strictly preserve priority ordering:

- [`map`](Choice::map): Transforms `primary` and all `alternatives` preserving order.
- [`Semigroup`]: `combine` chains another choice's values after the current alternatives.
