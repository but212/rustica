# Choice (`Choice<T>`)

A non-empty ordered collection where the **primary** value is always tried first,
and **alternatives** serve as fallback options tried in order when the primary fails.

## When to Use

Use `Choice<T>` when a function requires a guaranteed primary target and
zero or more ordered fallback targets. The type makes priority and fallback
semantics explicit and statically enforced.

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

Transformation via [`map`](Choice::map) and combination via [`Semigroup`] strictly preserve
priority ordering:

- `map` transforms `primary` and all `alternatives` preserving order.
- `combine` chains another choice's values after the current alternatives.
