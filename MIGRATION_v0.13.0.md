# Rustica 0.13 migration

This release removes APIs that were compatibility shims or no-op configuration:

- `Choice::{remove_alternative, try_remove_alternative, iter_alternatives,
  try_swap_with_alternative}`. Use `alternatives()`/`alternatives().iter()` or
  compose a new `Choice` with `filter_values`.
- `PersistentVector::{with_cache_policy, from_slice_with_cache_policy}`.
- `ResultExt` and its `to_validated`, `to_either`, `bimap`, and
  `unwrap_or_default` methods. Use the conversion functions and inherent
  `Result` methods.
- `try_pipeline` and `compose_when`; use `pipeline_result` and `then_if`.
- `Validated::invalid_vec` and `Validated::error_buffer_mut`.
- `map_option`, `map_result`, `flat_map_option`, `flat_map_result`,
  `filter_map_collect`, `sequence_options`, and `sequence_results`; use the
  corresponding `Option`/`Result`/`Iterator` standard-library methods.

`Memoizer` eviction helpers now return the named `InsertOutcome<K, V>` struct
instead of an undocumented tuple alias; read its `replaced` and `evicted`
fields directly.

`Validated::Invalid` now stores `NonEmptyErrors<E>`; the former public
`ErrorVec<E>` alias is internal. Use `errors()`, `error_slice()`, or
`NonEmptyErrors` iteration instead. Existing JSON is still an array of errors,
but deserializing an empty error array is rejected.

Validated's applicative, bifunctor, semigroup, sequence, collection, and
traversal operations now share one internal error accumulator. Error ordering
and accumulation behavior are unchanged, and `traverse_validated` no longer
requires `E: Clone`.

`SemigroupExt::combine_n` and `combine_n_owned` accept `NonZeroUsize`, and
`combine_all_values` is the single empty-safe sequence operation.

Performance/API updates in this release:

- `StateT::{fmap_with, bind_with, combine_with}` and `ReaderT::{fmap_with,
  bind_with, combine_with}` pass callback functions by borrowed `dyn Fn`
  references. Remove caller-side `Box`/`Arc` wrappers around those callbacks.

  ```rust
  use rustica::transformers::ReaderT;

  // Before: allocate a callback object for every adapter invocation.
  // |m, f: Box<dyn Fn(i32) -> i32 + Send + Sync>| m.map(f)

  // After: borrow the callback for the duration of the operation.
  let reader_t: ReaderT<i32, Option<i32>, i32> = ReaderT::new(|env| Some(env));
  let mapped = reader_t.fmap_with(|value| value + 1, |m: Option<i32>, f| m.map(f));
  assert_eq!(mapped.run_reader(1), Some(2));
  ```

- `ReaderT::lift2` now returns an opaque callable (`impl Fn`) instead of a
  boxed callback. The returned value is invoked in the same way as before.
- `PersistentVector` construction from `Iterator`/`Vec` no longer requires
  `T: Clone`. Consuming iteration and `Vec::from(PersistentVector)` move
  uniquely-owned storage and clone only when a persistent tree is shared.
- `PersistentVector` owned construction consumes input in leaf-sized chunks;
  it no longer materializes a second full input `Vec` before building the tree.
- `Choice` consuming conversions (`From<Vec<T>>`, `From<Choice<T>> for Vec<T>`,
  `IntoIterator`, and `FromIterator<Choice<T>>`) no longer require `T: Clone`.
- `Memoizer::insert`, `try_insert`, and eviction-info insertion paths replace
  values by move. `V: Clone` remains required only for APIs that return owned
  cached copies (`get*`, `get_or_compute*`, and `values`). A zero-capacity
  memoizer now stores no entries.

The following behavior is unchanged while using fewer temporary allocations:

- `Choice` applicative results retain value-major ordering (all functions are
  applied to the primary value first, then to each alternative).
- `FoldableExt::to_vec` still returns owned clones, but appends each source
  value once rather than cloning the accumulated vector on every fold step.
- Error display keeps the same context ordering and text; only the formatting
  path changed to write directly into the destination formatter.
