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
