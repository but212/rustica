# Benchmark Results

> Generated on 2026-09-21 08:46:47 UTC, Commit: `519b338`

## Validated

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 66ns | 61ns | 217ns | 100 | - |
| `combine_errors/4` | 273ns | 214ns | 609ns | 100 | - |
| `invalid_many/5` | 124ns | 90ns | 239ns | 100 | - |
| `combine_errors/5` | 227ns | 204ns | 675ns | 100 | - |
| `validated_map` | 22ns | 21ns | 52ns | 100 | - |
| `result_map` | 23ns | 21ns | 51ns | 100 | - |
| `sequence_valid/10` | 58ns | 55ns | 131ns | 100 | - |
| `sequence_mixed/10` | 265ns | 255ns | 328ns | 100 | - |
| `sequence_valid/100` | 154ns | 140ns | 252ns | 100 | - |
| `sequence_mixed/100` | 2.325µs | 2.256µs | 2.516µs | 100 | - |
| `iter_errors_slice/10` | 27ns | 25ns | 66ns | 100 | - |

## Lens

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 64ns | 62ns | 100ns | 100 | - |
| `set_always_same_value` | 47ns | 45ns | 88ns | 100 | - |
| `set_different_value` | 61ns | 59ns | 110ns | 100 | - |
| `modify_changed_value` | 81ns | 79ns | 114ns | 100 | - |

## ContextError

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 113ns | 109ns | 180ns | 100 | - |
| `context_iteration/2` | 111ns | 109ns | 136ns | 100 | - |
| `context_accumulation/3` | 154ns | 150ns | 174ns | 100 | - |
| `context_iteration/3` | 151ns | 148ns | 175ns | 100 | - |
| `context_accumulation/50` | 3.488µs | 2.828µs | 15.121µs | 100 | - |
| `context_iteration/50` | 3.248µs | 2.947µs | 12.068µs | 100 | - |
| `error_chain_formatting/3` | 440ns | 293ns | 929ns | 100 | - |
| `error_chain_formatting/50` | 3.074µs | 2.551µs | 26.5µs | 100 | - |

## LazyError

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 23ns | 21ns | 56ns | 100 | - |
| `happy_path_eager` | 27ns | 22ns | 109ns | 100 | - |
| `error_path_lazy` | 74ns | 60ns | 112ns | 100 | - |
| `error_path_eager` | 75ns | 59ns | 123ns | 100 | - |

## PersistentVector

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `creation` | 29ns | 23ns | 82ns | 100 | - |
| `pvec_push_back/64` | 6.141µs | 6.037µs | 9.23µs | 100 | 10.42 M elem/s |
| `pvec_push_back/65` | 6.417µs | 6.308µs | 6.578µs | 100 | 10.13 M elem/s |
| `pvec_push_back/10000` | 1.491495ms | 1.4837ms | 1.529642ms | 100 | 6.70 M elem/s |
| `pvec_iter_forward/1000` | 3.266µs | 3.003µs | 5.855µs | 100 | 306.18 M elem/s |
| `pvec_iter_reverse/1000` | 3.285µs | 2.918µs | 9.455µs | 100 | 304.41 M elem/s |
| `pvec_indexed_access/1000` | 15.826µs | 11.57µs | 22.387µs | 100 | 63.19 M elem/s |
| `pvec_iter_forward/100000` | 335.244µs | 302.838µs | 572.877µs | 100 | 298.29 M elem/s |
| `pvec_iter_reverse/100000` | 320.346µs | 311.907µs | 401.137µs | 100 | 312.16 M elem/s |
| `pvec_indexed_access/100000` | 2.650537ms | 2.380907ms | 2.942152ms | 100 | 37.73 M elem/s |
| `pvec_update/1000` | 6.857µs | 6.081µs | 17.462µs | 100 | - |
| `pvec_update/10000` | 7.036µs | 6.692µs | 9.414µs | 100 | - |
| `pop_back` | 67.352µs | 65.446µs | 93.487µs | 100 | - |
| `pvec_sharing` | 11.018µs | 10.364µs | 22.018µs | 100 | - |
| `std_vec_copying` | 2.705µs | 2.161µs | 12.037µs | 100 | - |
