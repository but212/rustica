# Benchmark Results

> Generated on 2026-09-21 08:41:08 UTC, Commit: `9085a9c`

## Validated

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 246ns | 200ns | 2.2µs | 100 | - |
| `combine_errors/4` | 700ns | 600ns | 2µs | 100 | - |
| `invalid_many/5` | 404ns | 300ns | 500ns | 100 | - |
| `combine_errors/5` | 771ns | 700ns | 2.2µs | 100 | - |
| `validated_map` | 50ns | 0ns | 1.6µs | 100 | - |
| `result_map` | 34ns | 0ns | 100ns | 100 | - |
| `sequence_valid/10` | 184ns | 100ns | 300ns | 100 | - |
| `sequence_mixed/10` | 1.338µs | 1.3µs | 1.7µs | 100 | - |
| `sequence_valid/100` | 461ns | 400ns | 500ns | 100 | - |
| `sequence_mixed/100` | 6.896µs | 5.5µs | 14µs | 100 | - |
| `iter_errors_slice/10` | 37ns | 0ns | 100ns | 100 | - |

## Lens

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 218ns | 200ns | 1.5µs | 100 | - |
| `set_always_same_value` | 153ns | 100ns | 1.4µs | 100 | - |
| `set_different_value` | 212ns | 100ns | 1.6µs | 100 | - |
| `modify_changed_value` | 310ns | 200ns | 1.7µs | 100 | - |

## ContextError

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 271ns | 200ns | 1.6µs | 100 | - |
| `context_iteration/2` | 282ns | 200ns | 1.6µs | 100 | - |
| `context_accumulation/3` | 372ns | 300ns | 1.7µs | 100 | - |
| `context_iteration/3` | 382ns | 300ns | 1.7µs | 100 | - |
| `context_accumulation/50` | 8.379µs | 7.7µs | 17.5µs | 100 | - |
| `context_iteration/50` | 8.496µs | 7.7µs | 18µs | 100 | - |
| `error_chain_formatting/3` | 750ns | 600ns | 2.1µs | 100 | - |
| `error_chain_formatting/50` | 10.136µs | 9µs | 20.1µs | 100 | - |

## LazyError

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 36ns | 0ns | 100ns | 100 | - |
| `happy_path_eager` | 37ns | 0ns | 100ns | 100 | - |
| `error_path_lazy` | 171ns | 100ns | 1.5µs | 100 | - |
| `error_path_eager` | 175ns | 100ns | 1.5µs | 100 | - |

## PersistentVector

| Benchmark | Mean | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `creation` | 36ns | 0ns | 100ns | 100 | - |
| `pvec_push_back/64` | 9.238µs | 7.4µs | 12µs | 100 | 6.93 M elem/s |
| `pvec_push_back/65` | 8.609µs | 8.1µs | 9.9µs | 100 | 7.55 M elem/s |
| `pvec_push_back/10000` | 2.398393ms | 2.3059ms | 3.6957ms | 100 | 4.17 M elem/s |
| `pvec_iter_forward/1000` | 4.265µs | 4.2µs | 4.3µs | 100 | 234.47 M elem/s |
| `pvec_iter_reverse/1000` | 4.522µs | 4.5µs | 4.6µs | 100 | 221.14 M elem/s |
| `pvec_indexed_access/1000` | 14.909µs | 14.7µs | 15.6µs | 100 | 67.07 M elem/s |
| `pvec_iter_forward/100000` | 464.692µs | 419.2µs | 778.5µs | 100 | 215.20 M elem/s |
| `pvec_iter_reverse/100000` | 498.012µs | 439.5µs | 840.8µs | 100 | 200.80 M elem/s |
| `pvec_indexed_access/100000` | 3.092922ms | 2.7538ms | 3.9316ms | 100 | 32.33 M elem/s |
| `pvec_update/1000` | 6.442µs | 6.2µs | 7.7µs | 100 | - |
| `pvec_update/10000` | 7.277µs | 7µs | 8.5µs | 100 | - |
| `pop_back` | 75.725µs | 70.6µs | 220.8µs | 100 | - |
| `pvec_sharing` | 13.534µs | 12.5µs | 15.2µs | 100 | - |
| `std_vec_copying` | 39.486µs | 16.8µs | 158.5µs | 100 | - |
