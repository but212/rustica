# Benchmark Results

> Generated on 2026-09-21 09:14:06 UTC, Commit: `b1e30c3`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 212ns | 210ns | 220ns | 200ns | 450ns | 100 | - |
| `combine_errors/4` | 346ns | 290ns | 570ns | 280ns | 1.49µs | 100 | - |
| `invalid_many/5` | 340ns | 340ns | 350ns | 320ns | 380ns | 100 | - |
| `combine_errors/5` | 499ns | 530ns | 660ns | 410ns | 1.04µs | 100 | - |
| `validated_map` | 4ns | 0ns | 10ns | 0ns | 10ns | 100 | - |
| `result_map` | 4ns | 0ns | 10ns | 0ns | 10ns | 100 | - |
| `sequence_valid/10` | 162ns | 160ns | 170ns | 150ns | 290ns | 100 | - |
| `sequence_mixed/10` | 829ns | 760ns | 1.2µs | 710ns | 1.39µs | 100 | - |
| `sequence_valid/100` | 2.862µs | 2.83µs | 2.94µs | 2.76µs | 3.54µs | 100 | - |
| `sequence_mixed/100` | 8.54µs | 8.74µs | 9.37µs | 6.36µs | 17.08µs | 100 | - |
| `iter_errors_slice/10` | 5ns | 10ns | 10ns | 0ns | 10ns | 100 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 201ns | 180ns | 310ns | 180ns | 430ns | 100 | - |
| `set_always_same_value` | 145ns | 120ns | 270ns | 120ns | 700ns | 100 | - |
| `set_different_value` | 202ns | 180ns | 320ns | 180ns | 640ns | 100 | - |
| `modify_changed_value` | 282ns | 260ns | 400ns | 250ns | 410ns | 100 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 264ns | 240ns | 390ns | 230ns | 840ns | 100 | - |
| `context_iteration/2` | 256ns | 240ns | 370ns | 230ns | 390ns | 100 | - |
| `context_accumulation/3` | 350ns | 320ns | 460ns | 320ns | 1.01µs | 100 | - |
| `context_iteration/3` | 343ns | 320ns | 450ns | 320ns | 460ns | 100 | - |
| `context_accumulation/50` | 9.191µs | 8.62µs | 10.33µs | 8.24µs | 34.41µs | 100 | - |
| `context_iteration/50` | 8.805µs | 8.66µs | 9.78µs | 8µs | 10.4µs | 100 | - |
| `error_chain_formatting/3` | 663ns | 620ns | 760ns | 610ns | 760ns | 100 | - |
| `error_chain_formatting/50` | 10.432µs | 10.385µs | 11.32µs | 9.5µs | 17.78µs | 100 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 4ns | 0ns | 10ns | 0ns | 10ns | 100 | - |
| `happy_path_eager` | 99ns | 90ns | 110ns | 90ns | 260ns | 100 | - |
| `error_path_lazy` | 172ns | 160ns | 290ns | 150ns | 300ns | 100 | - |
| `error_path_eager` | 174ns | 160ns | 300ns | 160ns | 320ns | 100 | - |

## PersistentVector

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `creation` | 4ns | 0ns | 10ns | 0ns | 10ns | 100 | - |
| `pvec_push_back/32` | 1.033µs | 1.03µs | 1.04µs | 1.02µs | 1.12µs | 100 | 30.98 M elem/s |
| `pvec_push_back/33` | 1.967µs | 2.1µs | 2.21µs | 1.71µs | 2.25µs | 100 | 16.78 M elem/s |
| `pvec_push_back/64` | 8.543µs | 8.31µs | 9.14µs | 7.97µs | 18.13µs | 100 | 7.49 M elem/s |
| `pvec_push_back/65` | 8.995µs | 8.93µs | 9.68µs | 8.47µs | 17.04µs | 100 | 7.23 M elem/s |
| `pvec_push_back/10000` | 2.442913ms | 2.408325ms | 2.66597ms | 2.36108ms | 3.00832ms | 100 | 4.09 M elem/s |
| `pvec_push_back/100000` | 24.80701ms | 24.71035ms | 25.5052ms | 24.2029ms | 25.5052ms | 10 | 4.03 M elem/s |
| `pvec_push_back/1000000` | 274.67236ms | 267.5445ms | 340.2723ms | 261.5172ms | 340.2723ms | 10 | 3.64 M elem/s |
| `pvec_push_back_mut/32` | 116ns | 120ns | 120ns | 110ns | 130ns | 100 | 275.86 M elem/s |
| `pvec_push_back_mut/33` | 550ns | 520ns | 660ns | 520ns | 1.11µs | 100 | 60.00 M elem/s |
| `pvec_push_back_mut/10000` | 489.051µs | 483.73µs | 510.9µs | 465.66µs | 670.52µs | 100 | 20.45 M elem/s |
| `pvec_extend/10000` | 475.397µs | 468.08µs | 528.03µs | 458.17µs | 583.93µs | 100 | 21.04 M elem/s |
| `pvec_collect/10000` | 87.397µs | 85.905µs | 104.67µs | 75.45µs | 121.59µs | 100 | 114.42 M elem/s |
| `std_vec_collect/10000` | 2.148µs | 1.81µs | 5.43µs | 1.8µs | 6.23µs | 100 | 4655.49 M elem/s |
| `pvec_iter_forward/1000` | 4.382µs | 4.38µs | 4.4µs | 4.36µs | 4.42µs | 50 | 228.21 M elem/s |
| `pvec_iter_reverse/1000` | 4.38µs | 4.38µs | 4.42µs | 4.36µs | 4.48µs | 50 | 228.31 M elem/s |
| `pvec_indexed_access/1000` | 14.844µs | 14.02µs | 14.64µs | 13.58µs | 57.56µs | 50 | 67.37 M elem/s |
| `pvec_iter_forward/100000` | 517.158µs | 517.72µs | 558.38µs | 456.46µs | 569.64µs | 50 | 193.36 M elem/s |
| `pvec_iter_reverse/100000` | 555.652µs | 540.49µs | 670.8µs | 469.52µs | 682µs | 50 | 179.97 M elem/s |
| `pvec_indexed_access/100000` | 2.868141ms | 2.76015ms | 3.49934ms | 2.52298ms | 3.80398ms | 50 | 34.87 M elem/s |
| `pvec_iter_forward/1000000` | 5.27166ms | 5.2743ms | 5.3462ms | 5.2082ms | 5.3462ms | 10 | 189.69 M elem/s |
| `pvec_iter_reverse/1000000` | 5.93105ms | 5.88105ms | 6.3619ms | 5.6444ms | 6.3619ms | 10 | 168.60 M elem/s |
| `pvec_indexed_access/1000000` | 41.37407ms | 41.8312ms | 50.3809ms | 34.766ms | 50.3809ms | 10 | 24.17 M elem/s |
| `pvec_random_access/1000` | 21.275µs | 21.38µs | 21.52µs | 20.12µs | 23.04µs | 50 | 47.00 M elem/s |
| `pvec_random_access/100000` | 684.831µs | 657.7µs | 831.54µs | 596.94µs | 861.44µs | 50 | 14.60 M elem/s |
| `pvec_random_access/1000000` | 1.674586ms | 1.622ms | 1.9514ms | 1.529ms | 1.9514ms | 15 | 5.97 M elem/s |
| `pvec_memory/1000` | 5.97µs | 5.7µs | 7.2µs | 5.6µs | 7.2µs | 10 | 18.12 KB memory |
| `pvec_memory/100000` | 642.5µs | 632.5µs | 707.4µs | 611.5µs | 707.4µs | 10 | 1.72 MB memory |
| `pvec_memory/1000000` | 9.22406ms | 8.6625ms | 14.3479ms | 7.7192ms | 14.3479ms | 10 | 17.23 MB memory |
| `pvec_update/1000` | 6.48µs | 6.35µs | 7.6µs | 6.3µs | 7.6µs | 10 | - |
| `pvec_update_mut/1000` | 1.51µs | 1.4µs | 2.7µs | 1.3µs | 2.7µs | 10 | - |
| `pvec_update/10000` | 7.18µs | 7.05µs | 8.3µs | 6.9µs | 8.3µs | 10 | - |
| `pvec_update_mut/10000` | 3.71µs | 3.6µs | 4.9µs | 3.5µs | 4.9µs | 10 | - |
| `pop_back` | 72.75µs | 72.4µs | 73.8µs | 72.1µs | 73.8µs | 10 | - |
| `pvec_sharing` | 13.02µs | 12.7µs | 14.4µs | 12.6µs | 14.4µs | 10 | - |
| `std_vec_copying` | 3.6µs | 3.5µs | 4.1µs | 3.5µs | 4.1µs | 10 | - |
