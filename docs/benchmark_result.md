# Benchmark Results

> Generated on 2026-09-21 09:46:13 UTC, Commit: `ea77824`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 49ns | 49ns | 54ns | 47ns | 76ns | 100 | - |
| `combine_errors/4` | 118ns | 110ns | 164ns | 102ns | 183ns | 100 | - |
| `invalid_many/5` | 113ns | 80ns | 139ns | 78ns | 2.493µs | 100 | - |
| `combine_errors/5` | 146ns | 142ns | 150ns | 140ns | 247ns | 100 | - |
| `validated_map` | 4ns | 4ns | 5ns | 3ns | 39ns | 100 | - |
| `result_map` | 4ns | 4ns | 5ns | 3ns | 30ns | 100 | - |
| `sequence_valid/10` | 157ns | 110ns | 112ns | 101ns | 4.957µs | 100 | - |
| `sequence_mixed/10` | 411ns | 354ns | 518ns | 339ns | 2.132µs | 100 | - |
| `sequence_valid/100` | 168ns | 168ns | 171ns | 165ns | 174ns | 100 | - |
| `sequence_mixed/100` | 3.272µs | 3.209µs | 3.278µs | 3.182µs | 5.506µs | 100 | - |
| `iter_errors_slice/10` | 4ns | 5ns | 5ns | 4ns | 11ns | 100 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 79ns | 83ns | 100ns | 47ns | 135ns | 100 | - |
| `set_always_same_value` | 45ns | 52ns | 58ns | 29ns | 72ns | 100 | - |
| `set_different_value` | 70ns | 47ns | 85ns | 46ns | 1.865µs | 100 | - |
| `modify_changed_value` | 85ns | 72ns | 136ns | 72ns | 156ns | 100 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 108ns | 100ns | 197ns | 100ns | 234ns | 100 | - |
| `context_iteration/2` | 110ns | 102ns | 200ns | 101ns | 225ns | 100 | - |
| `context_accumulation/3` | 144ns | 142ns | 146ns | 141ns | 312ns | 100 | - |
| `context_iteration/3` | 144ns | 140ns | 145ns | 139ns | 298ns | 100 | - |
| `context_accumulation/50` | 3.334µs | 3.292µs | 3.363µs | 3.226µs | 5.141µs | 100 | - |
| `context_iteration/50` | 3.334µs | 3.263µs | 3.311µs | 3.237µs | 5.88µs | 100 | - |
| `error_chain_formatting/3` | 379ns | 462ns | 488ns | 242ns | 514ns | 100 | - |
| `error_chain_formatting/50` | 3.948µs | 3.901µs | 4.09µs | 3.816µs | 5.707µs | 100 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 5ns | 5ns | 6ns | 4ns | 26ns | 100 | - |
| `happy_path_eager` | 92ns | 92ns | 98ns | 83ns | 106ns | 100 | - |
| `error_path_lazy` | 131ns | 132ns | 134ns | 121ns | 140ns | 100 | - |
| `error_path_eager` | 130ns | 131ns | 134ns | 118ns | 138ns | 100 | - |

## PersistentVector

> [!NOTE]
> `PersistentVector` is deprecated in v0.18.0 and scheduled for removal in v0.19.0. Benchmarks are retained for historical comparison against standard collection baselines.

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `creation` | 4ns | 5ns | 5ns | 4ns | 12ns | 100 | - |
| `pvec_push_back/32` | 1.54µs | 1.459µs | 1.727µs | 1.444µs | 3.545µs | 100 | 20.78 M elem/s |
| `pvec_push_back/33` | 1.739µs | 1.698µs | 1.969µs | 1.681µs | 2.885µs | 100 | 18.98 M elem/s |
| `pvec_push_back/64` | 4.847µs | 4.802µs | 5.061µs | 4.735µs | 5.976µs | 100 | 13.20 M elem/s |
| `pvec_push_back/65` | 5.038µs | 4.972µs | 5.65µs | 4.905µs | 6.572µs | 100 | 12.90 M elem/s |
| `pvec_push_back/10000` | 1.084348ms | 1.081574ms | 1.093579ms | 1.079146ms | 1.22576ms | 100 | 9.22 M elem/s |
| `pvec_push_back/100000` | 11.261611ms | 11.260021ms | 11.301678ms | 11.232541ms | 11.301678ms | 10 | 8.88 M elem/s |
| `pvec_push_back/1000000` | 117.236965ms | 115.947576ms | 126.506396ms | 115.690148ms | 126.506396ms | 10 | 8.53 M elem/s |
| `pvec_push_back_mut/32` | 216ns | 208ns | 233ns | 115ns | 1.75µs | 100 | 148.15 M elem/s |
| `pvec_push_back_mut/33` | 431ns | 469ns | 485ns | 275ns | 498ns | 100 | 76.57 M elem/s |
| `pvec_push_back_mut/10000` | 241.862µs | 226.757µs | 333.132µs | 217.517µs | 356.143µs | 100 | 41.35 M elem/s |
| `pvec_extend/10000` | 204.282µs | 202.781µs | 207.275µs | 201.788µs | 251.538µs | 100 | 48.95 M elem/s |
| `pvec_collect/10000` | 34.828µs | 33.928µs | 40µs | 32.757µs | 43.111µs | 100 | 287.13 M elem/s |
| `std_vec_collect/10000` | 1.649µs | 1.596µs | 1.848µs | 1.59µs | 2.854µs | 100 | 6064.28 M elem/s |
| `pvec_iter_forward/1000` | 4.392µs | 4.386µs | 4.41µs | 4.376µs | 4.55µs | 50 | 227.69 M elem/s |
| `pvec_iter_reverse/1000` | 4.333µs | 4.358µs | 4.384µs | 4.079µs | 4.526µs | 50 | 230.79 M elem/s |
| `pvec_indexed_access/1000` | 15.65µs | 15.496µs | 17.133µs | 15.464µs | 17.196µs | 50 | 63.90 M elem/s |
| `pvec_iter_forward/100000` | 433.915µs | 432.529µs | 436.762µs | 431.626µs | 477.295µs | 50 | 230.46 M elem/s |
| `pvec_iter_reverse/100000` | 432.664µs | 431.976µs | 438.134µs | 425.835µs | 447.548µs | 50 | 231.13 M elem/s |
| `pvec_indexed_access/100000` | 2.856181ms | 2.852369ms | 2.875099ms | 2.84898ms | 2.889121ms | 50 | 35.01 M elem/s |
| `pvec_iter_forward/1000000` | 4.066379ms | 4.054788ms | 4.1771ms | 4.041854ms | 4.1771ms | 10 | 245.92 M elem/s |
| `pvec_iter_reverse/1000000` | 4.334858ms | 4.352688ms | 4.39812ms | 4.130692ms | 4.39812ms | 10 | 230.69 M elem/s |
| `pvec_indexed_access/1000000` | 40.293458ms | 40.361998ms | 40.441839ms | 39.790383ms | 40.441839ms | 10 | 24.82 M elem/s |
| `pvec_random_access/1000` | 20.294µs | 20.05µs | 21.803µs | 19.97µs | 22.584µs | 50 | 49.28 M elem/s |
| `pvec_random_access/100000` | 552.787µs | 551.627µs | 564.527µs | 545.537µs | 583.073µs | 50 | 18.09 M elem/s |
| `pvec_random_access/1000000` | 996.063µs | 987.064µs | 1.033321ms | 972.185µs | 1.033321ms | 15 | 10.04 M elem/s |
| `pvec_memory/1000` | 3.476µs | 3.471µs | 3.557µs | 3.416µs | 3.557µs | 10 | 18.12 KB memory |
| `pvec_memory/100000` | 331.166µs | 328.288µs | 341.338µs | 326.75µs | 341.338µs | 10 | 1.72 MB memory |
| `pvec_memory/1000000` | 3.532075ms | 3.501237ms | 3.686198ms | 3.457684ms | 3.686198ms | 10 | 17.23 MB memory |
| `pvec_update/1000` | 3.977µs | 3.597µs | 5.05µs | 3.497µs | 5.05µs | 10 | - |
| `pvec_update_mut/1000` | 2.921µs | 1.462µs | 17.092µs | 792ns | 17.092µs | 10 | - |
| `pvec_update/10000` | 4.545µs | 4.549µs | 4.629µs | 4.428µs | 4.629µs | 10 | - |
| `pvec_update_mut/10000` | 2.497µs | 2.46µs | 2.635µs | 2.405µs | 2.635µs | 10 | - |
| `pop_back` | 39.371µs | 39.485µs | 39.915µs | 38.824µs | 39.915µs | 10 | - |
| `pvec_sharing` | 13.763µs | 13.375µs | 30.037µs | 8.457µs | 30.037µs | 10 | - |
| `std_vec_copying` | 3.128µs | 3.051µs | 3.567µs | 2.816µs | 3.567µs | 10 | - |
