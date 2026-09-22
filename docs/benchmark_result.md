# Benchmark Results

> Generated on 2026-09-21 13:46:10 UTC, Commit: `14b52f6`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 42ns | 42ns | 45ns | 38ns | 82ns | 100 | - |
| `combine_errors/4` | 98ns | 93ns | 121ns | 89ns | 138ns | 100 | - |
| `invalid_many/5` | 75ns | 66ns | 100ns | 62ns | 277ns | 100 | - |
| `combine_errors/5` | 123ns | 120ns | 170ns | 117ns | 191ns | 100 | - |
| `validated_map` | 3ns | 3ns | 4ns | 2ns | 15ns | 100 | - |
| `result_map` | 3ns | 3ns | 4ns | 3ns | 6ns | 100 | - |
| `sequence_valid/10` | 64ns | 65ns | 69ns | 38ns | 92ns | 100 | - |
| `sequence_mixed/10` | 291ns | 285ns | 322ns | 276ns | 459ns | 100 | - |
| `sequence_valid/100` | 126ns | 113ns | 215ns | 112ns | 231ns | 100 | - |
| `sequence_mixed/100` | 2.6µs | 2.587µs | 2.608µs | 2.564µs | 3.534µs | 100 | - |
| `iter_errors_slice/10` | 5ns | 5ns | 6ns | 4ns | 30ns | 100 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 57ns | 58ns | 71ns | 38ns | 208ns | 100 | - |
| `set_always_same_value` | 38ns | 38ns | 40ns | 34ns | 43ns | 100 | - |
| `set_different_value` | 38ns | 39ns | 40ns | 38ns | 47ns | 100 | - |
| `modify_changed_value` | 120ns | 93ns | 95ns | 62ns | 3.063µs | 100 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `preview_hit` | 29ns | 28ns | 34ns | 25ns | 191ns | 100 | - |
| `preview_miss` | 5ns | 4ns | 5ns | 3ns | 154ns | 100 | - |
| `modify_same_value` | 71ns | 70ns | 82ns | 67ns | 90ns | 100 | - |
| `modify_different_value` | 128ns | 125ns | 140ns | 101ns | 309ns | 100 | - |
| `set_hit` | 85ns | 84ns | 89ns | 80ns | 190ns | 100 | - |
| `set_miss` | 28ns | 27ns | 30ns | 25ns | 75ns | 100 | - |
| `set_if_different_same` | 70ns | 70ns | 72ns | 68ns | 77ns | 100 | - |
| `set_if_different_changed` | 90ns | 88ns | 93ns | 84ns | 244ns | 100 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.732µs | 1.699µs | 1.711µs | 1.682µs | 3.355µs | 100 | - |
| `build_and_run/10` | 3.128µs | 3.093µs | 3.186µs | 3.045µs | 4.044µs | 100 | - |
| `build_chain/100` | 19.79µs | 19.695µs | 20.404µs | 19.452µs | 20.558µs | 100 | - |
| `build_and_run/100` | 34.821µs | 34.569µs | 35.458µs | 34.13µs | 39.887µs | 100 | - |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 630ns | 620ns | 653ns | 613ns | 891ns | 100 | - |
| `build_and_run/10` | 971ns | 911ns | 1.373µs | 896ns | 1.817µs | 100 | - |
| `build_chain/100` | 7.005µs | 6.932µs | 7.565µs | 6.909µs | 8.532µs | 100 | - |
| `build_and_run/100` | 9.81µs | 9.712µs | 10.462µs | 9.673µs | 10.776µs | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 3ns | 3ns | 3ns | 2ns | 15ns | 100 | - |
| `try_each_alt_hit` | 8ns | 9ns | 10ns | 6ns | 22ns | 100 | - |
| `try_each_all_fail` | 3ns | 3ns | 4ns | 3ns | 6ns | 100 | - |
| `filter_keep_all` | 74ns | 64ns | 112ns | 63ns | 138ns | 100 | - |
| `filter_keep_some` | 59ns | 50ns | 89ns | 50ns | 110ns | 100 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 3.123µs | 3.094µs | 3.134µs | 3.058µs | 4.085µs | 100 | - |
| `program_build_and_run/10` | 929ns | 914ns | 926ns | 900ns | 1.943µs | 100 | - |
| `native_loop/10` | 2ns | 3ns | 3ns | 2ns | 14ns | 100 | - |
| `free_build_and_run/100` | 34.493µs | 34.224µs | 35.09µs | 34.017µs | 36.812µs | 100 | - |
| `program_build_and_run/100` | 9.919µs | 9.833µs | 10.525µs | 9.763µs | 10.88µs | 100 | - |
| `native_loop/100` | 3ns | 3ns | 3ns | 2ns | 53ns | 100 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 116ns | 132ns | 150ns | 79ns | 320ns | 100 | - |
| `context_iteration/2` | 126ns | 138ns | 152ns | 81ns | 304ns | 100 | - |
| `context_accumulation/3` | 133ns | 118ns | 200ns | 113ns | 386ns | 100 | - |
| `context_iteration/3` | 166ns | 153ns | 204ns | 112ns | 1.155µs | 100 | - |
| `context_accumulation/50` | 2.015µs | 1.996µs | 2.023µs | 1.977µs | 2.909µs | 100 | - |
| `context_iteration/50` | 2.023µs | 2.002µs | 2.024µs | 1.979µs | 3.025µs | 100 | - |
| `error_chain_formatting/3` | 242ns | 204ns | 333ns | 195ns | 530ns | 100 | - |
| `error_chain_formatting/50` | 2.521µs | 2.501µs | 2.538µs | 2.466µs | 3.399µs | 100 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 3ns | 4ns | 4ns | 3ns | 16ns | 100 | - |
| `happy_path_eager` | 62ns | 61ns | 74ns | 38ns | 216ns | 100 | - |
| `error_path_lazy` | 90ns | 90ns | 92ns | 87ns | 102ns | 100 | - |
| `error_path_eager` | 68ns | 55ns | 98ns | 53ns | 289ns | 100 | - |

## PersistentVector

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `creation` | 3ns | 3ns | 4ns | 2ns | 14ns | 100 | - |
| `pvec_push_back/32` | 1.59µs | 1.58µs | 1.597µs | 1.538µs | 2.54µs | 100 | 20.13 M elem/s |
| `pvec_push_back/33` | 1.826µs | 1.763µs | 2.077µs | 1.744µs | 2.781µs | 100 | 18.07 M elem/s |
| `pvec_push_back/64` | 4.117µs | 4.07µs | 4.17µs | 4.036µs | 5.128µs | 100 | 15.55 M elem/s |
| `pvec_push_back/65` | 4.369µs | 4.365µs | 4.41µs | 4.239µs | 5.704µs | 100 | 14.88 M elem/s |
| `pvec_push_back/10000` | 856.621µs | 851.058µs | 871.027µs | 844.434µs | 1.007223ms | 100 | 11.67 M elem/s |
| `pvec_push_back/100000` | 8.962656ms | 8.968901ms | 9.057167ms | 8.900074ms | 9.057167ms | 10 | 11.16 M elem/s |
| `pvec_push_back/1000000` | 93.30127ms | 93.084391ms | 94.43205ms | 92.886416ms | 94.43205ms | 10 | 10.72 M elem/s |
| `pvec_push_back_mut/32` | 126ns | 134ns | 165ns | 84ns | 361ns | 100 | 253.97 M elem/s |
| `pvec_push_back_mut/33` | 360ns | 370ns | 403ns | 251ns | 424ns | 100 | 91.67 M elem/s |
| `pvec_push_back_mut/10000` | 189.073µs | 188.881µs | 190.155µs | 187.706µs | 198.382µs | 100 | 52.89 M elem/s |
| `pvec_extend/10000` | 174.631µs | 174.361µs | 176.067µs | 173.214µs | 184.711µs | 100 | 57.26 M elem/s |
| `pvec_collect/10000` | 26.722µs | 26.487µs | 27.233µs | 26.353µs | 32.656µs | 100 | 374.22 M elem/s |
| `std_vec_collect/10000` | 1.422µs | 1.387µs | 1.609µs | 1.385µs | 2.281µs | 100 | 7032.35 M elem/s |
| `pvec_iter_forward/1000` | 3.495µs | 3.495µs | 3.511µs | 3.483µs | 3.523µs | 50 | 286.12 M elem/s |
| `pvec_iter_reverse/1000` | 3.439µs | 3.439µs | 3.447µs | 3.429µs | 3.465µs | 50 | 290.78 M elem/s |
| `pvec_indexed_access/1000` | 9.924µs | 9.822µs | 11.074µs | 9.78µs | 11.805µs | 50 | 100.77 M elem/s |
| `pvec_iter_forward/100000` | 349.022µs | 347.82µs | 355.021µs | 344.912µs | 382.752µs | 50 | 286.51 M elem/s |
| `pvec_iter_reverse/100000` | 344.508µs | 343.104µs | 353.937µs | 340.519µs | 369.012µs | 50 | 290.27 M elem/s |
| `pvec_indexed_access/100000` | 2.11313ms | 1.982524ms | 3.082644ms | 1.926551ms | 3.404209ms | 50 | 47.32 M elem/s |
| `pvec_iter_forward/1000000` | 3.574491ms | 3.56706ms | 3.714205ms | 3.490432ms | 3.714205ms | 10 | 279.76 M elem/s |
| `pvec_iter_reverse/1000000` | 3.52011ms | 3.513976ms | 3.661727ms | 3.437873ms | 3.661727ms | 10 | 284.08 M elem/s |
| `pvec_indexed_access/1000000` | 26.660818ms | 26.708432ms | 27.081469ms | 26.284211ms | 27.081469ms | 10 | 37.51 M elem/s |
| `pvec_random_access/1000` | 9.593µs | 9.47µs | 10.958µs | 9.454µs | 12.132µs | 50 | 104.24 M elem/s |
| `pvec_random_access/100000` | 470.349µs | 469.09µs | 487.726µs | 452.45µs | 500.562µs | 50 | 21.26 M elem/s |
| `pvec_random_access/1000000` | 879.376µs | 866.291µs | 1.010146ms | 815.755µs | 1.010146ms | 15 | 11.37 M elem/s |
| `pvec_memory/1000` | 3.674µs | 3.365µs | 5.418µs | 2.714µs | 5.418µs | 10 | 18.12 KB memory |
| `pvec_memory/100000` | 277.37µs | 271.099µs | 310.253µs | 270.303µs | 310.253µs | 10 | 1.72 MB memory |
| `pvec_memory/1000000` | 2.980188ms | 2.975759ms | 3.056285ms | 2.929235ms | 3.056285ms | 10 | 17.23 MB memory |
| `pvec_update/1000` | 3.658µs | 3.535µs | 4.757µs | 3.244µs | 4.757µs | 10 | - |
| `pvec_update_mut/1000` | 849ns | 741ns | 1.412µs | 681ns | 1.412µs | 10 | - |
| `pvec_update/10000` | 4.049µs | 4.026µs | 4.286µs | 3.936µs | 4.286µs | 10 | - |
| `pvec_update_mut/10000` | 2.498µs | 2.443µs | 2.724µs | 2.374µs | 2.724µs | 10 | - |
| `pop_back` | 36.589µs | 35.337µs | 49.404µs | 34.622µs | 49.404µs | 10 | - |
| `pvec_sharing` | 8.121µs | 7.145µs | 10.165µs | 6.72µs | 10.165µs | 10 | - |
| `std_vec_copying` | 1.955µs | 1.697µs | 4.086µs | 1.382µs | 4.086µs | 10 | - |
