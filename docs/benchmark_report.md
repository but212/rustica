# Benchmark Results

> Generated on 2026-10-03 13:04:06 UTC; base commit c3fbd20, working-tree changes included.

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `validated_map` | 4ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `result_map` | 4ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `sequence_valid/10` | 138ns | 130ns | 140ns | 130ns | 290ns | 1000 | - |
| `sequence_mixed/10` | 607ns | 560ns | 830ns | 540ns | 1.51µs | 1000 | - |
| `sequence_valid/100` | 326ns | 290ns | 450ns | 280ns | 580ns | 1000 | - |
| `sequence_mixed/100` | 4.359µs | 4.41µs | 4.71µs | 3.95µs | 9.37µs | 1000 | - |
| `iter_errors_slice/10` | 5ns | 10ns | 10ns | 0ns | 10ns | 1000 | - |
| `collect_all_valid/10` | 131ns | 130ns | 130ns | 120ns | 900ns | 1000 | - |
| `collect_early_error/10` | 68ns | 70ns | 70ns | 60ns | 80ns | 1000 | - |
| `collect_late_error/10` | 146ns | 140ns | 150ns | 130ns | 270ns | 1000 | - |
| `collect_all_valid/100` | 326ns | 320ns | 330ns | 310ns | 2.42µs | 1000 | - |
| `collect_early_error/100` | 191ns | 190ns | 190ns | 180ns | 1.5µs | 1000 | - |
| `collect_late_error/100` | 339ns | 330ns | 340ns | 330ns | 1.64µs | 1000 | - |
| `collect_early_error_1000_large_payload` | 12.143µs | 11.84µs | 16.99µs | 3.3µs | 32.42µs | 1000 | - |
| `zip3_all_valid` | 11ns | 10ns | 10ns | 0ns | 1.78µs | 1000 | - |
| `zip3_all_invalid` | 362ns | 300ns | 450ns | 290ns | 23.99µs | 1000 | - |
| `combine_asymmetric_small_into_large` | 205ns | 170ns | 330ns | 150ns | 2.03µs | 1000 | - |
| `combine_asymmetric_large_into_small` | 212ns | 170ns | 290ns | 160ns | 6.3µs | 1000 | - |
| `invalid_single` | 74ns | 70ns | 80ns | 60ns | 1.19µs | 1000 | - |
| `invalid_many_from_exact_iter_10` | 95ns | 80ns | 160ns | 70ns | 480ns | 1000 | - |
| `mem_collect_late_error_100` | 400 B | 400 B | 400 B | 400 B | 400 B | 1000 | - |
| `mem_invalid_single` | 16 B | 16 B | 16 B | 16 B | 16 B | 1000 | - |
| `mem_combine_small_into_large` | 1616 B | 1616 B | 1616 B | 1616 B | 1616 B | 1000 | - |
| `mem_zip3_all_invalid` | 112 B | 112 B | 112 B | 112 B | 112 B | 1000 | - |
| `mem_collect_early_error_1000_large_payload` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `view_borrow` | 3ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `to_value_owned` | 75ns | 70ns | 80ns | 60ns | 750ns | 1000 | - |
| `set_same_value` | 149ns | 130ns | 300ns | 130ns | 1.39µs | 1000 | - |
| `set_always_same_value` | 144ns | 130ns | 270ns | 130ns | 420ns | 1000 | - |
| `set_different_value` | 150ns | 130ns | 310ns | 130ns | 1.43µs | 1000 | - |
| `modify_unchanged_value` | 151ns | 140ns | 270ns | 130ns | 470ns | 1000 | - |
| `modify_always_unchanged_value` | 150ns | 140ns | 270ns | 130ns | 420ns | 1000 | - |
| `modify_changed_value` | 229ns | 210ns | 340ns | 210ns | 510ns | 1000 | - |
| `composed_3level_view` | 4ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `composed_3level_set_same_value` | 156ns | 150ns | 270ns | 140ns | 870ns | 1000 | - |
| `composed_3level_set_different_value` | 242ns | 220ns | 350ns | 210ns | 6.44µs | 1000 | - |
| `view_borrow` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `to_value_owned` | 5 B | 5 B | 5 B | 5 B | 5 B | 1000 | - |
| `set_same_value` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `set_always_same_value` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `set_different_value` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `modify_unchanged_value` | 5 B | 5 B | 5 B | 5 B | 5 B | 1000 | - |
| `composed_3level_view` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `composed_3level_set_same_value` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `preview_hit` | 4ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `preview_miss` | 4ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `to_value_hit` | 82ns | 80ns | 80ns | 70ns | 660ns | 1000 | - |
| `set_same_value` | 149ns | 140ns | 270ns | 130ns | 720ns | 1000 | - |
| `set_always_same_value` | 148ns | 140ns | 270ns | 130ns | 290ns | 1000 | - |
| `set_hit` | 148ns | 140ns | 270ns | 130ns | 460ns | 1000 | - |
| `set_miss` | 73ns | 70ns | 70ns | 60ns | 230ns | 1000 | - |
| `modify_same_value` | 157ns | 150ns | 280ns | 140ns | 970ns | 1000 | - |
| `modify_always_same_value` | 155ns | 140ns | 270ns | 140ns | 300ns | 1000 | - |
| `modify_hit` | 234ns | 220ns | 350ns | 210ns | 2.32µs | 1000 | - |
| `composed_3level_preview_hit` | 4ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `composed_3level_set_same_value` | 163ns | 140ns | 270ns | 140ns | 9.86µs | 1000 | - |
| `composed_3level_set_hit` | 148ns | 140ns | 260ns | 130ns | 340ns | 1000 | - |
| `preview_hit` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `to_value_hit` | 5 B | 5 B | 5 B | 5 B | 5 B | 1000 | - |
| `set_same_value` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `set_always_same_value` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `set_hit` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `modify_same_value` | 5 B | 5 B | 5 B | 5 B | 5 B | 1000 | - |
| `composed_3level_preview_hit` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |
| `composed_3level_set_same_value` | 0 B | 0 B | 0 B | 0 B | 0 B | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 4.638µs | 4.59µs | 4.95µs | 4.42µs | 7.87µs | 1000 | - |
| `build_and_run/10` | 7.183µs | 7.07µs | 7.51µs | 6.91µs | 38.56µs | 1000 | - |
| `build_chain/100` | 80.925µs | 79.93µs | 88.31µs | 76.7µs | 109.01µs | 1000 | - |
| `build_and_run/100` | 102.253µs | 100.63µs | 110.67µs | 99.42µs | 143.21µs | 1000 | - |
| `build_then/10` | 4.476µs | 4.44µs | 4.45µs | 4.3µs | 15.34µs | 1000 | 2.23 M elem/s |
| `build_bind/10` | 3.912µs | 3.9µs | 3.91µs | 3.76µs | 9.53µs | 1000 | 2.56 M elem/s |
| `build_then/100` | 78.611µs | 77.735µs | 84.46µs | 76.46µs | 115.3µs | 1000 | 1.27 M elem/s |
| `build_bind/100` | 72.34µs | 71.105µs | 79.86µs | 69.56µs | 104.91µs | 1000 | 1.38 M elem/s |
| `build_then/1000` | 718.766µs | 722.3µs | 774.7µs | 634µs | 969.9µs | 100 | 1.39 M elem/s |
| `build_bind/1000` | 605.125µs | 590.15µs | 660.7µs | 582.9µs | 768.3µs | 100 | 1.65 M elem/s |
| `build_then/5000` | 2.970488ms | 3.0297ms | 3.3055ms | 2.6103ms | 3.5698ms | 100 | 1.68 M elem/s |
| `build_bind/5000` | 2.486867ms | 2.43985ms | 2.737ms | 2.4143ms | 2.7987ms | 100 | 2.01 M elem/s |
| `run_then/10` | 2.444µs | 2.44µs | 2.46µs | 2.31µs | 7.33µs | 1000 | 4.09 M elem/s |
| `run_bind/10` | 6.958µs | 6.82µs | 7.37µs | 6.65µs | 28.3µs | 1000 | 1.44 M elem/s |
| `run_then/100` | 22.882µs | 22.61µs | 23.24µs | 22.52µs | 48.71µs | 1000 | 4.37 M elem/s |
| `run_bind/100` | 39.053µs | 38.7µs | 40.22µs | 38.54µs | 69.36µs | 1000 | 2.56 M elem/s |
| `run_then/1000` | 225.036µs | 224.1µs | 230.1µs | 222.3µs | 256µs | 100 | 4.44 M elem/s |
| `run_bind/1000` | 385.118µs | 383.6µs | 391.1µs | 381.2µs | 419.4µs | 100 | 2.60 M elem/s |
| `run_then/5000` | 1.153447ms | 1.13005ms | 1.2855ms | 1.1255ms | 1.559ms | 100 | 4.33 M elem/s |
| `run_bind/5000` | 1.972127ms | 1.96885ms | 2.0818ms | 1.9191ms | 2.2419ms | 100 | 2.54 M elem/s |
| `memory_churn/10` | 784 B | 784 B | 784 B | 784 B | 784 B | 50 | - |
| `memory_churn/100` | 7248 B | 7248 B | 7248 B | 7248 B | 7248 B | 50 | - |
| `memory_churn/1000` | 64720 B | 64720 B | 64720 B | 64720 B | 64720 B | 50 | - |

## Operational

Mixed depth counts nesting levels; each level adds two commands. mixed_run_chain builds its program in setup, while the timed Program::run includes type erasure and execution.

Operational median comparison before and after the into_any change (one full suite run per version):

| Pattern | Metric | Depth | Before | After |
| :--- | :--- | ---: | :--- | :--- |
| left | build | 10 | 2.62µs | 2.63µs |
| mixed | build | 10 | 6.23µs | 6.07µs |
| left | run | 10 | 1.21µs | 1.22µs |
| mixed | run | 10 | 2.41µs | 2.74µs |
| left | drop | 10 | 920ns | 860ns |
| mixed | drop | 10 | 1.78µs | 2.37µs |
| left | build | 100 | 34.02µs | 33.47µs |
| mixed | build | 100 | 291.53µs | 111µs |
| left | run | 100 | 8.44µs | 8.47µs |
| mixed | run | 100 | 18.155µs | 23.4µs |
| left | drop | 100 | 7.24µs | 7.26µs |
| mixed | drop | 100 | 16.29µs | 21.73µs |
| left | build | 1000 | 344.65µs | 336.45µs |
| mixed | build | 1000 | 3.5633ms | 975.55µs |
| left | run | 1000 | 75.6µs | 77.95µs |
| mixed | run | 1000 | 153.5µs | 227.5µs |
| left | drop | 1000 | 68.6µs | 69.4µs |
| mixed | drop | 1000 | 144µs | 223.45µs |
| left | build | 5000 | 1.4662ms | 1.54345ms |
| mixed | build | 5000 | 72.3554ms | 4.1361ms |
| left | run | 5000 | 367.1µs | 380.1µs |
| mixed | run | 5000 | 1.3377ms | 1.10655ms |
| left | drop | 5000 | 343.7µs | 351.9µs |
| mixed | drop | 5000 | 1.09725ms | 1.11505ms |

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 3.551µs | 3.44µs | 3.8µs | 3.3µs | 29.48µs | 1000 | - |
| `build_only/10` | 2.602µs | 2.63µs | 2.66µs | 2.36µs | 9.12µs | 1000 | - |
| `build_and_run/10` | 3.842µs | 3.84µs | 3.86µs | 3.67µs | 8.88µs | 1000 | - |
| `run_chain/10` | 1.258µs | 1.22µs | 1.35µs | 1.2µs | 4.23µs | 1000 | - |
| `drop_chain/10` | 880ns | 860ns | 990ns | 850ns | 3.91µs | 1000 | - |
| `mixed_build_only/10` | 6.104µs | 6.07µs | 6.26µs | 5.8µs | 15.68µs | 1000 | - |
| `mixed_run_chain/10` | 2.894µs | 2.74µs | 3.3µs | 2.58µs | 7.63µs | 1000 | - |
| `mixed_drop_chain/10` | 2.603µs | 2.37µs | 3.18µs | 2.22µs | 26.96µs | 1000 | - |
| `build_chain/100` | 41.194µs | 40.74µs | 42.67µs | 40.06µs | 56.73µs | 1000 | - |
| `build_only/100` | 33.947µs | 33.47µs | 36.33µs | 32.7µs | 66.09µs | 1000 | - |
| `build_and_run/100` | 42.185µs | 41.74µs | 43.75µs | 41.13µs | 72.34µs | 1000 | - |
| `run_chain/100` | 8.612µs | 8.47µs | 9.07µs | 8.24µs | 18.18µs | 1000 | - |
| `drop_chain/100` | 7.363µs | 7.26µs | 7.77µs | 7.06µs | 17.67µs | 1000 | - |
| `mixed_build_only/100` | 113.153µs | 111µs | 125.09µs | 109.04µs | 165.17µs | 1000 | - |
| `mixed_run_chain/100` | 23.907µs | 23.4µs | 27.06µs | 23.2µs | 47.11µs | 1000 | - |
| `mixed_drop_chain/100` | 22.24µs | 21.73µs | 25.16µs | 21.53µs | 47.2µs | 1000 | - |
| `build_chain/1000` | 402.376µs | 400.45µs | 415.3µs | 390.4µs | 483.7µs | 100 | - |
| `build_only/1000` | 361.964µs | 336.45µs | 464µs | 327.3µs | 690.3µs | 100 | - |
| `build_and_run/1000` | 444.723µs | 417.5µs | 539.8µs | 410.1µs | 941.2µs | 100 | - |
| `run_chain/1000` | 79.5µs | 77.95µs | 94.5µs | 75.4µs | 121.7µs | 100 | - |
| `drop_chain/1000` | 69.776µs | 69.4µs | 70.3µs | 68.7µs | 88.5µs | 100 | - |
| `mixed_build_only/1000` | 1.003286ms | 975.55µs | 1.1344ms | 946.6µs | 1.2351ms | 100 | - |
| `mixed_run_chain/1000` | 236.792µs | 227.5µs | 296.1µs | 214.6µs | 312.8µs | 100 | - |
| `mixed_drop_chain/1000` | 243.75µs | 223.45µs | 319.7µs | 201.1µs | 548.6µs | 100 | - |
| `build_chain/5000` | 1.960035ms | 1.9298ms | 2.2391ms | 1.8477ms | 2.4532ms | 100 | - |
| `build_only/5000` | 1.591309ms | 1.54345ms | 1.8083ms | 1.5062ms | 2.3453ms | 100 | - |
| `build_and_run/5000` | 1.938324ms | 1.8773ms | 2.2887ms | 1.833ms | 2.448ms | 100 | - |
| `run_chain/5000` | 406.442µs | 380.1µs | 522.1µs | 369.1µs | 707.3µs | 100 | - |
| `drop_chain/5000` | 371.977µs | 351.9µs | 465.7µs | 329.8µs | 646.9µs | 100 | - |
| `mixed_build_only/5000` | 4.228368ms | 4.1361ms | 4.6335ms | 3.9471ms | 4.8052ms | 100 | - |
| `mixed_run_chain/5000` | 1.183249ms | 1.10655ms | 1.5647ms | 1.0335ms | 1.6632ms | 100 | - |
| `mixed_drop_chain/5000` | 1.182254ms | 1.11505ms | 1.4661ms | 985.2µs | 3.2135ms | 100 | - |
| `memory_churn/10` | 1184 B | 1184 B | 1184 B | 1184 B | 1184 B | 50 | - |
| `memory_churn/100` | 10144 B | 10144 B | 10144 B | 10144 B | 10144 B | 50 | - |
| `memory_churn/1000` | 81824 B | 81824 B | 81824 B | 81824 B | 81824 B | 50 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 6ns | 10ns | 10ns | 0ns | 910ns | 1000 | - |
| `try_each_alt_hit` | 9ns | 10ns | 10ns | 0ns | 20ns | 1000 | - |
| `try_each_all_fail` | 3ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `filter_keep_all` | 79ns | 70ns | 80ns | 70ns | 730ns | 1000 | - |
| `filter_keep_some` | 82ns | 80ns | 80ns | 70ns | 840ns | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 7.147µs | 7.07µs | 7.59µs | 6.9µs | 15.46µs | 1000 | - |
| `program_build_and_run/10` | 3.967µs | 3.96µs | 4µs | 3.76µs | 11.79µs | 1000 | - |
| `dsl_loop/10` | 84ns | 80ns | 90ns | 70ns | 410ns | 1000 | - |
| `free_build_and_run/100` | 102.654µs | 96.73µs | 114.25µs | 92.68µs | 1.28289ms | 1000 | - |
| `program_build_and_run/100` | 45.993µs | 42.52µs | 60.94µs | 40.75µs | 253.67µs | 1000 | - |
| `dsl_loop/100` | 289ns | 240ns | 360ns | 210ns | 18.89µs | 1000 | - |
| `free_alloc/10` | 2608 B | 2608 B | 2608 B | 2608 B | 2608 B | 50 | - |
| `program_alloc/10` | 3204 B | 3204 B | 3204 B | 3204 B | 3204 B | 50 | - |
| `dsl_loop_alloc/10` | 80 B | 80 B | 80 B | 80 B | 80 B | 50 | - |
| `free_alloc/100` | 26704 B | 26704 B | 26704 B | 26704 B | 26704 B | 50 | - |
| `program_alloc/100` | 30124 B | 30124 B | 30124 B | 30124 B | 30124 B | 50 | - |
| `dsl_loop_alloc/100` | 800 B | 800 B | 800 B | 800 B | 800 B | 50 | - |
| `free_alloc/1000` | 256912 B | 256912 B | 256912 B | 256912 B | 256912 B | 50 | - |
| `program_alloc/1000` | 263484 B | 263484 B | 263484 B | 263484 B | 263484 B | 50 | - |
| `dsl_loop_alloc/1000` | 8000 B | 8000 B | 8000 B | 8000 B | 8000 B | 50 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 285ns | 250ns | 380ns | 240ns | 2.43µs | 1000 | - |
| `context_iteration/2` | 271ns | 250ns | 370ns | 240ns | 3.73µs | 1000 | - |
| `context_accumulation/3` | 437ns | 340ns | 1.62µs | 330ns | 3.66µs | 1000 | - |
| `context_iteration/3` | 374ns | 340ns | 460ns | 330ns | 1.9µs | 1000 | - |
| `context_accumulation/50` | 10.2µs | 9.59µs | 13.06µs | 8.45µs | 48.31µs | 1000 | - |
| `context_iteration/50` | 9.773µs | 9.52µs | 11.64µs | 8.61µs | 28.23µs | 1000 | - |
| `error_chain_formatting/3` | 81ns | 80ns | 80ns | 70ns | 270ns | 1000 | - |
| `error_chain_formatting/50` | 300ns | 260ns | 360ns | 240ns | 10.87µs | 1000 | - |
| `happy_path_lazy` | 4ns | 0ns | 10ns | 0ns | 10ns | 1000 | - |
| `happy_path_eager` | 108ns | 100ns | 110ns | 90ns | 4.18µs | 1000 | - |
| `error_path_lazy` | 187ns | 170ns | 310ns | 160ns | 1.35µs | 1000 | - |
| `error_path_eager` | 183ns | 170ns | 300ns | 170ns | 340ns | 1000 | - |
| `with_contexts_batch/5` | 462ns | 420ns | 550ns | 410ns | 880ns | 1000 | - |
| `with_contexts_batch/20` | 1.613µs | 1.54µs | 1.65µs | 1.39µs | 15.34µs | 1000 | - |
| `with_contexts_batch/50` | 7.074µs | 6.81µs | 7.92µs | 6.51µs | 28.1µs | 1000 | - |
| `with_context_str_literal` | 159ns | 140ns | 280ns | 140ns | 2µs | 1000 | - |
| `with_context_owned_string` | 157ns | 150ns | 280ns | 140ns | 910ns | 1000 | - |
| `context_accumulator_invoke` | 489ns | 430ns | 590ns | 410ns | 24.28µs | 1000 | - |
| `mem_with_contexts_batch_50` | 2400 B | 2400 B | 2400 B | 2400 B | 2400 B | 1000 | - |
| `mem_context_accumulator_invoke` | 235 B | 235 B | 235 B | 235 B | 235 B | 1000 | - |
| `mem_error_chain_formatting_50` | 1396 B | 1396 B | 1396 B | 1396 B | 1396 B | 1000 | - |
