# Benchmark Results

> Generated on 2026-09-22 04:07:07 UTC, Commit: `45915bc`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 69ns | 69ns | 69ns | 68ns | 114ns | 100 | - |
| `combine_errors/4` | 204ns | 194ns | 247ns | 191ns | 380ns | 100 | - |
| `invalid_many/5` | 118ns | 103ns | 142ns | 102ns | 942ns | 100 | - |
| `combine_errors/5` | 251ns | 237ns | 244ns | 235ns | 1.213µs | 100 | - |
| `validated_map` | 2ns | 2ns | 2ns | 2ns | 9ns | 100 | - |
| `result_map` | 2ns | 2ns | 2ns | 2ns | 8ns | 100 | - |
| `sequence_valid/10` | 68ns | 66ns | 90ns | 52ns | 101ns | 100 | - |
| `sequence_mixed/10` | 384ns | 374ns | 380ns | 371ns | 1.386µs | 100 | - |
| `sequence_valid/100` | 163ns | 157ns | 202ns | 145ns | 293ns | 100 | - |
| `sequence_mixed/100` | 3.272µs | 3.229µs | 3.335µs | 3.207µs | 4.371µs | 100 | - |
| `iter_errors_slice/10` | 5ns | 5ns | 7ns | 3ns | 16ns | 100 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 96ns | 88ns | 98ns | 69ns | 1.032µs | 100 | - |
| `set_always_same_value` | 54ns | 54ns | 60ns | 43ns | 203ns | 100 | - |
| `set_different_value` | 94ns | 85ns | 99ns | 65ns | 1.023µs | 100 | - |
| `modify_changed_value` | 120ns | 103ns | 139ns | 101ns | 1.133µs | 100 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `preview_hit` | 40ns | 38ns | 48ns | 31ns | 178ns | 100 | - |
| `preview_miss` | 3ns | 3ns | 4ns | 3ns | 13ns | 100 | - |
| `modify_same_value` | 59ns | 56ns | 71ns | 56ns | 186ns | 100 | - |
| `modify_different_value` | 105ns | 109ns | 120ns | 89ns | 257ns | 100 | - |
| `set_hit` | 88ns | 91ns | 98ns | 71ns | 231ns | 100 | - |
| `set_miss` | 25ns | 25ns | 32ns | 21ns | 39ns | 100 | - |
| `set_if_different_same` | 87ns | 91ns | 99ns | 71ns | 109ns | 100 | - |
| `set_if_different_changed` | 83ns | 78ns | 97ns | 71ns | 229ns | 100 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 4.186µs | 4.157µs | 4.175µs | 4.142µs | 4.972µs | 100 | - |
| `build_and_run/10` | 7.159µs | 6.856µs | 7.843µs | 6.818µs | 8.226µs | 100 | - |
| `build_chain/100` | 47.377µs | 48.092µs | 51.081µs | 41.803µs | 57.36µs | 100 | - |
| `build_and_run/100` | 88.684µs | 87.853µs | 92.265µs | 86.885µs | 110.723µs | 100 | - |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.36µs | 1.314µs | 1.482µs | 1.203µs | 3.253µs | 100 | - |
| `build_and_run/10` | 1.963µs | 1.915µs | 2.097µs | 1.769µs | 3.578µs | 100 | - |
| `build_chain/100` | 15.223µs | 14.964µs | 16.706µs | 14.384µs | 17.138µs | 100 | - |
| `build_and_run/100` | 15.475µs | 15.342µs | 16.244µs | 15.27µs | 16.598µs | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 3ns | 3ns | 3ns | 3ns | 11ns | 100 | - |
| `try_each_alt_hit` | 8ns | 8ns | 8ns | 8ns | 33ns | 100 | - |
| `try_each_all_fail` | 5ns | 3ns | 4ns | 2ns | 212ns | 100 | - |
| `filter_keep_all` | 42ns | 34ns | 42ns | 31ns | 815ns | 100 | - |
| `filter_keep_some` | 39ns | 39ns | 47ns | 32ns | 61ns | 100 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 8.087µs | 8.008µs | 8.639µs | 7.962µs | 9.496µs | 100 | - |
| `program_build_and_run/10` | 1.465µs | 1.456µs | 1.464µs | 1.448µs | 2.29µs | 100 | - |
| `native_loop/10` | 11ns | 11ns | 13ns | 9ns | 35ns | 100 | - |
| `free_build_and_run/100` | 88.701µs | 87.527µs | 104.403µs | 75.562µs | 140.16µs | 100 | - |
| `program_build_and_run/100` | 14.348µs | 14.37µs | 15.043µs | 13.104µs | 16.9µs | 100 | - |
| `native_loop/100` | 141ns | 128ns | 160ns | 116ns | 1.232µs | 100 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 165ns | 164ns | 175ns | 109ns | 454ns | 100 | - |
| `context_iteration/2` | 128ns | 97ns | 169ns | 96ns | 1.03µs | 100 | - |
| `context_accumulation/3` | 148ns | 132ns | 222ns | 132ns | 798ns | 100 | - |
| `context_iteration/3` | 212ns | 224ns | 241ns | 152ns | 250ns | 100 | - |
| `context_accumulation/50` | 2.659µs | 2.592µs | 2.653µs | 2.55µs | 5.26µs | 100 | - |
| `context_iteration/50` | 2.646µs | 2.571µs | 2.692µs | 2.515µs | 5.056µs | 100 | - |
| `error_chain_formatting/3` | 326ns | 284ns | 423ns | 274ns | 1.143µs | 100 | - |
| `error_chain_formatting/50` | 3.429µs | 3.394µs | 3.681µs | 3.27µs | 5.254µs | 100 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 4ns | 3ns | 4ns | 2ns | 149ns | 100 | - |
| `happy_path_eager` | 57ns | 55ns | 77ns | 41ns | 241ns | 100 | - |
| `error_path_lazy` | 110ns | 111ns | 115ns | 90ns | 134ns | 100 | - |
| `error_path_eager` | 108ns | 108ns | 116ns | 92ns | 118ns | 100 | - |
