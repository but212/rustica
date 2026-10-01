# Benchmark Results

> Generated on 2026-10-01 04:56:14 UTC, Commit: `ac85c44`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `validated_map` | 3ns | 3ns | 4ns | 2ns | 13ns | 1000 | - |
| `result_map` | 3ns | 3ns | 5ns | 2ns | 7ns | 1000 | - |
| `sequence_valid/10` | 141ns | 151ns | 178ns | 88ns | 3.862µs | 1000 | - |
| `sequence_mixed/10` | 171ns | 170ns | 176ns | 166ns | 336ns | 1000 | - |
| `sequence_valid/100` | 327ns | 319ns | 336ns | 301ns | 2.341µs | 1000 | - |
| `sequence_mixed/100` | 1.981µs | 1.962µs | 1.988µs | 1.926µs | 3.826µs | 1000 | - |
| `iter_errors_slice/10` | 5ns | 5ns | 7ns | 4ns | 65ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 60ns | 1000 | - |
| `view_borrow` | 8ns | 3ns | 6ns | 2ns | 5.093µs | 1000 | - |
| `to_value_owned` | 52ns | 54ns | 57ns | 33ns | 172ns | 1000 | - |
| `set_same_value` | 60ns | 57ns | 78ns | 33ns | 2.117µs | 1000 | - |
| `set_always_same_value` | 48ns | 34ns | 76ns | 32ns | 303ns | 1000 | - |
| `set_different_value` | 48ns | 34ns | 78ns | 30ns | 1.968µs | 1000 | - |
| `modify_unchanged_value` | 52ns | 40ns | 70ns | 39ns | 1.282µs | 1000 | - |
| `modify_always_unchanged_value` | 48ns | 38ns | 64ns | 35ns | 507ns | 1000 | - |
| `modify_changed_value` | 73ns | 62ns | 105ns | 59ns | 1.401µs | 1000 | - |
| `composed_3level_view` | 3ns | 3ns | 4ns | 2ns | 33ns | 1000 | - |
| `composed_3level_set_same_value` | 58ns | 48ns | 73ns | 45ns | 1.208µs | 1000 | - |
| `composed_3level_set_different_value` | 80ns | 71ns | 105ns | 69ns | 1.188µs | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 4ns | 4ns | 2ns | 11ns | 1000 | - |
| `preview_hit` | 4ns | 4ns | 5ns | 2ns | 9ns | 1000 | - |
| `preview_miss` | 3ns | 4ns | 5ns | 2ns | 5ns | 1000 | - |
| `to_value_hit` | 38ns | 38ns | 40ns | 36ns | 50ns | 1000 | - |
| `set_same_value` | 56ns | 58ns | 61ns | 35ns | 2.004µs | 1000 | - |
| `set_always_same_value` | 47ns | 41ns | 60ns | 37ns | 259ns | 1000 | - |
| `set_hit` | 46ns | 37ns | 61ns | 35ns | 284ns | 1000 | - |
| `set_miss` | 26ns | 29ns | 30ns | 16ns | 264ns | 1000 | - |
| `modify_same_value` | 60ns | 52ns | 74ns | 51ns | 1.821µs | 1000 | - |
| `modify_always_same_value` | 55ns | 47ns | 69ns | 45ns | 263ns | 1000 | - |
| `modify_hit` | 83ns | 73ns | 110ns | 71ns | 1.824µs | 1000 | - |
| `composed_3level_preview_hit` | 3ns | 3ns | 4ns | 2ns | 212ns | 1000 | - |
| `composed_3level_set_same_value` | 53ns | 57ns | 64ns | 42ns | 1.632µs | 1000 | - |
| `composed_3level_set_hit` | 42ns | 39ns | 57ns | 37ns | 324ns | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.431µs | 1.379µs | 1.966µs | 1.348µs | 3.868µs | 1000 | - |
| `build_and_run/10` | 2.196µs | 2.166µs | 2.222µs | 2.099µs | 4.168µs | 1000 | - |
| `build_chain/100` | 15.395µs | 15.2µs | 16.164µs | 15.06µs | 23.611µs | 1000 | - |
| `build_and_run/100` | 22.691µs | 22.451µs | 23.444µs | 22.246µs | 30.608µs | 1000 | - |
| `build_then/10` | 1.414µs | 1.391µs | 1.415µs | 1.357µs | 2.589µs | 1000 | 7.07 M elem/s |
| `build_bind/10` | 1.161µs | 1.143µs | 1.165µs | 1.112µs | 2.245µs | 1000 | 8.61 M elem/s |
| `build_then/100` | 15.405µs | 15.244µs | 16.148µs | 15.075µs | 23.442µs | 1000 | 6.49 M elem/s |
| `build_bind/100` | 12.707µs | 12.568µs | 13.489µs | 12.355µs | 21.196µs | 1000 | 7.87 M elem/s |
| `build_then/1000` | 174.247µs | 172.299µs | 182.964µs | 170.701µs | 207.81µs | 100 | 5.74 M elem/s |
| `build_bind/1000` | 138.761µs | 138.315µs | 148.039µs | 131.588µs | 150.493µs | 100 | 7.21 M elem/s |
| `build_then/5000` | 1.078309ms | 1.075331ms | 1.091813ms | 1.063128ms | 1.177974ms | 100 | 4.64 M elem/s |
| `build_bind/5000` | 702.243µs | 703.347µs | 722.849µs | 660.472µs | 839.488µs | 100 | 7.12 M elem/s |
| `run_then/10` | 706ns | 682ns | 712ns | 670ns | 3.045µs | 1000 | 14.16 M elem/s |
| `run_bind/10` | 1.135µs | 1.112µs | 1.154µs | 1.08µs | 2.776µs | 1000 | 8.81 M elem/s |
| `run_then/100` | 6.956µs | 6.874µs | 7.719µs | 6.825µs | 10.345µs | 1000 | 14.38 M elem/s |
| `run_bind/100` | 10.939µs | 10.796µs | 11.719µs | 10.689µs | 16.309µs | 1000 | 9.14 M elem/s |
| `run_then/1000` | 76.902µs | 76.198µs | 85.491µs | 75.862µs | 88.467µs | 100 | 13.00 M elem/s |
| `run_bind/1000` | 118.511µs | 117.802µs | 126.959µs | 115.106µs | 136.307µs | 100 | 8.44 M elem/s |
| `run_then/5000` | 463.9µs | 459.519µs | 488.128µs | 447.251µs | 533.152µs | 100 | 10.78 M elem/s |
| `run_bind/5000` | 665.548µs | 664.314µs | 689.506µs | 644.091µs | 702.971µs | 100 | 7.51 M elem/s |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.237µs | 1.22µs | 1.244µs | 1.175µs | 3.619µs | 1000 | - |
| `build_and_run/10` | 1.403µs | 1.377µs | 1.433µs | 1.337µs | 2.577µs | 1000 | - |
| `build_chain/100` | 13.594µs | 13.46µs | 14.373µs | 13.323µs | 17.074µs | 1000 | - |
| `build_and_run/100` | 15.426µs | 15.247µs | 16.2µs | 15.031µs | 26.497µs | 1000 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 3ns | 3ns | 4ns | 2ns | 11ns | 1000 | - |
| `try_each_alt_hit` | 13ns | 13ns | 14ns | 8ns | 1.627µs | 1000 | - |
| `try_each_all_fail` | 4ns | 4ns | 5ns | 3ns | 9ns | 1000 | - |
| `filter_keep_all` | 37ns | 37ns | 40ns | 26ns | 66ns | 1000 | - |
| `filter_keep_some` | 39ns | 43ns | 48ns | 25ns | 2.04µs | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 2.178µs | 2.153µs | 2.224µs | 2.044µs | 3.527µs | 1000 | - |
| `program_build_and_run/10` | 1.389µs | 1.367µs | 1.391µs | 1.336µs | 3.398µs | 1000 | - |
| `dsl_loop/10` | 40ns | 49ns | 54ns | 25ns | 294ns | 1000 | - |
| `free_build_and_run/100` | 22.582µs | 22.349µs | 23.342µs | 22.105µs | 31.965µs | 1000 | - |
| `program_build_and_run/100` | 15.586µs | 15.406µs | 16.378µs | 15.234µs | 25.863µs | 1000 | - |
| `dsl_loop/100` | 163ns | 144ns | 273ns | 143ns | 2.079µs | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 128ns | 102ns | 203ns | 101ns | 1.951µs | 1000 | - |
| `context_iteration/2` | 116ns | 100ns | 199ns | 100ns | 1.262µs | 1000 | - |
| `context_accumulation/3` | 159ns | 144ns | 284ns | 143ns | 1.484µs | 1000 | - |
| `context_iteration/3` | 157ns | 141ns | 280ns | 140ns | 1.261µs | 1000 | - |
| `context_accumulation/50` | 2.863µs | 2.833µs | 2.889µs | 2.783µs | 4.806µs | 1000 | - |
| `context_iteration/50` | 2.934µs | 2.9µs | 2.955µs | 2.84µs | 5.305µs | 1000 | - |
| `error_chain_formatting/3` | 234ns | 224ns | 266ns | 217ns | 1.998µs | 1000 | - |
| `error_chain_formatting/50` | 3.558µs | 3.525µs | 3.612µs | 3.448µs | 5.394µs | 1000 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 3ns | 3ns | 4ns | 2ns | 7ns | 1000 | - |
| `happy_path_eager` | 65ns | 46ns | 90ns | 45ns | 1.164µs | 1000 | - |
| `error_path_lazy` | 87ns | 72ns | 130ns | 70ns | 1.298µs | 1000 | - |
| `error_path_eager` | 87ns | 74ns | 133ns | 72ns | 368ns | 1000 | - |
