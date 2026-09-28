# Benchmark Results

> Generated on 2026-09-28 03:57:58 UTC, Commit: `4f29473`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 79ns | 79ns | 81ns | 62ns | 7.875µs | 1000 | - |
| `combine_errors/4` | 133ns | 126ns | 206ns | 122ns | 2.162µs | 1000 | - |
| `invalid_many/5` | 93ns | 88ns | 162ns | 86ns | 207ns | 1000 | - |
| `combine_errors/5` | 156ns | 147ns | 250ns | 143ns | 1.502µs | 1000 | - |
| `validated_map` | 3ns | 3ns | 4ns | 2ns | 232ns | 1000 | - |
| `result_map` | 3ns | 4ns | 4ns | 2ns | 19ns | 1000 | - |
| `sequence_valid/10` | 98ns | 95ns | 101ns | 90ns | 1.893µs | 1000 | - |
| `sequence_mixed/10` | 188ns | 183ns | 187ns | 179ns | 2.318µs | 1000 | - |
| `sequence_valid/100` | 292ns | 285ns | 309ns | 252ns | 1.508µs | 1000 | - |
| `sequence_mixed/100` | 2.086µs | 2.065µs | 2.094µs | 2.011µs | 5.1µs | 1000 | - |
| `iter_errors_slice/10` | 5ns | 5ns | 7ns | 4ns | 262ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 54ns | 47ns | 82ns | 46ns | 2.026µs | 1000 | - |
| `set_always_same_value` | 47ns | 51ns | 53ns | 29ns | 2.3µs | 1000 | - |
| `set_different_value` | 50ns | 46ns | 81ns | 46ns | 317ns | 1000 | - |
| `modify_changed_value` | 75ns | 71ns | 78ns | 70ns | 1.272µs | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `preview_hit` | 30ns | 29ns | 35ns | 28ns | 255ns | 1000 | - |
| `preview_miss` | 4ns | 4ns | 5ns | 2ns | 21ns | 1000 | - |
| `modify_same_value` | 46ns | 42ns | 63ns | 41ns | 96ns | 1000 | - |
| `modify_different_value` | 74ns | 69ns | 98ns | 66ns | 1.456µs | 1000 | - |
| `set_hit` | 52ns | 47ns | 82ns | 46ns | 335ns | 1000 | - |
| `set_miss` | 20ns | 16ns | 25ns | 15ns | 291ns | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.396µs | 1.38µs | 1.396µs | 1.354µs | 2.513µs | 1000 | - |
| `build_and_run/10` | 2.105µs | 2.083µs | 2.13µs | 2.04µs | 3.736µs | 1000 | - |
| `build_chain/100` | 15.327µs | 15.164µs | 16.103µs | 15.052µs | 22.88µs | 1000 | - |
| `build_and_run/100` | 22.101µs | 21.838µs | 22.967µs | 21.673µs | 30.727µs | 1000 | - |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.236µs | 1.198µs | 1.22µs | 1.177µs | 5.624µs | 1000 | - |
| `build_and_run/10` | 1.338µs | 1.321µs | 1.341µs | 1.294µs | 4.104µs | 1000 | - |
| `build_chain/100` | 13.118µs | 12.971µs | 13.879µs | 12.882µs | 18.786µs | 1000 | - |
| `build_and_run/100` | 14.74µs | 14.573µs | 15.497µs | 14.457µs | 23.98µs | 1000 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 4ns | 4ns | 5ns | 2ns | 20ns | 1000 | - |
| `try_each_alt_hit` | 10ns | 11ns | 12ns | 8ns | 29ns | 1000 | - |
| `try_each_all_fail` | 4ns | 4ns | 5ns | 2ns | 7ns | 1000 | - |
| `filter_keep_all` | 37ns | 36ns | 38ns | 23ns | 1.841µs | 1000 | - |
| `filter_keep_some` | 26ns | 24ns | 43ns | 23ns | 323ns | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 2.068µs | 2.047µs | 2.101µs | 1.977µs | 4.415µs | 1000 | - |
| `program_build_and_run/10` | 1.332µs | 1.316µs | 1.342µs | 1.29µs | 2.637µs | 1000 | - |
| `dsl_loop/10` | 31ns | 27ns | 49ns | 24ns | 300ns | 1000 | - |
| `free_build_and_run/100` | 22.06µs | 21.827µs | 22.792µs | 21.607µs | 36.854µs | 1000 | - |
| `program_build_and_run/100` | 14.835µs | 14.676µs | 15.599µs | 14.583µs | 20.606µs | 1000 | - |
| `dsl_loop/100` | 121ns | 115ns | 169ns | 114ns | 1.226µs | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 109ns | 104ns | 104ns | 103ns | 1.565µs | 1000 | - |
| `context_iteration/2` | 106ns | 103ns | 104ns | 102ns | 1.163µs | 1000 | - |
| `context_accumulation/3` | 148ns | 144ns | 145ns | 144ns | 1.172µs | 1000 | - |
| `context_iteration/3` | 149ns | 145ns | 146ns | 143ns | 1.229µs | 1000 | - |
| `context_accumulation/50` | 2.946µs | 2.919µs | 2.936µs | 2.89µs | 5.28µs | 1000 | - |
| `context_iteration/50` | 2.854µs | 2.824µs | 2.847µs | 2.792µs | 7.155µs | 1000 | - |
| `error_chain_formatting/3` | 261ns | 245ns | 389ns | 241ns | 1.422µs | 1000 | - |
| `error_chain_formatting/50` | 3.426µs | 3.387µs | 3.45µs | 3.326µs | 5.395µs | 1000 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 3ns | 3ns | 4ns | 2ns | 6ns | 1000 | - |
| `happy_path_eager` | 55ns | 47ns | 87ns | 46ns | 1.347µs | 1000 | - |
| `error_path_lazy` | 92ns | 70ns | 128ns | 68ns | 2.574µs | 1000 | - |
| `error_path_eager` | 74ns | 68ns | 116ns | 67ns | 2.295µs | 1000 | - |
