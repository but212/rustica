# Benchmark Results

> Generated on 2026-09-26 16:13:31 UTC, Commit: `6943c31`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 63ns | 63ns | 65ns | 61ns | 130ns | 1000 | - |
| `combine_errors/4` | 153ns | 152ns | 160ns | 137ns | 1.633µs | 1000 | - |
| `invalid_many/5` | 93ns | 93ns | 95ns | 89ns | 191ns | 1000 | - |
| `combine_errors/5` | 184ns | 168ns | 259ns | 152ns | 1.626µs | 1000 | - |
| `validated_map` | 3ns | 4ns | 5ns | 2ns | 63ns | 1000 | - |
| `result_map` | 3ns | 3ns | 4ns | 2ns | 16ns | 1000 | - |
| `sequence_valid/10` | 98ns | 90ns | 153ns | 86ns | 2.131µs | 1000 | - |
| `sequence_mixed/10` | 190ns | 188ns | 194ns | 182ns | 381ns | 1000 | - |
| `sequence_valid/100` | 295ns | 282ns | 331ns | 240ns | 2.074µs | 1000 | - |
| `sequence_mixed/100` | 2.077µs | 2.047µs | 2.08µs | 1.998µs | 5.017µs | 1000 | - |
| `iter_errors_slice/10` | 5ns | 5ns | 7ns | 4ns | 62ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 51ns | 47ns | 82ns | 46ns | 115ns | 1000 | - |
| `set_always_same_value` | 33ns | 30ns | 52ns | 29ns | 1.461µs | 1000 | - |
| `set_different_value` | 48ns | 46ns | 78ns | 46ns | 111ns | 1000 | - |
| `modify_changed_value` | 81ns | 78ns | 83ns | 74ns | 1.5µs | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `preview_hit` | 29ns | 28ns | 36ns | 28ns | 87ns | 1000 | - |
| `preview_miss` | 5ns | 4ns | 5ns | 2ns | 1.478µs | 1000 | - |
| `modify_same_value` | 47ns | 42ns | 64ns | 41ns | 93ns | 1000 | - |
| `modify_different_value` | 78ns | 74ns | 98ns | 66ns | 1.307µs | 1000 | - |
| `set_hit` | 53ns | 47ns | 81ns | 46ns | 1.203µs | 1000 | - |
| `set_miss` | 19ns | 21ns | 25ns | 15ns | 77ns | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.385µs | 1.372µs | 1.396µs | 1.342µs | 2.604µs | 1000 | - |
| `build_and_run/10` | 2.123µs | 2.101µs | 2.143µs | 2.045µs | 4.007µs | 1000 | - |
| `build_chain/100` | 15.709µs | 15.532µs | 16.516µs | 15.398µs | 19.232µs | 1000 | - |
| `build_and_run/100` | 22.684µs | 22.434µs | 23.446µs | 22.274µs | 29.29µs | 1000 | - |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.248µs | 1.236µs | 1.25µs | 1.209µs | 2.378µs | 1000 | - |
| `build_and_run/10` | 1.395µs | 1.381µs | 1.433µs | 1.337µs | 2.388µs | 1000 | - |
| `build_chain/100` | 13.62µs | 13.458µs | 14.382µs | 13.372µs | 17.773µs | 1000 | - |
| `build_and_run/100` | 15.267µs | 15.091µs | 16.041µs | 14.922µs | 20.282µs | 1000 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 4ns | 4ns | 5ns | 2ns | 20ns | 1000 | - |
| `try_each_alt_hit` | 10ns | 11ns | 12ns | 6ns | 66ns | 1000 | - |
| `try_each_all_fail` | 4ns | 4ns | 5ns | 2ns | 6ns | 1000 | - |
| `filter_keep_all` | 29ns | 26ns | 38ns | 22ns | 183ns | 1000 | - |
| `filter_keep_some` | 25ns | 24ns | 30ns | 23ns | 109ns | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 2.344µs | 2.304µs | 2.363µs | 2.253µs | 6.212µs | 1000 | - |
| `program_build_and_run/10` | 1.43µs | 1.414µs | 1.448µs | 1.379µs | 3.061µs | 1000 | - |
| `dsl_loop/10` | 33ns | 26ns | 50ns | 25ns | 1.125µs | 1000 | - |
| `free_build_and_run/100` | 22.414µs | 22.162µs | 23.181µs | 21.957µs | 27.064µs | 1000 | - |
| `program_build_and_run/100` | 15.261µs | 15.096µs | 16.015µs | 14.985µs | 19.338µs | 1000 | - |
| `dsl_loop/100` | 132ns | 116ns | 187ns | 114ns | 1.326µs | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 110ns | 104ns | 187ns | 103ns | 1.195µs | 1000 | - |
| `context_iteration/2` | 110ns | 103ns | 190ns | 102ns | 1.379µs | 1000 | - |
| `context_accumulation/3` | 152ns | 145ns | 150ns | 144ns | 1.708µs | 1000 | - |
| `context_iteration/3` | 151ns | 143ns | 150ns | 143ns | 1.289µs | 1000 | - |
| `context_accumulation/50` | 2.938µs | 2.911µs | 2.962µs | 2.859µs | 4.673µs | 1000 | - |
| `context_iteration/50` | 3.017µs | 2.949µs | 3.238µs | 2.908µs | 8.512µs | 1000 | - |
| `error_chain_formatting/3` | 268ns | 257ns | 279ns | 243ns | 1.739µs | 1000 | - |
| `error_chain_formatting/50` | 3.485µs | 3.448µs | 3.5µs | 3.398µs | 5.562µs | 1000 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 4ns | 4ns | 5ns | 2ns | 20ns | 1000 | - |
| `happy_path_eager` | 67ns | 47ns | 89ns | 46ns | 1.624µs | 1000 | - |
| `error_path_lazy` | 77ns | 69ns | 119ns | 68ns | 1.994µs | 1000 | - |
| `error_path_eager` | 76ns | 69ns | 119ns | 68ns | 1.718µs | 1000 | - |
