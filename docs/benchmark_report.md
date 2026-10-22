# Benchmark Results

> Generated on 2026-10-19 09:26:20 UTC, Commit: `d2c359c`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `validated_map` | 2ns | 2ns | 3ns | 2ns | 16ns | 1000 | - |
| `result_map` | 2ns | 3ns | 3ns | 2ns | 12ns | 1000 | - |
| `sequence_valid/10` | 86ns | 81ns | 103ns | 63ns | 3.911µs | 1000 | - |
| `sequence_mixed/10` | 277ns | 254ns | 258ns | 253ns | 8.046µs | 1000 | - |
| `sequence_valid/100` | 187ns | 175ns | 208ns | 170ns | 1.458µs | 1000 | - |
| `sequence_mixed/100` | 2.482µs | 2.456µs | 2.59µs | 2.25µs | 5.812µs | 1000 | - |
| `iter_errors_slice/10` | 3ns | 3ns | 4ns | 3ns | 14ns | 1000 | - |
| `collect_all_valid/10` | 63ns | 59ns | 82ns | 57ns | 796ns | 1000 | - |
| `collect_early_error/10` | 43ns | 41ns | 47ns | 34ns | 904ns | 1000 | - |
| `collect_late_error/10` | 76ns | 71ns | 93ns | 69ns | 1.022µs | 1000 | - |
| `collect_all_valid/100` | 182ns | 179ns | 191ns | 167ns | 1.5µs | 1000 | - |
| `collect_early_error/100` | 224ns | 229ns | 241ns | 133ns | 1.28µs | 1000 | - |
| `collect_late_error/100` | 200ns | 195ns | 209ns | 192ns | 1.432µs | 1000 | - |
| `collect_early_error_1000_large_payload` | 5.93µs | 5.842µs | 6.592µs | 5.432µs | 10.611µs | 1000 | - |
| `zip3_all_valid` | 5ns | 5ns | 7ns | 5ns | 19ns | 1000 | - |
| `zip3_all_invalid` | 147ns | 133ns | 178ns | 132ns | 1.797µs | 1000 | - |
| `combine_asymmetric_small_into_large` | 125ns | 120ns | 177ns | 118ns | 1.122µs | 1000 | - |
| `combine_asymmetric_large_into_small` | 124ns | 115ns | 178ns | 112ns | 1.376µs | 1000 | - |
| `invalid_single` | 34ns | 33ns | 38ns | 28ns | 1.017µs | 1000 | - |
| `invalid_many_from_exact_iter_10` | 36ns | 35ns | 43ns | 31ns | 168ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 2ns | 2ns | 3ns | 2ns | 9ns | 1000 | - |
| `view_borrow` | 2ns | 3ns | 3ns | 2ns | 18ns | 1000 | - |
| `to_value_owned` | 32ns | 31ns | 42ns | 31ns | 201ns | 1000 | - |
| `set_same_value` | 62ns | 58ns | 76ns | 58ns | 968ns | 1000 | - |
| `set_always_same_value` | 61ns | 58ns | 75ns | 57ns | 893ns | 1000 | - |
| `set_different_value` | 61ns | 58ns | 76ns | 58ns | 935ns | 1000 | - |
| `modify_unchanged_value` | 73ns | 69ns | 89ns | 69ns | 1.023µs | 1000 | - |
| `modify_always_unchanged_value` | 72ns | 67ns | 86ns | 66ns | 1.1µs | 1000 | - |
| `modify_changed_value` | 96ns | 93ns | 122ns | 90ns | 1.289µs | 1000 | - |
| `composed_3level_view` | 2ns | 3ns | 3ns | 2ns | 140ns | 1000 | - |
| `composed_3level_set_same_value` | 78ns | 75ns | 93ns | 74ns | 783ns | 1000 | - |
| `composed_3level_set_different_value` | 112ns | 109ns | 142ns | 108ns | 281ns | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 3ns | 2ns | 11ns | 1000 | - |
| `preview_hit` | 3ns | 3ns | 4ns | 2ns | 10ns | 1000 | - |
| `preview_miss` | 3ns | 3ns | 4ns | 2ns | 9ns | 1000 | - |
| `to_value_hit` | 48ns | 48ns | 51ns | 38ns | 1.202µs | 1000 | - |
| `set_same_value` | 69ns | 62ns | 83ns | 62ns | 995ns | 1000 | - |
| `set_always_same_value` | 68ns | 63ns | 85ns | 62ns | 868ns | 1000 | - |
| `set_hit` | 69ns | 64ns | 82ns | 62ns | 1.271µs | 1000 | - |
| `set_miss` | 34ns | 29ns | 40ns | 29ns | 928ns | 1000 | - |
| `modify_same_value` | 80ns | 76ns | 98ns | 75ns | 931ns | 1000 | - |
| `modify_always_same_value` | 80ns | 73ns | 95ns | 72ns | 2.354µs | 1000 | - |
| `modify_hit` | 109ns | 100ns | 136ns | 99ns | 1.206µs | 1000 | - |
| `composed_3level_preview_hit` | 2ns | 3ns | 4ns | 2ns | 135ns | 1000 | - |
| `composed_3level_set_same_value` | 78ns | 71ns | 93ns | 70ns | 1.108µs | 1000 | - |
| `composed_3level_set_hit` | 68ns | 65ns | 76ns | 65ns | 1.241µs | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 2.625µs | 2.616µs | 2.727µs | 2.526µs | 4.903µs | 1000 | - |
| `build_and_run/10` | 4.212µs | 4.192µs | 4.385µs | 4.019µs | 6.578µs | 1000 | - |
| `build_chain/100` | 27.845µs | 27.786µs | 29.296µs | 26.818µs | 33.22µs | 1000 | - |
| `build_and_run/100` | 43.432µs | 43.282µs | 45.239µs | 41.687µs | 50.355µs | 1000 | - |
| `build_then/10` | 2.662µs | 2.633µs | 2.954µs | 2.526µs | 6.248µs | 1000 | 3.76 M elem/s |
| `build_bind/10` | 2.246µs | 2.221µs | 2.467µs | 2.145µs | 4.99µs | 1000 | 4.45 M elem/s |
| `build_then/100` | 27.931µs | 27.832µs | 29.355µs | 26.843µs | 33.917µs | 1000 | 3.58 M elem/s |
| `build_bind/100` | 24.483µs | 24.375µs | 25.811µs | 23.524µs | 29.555µs | 1000 | 4.08 M elem/s |
| `build_then/1000` | 329.994µs | 326.087µs | 354.453µs | 314.245µs | 375.472µs | 100 | 3.03 M elem/s |
| `build_bind/1000` | 250.294µs | 248.763µs | 261.283µs | 240.054µs | 265.902µs | 100 | 4.00 M elem/s |
| `build_then/5000` | 1.629889ms | 1.633256ms | 1.681477ms | 1.577935ms | 1.72296ms | 100 | 3.07 M elem/s |
| `build_bind/5000` | 1.254408ms | 1.255489ms | 1.299112ms | 1.207327ms | 1.401134ms | 100 | 3.99 M elem/s |
| `run_then/10` | 1.547µs | 1.508µs | 1.607µs | 1.498µs | 3.408µs | 1000 | 6.46 M elem/s |
| `run_bind/10` | 2.402µs | 2.383µs | 2.512µs | 2.288µs | 3.55µs | 1000 | 4.16 M elem/s |
| `run_then/100` | 15.514µs | 15.363µs | 16.926µs | 14.821µs | 19.894µs | 1000 | 6.45 M elem/s |
| `run_bind/100` | 24.052µs | 23.875µs | 25.798µs | 22.736µs | 30.394µs | 1000 | 4.16 M elem/s |
| `run_then/1000` | 155.21µs | 154.17µs | 160.515µs | 148.769µs | 190.338µs | 100 | 6.44 M elem/s |
| `run_bind/1000` | 239.603µs | 236.22µs | 255.687µs | 227.64µs | 289.613µs | 100 | 4.17 M elem/s |
| `run_then/5000` | 804.523µs | 805.986µs | 834.497µs | 773.015µs | 843.993µs | 100 | 6.21 M elem/s |
| `run_bind/5000` | 1.229653ms | 1.227463ms | 1.298196ms | 1.174888ms | 1.373624ms | 100 | 4.07 M elem/s |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.798µs | 1.768µs | 1.952µs | 1.708µs | 4.868µs | 1000 | - |
| `build_only/10` | 1.321µs | 1.306µs | 1.353µs | 1.26µs | 4.255µs | 1000 | - |
| `build_and_run/10` | 1.966µs | 1.93µs | 2.004µs | 1.858µs | 3.912µs | 1000 | - |
| `run_chain/10` | 676ns | 672ns | 689ns | 643ns | 1.663µs | 1000 | - |
| `drop_chain/10` | 464ns | 452ns | 478ns | 434ns | 1.85µs | 1000 | - |
| `mixed_build_only/10` | 2.96µs | 2.949µs | 3.058µs | 2.845µs | 4.165µs | 1000 | - |
| `mixed_run_chain/10` | 1.442µs | 1.425µs | 1.477µs | 1.37µs | 4.727µs | 1000 | - |
| `mixed_drop_chain/10` | 1.168µs | 1.16µs | 1.208µs | 1.11µs | 2.443µs | 1000 | - |
| `build_chain/100` | 20.65µs | 20.584µs | 21.393µs | 19.845µs | 24.816µs | 1000 | - |
| `build_only/100` | 16.04µs | 16.014µs | 16.766µs | 15.422µs | 18.429µs | 1000 | - |
| `build_and_run/100` | 21.235µs | 21.243µs | 22.063µs | 20.385µs | 32.491µs | 1000 | - |
| `run_chain/100` | 6.828µs | 6.811µs | 7.333µs | 6.544µs | 9.75µs | 1000 | - |
| `drop_chain/100` | 5.729µs | 5.704µs | 6.207µs | 5.443µs | 8.694µs | 1000 | - |
| `mixed_build_only/100` | 35.128µs | 35.126µs | 36.482µs | 33.863µs | 50.167µs | 1000 | - |
| `mixed_run_chain/100` | 18.582µs | 18.508µs | 19.488µs | 17.595µs | 29.711µs | 1000 | - |
| `mixed_drop_chain/100` | 15.977µs | 15.811µs | 16.983µs | 15.025µs | 25.995µs | 1000 | - |
| `build_chain/1000` | 213.175µs | 211.568µs | 224.836µs | 185.683µs | 235.574µs | 100 | - |
| `build_only/1000` | 167.882µs | 166.065µs | 177.561µs | 147.121µs | 213.733µs | 100 | - |
| `build_and_run/1000` | 213.917µs | 213.768µs | 224.675µs | 193.061µs | 246.394µs | 100 | - |
| `run_chain/1000` | 45.287µs | 44.678µs | 48.549µs | 43.105µs | 97.146µs | 100 | - |
| `drop_chain/1000` | 37.207µs | 36.914µs | 38.428µs | 35.675µs | 49.536µs | 100 | - |
| `mixed_build_only/1000` | 363.328µs | 362.515µs | 382.429µs | 348.872µs | 396.57µs | 100 | - |
| `mixed_run_chain/1000` | 180.567µs | 179.139µs | 194.043µs | 171.659µs | 204.075µs | 100 | - |
| `mixed_drop_chain/1000` | 151.414µs | 150.903µs | 159.341µs | 145.159µs | 171.404µs | 100 | - |
| `build_chain/5000` | 1.25072ms | 1.251396ms | 1.294672ms | 1.20273ms | 1.406045ms | 100 | - |
| `build_only/5000` | 809.333µs | 803.871µs | 842.274µs | 769.478µs | 935.806µs | 100 | - |
| `build_and_run/5000` | 1.254935ms | 1.253455ms | 1.29506ms | 1.217647ms | 1.328904ms | 100 | - |
| `run_chain/5000` | 450.603µs | 449.353µs | 469.512µs | 430.359µs | 513.185µs | 100 | - |
| `drop_chain/5000` | 403.269µs | 402.144µs | 424.261µs | 386.309µs | 447.701µs | 100 | - |
| `mixed_build_only/5000` | 1.828665ms | 1.829206ms | 1.89134ms | 1.754496ms | 1.90111ms | 100 | - |
| `mixed_run_chain/5000` | 1.066782ms | 1.064316ms | 1.107219ms | 1.012701ms | 1.181813ms | 100 | - |
| `mixed_drop_chain/5000` | 927.185µs | 929.514µs | 955.857µs | 890.681µs | 978.48µs | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 4ns | 4ns | 5ns | 3ns | 13ns | 1000 | - |
| `try_each_alt_hit` | 14ns | 14ns | 15ns | 8ns | 825ns | 1000 | - |
| `try_each_all_fail` | 3ns | 3ns | 4ns | 2ns | 11ns | 1000 | - |
| `filter_keep_all` | 39ns | 35ns | 47ns | 34ns | 933ns | 1000 | - |
| `filter_keep_some` | 41ns | 35ns | 49ns | 35ns | 1.378µs | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 4.219µs | 4.176µs | 4.694µs | 3.996µs | 9.03µs | 1000 | - |
| `program_build_and_run/10` | 1.836µs | 1.792µs | 1.98µs | 1.781µs | 3.125µs | 1000 | - |
| `dsl_loop/10` | 41ns | 35ns | 50ns | 34ns | 639ns | 1000 | - |
| `free_build_and_run/100` | 43.254µs | 43.111µs | 45.157µs | 41.478µs | 49.255µs | 1000 | - |
| `program_build_and_run/100` | 20.226µs | 20.196µs | 21.047µs | 19.433µs | 25.554µs | 1000 | - |
| `dsl_loop/100` | 140ns | 122ns | 225ns | 121ns | 1.774µs | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 125ns | 121ns | 124ns | 120ns | 1.349µs | 1000 | - |
| `context_iteration/2` | 121ns | 119ns | 123ns | 115ns | 826ns | 1000 | - |
| `context_accumulation/3` | 166ns | 164ns | 168ns | 158ns | 906ns | 1000 | - |
| `context_iteration/3` | 165ns | 160ns | 166ns | 158ns | 1.248µs | 1000 | - |
| `context_accumulation/50` | 3.021µs | 2.96µs | 3.234µs | 2.835µs | 5.553µs | 1000 | - |
| `context_iteration/50` | 2.984µs | 2.953µs | 3.135µs | 2.831µs | 5.989µs | 1000 | - |
| `error_chain_formatting/3` | 38ns | 36ns | 47ns | 36ns | 229ns | 1000 | - |
| `error_chain_formatting/50` | 185ns | 179ns | 216ns | 148ns | 963ns | 1000 | - |
| `happy_path_lazy` | 3ns | 3ns | 4ns | 2ns | 149ns | 1000 | - |
| `happy_path_eager` | 50ns | 47ns | 64ns | 46ns | 809ns | 1000 | - |
| `error_path_lazy` | 95ns | 87ns | 127ns | 86ns | 817ns | 1000 | - |
| `error_path_eager` | 97ns | 87ns | 128ns | 86ns | 1.513µs | 1000 | - |
| `with_contexts_batch/5` | 185ns | 177ns | 237ns | 175ns | 1.176µs | 1000 | - |
| `with_contexts_batch/20` | 654ns | 635ns | 829ns | 613ns | 2.243µs | 1000 | - |
| `with_contexts_batch/50` | 2.332µs | 2.275µs | 2.384µs | 2.226µs | 6.134µs | 1000 | - |
| `with_context_str_literal` | 80ns | 73ns | 97ns | 70ns | 981ns | 1000 | - |
| `with_context_owned_string` | 80ns | 73ns | 98ns | 72ns | 1.293µs | 1000 | - |
| `context_accumulator_invoke` | 214ns | 206ns | 267ns | 206ns | 1.209µs | 1000 | - |
