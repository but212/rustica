# Benchmark Results

> Generated on 2026-10-30 10:30:02 UTC, Commit: `eefa4aa`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `validated_map` | 3ns | 3ns | 4ns | 2ns | 14ns | 1000 | - |
| `result_map` | 4ns | 4ns | 5ns | 2ns | 272ns | 1000 | - |
| `sequence_valid/10` | 56ns | 54ns | 93ns | 48ns | 106ns | 1000 | - |
| `sequence_mixed/10` | 212ns | 199ns | 238ns | 191ns | 3.14µs | 1000 | - |
| `sequence_valid/100` | 223ns | 213ns | 215ns | 212ns | 2.895µs | 1000 | - |
| `sequence_mixed/100` | 1.751µs | 1.722µs | 1.74µs | 1.697µs | 4.66µs | 1000 | - |
| `iter_errors_slice/10` | 5ns | 5ns | 6ns | 4ns | 233ns | 1000 | - |
| `collect_all_valid/10` | 63ns | 48ns | 94ns | 46ns | 1.783µs | 1000 | - |
| `collect_early_error/10` | 36ns | 33ns | 52ns | 31ns | 1.593µs | 1000 | - |
| `collect_late_error/10` | 55ns | 51ns | 88ns | 50ns | 2.146µs | 1000 | - |
| `collect_all_valid/100` | 214ns | 210ns | 212ns | 209ns | 2.211µs | 1000 | - |
| `collect_early_error/100` | 140ns | 136ns | 137ns | 134ns | 2.195µs | 1000 | - |
| `collect_late_error/100` | 230ns | 215ns | 241ns | 211ns | 3.364µs | 1000 | - |
| `collect_early_error_1000_large_payload` | 11.032µs | 10.836µs | 12.97µs | 10.365µs | 15.721µs | 1000 | - |
| `zip3_all_valid` | 11ns | 11ns | 12ns | 10ns | 253ns | 1000 | - |
| `zip3_all_invalid` | 97ns | 92ns | 105ns | 72ns | 6.122µs | 1000 | - |
| `combine_asymmetric_small_into_large` | 102ns | 90ns | 169ns | 85ns | 2.098µs | 1000 | - |
| `combine_asymmetric_large_into_small` | 94ns | 85ns | 161ns | 83ns | 2.179µs | 1000 | - |
| `invalid_single` | 14ns | 14ns | 16ns | 8ns | 1.644µs | 1000 | - |
| `invalid_many_from_exact_iter_10` | 18ns | 19ns | 22ns | 10ns | 237ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 19ns | 1000 | - |
| `view_borrow` | 3ns | 4ns | 4ns | 2ns | 8ns | 1000 | - |
| `to_value_owned` | 25ns | 25ns | 27ns | 23ns | 41ns | 1000 | - |
| `set_same_value` | 40ns | 39ns | 43ns | 24ns | 3.886µs | 1000 | - |
| `set_always_same_value` | 27ns | 25ns | 41ns | 24ns | 298ns | 1000 | - |
| `set_different_value` | 29ns | 25ns | 43ns | 25ns | 1.866µs | 1000 | - |
| `modify_unchanged_value` | 34ns | 33ns | 53ns | 32ns | 67ns | 1000 | - |
| `modify_always_unchanged_value` | 32ns | 31ns | 38ns | 30ns | 63ns | 1000 | - |
| `modify_changed_value` | 50ns | 47ns | 48ns | 46ns | 2.043µs | 1000 | - |
| `composed_3level_view` | 3ns | 4ns | 4ns | 2ns | 58ns | 1000 | - |
| `composed_3level_set_same_value` | 50ns | 49ns | 53ns | 37ns | 3.991µs | 1000 | - |
| `composed_3level_set_different_value` | 63ns | 58ns | 74ns | 56ns | 94ns | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 14ns | 1000 | - |
| `preview_hit` | 3ns | 3ns | 4ns | 2ns | 6ns | 1000 | - |
| `preview_miss` | 3ns | 3ns | 4ns | 2ns | 4ns | 1000 | - |
| `to_value_hit` | 15ns | 16ns | 16ns | 15ns | 23ns | 1000 | - |
| `set_same_value` | 37ns | 33ns | 42ns | 31ns | 2.879µs | 1000 | - |
| `set_always_same_value` | 39ns | 39ns | 41ns | 36ns | 292ns | 1000 | - |
| `set_hit` | 42ns | 40ns | 43ns | 35ns | 1.831µs | 1000 | - |
| `set_miss` | 16ns | 17ns | 17ns | 15ns | 28ns | 1000 | - |
| `modify_same_value` | 53ns | 53ns | 58ns | 38ns | 68ns | 1000 | - |
| `modify_always_same_value` | 48ns | 49ns | 53ns | 38ns | 296ns | 1000 | - |
| `modify_hit` | 60ns | 48ns | 83ns | 47ns | 2.133µs | 1000 | - |
| `composed_3level_preview_hit` | 3ns | 4ns | 4ns | 2ns | 249ns | 1000 | - |
| `composed_3level_set_same_value` | 39ns | 39ns | 41ns | 36ns | 57ns | 1000 | - |
| `composed_3level_set_hit` | 42ns | 40ns | 42ns | 35ns | 1.892µs | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.235µs | 1.155µs | 1.743µs | 1.136µs | 5.189µs | 1000 | - |
| `build_and_run/10` | 1.823µs | 1.786µs | 1.823µs | 1.754µs | 4.446µs | 1000 | - |
| `build_chain/100` | 17.246µs | 17.014µs | 17.988µs | 16.831µs | 35.991µs | 1000 | - |
| `build_and_run/100` | 23.674µs | 23.169µs | 24.194µs | 23.006µs | 59.457µs | 1000 | - |
| `build_then/10` | 1.179µs | 1.161µs | 1.179µs | 1.138µs | 4.036µs | 1000 | 8.48 M elem/s |
| `build_bind/10` | 661ns | 642ns | 658ns | 622ns | 2.749µs | 1000 | 15.13 M elem/s |
| `build_then/100` | 17.279µs | 17.093µs | 18.062µs | 16.877µs | 29.992µs | 1000 | 5.79 M elem/s |
| `build_bind/100` | 11.61µs | 11.437µs | 12.337µs | 11.368µs | 32.621µs | 1000 | 8.61 M elem/s |
| `build_then/1000` | 172.974µs | 173.129µs | 182.913µs | 168.425µs | 189.895µs | 100 | 5.78 M elem/s |
| `build_bind/1000` | 115.719µs | 114.499µs | 124.042µs | 114.174µs | 135.434µs | 100 | 8.64 M elem/s |
| `build_then/5000` | 888.717µs | 867.033µs | 960.598µs | 851.525µs | 1.621085ms | 100 | 5.63 M elem/s |
| `build_bind/5000` | 581.798µs | 583.236µs | 596.727µs | 571.581µs | 643.314µs | 100 | 8.59 M elem/s |
| `run_then/10` | 651ns | 633ns | 652ns | 617ns | 2.675µs | 1000 | 15.36 M elem/s |
| `run_bind/10` | 982ns | 958ns | 979ns | 925ns | 3.278µs | 1000 | 10.18 M elem/s |
| `run_then/100` | 6.349µs | 6.278µs | 7.136µs | 6.208µs | 9.914µs | 1000 | 15.75 M elem/s |
| `run_bind/100` | 9.478µs | 9.365µs | 10.244µs | 9.29µs | 16.244µs | 1000 | 10.55 M elem/s |
| `run_then/1000` | 66.862µs | 65.707µs | 76.294µs | 65.202µs | 88.976µs | 100 | 14.96 M elem/s |
| `run_bind/1000` | 94.38µs | 93.51µs | 102.912µs | 92.553µs | 104.556µs | 100 | 10.60 M elem/s |
| `run_then/5000` | 532.047µs | 527.567µs | 552.253µs | 514.363µs | 711.903µs | 100 | 9.40 M elem/s |
| `run_bind/5000` | 668.152µs | 664.97µs | 687.196µs | 652.522µs | 697.075µs | 100 | 7.48 M elem/s |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.184µs | 1.17µs | 1.181µs | 1.153µs | 3.549µs | 1000 | - |
| `build_only/10` | 940ns | 926ns | 953ns | 918ns | 3.026µs | 1000 | - |
| `build_and_run/10` | 1.286µs | 1.259µs | 1.448µs | 1.247µs | 3.424µs | 1000 | - |
| `run_chain/10` | 402ns | 398ns | 405ns | 390ns | 2.217µs | 1000 | - |
| `drop_chain/10` | 298ns | 292ns | 299ns | 287ns | 1.32µs | 1000 | - |
| `mixed_build_only/10` | 1.795µs | 1.771µs | 1.788µs | 1.755µs | 4.022µs | 1000 | - |
| `mixed_run_chain/10` | 1.082µs | 1.068µs | 1.102µs | 1.028µs | 3.237µs | 1000 | - |
| `mixed_drop_chain/10` | 1.118µs | 1.103µs | 1.13µs | 1.066µs | 2.895µs | 1000 | - |
| `build_chain/100` | 14.264µs | 14.104µs | 15.014µs | 14.029µs | 20.318µs | 1000 | - |
| `build_only/100` | 10.839µs | 10.714µs | 11.604µs | 10.645µs | 13.667µs | 1000 | - |
| `build_and_run/100` | 14.14µs | 13.936µs | 15.065µs | 13.808µs | 17.637µs | 1000 | - |
| `run_chain/100` | 3.569µs | 3.527µs | 3.569µs | 3.5µs | 5.914µs | 1000 | - |
| `drop_chain/100` | 2.938µs | 2.887µs | 2.975µs | 2.862µs | 8.546µs | 1000 | - |
| `mixed_build_only/100` | 23.077µs | 22.76µs | 23.755µs | 22.627µs | 54.657µs | 1000 | - |
| `mixed_run_chain/100` | 11.349µs | 10.492µs | 16.949µs | 10.121µs | 36.535µs | 1000 | - |
| `mixed_drop_chain/100` | 11.007µs | 10.807µs | 11.884µs | 10.681µs | 19.869µs | 1000 | - |
| `build_chain/1000` | 143.867µs | 142.452µs | 151.744µs | 141.856µs | 152.946µs | 100 | - |
| `build_only/1000` | 108.055µs | 106.569µs | 116.428µs | 105.989µs | 127.748µs | 100 | - |
| `build_and_run/1000` | 141.076µs | 139.521µs | 149.41µs | 138.73µs | 156.713µs | 100 | - |
| `run_chain/1000` | 33.395µs | 33.137µs | 33.373µs | 32.641µs | 42.369µs | 100 | - |
| `drop_chain/1000` | 27.204µs | 26.905µs | 27.231µs | 26.68µs | 36.349µs | 100 | - |
| `mixed_build_only/1000` | 226.235µs | 223.493µs | 236.012µs | 222.226µs | 262.221µs | 100 | - |
| `mixed_run_chain/1000` | 126.251µs | 109.871µs | 184.626µs | 99.206µs | 205.785µs | 100 | - |
| `mixed_drop_chain/1000` | 106.718µs | 105.432µs | 116.268µs | 104.346µs | 126.787µs | 100 | - |
| `build_chain/5000` | 924.012µs | 923.023µs | 941.322µs | 902.55µs | 959.777µs | 100 | - |
| `build_only/5000` | 639.546µs | 637.614µs | 656.99µs | 622.476µs | 708.396µs | 100 | - |
| `build_and_run/5000` | 913.623µs | 913.525µs | 928.568µs | 896.579µs | 938.077µs | 100 | - |
| `run_chain/5000` | 279.48µs | 275.992µs | 297.437µs | 269.525µs | 364.442µs | 100 | - |
| `drop_chain/5000` | 245.522µs | 244.237µs | 257.272µs | 237.815µs | 263.122µs | 100 | - |
| `mixed_build_only/5000` | 1.133538ms | 1.131849ms | 1.144493ms | 1.123814ms | 1.203273ms | 100 | - |
| `mixed_run_chain/5000` | 719.715µs | 719.261µs | 736.83µs | 702.144µs | 783.427µs | 100 | - |
| `mixed_drop_chain/5000` | 731.503µs | 730.868µs | 745.857µs | 717.282µs | 768.509µs | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 4ns | 4ns | 6ns | 2ns | 21ns | 1000 | - |
| `try_each_alt_hit` | 11ns | 13ns | 14ns | 6ns | 204ns | 1000 | - |
| `try_each_all_fail` | 4ns | 4ns | 5ns | 2ns | 58ns | 1000 | - |
| `filter_keep_all` | 24ns | 23ns | 28ns | 22ns | 245ns | 1000 | - |
| `filter_keep_some` | 25ns | 24ns | 41ns | 23ns | 223ns | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 1.787µs | 1.768µs | 1.791µs | 1.74µs | 4.157µs | 1000 | - |
| `program_build_and_run/10` | 1.286µs | 1.271µs | 1.279µs | 1.262µs | 3.302µs | 1000 | - |
| `dsl_loop/10` | 30ns | 21ns | 40ns | 20ns | 1.758µs | 1000 | - |
| `free_build_and_run/100` | 24.145µs | 23.845µs | 24.938µs | 23.659µs | 34.327µs | 1000 | - |
| `program_build_and_run/100` | 14.21µs | 14.019µs | 14.968µs | 13.928µs | 20.721µs | 1000 | - |
| `dsl_loop/100` | 193ns | 191ns | 197ns | 156ns | 2.378µs | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 113ns | 89ns | 174ns | 87ns | 4.197µs | 1000 | - |
| `context_iteration/2` | 102ns | 96ns | 165ns | 94ns | 2.144µs | 1000 | - |
| `context_accumulation/3` | 136ns | 127ns | 141ns | 126ns | 2.335µs | 1000 | - |
| `context_iteration/3` | 142ns | 134ns | 189ns | 130ns | 1.887µs | 1000 | - |
| `context_accumulation/50` | 3.154µs | 3.129µs | 3.16µs | 3.013µs | 7.268µs | 1000 | - |
| `context_iteration/50` | 3.268µs | 3.237µs | 3.275µs | 3.194µs | 5.541µs | 1000 | - |
| `error_chain_formatting/3` | 29ns | 26ns | 43ns | 25ns | 305ns | 1000 | - |
| `error_chain_formatting/50` | 198ns | 193ns | 194ns | 192ns | 2.114µs | 1000 | - |
| `happy_path_lazy` | 7ns | 4ns | 5ns | 2ns | 3.055µs | 1000 | - |
| `happy_path_eager` | 44ns | 42ns | 73ns | 42ns | 106ns | 1000 | - |
| `error_path_lazy` | 73ns | 58ns | 111ns | 57ns | 2.085µs | 1000 | - |
| `error_path_eager` | 74ns | 58ns | 111ns | 57ns | 2.225µs | 1000 | - |
| `with_contexts_batch/5` | 107ns | 96ns | 148ns | 92ns | 1.796µs | 1000 | - |
| `with_contexts_batch/20` | 418ns | 404ns | 415ns | 399ns | 2.309µs | 1000 | - |
| `with_contexts_batch/50` | 1.517µs | 1.499µs | 1.511µs | 1.481µs | 3.839µs | 1000 | - |
| `with_context_str_literal` | 46ns | 50ns | 55ns | 35ns | 297ns | 1000 | - |
| `with_context_owned_string` | 48ns | 39ns | 55ns | 36ns | 3.583µs | 1000 | - |
| `context_accumulator_invoke` | 107ns | 98ns | 137ns | 95ns | 1.952µs | 1000 | - |
