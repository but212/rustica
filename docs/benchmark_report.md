# Benchmark Results

> Generated on 2026-10-30 09:31:35 UTC, Commit: `45f780b`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `validated_map` | 2ns | 3ns | 3ns | 2ns | 12ns | 1000 | - |
| `result_map` | 3ns | 3ns | 4ns | 2ns | 199ns | 1000 | - |
| `sequence_valid/10` | 41ns | 36ns | 63ns | 34ns | 1.298µs | 1000 | - |
| `sequence_mixed/10` | 163ns | 161ns | 169ns | 151ns | 306ns | 1000 | - |
| `sequence_valid/100` | 150ns | 148ns | 152ns | 145ns | 1.294µs | 1000 | - |
| `sequence_mixed/100` | 1.337µs | 1.319µs | 1.347µs | 1.289µs | 3.637µs | 1000 | - |
| `iter_errors_slice/10` | 4ns | 4ns | 6ns | 3ns | 17ns | 1000 | - |
| `collect_all_valid/10` | 34ns | 34ns | 38ns | 31ns | 76ns | 1000 | - |
| `collect_early_error/10` | 29ns | 27ns | 38ns | 25ns | 696ns | 1000 | - |
| `collect_late_error/10` | 41ns | 36ns | 67ns | 32ns | 237ns | 1000 | - |
| `collect_all_valid/100` | 152ns | 144ns | 265ns | 140ns | 1.312µs | 1000 | - |
| `collect_early_error/100` | 116ns | 109ns | 194ns | 104ns | 1.176µs | 1000 | - |
| `collect_late_error/100` | 151ns | 145ns | 245ns | 141ns | 319ns | 1000 | - |
| `collect_early_error_1000_large_payload` | 9.306µs | 9.155µs | 10.678µs | 8.89µs | 12.441µs | 1000 | - |
| `zip3_all_valid` | 8ns | 9ns | 9ns | 8ns | 176ns | 1000 | - |
| `zip3_all_invalid` | 68ns | 64ns | 80ns | 55ns | 1.684µs | 1000 | - |
| `combine_asymmetric_small_into_large` | 81ns | 77ns | 116ns | 70ns | 1.491µs | 1000 | - |
| `combine_asymmetric_large_into_small` | 84ns | 79ns | 118ns | 74ns | 1.815µs | 1000 | - |
| `invalid_single` | 10ns | 11ns | 12ns | 6ns | 171ns | 1000 | - |
| `invalid_many_from_exact_iter_10` | 15ns | 15ns | 17ns | 12ns | 26ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 2ns | 3ns | 3ns | 2ns | 142ns | 1000 | - |
| `view_borrow` | 3ns | 3ns | 4ns | 2ns | 7ns | 1000 | - |
| `to_value_owned` | 16ns | 17ns | 18ns | 15ns | 22ns | 1000 | - |
| `set_same_value` | 27ns | 27ns | 30ns | 24ns | 39ns | 1000 | - |
| `set_always_same_value` | 27ns | 26ns | 28ns | 23ns | 1.066µs | 1000 | - |
| `set_different_value` | 27ns | 27ns | 29ns | 23ns | 37ns | 1000 | - |
| `modify_unchanged_value` | 35ns | 35ns | 38ns | 31ns | 915ns | 1000 | - |
| `modify_always_unchanged_value` | 31ns | 31ns | 37ns | 26ns | 217ns | 1000 | - |
| `modify_changed_value` | 41ns | 36ns | 55ns | 34ns | 197ns | 1000 | - |
| `composed_3level_view` | 3ns | 3ns | 4ns | 2ns | 19ns | 1000 | - |
| `composed_3level_set_same_value` | 39ns | 35ns | 50ns | 34ns | 1.105µs | 1000 | - |
| `composed_3level_set_different_value` | 57ns | 54ns | 66ns | 50ns | 1.185µs | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 8ns | 1000 | - |
| `preview_hit` | 3ns | 3ns | 4ns | 3ns | 7ns | 1000 | - |
| `preview_miss` | 3ns | 3ns | 4ns | 2ns | 5ns | 1000 | - |
| `to_value_hit` | 18ns | 18ns | 20ns | 16ns | 23ns | 1000 | - |
| `set_same_value` | 34ns | 33ns | 37ns | 28ns | 1.178µs | 1000 | - |
| `set_always_same_value` | 27ns | 27ns | 30ns | 23ns | 39ns | 1000 | - |
| `set_hit` | 28ns | 27ns | 32ns | 24ns | 1.213µs | 1000 | - |
| `set_miss` | 12ns | 12ns | 13ns | 10ns | 176ns | 1000 | - |
| `modify_same_value` | 35ns | 34ns | 41ns | 30ns | 53ns | 1000 | - |
| `modify_always_same_value` | 38ns | 36ns | 44ns | 33ns | 1.343µs | 1000 | - |
| `modify_hit` | 44ns | 41ns | 58ns | 36ns | 245ns | 1000 | - |
| `composed_3level_preview_hit` | 3ns | 3ns | 4ns | 2ns | 186ns | 1000 | - |
| `composed_3level_set_same_value` | 32ns | 31ns | 36ns | 27ns | 1.132µs | 1000 | - |
| `composed_3level_set_hit` | 26ns | 26ns | 31ns | 23ns | 199ns | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 909ns | 889ns | 901ns | 876ns | 4.949µs | 1000 | - |
| `build_and_run/10` | 1.469µs | 1.455µs | 1.478µs | 1.422µs | 2.841µs | 1000 | - |
| `build_chain/100` | 14.245µs | 14.091µs | 14.98µs | 13.861µs | 20.606µs | 1000 | - |
| `build_and_run/100` | 20.297µs | 20.117µs | 21.019µs | 19.793µs | 28.153µs | 1000 | - |
| `build_then/10` | 910ns | 889ns | 945ns | 877ns | 2.067µs | 1000 | 10.99 M elem/s |
| `build_bind/10` | 502ns | 487ns | 497ns | 477ns | 2.465µs | 1000 | 19.92 M elem/s |
| `build_then/100` | 14.205µs | 14.002µs | 14.888µs | 13.787µs | 29.794µs | 1000 | 7.04 M elem/s |
| `build_bind/100` | 9.503µs | 9.407µs | 10.113µs | 9.264µs | 14.53µs | 1000 | 10.52 M elem/s |
| `build_then/1000` | 145.351µs | 144.291µs | 152.299µs | 141.593µs | 159.839µs | 100 | 6.88 M elem/s |
| `build_bind/1000` | 96.347µs | 95.683µs | 102.223µs | 94.592µs | 102.684µs | 100 | 10.38 M elem/s |
| `build_then/5000` | 744.06µs | 742.944µs | 762.072µs | 719.719µs | 821.862µs | 100 | 6.72 M elem/s |
| `build_bind/5000` | 483.413µs | 481.842µs | 489.714µs | 473.29µs | 573.059µs | 100 | 10.34 M elem/s |
| `run_then/10` | 546ns | 534ns | 590ns | 518ns | 1.93µs | 1000 | 18.32 M elem/s |
| `run_bind/10` | 799ns | 785ns | 814ns | 761ns | 2.309µs | 1000 | 12.52 M elem/s |
| `run_then/100` | 5.704µs | 5.656µs | 6.29µs | 5.578µs | 7.265µs | 1000 | 17.53 M elem/s |
| `run_bind/100` | 8.365µs | 8.284µs | 8.966µs | 8.13µs | 11.427µs | 1000 | 11.95 M elem/s |
| `run_then/1000` | 61.116µs | 60.355µs | 66.64µs | 59.839µs | 74.051µs | 100 | 16.36 M elem/s |
| `run_bind/1000` | 82.546µs | 81.817µs | 88.603µs | 80.942µs | 103.876µs | 100 | 12.11 M elem/s |
| `run_then/5000` | 472.301µs | 471.236µs | 483.775µs | 462.233µs | 505.538µs | 100 | 10.59 M elem/s |
| `run_bind/5000` | 579.05µs | 576.75µs | 591.627µs | 564.586µs | 704.346µs | 100 | 8.63 M elem/s |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.215µs | 1.204µs | 1.223µs | 1.176µs | 2.512µs | 1000 | - |
| `build_only/10` | 967ns | 958ns | 973ns | 936ns | 2.391µs | 1000 | - |
| `build_and_run/10` | 1.337µs | 1.325µs | 1.345µs | 1.291µs | 2.973µs | 1000 | - |
| `run_chain/10` | 490ns | 482ns | 506ns | 461ns | 1.879µs | 1000 | - |
| `drop_chain/10` | 374ns | 370ns | 377ns | 359ns | 1.121µs | 1000 | - |
| `mixed_build_only/10` | 1.978µs | 1.961µs | 1.991µs | 1.925µs | 3.963µs | 1000 | - |
| `mixed_run_chain/10` | 1.158µs | 1.15µs | 1.177µs | 1.106µs | 2.846µs | 1000 | - |
| `mixed_drop_chain/10` | 1.177µs | 1.169µs | 1.193µs | 1.128µs | 2.493µs | 1000 | - |
| `build_chain/100` | 15.246µs | 15.076µs | 15.944µs | 14.857µs | 20.266µs | 1000 | - |
| `build_only/100` | 11.858µs | 11.755µs | 12.504µs | 11.507µs | 14.586µs | 1000 | - |
| `build_and_run/100` | 15.438µs | 15.306µs | 16.079µs | 15.133µs | 20.082µs | 1000 | - |
| `run_chain/100` | 4.4µs | 4.355µs | 4.628µs | 4.317µs | 6.336µs | 1000 | - |
| `drop_chain/100` | 4.094µs | 3.691µs | 6.574µs | 3.642µs | 7.868µs | 1000 | - |
| `mixed_build_only/100` | 24.304µs | 22.846µs | 29.168µs | 22.662µs | 30.881µs | 1000 | - |
| `mixed_run_chain/100` | 10.749µs | 10.551µs | 11.326µs | 10.447µs | 18.72µs | 1000 | - |
| `mixed_drop_chain/100` | 11.745µs | 11.614µs | 12.436µs | 11.411µs | 18.386µs | 1000 | - |
| `build_chain/1000` | 151.017µs | 150.049µs | 158.417µs | 145.789µs | 161.452µs | 100 | - |
| `build_only/1000` | 116.452µs | 115.653µs | 122.884µs | 112.449µs | 135.493µs | 100 | - |
| `build_and_run/1000` | 152.436µs | 151.116µs | 159.239µs | 149.894µs | 164.016µs | 100 | - |
| `run_chain/1000` | 42.692µs | 42.053µs | 48.362µs | 41.642µs | 55.663µs | 100 | - |
| `drop_chain/1000` | 35.721µs | 35.388µs | 36.475µs | 35.162µs | 42.063µs | 100 | - |
| `mixed_build_only/1000` | 228.517µs | 226.884µs | 235.272µs | 225.528µs | 244.365µs | 100 | - |
| `mixed_run_chain/1000` | 104.506µs | 104.271µs | 106.499µs | 103.575µs | 108.683µs | 100 | - |
| `mixed_drop_chain/1000` | 115.634µs | 113.965µs | 123.505µs | 113.21µs | 156.064µs | 100 | - |
| `build_chain/5000` | 999.758µs | 999.521µs | 1.022301ms | 978.585µs | 1.065896ms | 100 | - |
| `build_only/5000` | 673.759µs | 670.804µs | 698.906µs | 650.985µs | 710.324µs | 100 | - |
| `build_and_run/5000` | 1.0364ms | 1.034649ms | 1.051785ms | 1.022931ms | 1.084944ms | 100 | - |
| `run_chain/5000` | 375.388µs | 375.006µs | 385.738µs | 365.076µs | 396.454µs | 100 | - |
| `drop_chain/5000` | 350.827µs | 348.982µs | 368.422µs | 330.895µs | 461.12µs | 100 | - |
| `mixed_build_only/5000` | 1.151471ms | 1.146396ms | 1.177383ms | 1.136582ms | 1.224012ms | 100 | - |
| `mixed_run_chain/5000` | 715.323µs | 711.235µs | 749.953µs | 691.215µs | 767.129µs | 100 | - |
| `mixed_drop_chain/5000` | 780.978µs | 769.141µs | 862.271µs | 748.801µs | 931.505µs | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 3ns | 3ns | 3ns | 2ns | 182ns | 1000 | - |
| `try_each_alt_hit` | 9ns | 10ns | 11ns | 6ns | 24ns | 1000 | - |
| `try_each_all_fail` | 3ns | 4ns | 4ns | 3ns | 7ns | 1000 | - |
| `filter_keep_all` | 23ns | 22ns | 26ns | 19ns | 1.091µs | 1000 | - |
| `filter_keep_some` | 20ns | 20ns | 26ns | 19ns | 69ns | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 1.53µs | 1.518µs | 1.555µs | 1.472µs | 2.877µs | 1000 | - |
| `program_build_and_run/10` | 1.331µs | 1.308µs | 1.379µs | 1.276µs | 7.747µs | 1000 | - |
| `dsl_loop/10` | 18ns | 16ns | 28ns | 15ns | 179ns | 1000 | - |
| `free_build_and_run/100` | 20.846µs | 20.683µs | 21.617µs | 20.349µs | 27.134µs | 1000 | - |
| `program_build_and_run/100` | 15.391µs | 15.264µs | 16.053µs | 15.104µs | 18.687µs | 1000 | - |
| `dsl_loop/100` | 86ns | 82ns | 125ns | 82ns | 379ns | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 86ns | 73ns | 135ns | 72ns | 1.32µs | 1000 | - |
| `context_iteration/2` | 89ns | 79ns | 135ns | 74ns | 1.279µs | 1000 | - |
| `context_accumulation/3` | 119ns | 110ns | 187ns | 106ns | 1.506µs | 1000 | - |
| `context_iteration/3` | 123ns | 111ns | 189ns | 108ns | 1.627µs | 1000 | - |
| `context_accumulation/50` | 2.39µs | 2.366µs | 2.389µs | 2.331µs | 4.108µs | 1000 | - |
| `context_iteration/50` | 2.473µs | 2.451µs | 2.49µs | 2.418µs | 4.061µs | 1000 | - |
| `error_chain_formatting/3` | 27ns | 28ns | 32ns | 20ns | 411ns | 1000 | - |
| `error_chain_formatting/50` | 197ns | 189ns | 261ns | 189ns | 1.555µs | 1000 | - |
| `happy_path_lazy` | 3ns | 3ns | 4ns | 2ns | 142ns | 1000 | - |
| `happy_path_eager` | 45ns | 36ns | 62ns | 35ns | 76ns | 1000 | - |
| `error_path_lazy` | 51ns | 49ns | 56ns | 48ns | 1.18µs | 1000 | - |
| `error_path_eager` | 52ns | 50ns | 54ns | 48ns | 244ns | 1000 | - |
| `with_contexts_batch/5` | 86ns | 85ns | 89ns | 79ns | 1.148µs | 1000 | - |
| `with_contexts_batch/20` | 349ns | 346ns | 352ns | 338ns | 1.785µs | 1000 | - |
| `with_contexts_batch/50` | 1.175µs | 1.165µs | 1.18µs | 1.138µs | 2.513µs | 1000 | - |
| `with_context_str_literal` | 35ns | 35ns | 39ns | 32ns | 213ns | 1000 | - |
| `with_context_owned_string` | 37ns | 36ns | 40ns | 31ns | 1.101µs | 1000 | - |
| `context_accumulator_invoke` | 92ns | 91ns | 94ns | 82ns | 1.114µs | 1000 | - |
