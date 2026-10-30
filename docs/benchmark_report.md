# Benchmark Results

> Generated on 2026-10-29 16:43:21 UTC, Commit: `7f786f5`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `validated_map` | 3ns | 3ns | 4ns | 2ns | 15ns | 1000 | - |
| `result_map` | 3ns | 4ns | 4ns | 2ns | 229ns | 1000 | - |
| `sequence_valid/10` | 66ns | 49ns | 98ns | 48ns | 2.438µs | 1000 | - |
| `sequence_mixed/10` | 220ns | 209ns | 218ns | 197ns | 2.37µs | 1000 | - |
| `sequence_valid/100` | 233ns | 214ns | 428ns | 212ns | 2.306µs | 1000 | - |
| `sequence_mixed/100` | 1.752µs | 1.723µs | 1.755µs | 1.661µs | 4.348µs | 1000 | - |
| `iter_errors_slice/10` | 5ns | 5ns | 7ns | 4ns | 253ns | 1000 | - |
| `collect_all_valid/10` | 70ns | 83ns | 92ns | 45ns | 648ns | 1000 | - |
| `collect_early_error/10` | 39ns | 33ns | 52ns | 31ns | 2.231µs | 1000 | - |
| `collect_late_error/10` | 59ns | 50ns | 93ns | 48ns | 330ns | 1000 | - |
| `collect_all_valid/100` | 225ns | 210ns | 220ns | 208ns | 2.288µs | 1000 | - |
| `collect_early_error/100` | 144ns | 135ns | 246ns | 133ns | 2.41µs | 1000 | - |
| `collect_late_error/100` | 229ns | 213ns | 239ns | 209ns | 2.419µs | 1000 | - |
| `collect_early_error_1000_large_payload` | 11.047µs | 10.827µs | 12.288µs | 10.357µs | 17.652µs | 1000 | - |
| `zip3_all_valid` | 11ns | 11ns | 13ns | 10ns | 34ns | 1000 | - |
| `zip3_all_invalid` | 112ns | 109ns | 115ns | 87ns | 2.917µs | 1000 | - |
| `combine_asymmetric_small_into_large` | 99ns | 87ns | 160ns | 85ns | 2.256µs | 1000 | - |
| `combine_asymmetric_large_into_small` | 102ns | 95ns | 159ns | 86ns | 200ns | 1000 | - |
| `invalid_single` | 13ns | 14ns | 16ns | 8ns | 261ns | 1000 | - |
| `invalid_many_from_exact_iter_10` | 15ns | 18ns | 20ns | 10ns | 255ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 222ns | 1000 | - |
| `view_borrow` | 3ns | 4ns | 4ns | 2ns | 7ns | 1000 | - |
| `to_value_owned` | 24ns | 24ns | 25ns | 22ns | 29ns | 1000 | - |
| `set_same_value` | 34ns | 37ns | 41ns | 24ns | 1.878µs | 1000 | - |
| `set_always_same_value` | 32ns | 36ns | 39ns | 23ns | 282ns | 1000 | - |
| `set_different_value` | 35ns | 38ns | 42ns | 24ns | 2.008µs | 1000 | - |
| `modify_unchanged_value` | 40ns | 46ns | 51ns | 31ns | 299ns | 1000 | - |
| `modify_always_unchanged_value` | 40ns | 42ns | 48ns | 29ns | 1.949µs | 1000 | - |
| `modify_changed_value` | 54ns | 44ns | 75ns | 44ns | 314ns | 1000 | - |
| `composed_3level_view` | 3ns | 4ns | 5ns | 2ns | 200ns | 1000 | - |
| `composed_3level_set_same_value` | 46ns | 47ns | 53ns | 37ns | 1.872µs | 1000 | - |
| `composed_3level_set_different_value` | 58ns | 57ns | 69ns | 54ns | 334ns | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 18ns | 1000 | - |
| `preview_hit` | 3ns | 3ns | 4ns | 2ns | 6ns | 1000 | - |
| `preview_miss` | 3ns | 3ns | 4ns | 2ns | 19ns | 1000 | - |
| `to_value_hit` | 16ns | 15ns | 25ns | 15ns | 34ns | 1000 | - |
| `set_same_value` | 36ns | 34ns | 40ns | 32ns | 1.952µs | 1000 | - |
| `set_always_same_value` | 32ns | 29ns | 41ns | 27ns | 251ns | 1000 | - |
| `set_hit` | 32ns | 29ns | 42ns | 27ns | 255ns | 1000 | - |
| `set_miss` | 15ns | 16ns | 18ns | 11ns | 270ns | 1000 | - |
| `modify_same_value` | 40ns | 38ns | 54ns | 37ns | 268ns | 1000 | - |
| `modify_always_same_value` | 44ns | 41ns | 50ns | 37ns | 1.954µs | 1000 | - |
| `modify_hit` | 51ns | 47ns | 76ns | 44ns | 317ns | 1000 | - |
| `composed_3level_preview_hit` | 3ns | 4ns | 5ns | 2ns | 26ns | 1000 | - |
| `composed_3level_set_same_value` | 33ns | 32ns | 39ns | 30ns | 271ns | 1000 | - |
| `composed_3level_set_hit` | 29ns | 28ns | 37ns | 26ns | 261ns | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.511µs | 1.529µs | 1.573µs | 1.327µs | 3.445µs | 1000 | - |
| `build_and_run/10` | 2.694µs | 2.716µs | 2.786µs | 1.98µs | 4.817µs | 1000 | - |
| `build_chain/100` | 21.492µs | 21.322µs | 22.262µs | 20.211µs | 31.552µs | 1000 | - |
| `build_and_run/100` | 31.772µs | 31.577µs | 32.704µs | 29.506µs | 45.837µs | 1000 | - |
| `build_then/10` | 1.569µs | 1.562µs | 1.611µs | 1.317µs | 3.671µs | 1000 | 6.37 M elem/s |
| `build_bind/10` | 1.126µs | 1.112µs | 1.136µs | 992ns | 3.764µs | 1000 | 8.88 M elem/s |
| `build_then/100` | 21.392µs | 21.166µs | 22.209µs | 20.039µs | 30.728µs | 1000 | 4.67 M elem/s |
| `build_bind/100` | 17.47µs | 17.292µs | 18.221µs | 15.874µs | 21.582µs | 1000 | 5.72 M elem/s |
| `build_then/1000` | 222.881µs | 220.889µs | 232.666µs | 208.15µs | 247.745µs | 100 | 4.49 M elem/s |
| `build_bind/1000` | 179.783µs | 178.004µs | 187.521µs | 176.512µs | 196.989µs | 100 | 5.56 M elem/s |
| `build_then/5000` | 1.124575ms | 1.122325ms | 1.138785ms | 1.10366ms | 1.2473ms | 100 | 4.45 M elem/s |
| `build_bind/5000` | 899.904µs | 905.238µs | 913.854µs | 778.48µs | 927.72µs | 100 | 5.56 M elem/s |
| `run_then/10` | 882ns | 880ns | 932ns | 750ns | 2.756µs | 1000 | 11.34 M elem/s |
| `run_bind/10` | 1.463µs | 1.476µs | 1.541µs | 1.154µs | 3.357µs | 1000 | 6.84 M elem/s |
| `run_then/100` | 7.898µs | 7.811µs | 8.651µs | 7.627µs | 10.823µs | 1000 | 12.66 M elem/s |
| `run_bind/100` | 14.636µs | 14.517µs | 15.397µs | 13.857µs | 16.52µs | 1000 | 6.83 M elem/s |
| `run_then/1000` | 78.737µs | 77.871µs | 87.063µs | 76.523µs | 102.231µs | 100 | 12.70 M elem/s |
| `run_bind/1000` | 146.674µs | 145.518µs | 154.78µs | 143.359µs | 155.662µs | 100 | 6.82 M elem/s |
| `run_then/5000` | 583.701µs | 581.611µs | 603.722µs | 566.823µs | 743.515µs | 100 | 8.57 M elem/s |
| `run_bind/5000` | 926.996µs | 925.586µs | 945.573µs | 909.546µs | 978.435µs | 100 | 5.39 M elem/s |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.405µs | 1.387µs | 1.405µs | 1.363µs | 3.644µs | 1000 | - |
| `build_only/10` | 1.151µs | 1.142µs | 1.168µs | 1.083µs | 3.213µs | 1000 | - |
| `build_and_run/10` | 1.705µs | 1.687µs | 1.734µs | 1.559µs | 3.891µs | 1000 | - |
| `run_chain/10` | 799ns | 787ns | 850ns | 699ns | 1.825µs | 1000 | - |
| `drop_chain/10` | 466ns | 447ns | 458ns | 441ns | 2.806µs | 1000 | - |
| `mixed_build_only/10` | 2.355µs | 2.325µs | 2.399µs | 2.219µs | 4.312µs | 1000 | - |
| `mixed_run_chain/10` | 2.029µs | 2.011µs | 2.081µs | 1.689µs | 3.118µs | 1000 | - |
| `mixed_drop_chain/10` | 1.498µs | 1.483µs | 1.51µs | 1.44µs | 2.498µs | 1000 | - |
| `build_chain/100` | 17.95µs | 17.746µs | 18.679µs | 17.595µs | 25.887µs | 1000 | - |
| `build_only/100` | 13.741µs | 13.575µs | 14.467µs | 13.444µs | 20.219µs | 1000 | - |
| `build_and_run/100` | 20.505µs | 20.319µs | 21.252µs | 19.957µs | 24.333µs | 1000 | - |
| `run_chain/100` | 6.955µs | 6.85µs | 7.727µs | 6.653µs | 12.699µs | 1000 | - |
| `drop_chain/100` | 4.606µs | 4.55µs | 5.404µs | 4.466µs | 7.947µs | 1000 | - |
| `mixed_build_only/100` | 28.453µs | 28.183µs | 29.149µs | 27.978µs | 35.056µs | 1000 | - |
| `mixed_run_chain/100` | 21.007µs | 20.878µs | 22.022µs | 19.944µs | 25.739µs | 1000 | - |
| `mixed_drop_chain/100` | 15.185µs | 14.981µs | 16.023µs | 14.811µs | 25.188µs | 1000 | - |
| `build_chain/1000` | 176.664µs | 175.113µs | 184.857µs | 173.525µs | 191.028µs | 100 | - |
| `build_only/1000` | 136.595µs | 135.274µs | 144.962µs | 132.589µs | 155.662µs | 100 | - |
| `build_and_run/1000` | 200.317µs | 197.62µs | 208.401µs | 195.977µs | 224.601µs | 100 | - |
| `run_chain/1000` | 65.664µs | 63.895µs | 77.425µs | 61.886µs | 92.233µs | 100 | - |
| `drop_chain/1000` | 43.175µs | 43.025µs | 43.932µs | 42.18µs | 53.35µs | 100 | - |
| `mixed_build_only/1000` | 280.742µs | 278.532µs | 289.584µs | 275.557µs | 293.07µs | 100 | - |
| `mixed_run_chain/1000` | 205.629µs | 203.141µs | 216.817µs | 195.536µs | 263.735µs | 100 | - |
| `mixed_drop_chain/1000` | 149.247µs | 147.401µs | 157.616µs | 146.104µs | 168.276µs | 100 | - |
| `build_chain/5000` | 1.166757ms | 1.152156ms | 1.290882ms | 1.132896ms | 1.388054ms | 100 | - |
| `build_only/5000` | 776.547µs | 770.956µs | 801.313µs | 750.288µs | 807.765µs | 100 | - |
| `build_and_run/5000` | 1.299458ms | 1.293841ms | 1.338731ms | 1.2634ms | 1.469376ms | 100 | - |
| `run_chain/5000` | 504.246µs | 503.033µs | 525.025µs | 480.211µs | 570.77µs | 100 | - |
| `drop_chain/5000` | 396.656µs | 392.686µs | 410.45µs | 380.424µs | 612.54µs | 100 | - |
| `mixed_build_only/5000` | 1.412354ms | 1.409554ms | 1.43411ms | 1.3969ms | 1.571117ms | 100 | - |
| `mixed_run_chain/5000` | 1.235873ms | 1.23186ms | 1.261036ms | 1.215469ms | 1.27919ms | 100 | - |
| `mixed_drop_chain/5000` | 944.644µs | 940.844µs | 960.542µs | 921.298µs | 1.153394ms | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 3ns | 4ns | 4ns | 2ns | 11ns | 1000 | - |
| `try_each_alt_hit` | 10ns | 11ns | 14ns | 6ns | 286ns | 1000 | - |
| `try_each_all_fail` | 4ns | 4ns | 5ns | 2ns | 6ns | 1000 | - |
| `filter_keep_all` | 32ns | 27ns | 29ns | 22ns | 5.263µs | 1000 | - |
| `filter_keep_some` | 38ns | 40ns | 44ns | 23ns | 78ns | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 2.895µs | 2.989µs | 3.051µs | 2.164µs | 5.549µs | 1000 | - |
| `program_build_and_run/10` | 1.789µs | 1.681µs | 2.075µs | 1.606µs | 4.057µs | 1000 | - |
| `dsl_loop/10` | 34ns | 35ns | 36ns | 33ns | 51ns | 1000 | - |
| `free_build_and_run/100` | 37.229µs | 36.266µs | 45.18µs | 33.458µs | 49.384µs | 1000 | - |
| `program_build_and_run/100` | 19.797µs | 19.741µs | 20.87µs | 18.849µs | 49.462µs | 1000 | - |
| `dsl_loop/100` | 118ns | 109ns | 174ns | 108ns | 1.859µs | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 114ns | 96ns | 179ns | 94ns | 2.043µs | 1000 | - |
| `context_iteration/2` | 109ns | 98ns | 179ns | 97ns | 2.438µs | 1000 | - |
| `context_accumulation/3` | 167ns | 137ns | 257ns | 136ns | 2.205µs | 1000 | - |
| `context_iteration/3` | 171ns | 142ns | 262ns | 138ns | 2.37µs | 1000 | - |
| `context_accumulation/50` | 3.157µs | 3.113µs | 3.208µs | 3.053µs | 6.148µs | 1000 | - |
| `context_iteration/50` | 3.24µs | 3.201µs | 3.25µs | 3.168µs | 6.329µs | 1000 | - |
| `error_chain_formatting/3` | 43ns | 41ns | 44ns | 35ns | 1.959µs | 1000 | - |
| `error_chain_formatting/50` | 219ns | 196ns | 321ns | 195ns | 2.21µs | 1000 | - |
| `happy_path_lazy` | 4ns | 4ns | 5ns | 2ns | 19ns | 1000 | - |
| `happy_path_eager` | 58ns | 45ns | 84ns | 44ns | 4.928µs | 1000 | - |
| `error_path_lazy` | 65ns | 60ns | 110ns | 59ns | 126ns | 1000 | - |
| `error_path_eager` | 83ns | 61ns | 114ns | 59ns | 367ns | 1000 | - |
| `with_contexts_batch/5` | 118ns | 98ns | 150ns | 91ns | 2.029µs | 1000 | - |
| `with_contexts_batch/20` | 426ns | 402ns | 635ns | 397ns | 2.208µs | 1000 | - |
| `with_contexts_batch/50` | 1.469µs | 1.449µs | 1.466µs | 1.437µs | 3.433µs | 1000 | - |
| `with_context_str_literal` | 55ns | 54ns | 57ns | 36ns | 1.84µs | 1000 | - |
| `with_context_owned_string` | 46ns | 51ns | 56ns | 36ns | 298ns | 1000 | - |
| `context_accumulator_invoke` | 114ns | 97ns | 138ns | 94ns | 1.738µs | 1000 | - |
