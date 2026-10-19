# Benchmark Results

> Generated on 2026-10-19 07:41:21 UTC, Commit: `0681813`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `validated_map` | 3ns | 3ns | 4ns | 2ns | 12ns | 1000 | - |
| `result_map` | 3ns | 3ns | 4ns | 2ns | 268ns | 1000 | - |
| `sequence_valid/10` | 81ns | 69ns | 146ns | 61ns | 3.232µs | 1000 | - |
| `sequence_mixed/10` | 175ns | 172ns | 179ns | 168ns | 1.944µs | 1000 | - |
| `sequence_valid/100` | 222ns | 220ns | 226ns | 216ns | 1.894µs | 1000 | - |
| `sequence_mixed/100` | 1.991µs | 1.963µs | 1.999µs | 1.913µs | 4.132µs | 1000 | - |
| `iter_errors_slice/10` | 6ns | 6ns | 7ns | 4ns | 241ns | 1000 | - |
| `collect_all_valid/10` | 69ns | 65ns | 109ns | 56ns | 141ns | 1000 | - |
| `collect_early_error/10` | 49ns | 43ns | 67ns | 42ns | 1.251µs | 1000 | - |
| `collect_late_error/10` | 78ns | 69ns | 120ns | 63ns | 1.258µs | 1000 | - |
| `collect_all_valid/100` | 232ns | 220ns | 231ns | 212ns | 1.066µs | 1000 | - |
| `collect_early_error/100` | 143ns | 138ns | 226ns | 137ns | 281ns | 1000 | - |
| `collect_late_error/100` | 237ns | 227ns | 236ns | 219ns | 1.08µs | 1000 | - |
| `collect_early_error_1000_large_payload` | 10.663µs | 10.459µs | 12.351µs | 9.577µs | 19.011µs | 1000 | - |
| `zip3_all_valid` | 10ns | 10ns | 12ns | 8ns | 26ns | 1000 | - |
| `zip3_all_invalid` | 111ns | 88ns | 137ns | 84ns | 5.022µs | 1000 | - |
| `combine_asymmetric_small_into_large` | 114ns | 105ns | 188ns | 102ns | 1.484µs | 1000 | - |
| `combine_asymmetric_large_into_small` | 110ns | 99ns | 181ns | 96ns | 2.192µs | 1000 | - |
| `invalid_single` | 21ns | 23ns | 24ns | 12ns | 245ns | 1000 | - |
| `invalid_many_from_exact_iter_10` | 29ns | 29ns | 31ns | 23ns | 45ns | 1000 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 60ns | 1000 | - |
| `view_borrow` | 4ns | 4ns | 5ns | 2ns | 8ns | 1000 | - |
| `to_value_owned` | 27ns | 32ns | 34ns | 18ns | 66ns | 1000 | - |
| `set_same_value` | 30ns | 31ns | 33ns | 30ns | 46ns | 1000 | - |
| `set_always_same_value` | 54ns | 53ns | 54ns | 29ns | 4.346µs | 1000 | - |
| `set_different_value` | 37ns | 31ns | 56ns | 30ns | 268ns | 1000 | - |
| `modify_unchanged_value` | 44ns | 39ns | 68ns | 39ns | 297ns | 1000 | - |
| `modify_always_unchanged_value` | 43ns | 37ns | 63ns | 36ns | 1.183µs | 1000 | - |
| `modify_changed_value` | 66ns | 62ns | 101ns | 58ns | 309ns | 1000 | - |
| `composed_3level_view` | 3ns | 4ns | 4ns | 2ns | 19ns | 1000 | - |
| `composed_3level_set_same_value` | 59ns | 66ns | 69ns | 45ns | 1.674µs | 1000 | - |
| `composed_3level_set_different_value` | 82ns | 71ns | 99ns | 69ns | 3.716µs | 1000 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `direct_borrow_baseline` | 3ns | 3ns | 4ns | 2ns | 14ns | 1000 | - |
| `preview_hit` | 3ns | 3ns | 4ns | 2ns | 14ns | 1000 | - |
| `preview_miss` | 3ns | 3ns | 4ns | 2ns | 4ns | 1000 | - |
| `to_value_hit` | 26ns | 27ns | 28ns | 25ns | 53ns | 1000 | - |
| `set_same_value` | 34ns | 34ns | 35ns | 33ns | 45ns | 1000 | - |
| `set_always_same_value` | 42ns | 35ns | 56ns | 33ns | 4.369µs | 1000 | - |
| `set_hit` | 47ns | 55ns | 58ns | 32ns | 275ns | 1000 | - |
| `set_miss` | 26ns | 25ns | 27ns | 14ns | 2.079µs | 1000 | - |
| `modify_same_value` | 57ns | 51ns | 72ns | 49ns | 298ns | 1000 | - |
| `modify_always_same_value` | 55ns | 46ns | 67ns | 44ns | 1.679µs | 1000 | - |
| `modify_hit` | 81ns | 71ns | 108ns | 67ns | 1.959µs | 1000 | - |
| `composed_3level_preview_hit` | 4ns | 4ns | 4ns | 2ns | 203ns | 1000 | - |
| `composed_3level_set_same_value` | 51ns | 54ns | 61ns | 38ns | 2.016µs | 1000 | - |
| `composed_3level_set_hit` | 44ns | 36ns | 58ns | 32ns | 293ns | 1000 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.455µs | 1.417µs | 1.685µs | 1.367µs | 3.733µs | 1000 | - |
| `build_and_run/10` | 2.151µs | 2.13µs | 2.177µs | 2.067µs | 4.048µs | 1000 | - |
| `build_chain/100` | 16.063µs | 15.262µs | 23.337µs | 15.088µs | 27.148µs | 1000 | - |
| `build_and_run/100` | 22.759µs | 22.484µs | 23.478µs | 22.302µs | 35.946µs | 1000 | - |
| `build_then/10` | 1.427µs | 1.406µs | 1.439µs | 1.357µs | 3.562µs | 1000 | 7.01 M elem/s |
| `build_bind/10` | 1.168µs | 1.151µs | 1.168µs | 1.119µs | 2.577µs | 1000 | 8.56 M elem/s |
| `build_then/100` | 15.488µs | 15.331µs | 16.221µs | 15.179µs | 21.619µs | 1000 | 6.46 M elem/s |
| `build_bind/100` | 12.543µs | 12.422µs | 13.276µs | 12.314µs | 15.972µs | 1000 | 7.97 M elem/s |
| `build_then/1000` | 206.739µs | 205.5µs | 214.621µs | 201.317µs | 218.248µs | 100 | 4.84 M elem/s |
| `build_bind/1000` | 134.381µs | 134.291µs | 143.197µs | 128.18µs | 145.261µs | 100 | 7.44 M elem/s |
| `build_then/5000` | 1.074382ms | 1.072431ms | 1.088827ms | 1.060283ms | 1.135895ms | 100 | 4.65 M elem/s |
| `build_bind/5000` | 696.771µs | 697.855µs | 717.933µs | 652.531µs | 756.946µs | 100 | 7.18 M elem/s |
| `run_then/10` | 778ns | 759ns | 792ns | 729ns | 3.172µs | 1000 | 12.85 M elem/s |
| `run_bind/10` | 1.138µs | 1.119µs | 1.157µs | 1.079µs | 3.454µs | 1000 | 8.79 M elem/s |
| `run_then/100` | 7.082µs | 7.017µs | 7.846µs | 6.89µs | 9.528µs | 1000 | 14.12 M elem/s |
| `run_bind/100` | 10.915µs | 10.779µs | 11.668µs | 10.667µs | 14.963µs | 1000 | 9.16 M elem/s |
| `run_then/1000` | 77.836µs | 76.844µs | 85.701µs | 75.832µs | 105.177µs | 100 | 12.85 M elem/s |
| `run_bind/1000` | 116.602µs | 115.481µs | 124.353µs | 114.885µs | 128.15µs | 100 | 8.58 M elem/s |
| `run_then/5000` | 465.167µs | 464.208µs | 477.524µs | 450.854µs | 487.061µs | 100 | 10.75 M elem/s |
| `run_bind/5000` | 658.324µs | 659.122µs | 668.821µs | 640.297µs | 723.814µs | 100 | 7.60 M elem/s |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 1.173µs | 1.158µs | 1.173µs | 1.144µs | 2.461µs | 1000 | - |
| `build_only/10` | 914ns | 887ns | 1.112µs | 875ns | 2.684µs | 1000 | - |
| `build_and_run/10` | 1.454µs | 1.474µs | 1.5µs | 1.347µs | 3.8µs | 1000 | - |
| `run_chain/10` | 558ns | 543ns | 659ns | 522ns | 1.802µs | 1000 | - |
| `drop_chain/10` | 345ns | 339ns | 345ns | 332ns | 1.464µs | 1000 | - |
| `mixed_build_only/10` | 1.97µs | 1.946µs | 1.962µs | 1.921µs | 5.302µs | 1000 | - |
| `mixed_run_chain/10` | 1.132µs | 1.121µs | 1.141µs | 1.097µs | 1.979µs | 1000 | - |
| `mixed_drop_chain/10` | 884ns | 864ns | 879ns | 847ns | 2.575µs | 1000 | - |
| `build_chain/100` | 15.377µs | 15.226µs | 16.098µs | 15.115µs | 23.224µs | 1000 | - |
| `build_only/100` | 12.227µs | 12.105µs | 12.97µs | 12.001µs | 16.189µs | 1000 | - |
| `build_and_run/100` | 16.431µs | 16.267µs | 17.192µs | 16.05µs | 21.05µs | 1000 | - |
| `run_chain/100` | 6.102µs | 6.017µs | 6.875µs | 5.869µs | 10.074µs | 1000 | - |
| `drop_chain/100` | 5.429µs | 5.342µs | 6.173µs | 5.252µs | 7.886µs | 1000 | - |
| `mixed_build_only/100` | 24.995µs | 24.771µs | 25.759µs | 24.387µs | 30.332µs | 1000 | - |
| `mixed_run_chain/100` | 16.922µs | 16.744µs | 17.878µs | 16.223µs | 32.958µs | 1000 | - |
| `mixed_drop_chain/100` | 13.396µs | 13.278µs | 14.319µs | 12.893µs | 21.391µs | 1000 | - |
| `build_chain/1000` | 156.599µs | 155.752µs | 164.852µs | 131.213µs | 165.714µs | 100 | - |
| `build_only/1000` | 123.799µs | 123.059µs | 131.894µs | 98.335µs | 134.989µs | 100 | - |
| `build_and_run/1000` | 159.004µs | 157.555µs | 167.448µs | 136.953µs | 180.921µs | 100 | - |
| `run_chain/1000` | 38.083µs | 37.241µs | 41.705µs | 37.056µs | 61.719µs | 100 | - |
| `drop_chain/1000` | 28.742µs | 28.545µs | 28.811µs | 28.36µs | 37.607µs | 100 | - |
| `mixed_build_only/1000` | 237.077µs | 233.174µs | 252.749µs | 231.822µs | 307.876µs | 100 | - |
| `mixed_run_chain/1000` | 163.769µs | 160.68µs | 173.668µs | 158.912µs | 206.527µs | 100 | - |
| `mixed_drop_chain/1000` | 138.432µs | 127.526µs | 211.195µs | 126.374µs | 224.829µs | 100 | - |
| `build_chain/5000` | 1.214608ms | 1.206793ms | 1.249029ms | 1.18819ms | 1.326045ms | 100 | - |
| `build_only/5000` | 664.355µs | 648.737µs | 714.178µs | 627.304µs | 772.452µs | 100 | - |
| `build_and_run/5000` | 1.230574ms | 1.223959ms | 1.277008ms | 1.200913ms | 1.322749ms | 100 | - |
| `run_chain/5000` | 558.904µs | 556.698µs | 590.428µs | 531.725µs | 614.892µs | 100 | - |
| `drop_chain/5000` | 540.32µs | 541.224µs | 564.911µs | 511.491µs | 577.147µs | 100 | - |
| `mixed_build_only/5000` | 1.182138ms | 1.176784ms | 1.204561ms | 1.168593ms | 1.222605ms | 100 | - |
| `mixed_run_chain/5000` | 1.146649ms | 1.146633ms | 1.168514ms | 1.124342ms | 1.185575ms | 100 | - |
| `mixed_drop_chain/5000` | 977.231µs | 973.22µs | 1.005129ms | 949.235µs | 1.142486ms | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 5ns | 4ns | 5ns | 2ns | 1.92µs | 1000 | - |
| `try_each_alt_hit` | 12ns | 12ns | 14ns | 6ns | 28ns | 1000 | - |
| `try_each_all_fail` | 3ns | 4ns | 4ns | 2ns | 188ns | 1000 | - |
| `filter_keep_all` | 28ns | 26ns | 34ns | 24ns | 309ns | 1000 | - |
| `filter_keep_some` | 31ns | 27ns | 49ns | 25ns | 1.295µs | 1000 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 2.206µs | 2.167µs | 2.237µs | 2.086µs | 4.851µs | 1000 | - |
| `program_build_and_run/10` | 1.368µs | 1.326µs | 1.403µs | 1.283µs | 4.227µs | 1000 | - |
| `dsl_loop/10` | 40ns | 44ns | 48ns | 23ns | 253ns | 1000 | - |
| `free_build_and_run/100` | 23.005µs | 22.768µs | 23.706µs | 22.583µs | 29.707µs | 1000 | - |
| `program_build_and_run/100` | 15.708µs | 15.546µs | 16.421µs | 15.423µs | 20.383µs | 1000 | - |
| `dsl_loop/100` | 123ns | 115ns | 193ns | 114ns | 2.25µs | 1000 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 110ns | 102ns | 192ns | 102ns | 1.252µs | 1000 | - |
| `context_iteration/2` | 123ns | 109ns | 205ns | 105ns | 1.264µs | 1000 | - |
| `context_accumulation/3` | 164ns | 144ns | 283ns | 143ns | 1.892µs | 1000 | - |
| `context_iteration/3` | 166ns | 151ns | 285ns | 149ns | 1.315µs | 1000 | - |
| `context_accumulation/50` | 2.856µs | 2.816µs | 2.875µs | 2.791µs | 5.987µs | 1000 | - |
| `context_iteration/50` | 2.867µs | 2.811µs | 2.906µs | 2.778µs | 6.399µs | 1000 | - |
| `error_chain_formatting/3` | 44ns | 48ns | 53ns | 27ns | 277ns | 1000 | - |
| `error_chain_formatting/50` | 209ns | 196ns | 318ns | 195ns | 2.139µs | 1000 | - |
| `happy_path_lazy` | 6ns | 5ns | 7ns | 2ns | 1.769µs | 1000 | - |
| `happy_path_eager` | 64ns | 46ns | 90ns | 45ns | 318ns | 1000 | - |
| `error_path_lazy` | 83ns | 69ns | 131ns | 68ns | 1.917µs | 1000 | - |
| `error_path_eager` | 83ns | 69ns | 130ns | 68ns | 1.879µs | 1000 | - |
| `with_contexts_batch/5` | 110ns | 97ns | 177ns | 96ns | 442ns | 1000 | - |
| `with_contexts_batch/20` | 404ns | 387ns | 399ns | 370ns | 2.369µs | 1000 | - |
| `with_contexts_batch/50` | 1.884µs | 1.863µs | 1.9µs | 1.813µs | 4.405µs | 1000 | - |
| `with_context_str_literal` | 54ns | 46ns | 71ns | 40ns | 283ns | 1000 | - |
| `with_context_owned_string` | 53ns | 42ns | 71ns | 40ns | 1.867µs | 1000 | - |
| `context_accumulator_invoke` | 134ns | 122ns | 186ns | 118ns | 2.02µs | 1000 | - |
