# Benchmark Results

> Generated on 2026-09-22 04:02:31 UTC, Commit: `279cca8`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 93ns | 93ns | 103ns | 77ns | 121ns | 100 | - |
| `combine_errors/4` | 252ns | 253ns | 270ns | 219ns | 277ns | 100 | - |
| `invalid_many/5` | 144ns | 144ns | 152ns | 136ns | 175ns | 100 | - |
| `combine_errors/5` | 347ns | 322ns | 340ns | 284ns | 2.81µs | 100 | - |
| `validated_map` | 3ns | 4ns | 4ns | 2ns | 10ns | 100 | - |
| `result_map` | 4ns | 4ns | 5ns | 2ns | 7ns | 100 | - |
| `sequence_valid/10` | 87ns | 89ns | 95ns | 70ns | 98ns | 100 | - |
| `sequence_mixed/10` | 539ns | 508ns | 524ns | 459ns | 3.588µs | 100 | - |
| `sequence_valid/100` | 285ns | 281ns | 294ns | 226ns | 951ns | 100 | - |
| `sequence_mixed/100` | 4.01µs | 4.374µs | 4.585µs | 3.056µs | 7.926µs | 100 | - |
| `iter_errors_slice/10` | 6ns | 7ns | 8ns | 5ns | 12ns | 100 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 83ns | 83ns | 97ns | 47ns | 117ns | 100 | - |
| `set_always_same_value` | 53ns | 53ns | 55ns | 48ns | 60ns | 100 | - |
| `set_different_value` | 108ns | 82ns | 85ns | 80ns | 2.644µs | 100 | - |
| `modify_changed_value` | 132ns | 133ns | 135ns | 125ns | 138ns | 100 | - |

## Prism

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `preview_hit` | 37ns | 38ns | 39ns | 34ns | 42ns | 100 | - |
| `preview_miss` | 31ns | 5ns | 5ns | 4ns | 2.699µs | 100 | - |
| `modify_same_value` | 85ns | 65ns | 67ns | 61ns | 2.161µs | 100 | - |
| `modify_different_value` | 104ns | 103ns | 109ns | 99ns | 170ns | 100 | - |
| `set_hit` | 113ns | 84ns | 85ns | 80ns | 2.049µs | 100 | - |
| `set_miss` | 24ns | 24ns | 25ns | 23ns | 34ns | 100 | - |
| `set_if_different_same` | 84ns | 84ns | 85ns | 81ns | 93ns | 100 | - |
| `set_if_different_changed` | 83ns | 84ns | 85ns | 78ns | 91ns | 100 | - |

## Free

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 2.336µs | 2.145µs | 3.55µs | 2.094µs | 5.538µs | 100 | - |
| `build_and_run/10` | 3.772µs | 3.688µs | 4.034µs | 3.657µs | 5.931µs | 100 | - |
| `build_chain/100` | 24.445µs | 24.149µs | 26.185µs | 24.013µs | 27.051µs | 100 | - |
| `build_and_run/100` | 40.533µs | 40.211µs | 41.205µs | 39.931µs | 42.273µs | 100 | - |

## Operational

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `build_chain/10` | 749ns | 739ns | 747ns | 732ns | 1.761µs | 100 | - |
| `build_and_run/10` | 1.109µs | 1.097µs | 1.111µs | 1.088µs | 2.158µs | 100 | - |
| `build_chain/100` | 8.595µs | 8.463µs | 9.313µs | 8.427µs | 14.848µs | 100 | - |
| `build_and_run/100` | 12.192µs | 12.037µs | 12.951µs | 11.982µs | 14.119µs | 100 | - |

## Choice

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `try_each_primary_hit` | 3ns | 3ns | 4ns | 2ns | 7ns | 100 | - |
| `try_each_alt_hit` | 13ns | 11ns | 14ns | 7ns | 220ns | 100 | - |
| `try_each_all_fail` | 4ns | 4ns | 5ns | 3ns | 20ns | 100 | - |
| `filter_keep_all` | 36ns | 36ns | 46ns | 30ns | 67ns | 100 | - |
| `filter_keep_some` | 41ns | 45ns | 49ns | 24ns | 71ns | 100 | - |

## MonadComparison

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `free_build_and_run/10` | 3.723µs | 3.685µs | 3.718µs | 3.637µs | 5.816µs | 100 | - |
| `program_build_and_run/10` | 1.137µs | 1.11µs | 1.123µs | 1.105µs | 2.884µs | 100 | - |
| `native_loop/10` | 10ns | 10ns | 12ns | 7ns | 25ns | 100 | - |
| `free_build_and_run/100` | 40.629µs | 40.337µs | 41.283µs | 40.093µs | 41.761µs | 100 | - |
| `program_build_and_run/100` | 12.086µs | 11.949µs | 12.824µs | 11.826µs | 14.513µs | 100 | - |
| `native_loop/100` | 60ns | 65ns | 89ns | 34ns | 331ns | 100 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 162ns | 198ns | 205ns | 108ns | 221ns | 100 | - |
| `context_iteration/2` | 141ns | 113ns | 220ns | 112ns | 487ns | 100 | - |
| `context_accumulation/3` | 186ns | 150ns | 295ns | 150ns | 1.31µs | 100 | - |
| `context_iteration/3` | 209ns | 151ns | 294ns | 150ns | 565ns | 100 | - |
| `context_accumulation/50` | 2.929µs | 2.889µs | 2.914µs | 2.841µs | 5.213µs | 100 | - |
| `context_iteration/50` | 2.884µs | 2.861µs | 2.934µs | 2.825µs | 3.716µs | 100 | - |
| `error_chain_formatting/3` | 317ns | 255ns | 472ns | 244ns | 2.089µs | 100 | - |
| `error_chain_formatting/50` | 3.549µs | 3.49µs | 3.61µs | 3.451µs | 5.843µs | 100 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 5ns | 5ns | 5ns | 4ns | 33ns | 100 | - |
| `happy_path_eager` | 80ns | 88ns | 102ns | 46ns | 338ns | 100 | - |
| `error_path_lazy` | 125ns | 128ns | 131ns | 69ns | 156ns | 100 | - |
| `error_path_eager` | 88ns | 69ns | 143ns | 68ns | 366ns | 100 | - |

## PersistentVector

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `creation` | 4ns | 4ns | 5ns | 3ns | 18ns | 100 | - |
| `pvec_push_back/32` | 1.525µs | 1.466µs | 1.476µs | 1.434µs | 5.415µs | 100 | 20.98 M elem/s |
| `pvec_push_back/33` | 1.794µs | 1.744µs | 1.758µs | 1.733µs | 4.753µs | 100 | 18.39 M elem/s |
| `pvec_push_back/64` | 4.805µs | 4.751µs | 4.842µs | 4.69µs | 6.459µs | 100 | 13.32 M elem/s |
| `pvec_push_back/65` | 4.993µs | 4.94µs | 5.019µs | 4.894µs | 6.615µs | 100 | 13.02 M elem/s |
| `pvec_push_back/10000` | 1.088367ms | 1.087664ms | 1.093676ms | 1.085168ms | 1.102437ms | 100 | 9.19 M elem/s |
| `pvec_push_back/100000` | 11.266096ms | 11.263362ms | 11.31339ms | 11.246416ms | 11.31339ms | 10 | 8.88 M elem/s |
| `pvec_push_back/1000000` | 115.890458ms | 115.872312ms | 116.289328ms | 115.691018ms | 116.289328ms | 10 | 8.63 M elem/s |
| `pvec_push_back_mut/32` | 107ns | 107ns | 108ns | 106ns | 117ns | 100 | 299.07 M elem/s |
| `pvec_push_back_mut/33` | 347ns | 282ns | 443ns | 279ns | 2.96µs | 100 | 95.10 M elem/s |
| `pvec_push_back_mut/10000` | 224.623µs | 223.91µs | 227.266µs | 222.918µs | 238.91µs | 100 | 44.52 M elem/s |
| `pvec_extend/10000` | 205.216µs | 204.516µs | 208.403µs | 203.914µs | 224.024µs | 100 | 48.73 M elem/s |
| `pvec_collect/10000` | 36.504µs | 37.503µs | 38.457µs | 32.425µs | 40.213µs | 100 | 273.94 M elem/s |
| `std_vec_collect/10000` | 1.625µs | 1.591µs | 1.735µs | 1.586µs | 2.781µs | 100 | 6153.85 M elem/s |
| `pvec_iter_forward/1000` | 4.375µs | 4.39µs | 4.418µs | 4.097µs | 4.702µs | 50 | 228.57 M elem/s |
| `pvec_iter_reverse/1000` | 4.424µs | 4.368µs | 4.4µs | 4.103µs | 8.409µs | 50 | 226.04 M elem/s |
| `pvec_indexed_access/1000` | 15.63µs | 15.528µs | 17.148µs | 15.434µs | 17.404µs | 50 | 63.98 M elem/s |
| `pvec_iter_forward/100000` | 437.961µs | 437.79µs | 444.545µs | 433.078µs | 455.351µs | 50 | 228.33 M elem/s |
| `pvec_iter_reverse/100000` | 419.152µs | 414.847µs | 437.552µs | 404.36µs | 439.734µs | 50 | 238.58 M elem/s |
| `pvec_indexed_access/100000` | 2.87239ms | 2.869356ms | 2.898681ms | 2.856446ms | 2.912828ms | 50 | 34.81 M elem/s |
| `pvec_iter_forward/1000000` | 4.139018ms | 4.0874ms | 4.353853ms | 4.05771ms | 4.353853ms | 10 | 241.60 M elem/s |
| `pvec_iter_reverse/1000000` | 4.114136ms | 4.096943ms | 4.262973ms | 4.051608ms | 4.262973ms | 10 | 243.06 M elem/s |
| `pvec_indexed_access/1000000` | 40.395712ms | 40.372518ms | 40.639743ms | 40.300458ms | 40.639743ms | 10 | 24.76 M elem/s |
| `pvec_random_access/1000` | 20.09µs | 19.898µs | 21.822µs | 19.835µs | 22.616µs | 50 | 49.78 M elem/s |
| `pvec_random_access/100000` | 573.436µs | 561.216µs | 637.109µs | 552.405µs | 744.37µs | 50 | 17.44 M elem/s |
| `pvec_random_access/1000000` | 1.110361ms | 1.102892ms | 1.270636ms | 1.016992ms | 1.270636ms | 15 | 9.01 M elem/s |
| `pvec_memory/1000` | 5.97µs | 5.71µs | 11.432µs | 3.747µs | 11.432µs | 10 | 18.12 KB memory |
| `pvec_memory/100000` | 352.535µs | 348.822µs | 365.103µs | 346.528µs | 365.103µs | 10 | 1.72 MB memory |
| `pvec_memory/1000000` | 3.63407ms | 3.645022ms | 3.691354ms | 3.558656ms | 3.691354ms | 10 | 17.23 MB memory |
| `pvec_update/1000` | 4.264µs | 3.601µs | 8.005µs | 3.436µs | 8.005µs | 10 | - |
| `pvec_update_mut/1000` | 402ns | 446ns | 601ns | 250ns | 601ns | 10 | - |
| `pvec_update/10000` | 4.751µs | 4.724µs | 4.899µs | 4.619µs | 4.899µs | 10 | - |
| `pvec_update_mut/10000` | 397ns | 381ns | 521ns | 361ns | 521ns | 10 | - |
| `pop_back` | 40.56µs | 40.191µs | 41.699µs | 39.951µs | 43.004µs | 100 | - |
| `pvec_sharing` | 8.239µs | 8.093µs | 8.978µs | 7.929µs | 10.036µs | 100 | - |
| `std_vec_copying` | 1.964µs | 1.938µs | 1.968µs | 1.922µs | 3.226µs | 100 | - |
