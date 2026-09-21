# Benchmark Results

> Generated on 2026-09-21 13:09:09 UTC, Commit: `b5062f0`

## Validated

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `invalid_many/4` | 44ns | 44ns | 48ns | 42ns | 73ns | 100 | - |
| `combine_errors/4` | 107ns | 100ns | 132ns | 96ns | 150ns | 100 | - |
| `invalid_many/5` | 78ns | 68ns | 110ns | 67ns | 144ns | 100 | - |
| `combine_errors/5` | 131ns | 125ns | 182ns | 122ns | 239ns | 100 | - |
| `validated_map` | 3ns | 3ns | 4ns | 3ns | 19ns | 100 | - |
| `result_map` | 3ns | 3ns | 4ns | 3ns | 6ns | 100 | - |
| `sequence_valid/10` | 69ns | 70ns | 73ns | 57ns | 89ns | 100 | - |
| `sequence_mixed/10` | 335ns | 302ns | 404ns | 293ns | 447ns | 100 | - |
| `sequence_valid/100` | 207ns | 229ns | 246ns | 121ns | 1.235µs | 100 | - |
| `sequence_mixed/100` | 2.738µs | 2.72µs | 2.761µs | 2.699µs | 3.863µs | 100 | - |
| `iter_errors_slice/10` | 4ns | 4ns | 4ns | 3ns | 21ns | 100 | - |

## Lens

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `set_same_value` | 59ns | 59ns | 77ns | 39ns | 239ns | 100 | - |
| `set_always_same_value` | 37ns | 37ns | 44ns | 31ns | 55ns | 100 | - |
| `set_different_value` | 66ns | 67ns | 72ns | 53ns | 80ns | 100 | - |
| `modify_changed_value` | 137ns | 111ns | 122ns | 92ns | 2.699µs | 100 | - |

## ContextError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `context_accumulation/2` | 162ns | 162ns | 169ns | 142ns | 195ns | 100 | - |
| `context_iteration/2` | 148ns | 149ns | 172ns | 84ns | 181ns | 100 | - |
| `context_accumulation/3` | 122ns | 122ns | 126ns | 119ns | 135ns | 100 | - |
| `context_iteration/3` | 121ns | 121ns | 124ns | 117ns | 127ns | 100 | - |
| `context_accumulation/50` | 3.087µs | 2.71µs | 4.77µs | 2.673µs | 7.876µs | 100 | - |
| `context_iteration/50` | 2.79µs | 2.734µs | 3.428µs | 2.7µs | 3.743µs | 100 | - |
| `error_chain_formatting/3` | 220ns | 211ns | 340ns | 202ns | 386ns | 100 | - |
| `error_chain_formatting/50` | 3.168µs | 3.138µs | 3.2µs | 3.095µs | 3.945µs | 100 | - |

## LazyError

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `happy_path_lazy` | 2ns | 3ns | 3ns | 2ns | 5ns | 100 | - |
| `happy_path_eager` | 65ns | 64ns | 78ns | 40ns | 281ns | 100 | - |
| `error_path_lazy` | 68ns | 60ns | 102ns | 57ns | 119ns | 100 | - |
| `error_path_eager` | 79ns | 60ns | 106ns | 56ns | 822ns | 100 | - |

## PersistentVector

| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `creation` | 3ns | 3ns | 4ns | 3ns | 15ns | 100 | - |
| `pvec_push_back/32` | 1.698µs | 1.683µs | 1.696µs | 1.665µs | 3.027µs | 100 | 18.85 M elem/s |
| `pvec_push_back/33` | 1.98µs | 1.968µs | 2.007µs | 1.926µs | 3.103µs | 100 | 16.67 M elem/s |
| `pvec_push_back/64` | 4.523µs | 4.486µs | 4.716µs | 4.418µs | 5.328µs | 100 | 14.15 M elem/s |
| `pvec_push_back/65` | 4.695µs | 4.67µs | 4.706µs | 4.576µs | 5.575µs | 100 | 13.84 M elem/s |
| `pvec_push_back/10000` | 953.293µs | 949.802µs | 1.025893ms | 878.93µs | 1.09087ms | 100 | 10.49 M elem/s |
| `pvec_push_back/100000` | 10.142211ms | 10.191955ms | 10.509983ms | 9.725887ms | 10.509983ms | 10 | 9.86 M elem/s |
| `pvec_push_back/1000000` | 104.294851ms | 103.035951ms | 114.020672ms | 100.700186ms | 114.020672ms | 10 | 9.59 M elem/s |
| `pvec_push_back_mut/32` | 92ns | 93ns | 94ns | 89ns | 109ns | 100 | 347.83 M elem/s |
| `pvec_push_back_mut/33` | 372ns | 386ns | 404ns | 310ns | 433ns | 100 | 88.71 M elem/s |
| `pvec_push_back_mut/10000` | 206.16µs | 206.009µs | 211.54µs | 200.389µs | 229.927µs | 100 | 48.51 M elem/s |
| `pvec_extend/10000` | 195.67µs | 194.391µs | 202.6µs | 189.664µs | 203.286µs | 100 | 51.11 M elem/s |
| `pvec_collect/10000` | 30.601µs | 29.712µs | 31.527µs | 29.098µs | 53.951µs | 100 | 326.79 M elem/s |
| `std_vec_collect/10000` | 1.599µs | 1.543µs | 1.782µs | 1.54µs | 2.631µs | 100 | 6253.91 M elem/s |
| `pvec_iter_forward/1000` | 3.875µs | 3.88µs | 3.899µs | 3.847µs | 3.923µs | 50 | 258.06 M elem/s |
| `pvec_iter_reverse/1000` | 3.87µs | 3.795µs | 4.03µs | 3.787µs | 5.802µs | 50 | 258.40 M elem/s |
| `pvec_indexed_access/1000` | 14.074µs | 14.017µs | 15.304µs | 13.816µs | 15.835µs | 50 | 71.05 M elem/s |
| `pvec_iter_forward/100000` | 383.348µs | 380.34µs | 417.978µs | 356.529µs | 439.277µs | 50 | 260.86 M elem/s |
| `pvec_iter_reverse/100000` | 419.037µs | 419.727µs | 503.895µs | 357.258µs | 511.338µs | 50 | 238.64 M elem/s |
| `pvec_indexed_access/100000` | 2.933378ms | 2.826622ms | 3.563638ms | 2.685066ms | 4.26016ms | 50 | 34.09 M elem/s |
| `pvec_iter_forward/1000000` | 5.883765ms | 5.986196ms | 7.70626ms | 4.574337ms | 7.70626ms | 10 | 169.96 M elem/s |
| `pvec_iter_reverse/1000000` | 4.948492ms | 4.812009ms | 6.036701ms | 4.027939ms | 6.036701ms | 10 | 202.08 M elem/s |
| `pvec_indexed_access/1000000` | 44.511621ms | 41.847163ms | 52.132485ms | 39.069219ms | 52.132485ms | 10 | 22.47 M elem/s |
| `pvec_random_access/1000` | 13.841µs | 13.56µs | 15.43µs | 13.556µs | 20.452µs | 50 | 72.25 M elem/s |
| `pvec_random_access/100000` | 583.328µs | 537.669µs | 821.018µs | 482.926µs | 911.716µs | 50 | 17.14 M elem/s |
| `pvec_random_access/1000000` | 1.039087ms | 1.01414ms | 1.323919ms | 927.171µs | 1.323919ms | 15 | 9.62 M elem/s |
| `pvec_memory/1000` | 2.8µs | 2.804µs | 2.874µs | 2.744µs | 2.874µs | 10 | 18.12 KB memory |
| `pvec_memory/100000` | 292.537µs | 288.16µs | 313.453µs | 286.483µs | 313.453µs | 10 | 1.72 MB memory |
| `pvec_memory/1000000` | 3.61696ms | 3.650691ms | 4.097983ms | 3.282246ms | 4.097983ms | 10 | 17.23 MB memory |
| `pvec_update/1000` | 3.344µs | 3.33µs | 3.745µs | 3.174µs | 3.745µs | 10 | - |
| `pvec_update_mut/1000` | 893ns | 786ns | 1.562µs | 731ns | 1.562µs | 10 | - |
| `pvec_update/10000` | 4.398µs | 4.386µs | 4.557µs | 4.266µs | 4.557µs | 10 | - |
| `pvec_update_mut/10000` | 3.144µs | 3.135µs | 3.245µs | 3.085µs | 3.245µs | 10 | - |
| `pop_back` | 40.941µs | 39.178µs | 54.711µs | 38.818µs | 54.711µs | 10 | - |
| `pvec_sharing` | 11.684µs | 11.662µs | 13.119µs | 10.956µs | 13.119µs | 10 | - |
| `std_vec_copying` | 2.288µs | 2.218µs | 2.714µs | 2.194µs | 2.714µs | 10 | - |
