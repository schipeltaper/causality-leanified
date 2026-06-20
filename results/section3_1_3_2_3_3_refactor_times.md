# Sections 3.1, 3.2, 3.3 — time needed to solve, per refactor iteration

Cell = `time_needed_to_solve` formatted as Xh Ym Zs for that row in that iteration. Blank = the row was not (re-)solved in that iteration. Iteration 0 is the initial solve; later columns are refactors in chronological order. See `extract_section3_refactor_times.py` for exactly how each number is sourced.

| ref | section | iter 0<br>initial | iter 1<br>total_order_helper<br>2026-06-07 | iter 2<br>marginalize_loose_self_cycle<br>2026-06-13 | iter 3<br>blockable_noncollider_first<br>2026-06-15 | iter 4<br>sigma_separation_J_empty_premise<br>2026-06-15 | iter 5<br>cdmg_typed_edges<br>2026-06-17 | **row total** |
|---|---|---|---|---|---|---|---|---|
| def_3_1 | 3.1 | 34m 12s |  |  |  |  | 48m 0s | **1h 22m 12s** |
| def_3_2 | 3.1 | 45m 5s |  |  |  |  | 59m 20s | **1h 44m 25s** |
| def_3_3 | 3.1 | 48m 53s |  |  |  |  | 50m 23s | **1h 39m 16s** |
| claim_3_1 | 3.1 | 58m 6s |  |  |  |  | 41m 34s | **1h 39m 40s** |
| def_3_4 | 3.1 | 2h 42m 36s |  |  |  |  | 2h 59m 45s | **5h 42m 21s** |
| def_3_5 | 3.1 | 1h 23m 55s |  |  |  |  | 43m 38s | **2h 7m 33s** |
| def_3_6 | 3.1 | 39m 7s |  |  |  |  | 38m 43s | **1h 17m 50s** |
| def_3_7 | 3.1 | 31m 7s |  |  |  |  | 27m 11s | **58m 18s** |
| def_3_8 | 3.1 | 38m 15s | 42m 41s |  |  |  | 30m 51s | **1h 51m 47s** |
| claim_3_2 | 3.1 | 1h 6m 41s | 48m 47s |  |  |  | 57m 15s | **2h 52m 43s** |
| def_3_9 | 3.1 | 36m 30s | 39m 15s |  |  |  | 34m 52s | **1h 50m 37s** |
| def_3_10 | 3.2 | 1h 19m 13s |  |  |  |  | 1h 6m 23s | **2h 25m 36s** |
| claim_3_3 | 3.2 | 1h 5m 56s |  |  |  |  | 49m 33s | **1h 55m 29s** |
| claim_3_4 | 3.2 | 1h 10m 24s |  |  |  |  | 46m 57s | **1h 57m 21s** |
| claim_3_5 | 3.2 | 5h 22m 59s |  |  |  |  | 2h 26m 59s | **7h 49m 58s** |
| def_3_11 | 3.2 | 1h 29m 22s |  |  |  |  | 1h 8m 37s | **2h 37m 59s** |
| claim_3_6 | 3.2 | 1h 54m 25s |  |  |  |  | 1h 28m 36s | **3h 23m 1s** |
| claim_3_7 | 3.2 | 2h 31m 41s |  |  |  |  | 54m 53s | **3h 26m 34s** |
| claim_3_8 | 3.2 | 1h 27m 11s |  |  |  |  | 40m 18s | **2h 7m 29s** |
| def_3_12 | 3.2 | 1h 30m 14s |  |  |  |  | 55m 47s | **2h 26m 1s** |
| claim_3_9 | 3.2 | 1h 8m 55s |  |  |  |  | 52m 47s | **2h 1m 42s** |
| claim_3_10 | 3.2 | 1h 34m 46s |  |  |  |  | 32m 8s | **2h 6m 54s** |
| claim_3_11 | 3.2 | 1h 21m 28s |  |  |  |  | 47m 8s | **2h 8m 36s** |
| claim_3_12 | 3.2 | 14m 44s |  |  |  |  |  | **14m 44s** |
| def_3_13 | 3.2 | 1h 18m 8s |  |  |  |  | 58m 26s | **2h 16m 34s** |
| claim_3_13 | 3.2 | 1h 28m 25s |  |  |  |  | 1h 19m 23s | **2h 47m 48s** |
| claim_3_14 | 3.2 | 2h 27m 48s |  |  |  |  | 45m 0s | **3h 12m 48s** |
| claim_3_15 | 3.2 | 1h 48m 59s |  |  |  |  | 1h 9m 46s | **2h 58m 45s** |
| def_3_14 | 3.2 | 1h 45m 43s |  | 2h 27m 40s |  |  | 1h 5m 51s | **5h 19m 14s** |
| claim_3_16 | 3.2 | 9h 15m 7s |  | 2h 31m 39s |  |  | 4h 36m 27s | **16h 23m 13s** |
| claim_3_17 | 3.2 | 7h 36m 44s |  |  |  |  | 1h 57m 41s | **9h 34m 25s** |
| claim_3_18 | 3.2 | 11h 36m 18s |  |  |  |  | 10h 20m 33s | **21h 56m 51s** |
| claim_3_19 | 3.2 | 1h 51m 30s |  |  |  |  | 1h 30m 44s | **3h 22m 14s** |
| def_3_15 | 3.3 | 1h 22m 34s |  |  |  |  | 2h 27m 4s | **3h 49m 38s** |
| def_3_16 | 3.3 | 1h 37m 9s |  |  | 1h 48m 52s |  | 1h 26m 55s | **4h 52m 56s** |
| claim_3_20 | 3.3 | 1h 18m 50s |  |  | 1h 3m 11s |  | 51m 35s | **3h 13m 36s** |
| def_3_17 | 3.3 | 47m 14s |  |  | 23m 48s |  | 53m 34s | **2h 4m 36s** |
| claim_3_21 | 3.3 | 0s |  |  |  |  |  | **0s** |
| def_3_18 | 3.3 | 1h 7m 23s |  |  | 16m 51s | 57m 16s | 41m 49s | **3h 3m 19s** |
| claim_3_22 | 3.3 | 2h 22m 45s |  |  |  |  |  | **2h 22m 45s** |
| claim_3_27 | 3.3 | 5h 1m 2s |  |  |  |  |  | **5h 1m 2s** |
| claim_3_23 | 3.3 | 5m 36s |  |  |  |  |  | **5m 36s** |
| claim_3_24 | 3.3 | 0s |  |  |  |  |  | **0s** |
| claim_3_25 | 3.3 | 0s |  |  |  |  |  | **0s** |
| claim_3_26 | 3.3 | 0s |  |  |  |  |  | **0s** |
| **TOTAL** |  | **85h 47m 0s** | **2h 10m 43s** | **4h 59m 19s** | **3h 32m 42s** | **57m 16s** | **52h 46m 26s** | **150h 13m 26s** |

## Refactor iterations (chronological)

| iter | refactor | created_at | folder |
|---|---|---|---|
| 0 | (initial solve) | — | — |
| 1 | total_order_helper | 2026-06-07T12:34:26+00:00 | Refactor_total_order_helper_DONE_2026-06-07 |
| 2 | marginalize_loose_self_cycle | 2026-06-13T09:29:57+00:00 | Refactor_marginalize_loose_self_cycle_DONE_2026-06-13 |
| 3 | blockable_noncollider_first | 2026-06-15T16:10:52+00:00 | Refactor_blockable_noncollider_first_DONE_2026-06-15 |
| 4 | sigma_separation_J_empty_premise | 2026-06-15T21:29:20+00:00 | Refactor_sigma_separation_J_empty_premise_DONE_2026-06-15 |
| 5 | cdmg_typed_edges | 2026-06-17T02:07:35+00:00 | Refactor_cdmg_typed_edges_BUILDFAIL_2026-06-19 |
