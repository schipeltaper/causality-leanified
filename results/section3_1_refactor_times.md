# Section 3.1 — time needed to solve, per refactor iteration

Cell = `time_needed_to_solve` in seconds for that row in that iteration. Blank = the row was not (re-)solved in that iteration. See `extract_section3_1_refactor_times.py` for exactly how each number is sourced.

| ref | iter 0<br>initial | iter 1<br>total_order_helper<br>2026-06-07 | iter 2<br>marginalize_loose_self_cycle<br>2026-06-13 | iter 3<br>blockable_noncollider_first<br>2026-06-15 | iter 4<br>sigma_separation_J_empty_premise<br>2026-06-15 | iter 5<br>cdmg_typed_edges<br>2026-06-17 |
|---|---|---|---|---|---|---|
| def_3_1 | 2052 |  |  |  |  | 2880 |
| def_3_2 | 2705 |  |  |  |  | 3560 |
| def_3_3 | 2933 |  |  |  |  | 3023 |
| claim_3_1 | 3486 |  |  |  |  | 2494 |
| def_3_4 | 9756 |  |  |  |  | 10785 |
| def_3_5 | 5035 |  |  |  |  | 2618 |
| def_3_6 | 2347 |  |  |  |  | 2323 |
| def_3_7 | 1867 |  |  |  |  | 1631 |
| def_3_8 | 2295 | 2561 |  |  |  | 1851 |
| claim_3_2 | 4001 | 2927 |  |  |  | 3435 |
| def_3_9 | 2190 | 2355 |  |  |  | 2092 |

## Refactor iterations (chronological)

| iter | refactor | created_at | folder |
|---|---|---|---|
| 0 | (initial solve) | — | — |
| 1 | total_order_helper | 2026-06-07T12:34:26+00:00 | Refactor_total_order_helper_DONE_2026-06-07 |
| 2 | marginalize_loose_self_cycle | 2026-06-13T09:29:57+00:00 | Refactor_marginalize_loose_self_cycle_DONE_2026-06-13 |
| 3 | blockable_noncollider_first | 2026-06-15T16:10:52+00:00 | Refactor_blockable_noncollider_first_DONE_2026-06-15 |
| 4 | sigma_separation_J_empty_premise | 2026-06-15T21:29:20+00:00 | Refactor_sigma_separation_J_empty_premise_DONE_2026-06-15 |
| 5 | cdmg_typed_edges | 2026-06-17T02:07:35+00:00 | Refactor_cdmg_typed_edges_BUILDFAIL_2026-06-19 |
