# Sections 3.1, 3.2, 3.3 — time needed to solve, per refactor iteration

Cell = `time_needed_to_solve` in seconds for that row in that iteration. Blank = the row was not (re-)solved in that iteration. Iteration 0 is the initial solve; later columns are refactors in chronological order. See `extract_section3_refactor_times.py` for exactly how each number is sourced.

| ref | section | iter 0<br>initial | iter 1<br>total_order_helper<br>2026-06-07 | iter 2<br>marginalize_loose_self_cycle<br>2026-06-13 | iter 3<br>blockable_noncollider_first<br>2026-06-15 | iter 4<br>sigma_separation_J_empty_premise<br>2026-06-15 | iter 5<br>cdmg_typed_edges<br>2026-06-17 |
|---|---|---|---|---|---|---|---|
| def_3_1 | 3.1 | 2052 |  |  |  |  | 2880 |
| def_3_2 | 3.1 | 2705 |  |  |  |  | 3560 |
| def_3_3 | 3.1 | 2933 |  |  |  |  | 3023 |
| claim_3_1 | 3.1 | 3486 |  |  |  |  | 2494 |
| def_3_4 | 3.1 | 9756 |  |  |  |  | 10785 |
| def_3_5 | 3.1 | 5035 |  |  |  |  | 2618 |
| def_3_6 | 3.1 | 2347 |  |  |  |  | 2323 |
| def_3_7 | 3.1 | 1867 |  |  |  |  | 1631 |
| def_3_8 | 3.1 | 2295 | 2561 |  |  |  | 1851 |
| claim_3_2 | 3.1 | 4001 | 2927 |  |  |  | 3435 |
| def_3_9 | 3.1 | 2190 | 2355 |  |  |  | 2092 |
| def_3_10 | 3.2 | 4753 |  |  |  |  | 3983 |
| claim_3_3 | 3.2 | 3956 |  |  |  |  | 2973 |
| claim_3_4 | 3.2 | 4224 |  |  |  |  | 2817 |
| claim_3_5 | 3.2 | 19379 |  |  |  |  | 8819 |
| def_3_11 | 3.2 | 5362 |  |  |  |  | 4117 |
| claim_3_6 | 3.2 | 6865 |  |  |  |  | 5316 |
| claim_3_7 | 3.2 | 9101 |  |  |  |  | 3293 |
| claim_3_8 | 3.2 | 5231 |  |  |  |  | 2418 |
| def_3_12 | 3.2 | 5414 |  |  |  |  | 3347 |
| claim_3_9 | 3.2 | 4135 |  |  |  |  | 3167 |
| claim_3_10 | 3.2 | 5686 |  |  |  |  | 1928 |
| claim_3_11 | 3.2 | 4888 |  |  |  |  | 2828 |
| claim_3_12 | 3.2 | 884 |  |  |  |  |  |
| def_3_13 | 3.2 | 4688 |  |  |  |  | 3506 |
| claim_3_13 | 3.2 | 5305 |  |  |  |  | 4763 |
| claim_3_14 | 3.2 | 8868 |  |  |  |  | 2700 |
| claim_3_15 | 3.2 | 6539 |  |  |  |  | 4186 |
| def_3_14 | 3.2 | 6343 |  | 8860 |  |  | 3951 |
| claim_3_16 | 3.2 | 33307 |  | 9099 |  |  | 16587 |
| claim_3_17 | 3.2 | 27404 |  |  |  |  | 7061 |
| claim_3_18 | 3.2 | 41778 |  |  |  |  | 37233 |
| claim_3_19 | 3.2 | 6690 |  |  |  |  | 5444 |
| def_3_15 | 3.3 | 4954 |  |  |  |  | 8824 |
| def_3_16 | 3.3 | 5829 |  |  | 6532 |  | 5215 |
| claim_3_20 | 3.3 | 4730 |  |  | 3791 |  | 3095 |
| def_3_17 | 3.3 | 2834 |  |  | 1428 |  | 3214 |
| claim_3_21 | 3.3 | 0 |  |  |  |  |  |
| def_3_18 | 3.3 | 4043 |  |  | 1011 | 3436 | 2509 |
| claim_3_22 | 3.3 | 8565 |  |  |  |  |  |
| claim_3_27 | 3.3 | 18062 |  |  |  |  |  |
| claim_3_23 | 3.3 | 336 |  |  |  |  |  |
| claim_3_24 | 3.3 | 0 |  |  |  |  |  |
| claim_3_25 | 3.3 | 0 |  |  |  |  |  |
| claim_3_26 | 3.3 | 0 |  |  |  |  |  |

## Refactor iterations (chronological)

| iter | refactor | created_at | folder |
|---|---|---|---|
| 0 | (initial solve) | — | — |
| 1 | total_order_helper | 2026-06-07T12:34:26+00:00 | Refactor_total_order_helper_DONE_2026-06-07 |
| 2 | marginalize_loose_self_cycle | 2026-06-13T09:29:57+00:00 | Refactor_marginalize_loose_self_cycle_DONE_2026-06-13 |
| 3 | blockable_noncollider_first | 2026-06-15T16:10:52+00:00 | Refactor_blockable_noncollider_first_DONE_2026-06-15 |
| 4 | sigma_separation_J_empty_premise | 2026-06-15T21:29:20+00:00 | Refactor_sigma_separation_J_empty_premise_DONE_2026-06-15 |
| 5 | cdmg_typed_edges | 2026-06-17T02:07:35+00:00 | Refactor_cdmg_typed_edges_BUILDFAIL_2026-06-19 |
