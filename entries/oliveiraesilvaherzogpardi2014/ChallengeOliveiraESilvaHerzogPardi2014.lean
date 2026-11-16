module

public import Mathlib

/-!
# Table 4 of Oliveira e Silva, Herzog and Pardi on the even numbers up to 10^8

T. Oliveira e Silva, S. Herzog and S. Pardi, Empirical verification of the even Goldbach
conjecture and computation of prime gaps up to 4 · 10^18, Math. Comp. 83, 2014, pages 2033 to 2060.
For an even `n`, `p(n)` is the least prime `p` such that `n - p` is prime. Table 4 on page 2043
lists the 68 pairs `(n, p(n))` at which `p(n)` reaches a new maximum, that is the even `n ≥ 6`
with `p(m) < p(n)` for every even `m` with `6 ≤ m < n`, from `n = 6` up to
`n = 3325581707333960528`.

This file states, for the part of the table with `n ≤ 10^8`, the 28 rows from `(6, 3)` to
`(60119912, 1093)`: every such row is exact and is a record, `table4_least`, and no record of
`p(n)` with `n ≤ 10^8` is missing from the table, `table4_complete`, which also states that
every even `m` with `6 ≤ m ≤ 10^8` has a Goldbach partition. This is a finite check on part of
the paper's data; the 40 rows above 10^8 and the paper's verification up to 4 · 10^18 are not
claimed. `minGB n` is the least prime `p` with `n - p` prime, and `0` when there is none; for
even `n ≥ 6` it is the paper's `p(n)`.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

/-- The least prime `p` with `n - p` prime, and `0` when there is no such prime. -/
noncomputable def minGB (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, p.Prime ∧ (n - p).Prime then Nat.find h else 0

set_option maxRecDepth 20000

/-- Table 4 of the paper, page 2043: the rows `(n, p(n))`, the even `n` at which the least
prime `p(n)` of a Goldbach partition reaches a new record, from 6 to 3325581707333960528. -/
def table4 : List (ℕ × ℕ) := [
    (6, 3),
    (12, 5),
    (30, 7),
    (98, 19),
    (220, 23),
    (308, 31),
    (556, 47),
    (992, 73),
    (2642, 103),
    (5372, 139),
    (7426, 173),
    (43532, 211),
    (54244, 233),
    (63274, 293),
    (113672, 313),
    (128168, 331),
    (194428, 359),
    (194470, 383),
    (413572, 389),
    (503222, 523),
    (1077422, 601),
    (3526958, 727),
    (3807404, 751),
    (10759922, 829),
    (24106882, 929),
    (27789878, 997),
    (37998938, 1039),
    (60119912, 1093),
    (113632822, 1163),
    (187852862, 1321),
    (335070838, 1427),
    (419911924, 1583),
    (721013438, 1789),
    (1847133842, 1861),
    (7473202036, 1877),
    (11001080372, 1879),
    (12703943222, 2029),
    (21248558888, 2089),
    (35884080836, 2803),
    (105963812462, 3061),
    (244885595672, 3163),
    (599533546358, 3457),
    (3132059294006, 3463),
    (3620821173302, 3529),
    (4438327672994, 3613),
    (5320503815888, 3769),
    (8342945544436, 3917),
    (10591605900482, 4003),
    (12982270197518, 4027),
    (15197900994218, 4057),
    (28998050650046, 4327),
    (46878442766282, 4519),
    (76903574497118, 4909),
    (184162477860248, 5077),
    (217361316706568, 5209),
    (389965026819938, 5569),
    (1047610575836828, 6469),
    (6253262345930828, 6961),
    (24925556008175266, 7559),
    (31284177910528922, 7753),
    (121005022304007026, 8443),
    (255329126688555994, 8501),
    (258549426916149682, 8933),
    (555274351556750822, 8941),
    (887123803077837868, 9161),
    (906030579562279642, 9341),
    (2795935116574469638, 9629),
    (3325581707333960528, 9781)]

/-- Every row `(n, p)` of Table 4 with `n ≤ 10^8` is exact and is a record: `p(n) = p`, and
every even `m` with `6 ≤ m < n` has `p(m) < p`. -/
theorem table4_least : ∀ x ∈ table4, x.1 ≤ 100000000 →
    minGB x.1 = x.2 ∧ ∀ m, Even m → 6 ≤ m → m < x.1 → minGB m < x.2 := by
  sorry

/-- Every even `m` with `6 ≤ m ≤ 10^8` has a Goldbach partition `m = p(m) + (m - p(m))`, and
`p(m)` is at most the `p` of a row `(n, p)` of Table 4 with `n ≤ m`, so no record of `p(n)` with
`n ≤ 10^8` is missing from the table. -/
theorem table4_complete : ∀ m, Even m → 6 ≤ m → m ≤ 100000000 →
    (minGB m).Prime ∧ (m - minGB m).Prime ∧ ∃ x ∈ table4, x.1 ≤ m ∧ minGB m ≤ x.2 := by
  sorry

end LeanLab.OeSHP2014
