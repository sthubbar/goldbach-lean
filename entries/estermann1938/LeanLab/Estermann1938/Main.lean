module

public import LeanLab.ExceptionalSet.Statements
public import LeanLab.PNTPort.PsiChi.Unconditional

/-!
# Estermann 1938, Proc. London Math. Soc. series 2, volume 44, pages 307-314: the main result

T. Estermann, On Goldbach's problem: proof that almost all even positive integers are sums of
two primes, doi 10.1112/plms/s2-44.4.307. The Introduction, p. 307:

  Let `Q(n)` denote the number of those even positive integers less than `n` which are not
  representable as sums of two primes. Then, as `n → ∞`, `Q(n) = O(n log^{-a} n)` for any
  positive number `a`.

p. 314 closes the proof with `Q(n) ≤ A₁₅ n log^{4-η/3} n` for every `η > 4`, the same statement
with `a = η/3 - 4`. Here `Q` and `theorem_stmt`, in the paper's own big-O form.

The proof is not Estermann's circle method text. It goes through Heath-Brown's route from the
Siegel-Walfisz theorem, `PNTPort.PsiChi.goldbach_logPowerSaving`, which bounds the lab's `E(X)`,
the even `4 ≤ m ≤ X` not sums of two primes; `Q(n) ≤ E(n) + 1` finishes. Binary Goldbach is
open; this says the exceptions, if any, are rare. AI-written Lean code, Claude, 2026-10-19.
-/

@[expose] public section

namespace LeanLab.Estermann1938
open Real Filter Asymptotics

attribute [local instance] Classical.propDecidable

/-- Estermann's `Q(n)`, p. 307: the even positive integers `m < n` that are not a sum of two
primes. The primes may be `2`, as in the paper, which says "two primes", not "two odd primes". -/
noncomputable def Q (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun m => 0 < m ∧ Even m ∧ ¬ IsGoldbachSum m)).card

/-- The main result, p. 307: for every `a > 0`, `Q(n) = O(n log^{-a} n)` as `n → ∞`. -/
def theorem_stmt : Prop :=
  ∀ a : ℝ, 0 < a →
    (fun n : ℕ => (Q n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log n ^ (-a))

/-- `Q(n) ≤ E(n) + 1`: the only even positive `m` below `4` is `2`, which is not a sum of two
primes; every other counted `m` lies in `[4, n]`. -/
theorem Q_le_E (n : ℕ) : Q n ≤ ExceptionalSet.E n + 1 := by
  unfold Q ExceptionalSet.E
  calc ((Finset.range n).filter (fun m => 0 < m ∧ Even m ∧ ¬ IsGoldbachSum m)).card
      ≤ (insert 2 ((Finset.Icc 4 n).filter (fun m => Even m ∧ ¬ IsGoldbachSum m))).card := by
        apply Finset.card_le_card
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        obtain ⟨hmn, hm0, hme, hmg⟩ := hm
        by_cases h2 : m = 2
        · exact Or.inl h2
        · right
          have : m ≠ 1 := by rintro rfl; exact absurd hme (by decide)
          have : m ≠ 3 := by rintro rfl; exact absurd hme (by decide)
          exact ⟨⟨by omega, by omega⟩, hme, hmg⟩
    _ ≤ _ := Finset.card_insert_le _ _

/-- `n log^{-a} n` is nonnegative on `ℕ`. -/
theorem g_nonneg (a : ℝ) (n : ℕ) : 0 ≤ (n : ℝ) * Real.log n ^ (-a) := by
  rcases Nat.lt_or_ge n 1 with h | h
  · have : n = 0 := by omega
    subst this; simp
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Real.log_natCast_nonneg n) _)

/-- `1 = O(n log^{-a} n)`: `log^a n ≤ n` eventually, since `log^a x = o(x)`. -/
theorem one_isBigO (a : ℝ) :
    (fun _ : ℕ => (1 : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log n ^ (-a)) := by
  have hlo := (isLittleO_log_rpow_rpow_atTop a (s := 1) one_pos).bound (c := 1) one_pos
  have hlo' := tendsto_natCast_atTop_atTop.eventually (hlo.and (eventually_gt_atTop (3 : ℝ)))
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hlo'] with n ⟨hn, hn3⟩
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hpow : 0 < Real.log n ^ a := Real.rpow_pos_of_pos hlog a
  have hn' : Real.log n ^ a ≤ n := by
    have h := hn
    rw [Real.norm_of_nonneg hpow.le, Real.norm_of_nonneg (by positivity), Real.rpow_one,
      one_mul] at h
    exact h
  rw [norm_one, one_mul, Real.norm_of_nonneg (g_nonneg a n), Real.rpow_neg hlog.le,
    ← div_eq_mul_inv, le_div_iff₀ hpow, one_mul]
  exact hn'

/-- `E(n) = O(n log^{-a} n)` from the lab's `LogPowerSaving`. -/
theorem E_isBigO (h : ExceptionalSet.LogPowerSaving) {a : ℝ} (ha : 0 < a) :
    (fun n : ℕ => (ExceptionalSet.E n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log n ^ (-a)) := by
  obtain ⟨C, hC⟩ := h a ha
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (g_nonneg a n),
    Real.rpow_neg hlog.le, ← mul_assoc, ← div_eq_mul_inv]
  exact hC n hn

/-- The main result follows from the lab's `LogPowerSaving`. -/
theorem theorem_of_logPowerSaving (h : ExceptionalSet.LogPowerSaving) : theorem_stmt := by
  intro a ha
  have hsum := (E_isBigO h ha).add (one_isBigO a)
  refine IsBigO.trans ?_ hsum
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have h1 := (Nat.cast_le (α := ℝ)).mpr (Q_le_E n)
  push_cast at h1
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity), one_mul]
  exact h1

/-- Estermann 1938, the main result, p. 307, with no hypothesis. -/
theorem main : theorem_stmt :=
  theorem_of_logPowerSaving LeanLab.PNTPort.PsiChi.goldbach_logPowerSaving

/-- A concrete instance of `Q`: below `10` the even positive integers are `2, 4, 6, 8`, and only
`2` is not a sum of two primes, so `Q(10) = 1`; the count is not empty. -/
theorem Q_ten : Q 10 = 1 := by
  have h2 : ¬ IsGoldbachSum 2 := by
    rintro ⟨p, q, hp, hq, hpq⟩
    have := hp.two_le; have := hq.two_le; omega
  have h4 : IsGoldbachSum 4 := ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  have h6 : IsGoldbachSum 6 := ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
  have h8 : IsGoldbachSum 8 := ⟨3, 5, Nat.prime_three, Nat.prime_five, rfl⟩
  unfold Q
  rw [Finset.card_eq_one]
  refine ⟨2, ?_⟩
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hm, hm0, hme, hmg⟩
    interval_cases m
    all_goals first | rfl | exact absurd hme (by decide) | exact absurd h4 hmg | exact absurd h6 hmg | exact absurd h8 hmg
  · rintro rfl
    exact ⟨by norm_num, by norm_num, by decide, h2⟩

end LeanLab.Estermann1938
