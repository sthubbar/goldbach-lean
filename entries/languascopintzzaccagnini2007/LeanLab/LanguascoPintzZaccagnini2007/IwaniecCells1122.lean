module

public import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
Unit P1122-0006, burst-20261122, the audit of the Iwaniec cells.

None of the four cells of `SPLIT_iwaniec_no_zero_open_strip481` is provable from Mathlib or
from the lab today; see `notes/burst-20261122/LanguascoPintzZaccagnini2007-iwaniec-audit.md`.
This file holds what the audit could prove outright, each a faithful piece of
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23 (1974), 97 to 104, read on the
page images of `papers/Iwaniec1974.pdf`:

* `iwaniec_radical_le_two_oddRad1122`: the radical `d` of page 97 is at most twice the odd
  radical the lab uses;
* `iwaniec_printed_denom_le1122`: the printed `1 / theta` of page 97 is at most
  `iwaniecDenom481`, so the lab region lies inside the printed one;
* `iwaniec_theta_identity1122`: the algebra that turns `theta = eta / (400 log M)` of
  Lemma 11, page 102, with `M` of Lemma 9, into the printed `1 / theta` of page 97;
* `iwaniec_sq_ne_one_of_nonreal1122`: a nonreal character has `chi ^ 2` nonprincipal, which
  is the first case of the region of step (i), page 103;
* `iwaniec_not_nonreal_of_le_two1122`: there is no nonreal character to a modulus below 3, the
  reason the hypothesis `q ≥ 3` of page 97 costs nothing;
* `iwaniecStatement481_of_printed1122`: the lab statement `IwaniecStatement481` follows from
  Theorem 2 of page 97 as printed, restricted to nonreal characters. This theorem is
  CONDITIONAL ON that printed statement, which is a hypothesis and is not proved here.

No new definition, and every proof is complete. AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Iwaniec 1974 page 97, `d = ∏_{p ∣ q} p`: the full radical is at most twice the odd
radical `oddRad131`, since the only prime factor left out is `2`. -/
theorem iwaniec_radical_le_two_oddRad1122 (r : ℕ) :
    ∏ p ∈ r.primeFactors, p ≤ 2 * oddRad131 r := by
  unfold oddRad131
  rw [← Finset.prod_filter_mul_prod_filter_not r.primeFactors (fun p => 2 < p)]
  have h : ∏ p ∈ r.primeFactors.filter (fun p => ¬ 2 < p), p ≤ 2 := by
    have hsub : r.primeFactors.filter (fun p => ¬ 2 < p) ⊆ {2} := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have h2 := (Nat.prime_of_mem_primeFactors hp.1).two_le
      rw [Finset.mem_singleton]
      omega
    calc ∏ p ∈ r.primeFactors.filter (fun p => ¬ 2 < p), p
        ≤ ∏ p ∈ ({2} : Finset ℕ), p :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub (by
            intro i hi _
            rw [Finset.mem_singleton] at hi
            omega)
      _ = 2 := by simp
  calc (∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p) *
        ∏ p ∈ r.primeFactors.filter (fun p => ¬ 2 < p), p
      ≤ (∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p) * 2 := Nat.mul_le_mul_left _ h
    _ = 2 * ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p := by ring

/-- Iwaniec 1974 page 97, the display for `1 / theta`: the printed denominator
`4 * 10 ^ 4 * (log d + (l log 2l) ^ (3 / 4))` with `d` the full radical and
`l = log (q (|t| + 3))` is at most the lab denominator `iwaniecDenom481`. -/
theorem iwaniec_printed_denom_le1122 (r : ℕ) (t : ℝ) :
    4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
      (Real.log ((r : ℝ) * (|t| + 3)) *
        Real.log (2 * Real.log ((r : ℝ) * (|t| + 3)))) ^ (3 / 4 : ℝ)) ≤
      iwaniecDenom481 r t := by
  have hpos : 0 < ∏ p ∈ r.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have h := iwaniec_radical_le_two_oddRad1122 r
  have hlog : Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) ≤
      Real.log (2 * (oddRad131 r : ℝ)) := by
    apply Real.log_le_log (by exact_mod_cast hpos)
    exact_mod_cast h
  dsimp only [iwaniecDenom481]
  linarith

/-- Iwaniec 1974, Lemma 9 and Lemma 11, page 102, against page 97: with
`1 / eta = sqrt l * (log 2l) ^ (3 / 4)` and `log M = 100 * (eta * log d + l ^ (1 / 4))`, the
quantity `400 * log M / eta` of Lemma 11 is the printed `4 * 10 ^ 4 * (log d + (l log 2l) ^ (3 / 4))`.
Here `D` stands for `log d`. -/
theorem iwaniec_theta_identity1122 (D l : ℝ) (hl : 0 < l) (hL : 0 < Real.log (2 * l)) :
    400 * (100 * ((Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹ * D + l ^ (1 / 4 : ℝ))) /
        (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹ =
      4 * 10 ^ 4 * (D + (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)) := by
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hp : 0 < Real.log (2 * l) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hL _
  have h1 : (l * Real.log (2 * l)) ^ (3 / 4 : ℝ) =
      l ^ (3 / 4 : ℝ) * Real.log (2 * l) ^ (3 / 4 : ℝ) := Real.mul_rpow hl.le hL.le
  have h2 : l ^ (3 / 4 : ℝ) = l ^ (1 / 4 : ℝ) * Real.sqrt l := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hl]
    norm_num
  rw [h1, h2]
  field_simp
  ring

/-- Iwaniec 1974 page 103, step (i), the case `chi ^ 2 ≠ chi_0` of the region: a character
with a nonreal value has a nonprincipal square. -/
theorem iwaniec_sq_ne_one_of_nonreal1122 {r : ℕ} (χ : DirichletCharacter ℂ r)
    (hnonreal : ∃ a, (χ a).im ≠ 0) : χ ^ 2 ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := hnonreal
  apply ha
  by_cases hu : IsUnit a
  · have h1 : (χ ^ 2) a = 1 := by rw [h]; exact MulChar.one_apply hu
    rw [MulChar.pow_apply' χ (by norm_num) a] at h1
    have h3 : (χ a - 1) * (χ a + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rw [sub_eq_zero.mp h4]; simp
    · rw [eq_neg_of_add_eq_zero_left h4]; simp
  · rw [MulChar.map_nonunit _ hu]; simp

/-- Iwaniec 1974 page 97, the hypothesis `q ≥ 3`: to a modulus `1` or `2` every character is
real, since the only unit is `1`. -/
theorem iwaniec_not_nonreal_of_le_two1122 {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (χ : DirichletCharacter ℂ r) (a : ZMod r) : (χ a).im = 0 := by
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    have h1 : u ^ Nat.totient r = 1 := ZMod.pow_totient u
    have h2 : Nat.totient r = 1 := by
      have : r = 1 ∨ r = 2 := by omega
      rcases this with rfl | rfl <;> simp
    rw [h2, pow_one] at h1
    rw [h1]
    simp
  · rw [MulChar.map_nonunit _ hu]; simp

/-- Iwaniec 1974 page 97, Theorem 2, read for nonreal characters: the theorem allows a zero
with `Re rho > 1 - theta` only for one real character, so a nonreal character to a modulus
`q ≥ 3` has none. With that printed statement as the hypothesis `h`, in the printed
normalization with the full radical `d`, the lab statement `IwaniecStatement481` follows. The
lab statement is weaker in three ways: `log (2 r')` with the odd radical in place of `log d`,
primitive characters only, and moduli `1` and `2` where it is empty.
CONDITIONAL ON `h`, which is cited and not proved here. -/
theorem iwaniecStatement481_of_printed1122
    (h : ∀ r : ℕ, 3 ≤ r → ∀ χ : DirichletCharacter ℂ r, (∃ a, (χ a).im ≠ 0) → ∀ s : ℂ,
      1 - 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (Real.log ((r : ℝ) * (|s.im| + 3)) *
          Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ))) < s.re →
      Lfun481 χ s ≠ 0) : IwaniecStatement481 := by
  intro r hr χ _ hnonreal s hs
  by_cases hr3 : 3 ≤ r
  · apply h r hr3 χ hnonreal s
    have hle := iwaniec_printed_denom_le1122 r s.im
    -- the printed denominator is positive
    have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have ht : 0 ≤ |s.im| := abs_nonneg _
    have hbase : (3 : ℝ) ≤ (r : ℝ) * (|s.im| + 3) := by nlinarith
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hl1 : 1 < Real.log ((r : ℝ) * (|s.im| + 3)) := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      linarith
    have hl2 : 0 < Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3))) :=
      Real.log_pos (by linarith)
    have hpow : 0 < (Real.log ((r : ℝ) * (|s.im| + 3)) *
        Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ) :=
      Real.rpow_pos_of_pos (mul_pos (by linarith) hl2) _
    have hd : (1 : ℝ) ≤ ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) := by
      have : 0 < ∏ p ∈ r.primeFactors, p :=
        Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
      exact_mod_cast this
    have hlogd : 0 ≤ Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) := Real.log_nonneg hd
    have hP : 0 < 4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (Real.log ((r : ℝ) * (|s.im| + 3)) *
          Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ)) := by
      have : 0 < Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (Real.log ((r : ℝ) * (|s.im| + 3)) *
          Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ) := by linarith
      positivity
    have hinv := one_div_le_one_div_of_le hP hle
    linarith
  · obtain ⟨a, ha⟩ := hnonreal
    exact absurd (iwaniec_not_nonreal_of_le_two1122 hr (by omega) χ a) ha

end

end LeanLab.LPZ2007
