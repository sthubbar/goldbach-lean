module

public import LeanLab.Song2020.State1562

/-!
AI wrote the Lean code, Codex by OpenAI, 2026-10-27.
Elementary local steps for the characteristic reduction on printed page 4.
Source: https://arxiv.org/pdf/2012.06322.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Decomp139

open LeanLab.Song2020 LeanLab.Song2020.State1562

noncomputable section

/-- Page 4. The centered fractional part used in Lemma 1. -/
def saw (x : ℝ) : ℝ := x - ⌊x⌋ - 1 / 2

/-- Page 4. The prime sum with the sawtooth difference in Lemma 4. -/
def sawSum (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
    ((saw (-((p : ℝ) + 1) ^ γ) - saw (-(p : ℝ) ^ γ) : ℝ) : ℂ)

end

end LeanLab.Song2020.Decomp139

namespace LeanLab.Song2020.Characteristic139

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139
open scoped Classical

noncomputable section

/-- Page 4. The sawtooth difference is the floor count minus the power increment. -/
theorem saw_difference139 (γ x : ℝ) :
    saw (-((x + 1) ^ γ)) - saw (-(x ^ γ)) =
      (⌊-(x ^ γ)⌋ : ℝ) - (⌊-((x + 1) ^ γ)⌋ : ℝ) - ((x + 1) ^ γ - x ^ γ) := by
  unfold saw
  ring

/-- Page 4. Membership is equivalent to an integer witness between consecutive gamma powers. -/
theorem isPSPrime_iff_witness_interval139 (γ : ℝ) (hγ : 0 < γ) (p : ℕ) (hp : p.Prime) :
    IsPSPrime γ p ↔ ∃ m : ℕ, (p : ℝ) ^ γ ≤ m ∧ (m : ℝ) < ((p : ℝ) + 1) ^ γ := by
  constructor
  · rintro ⟨_, m, _, hm⟩
    exact ⟨m, ps_witness_bounds139 hγ hm⟩
  · rintro ⟨m, hmlo, hmhi⟩
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hm1 : 1 ≤ m := by
      have := (Real.one_le_rpow hp1 hγ.le).trans hmlo
      exact_mod_cast this
    have hinv : 0 < 1 / γ := by positivity
    have he (x : ℝ) (hx : 0 ≤ x) : (x ^ γ) ^ (1 / γ) = x := by
      simpa only [one_div] using Real.rpow_rpow_inv hx hγ.ne'
    have hlo := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg p) γ) hmlo hinv.le
    have hhi := Real.rpow_lt_rpow (Nat.cast_nonneg m) hmhi hinv
    rw [he p (Nat.cast_nonneg p)] at hlo
    rw [he ((p : ℝ) + 1) (by positivity)] at hhi
    refine ⟨hp, m, hm1, ?_⟩
    symm
    apply Int.floor_eq_iff.mpr
    simpa only [Int.cast_natCast] using And.intro hlo hhi

/-- Page 4. The normalized power increment differs from one by at most 1 divided by x plus one. -/
theorem weighted_increment_error139 (γ x : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hx : 1 ≤ x) :
    |(1 / γ) * x ^ (1 - γ) * ((x + 1) ^ γ - x ^ γ) - 1| ≤ 1 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hc := Real.concaveOn_rpow hγ.le hγ1
  have hu := hc.slope_le_of_hasDerivAt (by simpa using hx0.le) (by simpa using hx1.le)
    (show x < x + 1 by linarith) (Real.hasDerivAt_rpow_const (Or.inl hx0.ne'))
  have hl := hc.le_slope_of_hasDerivAt (by simpa using hx0.le) (by simpa using hx1.le)
    (show x < x + 1 by linarith) (Real.hasDerivAt_rpow_const (Or.inl hx1.ne'))
  simp only [slope_def_field, add_sub_cancel_left, div_one] at hu hl
  let W : ℝ := (1 / γ) * x ^ (1 - γ)
  have hW : 0 < W := by dsimp [W]; positivity
  have huval : W * (γ * x ^ (γ - 1)) = 1 := by
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; norm_num)
    dsimp [W]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_one]
    ring
  have hlval : W * (γ * (x + 1) ^ (γ - 1)) = (x / (x + 1)) ^ (1 - γ) := by
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
    dsimp [W]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_one]
    ring
  have hr : 0 < x / (x + 1) := by positivity
  have hr1 : x / (x + 1) ≤ 1 := (div_le_one hx1).mpr (by linarith)
  have hrlower : x / (x + 1) ≤ (x / (x + 1)) ^ (1 - γ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (show 1 - γ ≤ 1 by linarith)
  have hupper : W * ((x + 1) ^ γ - x ^ γ) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hu hW.le).trans_eq huval
  have hlower : x / (x + 1) ≤ W * ((x + 1) ^ γ - x ^ γ) := by
    have h := mul_le_mul_of_nonneg_left hl hW.le
    rw [hlval] at h
    exact hrlower.trans h
  change |W * ((x + 1) ^ γ - x ^ γ) - 1| ≤ _
  rw [abs_of_nonpos (by linarith)]
  have he : 1 - x / (x + 1) = 1 / (x + 1) := by field_simp; ring
  linarith


/-- Page 4. The negative-power floor difference is exactly the restricted-prime indicator. -/
theorem ps_floor_count139 (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (p : ℕ) (hp : p.Prime) :
    (if IsPSPrime γ p then (1 : ℤ) else 0) =
      ⌊-((p : ℝ) ^ γ)⌋ - ⌊-(((p : ℝ) + 1) ^ γ)⌋ := by
  let A : ℝ := (p : ℝ) ^ γ
  let B : ℝ := ((p : ℝ) + 1) ^ γ
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hA1 : 1 ≤ A := Real.one_le_rpow hp1 hγ.le
  have hAB : A ≤ B := Real.rpow_le_rpow hp0.le (by linarith) hγ.le
  have hinc := rpow_increment_le139 γ p ((p : ℝ) + 1) hγ.le hγ1 hp0 (by linarith)
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hp1 (show γ - 1 ≤ 0 by linarith)
  have hγpow : γ * (p : ℝ) ^ (γ - 1) ≤ 1 := by nlinarith
  have hBA : B ≤ A + 1 := by dsimp [A, B]; nlinarith
  have hceilAB : ⌈A⌉ ≤ ⌈B⌉ := Int.ceil_mono hAB
  have hceilBA : ⌈B⌉ ≤ ⌈A⌉ + 1 := by
    simpa only [Int.ceil_add_one] using Int.ceil_mono hBA
  have hceilA : 0 ≤ ⌈A⌉ := by
    have hA : (0 : ℝ) < A := by linarith
    have := Int.one_le_ceil_iff.mpr hA
    omega
  rw [Int.floor_neg, Int.floor_neg]
  change (if IsPSPrime γ p then (1 : ℤ) else 0) = -⌈A⌉ - -⌈B⌉
  by_cases hPS : IsPSPrime γ p
  · obtain ⟨m, hmlo, hmhi⟩ := (isPSPrime_iff_witness_interval139 γ hγ p hp).mp hPS
    have hml : ⌈A⌉ ≤ (m : ℤ) := Int.ceil_le.mpr (by simpa only [Int.cast_natCast, A] using hmlo)
    have hmh : (m : ℤ) < ⌈B⌉ := Int.lt_ceil.mpr (by simpa only [Int.cast_natCast, B] using hmhi)
    simp only [if_pos hPS]
    omega
  · have hnot : ¬ ⌈A⌉ < ⌈B⌉ := by
      intro hlt
      have hm : ((⌈A⌉.toNat : ℕ) : ℤ) = ⌈A⌉ := Int.toNat_of_nonneg hceilA
      have hml : A ≤ (⌈A⌉.toNat : ℝ) := by
        have h := Int.le_ceil A
        exact_mod_cast (show A ≤ (((⌈A⌉.toNat : ℕ) : ℤ) : ℝ) by simpa only [hm] using h)
      have hmh : (⌈A⌉.toNat : ℝ) < B := by
        have h := Int.lt_ceil.mp hlt
        exact_mod_cast (show (((⌈A⌉.toNat : ℕ) : ℤ) : ℝ) < B by simpa only [hm] using h)
      exact hPS ((isPSPrime_iff_witness_interval139 γ hγ p hp).mpr ⟨⌈A⌉.toNat, hml, hmh⟩)
    simp only [if_neg hPS]
    omega


/-- Page 4. Sum the local normalized errors over the prime window. -/
theorem discrepancy_remainder_le_harmonic139 (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (n : ℕ) (y α : ℝ) (hyupper : y ≤ (n : ℝ) / 3) :
    ‖fS γ n y α - gS n y α - sawSum γ n y α‖ ≤ (harmonic (n + 1) : ℝ) := by
  let r (p : ℕ) : ℝ := psWeight γ p * (((p : ℝ) + 1) ^ γ - (p : ℝ) ^ γ) - 1
  have he : fS γ n y α - gS n y α - sawSum γ n y α =
      ∑ p ∈ windowPrimes n y, (r p : ℂ) * eC (α * p) := by
    unfold fS gS sawSum
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2.1
    have hc := ps_floor_count139 γ hγ hγ1 p hprime
    have hcc : (if IsPSPrime γ p then (1 : ℝ) else 0) =
        (⌊-((p : ℝ) ^ γ)⌋ : ℝ) - (⌊-(((p : ℝ) + 1) ^ γ)⌋ : ℝ) := by
      exact_mod_cast hc
    have hreal : (if IsPSPrime γ p then psWeight γ p else 0) - 1 - psWeight γ p *
        (saw (-((p : ℝ) + 1) ^ γ) - saw (-(p : ℝ) ^ γ)) = r p := by
      rw [saw_difference139]
      dsimp [r]
      split_ifs at hcc ⊢ with hPS <;> linear_combination (psWeight γ p) * hcc
    calc
      _ = (((if IsPSPrime γ p then psWeight γ p else 0) - 1 - psWeight γ p *
          (saw (-((p : ℝ) + 1) ^ γ) - saw (-(p : ℝ) ^ γ)) : ℝ) : ℂ) * eC (α * p) := by
        split_ifs <;> push_cast <;> ring
      _ = _ := by rw [hreal]
  have heC (x : ℝ) : ‖eC x‖ = 1 := by
    simp [eC, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hsub : windowPrimes n y ⊆ Finset.range (n + 1) := by
    intro p hp
    have hw := abs_lt.mp (Finset.mem_filter.mp hp).2.2
    have hpn : (p : ℝ) ≤ n := by linarith
    have hnat : p ≤ n := by exact_mod_cast hpn
    exact Finset.mem_range.mpr (by omega)
  rw [he]
  calc
    _ ≤ ∑ p ∈ windowPrimes n y, ‖(r p : ℂ) * eC (α * p)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ windowPrimes n y, 1 / ((p : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, heC, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le
      exact weighted_increment_error139 γ p hγ hγ1 hp1
    _ ≤ ∑ p ∈ Finset.range (n + 1), 1 / ((p : ℝ) + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intros
      positivity
    _ = (harmonic (n + 1) : ℝ) := by simp [harmonic, one_div]

/-- Page 4 and the page 5 remainder. The full characteristic reduction is elementary. -/
theorem characteristic_reduction139 :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ‖fS γ n y α - gS n y α - sawSum γ n y α‖ ≤ C * (n : ℝ) ^ (3 / 2 - γ) := by
  intro γ hγ hγ1
  refine ⟨5, by norm_num, 1, fun n hn y _ hyupper α => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hnR (by norm_num)
  have hinc : ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      _ ≤ (2 * (n : ℝ)) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) := Real.mul_rpow (by norm_num) hn0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have hlog := Real.log_le_rpow_div (show 0 ≤ (n : ℝ) + 1 by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
  have hhar := harmonic_le_one_add_log (n + 1)
  have hhar' : (harmonic (n + 1) : ℝ) ≤ 5 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    push_cast at hhar
    nlinarith
  calc
    _ ≤ (harmonic (n + 1) : ℝ) := discrepancy_remainder_le_harmonic139 γ (by linarith) hγ1.le n y α hyupper
    _ ≤ 5 * (n : ℝ) ^ ((1 : ℝ) / 2) := hhar'
    _ ≤ 5 * (n : ℝ) ^ (3 / 2 - γ) := by
      gcongr
      linarith

end

end LeanLab.Song2020.Characteristic139
