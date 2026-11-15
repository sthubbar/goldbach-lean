module

public import LeanLab.Tolev2009.Decomp310a
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
AI wrote this Lean code. Codex task336.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 page 86 displays 64 to 66.
The progression estimate is proved. Both exact row estimates are proved in Decomp336b.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Decomp336a

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a

/-- The single modulus progression in Tolev 1999 page 86 display 64.
All three product cutoffs and the fixed residue are retained. -/
noncomputable def progression (l₃ k N m : ℕ) (α x H H₁ : ℝ) : ℂ :=
  ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
        (m * l) % k = l₃ % k then ee (α * (m * l : ℕ)) else 0

/-- The geometric majorant in display 65, with its resonance case explicit.
The additional one retains the endpoint in the progression count. -/
noncomputable def phaseCap (α x : ℝ) (n : ℕ) : ℝ :=
  if ee (α * n) = 1 then 2 * x / n + 1
  else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)

/-- The majorant is nonnegative for a nonnegative shell endpoint. -/
theorem phaseCap_nonneg (α x : ℝ) (n : ℕ) (hx : 0 ≤ x) : 0 ≤ phaseCap α x n := by
  unfold phaseCap
  split_ifs <;> positivity

/-- The nearest integer denominator comparison used in Tolev 1999 page 86 display 65.
This supplies the exact constant for the geometric majorant. -/
theorem distance_comparison (t : ℝ) :
    4 * |t - (round t : ℝ)| ≤ ‖ee t - 1‖ := by
  let u : ℝ := t - round t
  have hperiod : ee t = ee u := by
    have h := ee_add u (round t : ℝ)
    rw [ee_int, mul_one] at h
    simpa only [u, sub_add_cancel] using h
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have hpi : |Real.pi * u| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hpi
  have hnorm : ‖ee u - 1‖ = 2 * |Real.sin (Real.pi * u)| := by
    have he : ee u = Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) := by
      unfold ee
      push_cast
      ring_nf
    rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2 * Real.pi * u / 2 = Real.pi * u by ring]
    rw [Real.norm_eq_abs, abs_mul]
    norm_num
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hcancel : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by
    field_simp
  rw [hcancel] at hs
  rw [hperiod, hnorm]
  change 4 * |u| ≤ _
  linarith


/-- Expanding the divisor weight gives the exact progression decomposition.
This is the adapted identity before Tolev 1999 display 64. -/
theorem row_eq_progressions (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ) :
    row lam l₃ K N α x H H₁ (fun _ => 1) m =
      ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        (lam k : ℂ) * progression l₃ k N m α x H H₁ := by
  classical
  unfold row progression
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  simp only [L2Bound.weight, sum_filter, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, one_mul, mul_sum]
  by_cases hc : x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N
  · simp only [hc, ite_true, true_and]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> simp_all <;> ring
  · simp only [hc, ite_false, false_and, mul_zero, ite_self, sum_const_zero]

/-- The triangle step in display 64 removes all bounded real weights. -/
theorem row_norm_le_progressions (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ)
    (hlam : ∀ k, |lam k| ≤ 1) :
    ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤
      ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        ‖progression l₃ k N m α x H H₁‖ := by
  rw [row_eq_progressions]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k hk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hlam k) (norm_nonneg _)).trans_eq (one_mul _)

/-- Every row is bounded by the same scalar phase sum, uniformly in its upper endpoint.
This is the elementary triangle reduction in display 64. -/
theorem row_norm_le_phase (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ)
    (hlam : ∀ k, |lam k| ≤ 1) (hm : 1 ≤ m) (hx : 0 < x)
    (hp : ∀ k ∈ Icc 1 K, Nat.Coprime k l₃ →
      ‖progression l₃ k N m α x H H₁‖ ≤ phaseCap α x (m * k)) :
    ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤
      ∑ k ∈ Icc 1 K, phaseCap α x (m * k) := by
  apply (row_norm_le_progressions lam l₃ K N m α x H H₁ hlam).trans
  apply (sum_le_sum (fun k hk => hp k (mem_filter.mp hk).1 (mem_filter.mp hk).2)).trans
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k hk hnot =>
    phaseCap_nonneg α x (m * k) hx.le)

/-- A uniform prefix estimate transfers to the logarithmic row by Abel summation.
This is the norm step in Tolev 1999 page 86 display 66.
Every prefix keeps the original product cutoffs. -/
theorem logarithmic_row_norm_le_prefix (lam : ℕ → ℝ) (l₃ K N m : ℕ)
    (α x H H₁ B : ℝ) (hB : 0 ≤ B) (hHH : ⌊H⌋₊ < ⌊H₁⌋₊)
    (hp : ∀ t : ℕ, ⌊H⌋₊ < t → t ≤ ⌊H₁⌋₊ →
      ‖row lam l₃ K N α x H (t : ℝ) (fun _ => 1) m‖ ≤ B) :
    ‖row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
      2 * Real.log ⌊H₁⌋₊ * B := by
  let U := ⌊H₁⌋₊
  let L := ⌊H⌋₊
  have hLU : L < U := hHH
  have hU : 1 ≤ U := by omega
  have htop : ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤ B := by
    simpa only [row, Nat.floor_natCast] using hp U hLU le_rfl
  have hd : ∀ l ∈ Ioc L (U - 1),
      0 ≤ Real.log (l + 1 : ℕ) - Real.log l := by
    intro l hl
    have hl0 : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by have := (mem_Ioc.mp hl).1; omega)
    exact sub_nonneg.mpr (Real.log_le_log hl0 (by exact_mod_cast Nat.le_succ l))
  have hs : (∑ l ∈ Ioc L (U - 1),
      (Real.log (l + 1 : ℕ) - Real.log l)) ≤ Real.log U := by
    have he : Ioc L (U - 1) = Ico (L + 1) U := by
      ext l
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [he, sum_Ico_sub (fun l : ℕ => Real.log l) (show L + 1 ≤ U by omega)]
    exact sub_le_self _ (Real.log_natCast_nonneg _)
  rw [logarithmic_row_by_parts lam l₃ K N α x H H₁ m hHH]
  apply (norm_sub_le _ _).trans
  have hfirst : ‖(Real.log ⌊H₁⌋₊ : ℂ) * row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤
      Real.log U * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg _)]
    exact mul_le_mul_of_nonneg_left htop (Real.log_natCast_nonneg _)
  have hsecond : ‖∑ l ∈ Ioc ⌊H⌋₊ (⌊H₁⌋₊ - 1),
        ((Real.log (l + 1 : ℕ) : ℂ) - (Real.log l : ℂ)) *
          row lam l₃ K N α x H (l : ℝ) (fun _ => 1) m‖ ≤ Real.log U * B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ l ∈ Ioc L (U - 1), (Real.log (l + 1 : ℕ) - Real.log l) * B := by
        apply sum_le_sum
        intro l hl
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hd l hl)]
        exact mul_le_mul_of_nonneg_left (hp l (mem_Ioc.mp hl).1 (by have := (mem_Ioc.mp hl).2; omega)) (hd l hl)
      _ = (∑ l ∈ Ioc L (U - 1), (Real.log (l + 1 : ℕ) - Real.log l)) * B := by rw [sum_mul]
      _ ≤ Real.log U * B := mul_le_mul_of_nonneg_right hs hB
  nlinarith

/-- The affine parametrization of the finite progression before display 65. -/
theorem progression_affine (l₃ k N m : ℕ) (α x H H₁ : ℝ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hcop : Nat.Coprime k l₃) (hx : 0 < x) :
    ∃ β : ℝ, ∃ J : ℕ,
      progression l₃ k N m α x H H₁ =
        ∑ j ∈ range J, ee (β + (j : ℝ) * (α * (m * k : ℕ))) ∧
      (J : ℝ) ≤ 2 * x / (m * k : ℕ) + 1 := by
  classical
  let s := (Ioc ⌊H⌋₊ ⌊H₁⌋₊).filter (fun l =>
    (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
      (m * l) % k = l₃ % k)
  have he : progression l₃ k N m α x H H₁ = ∑ l ∈ s, ee (α * (m * l : ℕ)) := by
    simp only [progression, s, sum_filter]
  have hmk : 0 < (m * k : ℕ) := by positivity
  by_cases hne : s.Nonempty
  · let a := s.min' hne
    let b := s.max' hne
    have ha : a ∈ s := s.min'_mem hne
    have hb : b ∈ s := s.max'_mem hne
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    have hab : a ≤ b := s.min'_le b hb
    have hkm : Nat.Coprime k m := by
      have hh : Nat.Coprime k (m * a) := by
        change Nat.gcd k (m * a) = 1
        rw [Nat.gcd_rec, ha'.2.2, ← Nat.gcd_rec]
        exact hcop
      exact hh.of_dvd_right (dvd_mul_right m a)
    have hmod : ∀ l ∈ s, a ≡ l [MOD k] := by
      intro l hl
      have hl' := mem_filter.mp hl
      exact Nat.ModEq.cancel_left_of_coprime hkm (ha'.2.2.trans hl'.2.2.symm)
    have hdiv : k ∣ b - a := (hmod b hb).dvd'
    have hbe : b = a + ((b - a) / k) * k := by
      rw [Nat.div_mul_cancel hdiv]
      omega
    let J := (b - a) / k + 1
    have hbetween : ∀ j < J, a ≤ a + j * k ∧ a + j * k ≤ b := by
      intro j hj
      dsimp [J] at hj
      constructor
      · omega
      · have hh := Nat.mul_le_mul_right k (show j ≤ (b - a) / k by omega)
        omega
    have hmem : ∀ j < J, a + j * k ∈ s := by
      intro j hj
      obtain ⟨hlo, hhi⟩ := hbetween j hj
      apply mem_filter.mpr
      constructor
      · exact mem_Ioc.mpr ⟨(mem_Ioc.mp ha'.1).1.trans_le hlo,
          hhi.trans (mem_Ioc.mp hb'.1).2⟩
      · have hprodlo : m * a ≤ m * (a + j * k) := Nat.mul_le_mul_left m hlo
        have hprodhi : m * (a + j * k) ≤ m * b := Nat.mul_le_mul_left m hhi
        constructor
        · refine ⟨ha'.2.1.1.trans_le (by exact_mod_cast hprodlo),
            (by exact_mod_cast hprodhi : ((m * (a + j * k) : ℕ) : ℝ) ≤ (m * b : ℕ)).trans hb'.2.1.2.1,
            hprodhi.trans hb'.2.1.2.2⟩
        · simpa [Nat.mul_add_mod, Nat.mul_mod, Nat.add_mod, Nat.mul_assoc] using ha'.2.2
    have hs : s = (range J).image (fun j => a + j * k) := by
      ext l
      constructor
      · intro hl
        have hal : a ≤ l := s.min'_le l hl
        have hlb : l ≤ b := s.le_max' l hl
        have hdl : k ∣ l - a := (hmod l hl).dvd'
        refine mem_image.mpr ⟨(l - a) / k, mem_range.mpr ?_, ?_⟩
        · dsimp [J]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : l - a ≤ b - a))
        · rw [Nat.div_mul_cancel hdl]
          omega
      · intro hl
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hl
        exact hmem j (mem_range.mp hj)
    refine ⟨α * (m * a : ℕ), J, ?_, ?_⟩
    · rw [he, hs, sum_image]
      · apply sum_congr rfl
        intro j hj
        congr 1
        push_cast
        ring
      · intro j hj j' hj' heq
        have hh : j * k = j' * k := Nat.add_left_cancel heq
        exact (Nat.mul_right_cancel (by omega : 0 < k) hh)
    · have hmkpos : (0 : ℝ) < (m * k : ℕ) := by exact_mod_cast hmk
      have hbprod : (m : ℝ) * b ≤ 2 * x := by
        simpa only [Nat.cast_mul] using hb'.2.1.2.1
      have hbeR : (b : ℝ) = a + ((b - a) / k : ℕ) * (k : ℝ) := by exact_mod_cast hbe
      have hJR : (J : ℝ) = ((b - a) / k : ℕ) + 1 := by simp [J]
      have hnum : ((J : ℝ) - 1) * (m * k : ℕ) ≤ 2 * x := by
        rw [hJR]
        push_cast
        have hh := congrArg (fun t : ℝ => (m : ℝ) * t) hbeR
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)
          (show (0 : ℝ) ≤ a from Nat.cast_nonneg a)]
      have hquot : (J : ℝ) - 1 ≤ 2 * x / (m * k : ℕ) :=
        (le_div_iff₀ hmkpos).mpr hnum
      linarith
  · refine ⟨0, 0, ?_, ?_⟩
    · rw [he, not_nonempty_iff_eq_empty.mp hne]
      simp
    · have : (0 : ℝ) ≤ 2 * x / (m * k : ℕ) := by positivity
      simpa using (show (0 : ℝ) ≤ 2 * x / (m * k : ℕ) + 1 by linarith)

/-- Tolev 1999 page 86 display 64 and its geometric estimate before 65.
This is one finite progression with no divisor coefficient or minor arc premise.
The resonance and endpoint cases are explicit. -/
theorem progression_bound (l₃ k N m : ℕ) (α x H H₁ : ℝ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hcop : Nat.Coprime k l₃) (hx : 0 < x) :
    ‖progression l₃ k N m α x H H₁‖ ≤ phaseCap α x (m * k) := by
  obtain ⟨β, J, he, hJ⟩ := progression_affine l₃ k N m α x H H₁ hk hm hcop hx
  rw [he]
  unfold phaseCap
  split_ifs with hθ
  · apply le_trans (norm_sum_le _ _)
    simpa only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one] using hJ
  · exact (progression_phase_bound β (α * (m * k : ℕ)) J hθ).trans
      (min_le_min hJ le_rfl)

/-- Abel summation bounds the logarithmic row by eight log N times the phase sum.
The upper dyadic endpoint is controlled explicitly. No product cutoff is dropped.
No minor arc input is used. -/
theorem logarithmic_row_norm_le_phase (lam : ℕ → ℝ) (l₃ K N m : ℕ)
    (α x M M₁ H H₁ : ℝ) (hlam : ∀ k, |lam k| ≤ 1)
    (hN : (3 : ℝ) ≤ N) (hx : 0 < x) (hxhi : x ≤ N)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) (hH : 0 < H) (hHH₁ : H ≤ H₁)
    (hH₁ : H₁ ≤ 2 * H) (hprod : M * H ≤ 2 * x)
    (hm : m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊) :
    ‖row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
      8 * Real.log N * ∑ k ∈ Icc 1 K, phaseCap α x (m * k) := by
  have hmp : 1 ≤ m := by have := (mem_Ioc.mp hm).1; omega
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hP : 0 ≤ ∑ k ∈ Icc 1 K, phaseCap α x (m * k) :=
    sum_nonneg (fun k hk => phaseCap_nonneg α x (m * k) hx.le)
  by_cases hHH : ⌊H⌋₊ < ⌊H₁⌋₊
  · have hmm : (m : ℝ) ≤ (⌊M₁⌋₊ : ℝ) := by exact_mod_cast (mem_Ioc.mp hm).2
    have hfloorpos : 0 < ⌊M₁⌋₊ := lt_of_lt_of_le (by omega : 0 < m) (mem_Ioc.mp hm).2
    have hM₁0 : 0 ≤ M₁ := by
      by_contra hh
      have hz := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hh))
      rw [hz] at hfloorpos
      omega
    have hmle : (m : ℝ) ≤ M₁ := hmm.trans (Nat.floor_le hM₁0)
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hmp
    have hMlo : (1 : ℝ) / 2 ≤ M := by linarith
    have hH₁0 : 0 < H₁ := hH.trans_le hHH₁
    have hendpoint : H₁ ≤ 8 * (N : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hH₁ hM.le,
        mul_le_mul_of_nonneg_right hMlo hH₁0.le]
    have hN0 : 0 < (N : ℝ) := by linarith
    have hNcube : (8 : ℝ) ≤ (N : ℝ) ^ 3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hN 3
      norm_num at hh
      linarith
    have htop4 : (⌊H₁⌋₊ : ℝ) ≤ (N : ℝ) ^ 4 := by
      calc
        _ ≤ H₁ := Nat.floor_le hH₁0.le
        _ ≤ 8 * (N : ℝ) := hendpoint
        _ ≤ (N : ℝ) ^ 3 * N := mul_le_mul_of_nonneg_right hNcube hN0.le
        _ = _ := by ring
    have hlog : Real.log ⌊H₁⌋₊ ≤ 4 * Real.log N := by
      have ht : 0 < (⌊H₁⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊H₁⌋₊ by omega)
      have hh := Real.log_le_log ht htop4
      rw [Real.log_pow] at hh
      norm_num at hh ⊢
      exact hh
    have hp : ∀ t : ℕ, ⌊H⌋₊ < t → t ≤ ⌊H₁⌋₊ →
        ‖row lam l₃ K N α x H (t : ℝ) (fun _ => 1) m‖ ≤
          ∑ k ∈ Icc 1 K, phaseCap α x (m * k) := by
      intro t ht htu
      apply row_norm_le_phase lam l₃ K N m α x H (t : ℝ) hlam hmp hx
      intro k hk hc
      exact progression_bound l₃ k N m α x H (t : ℝ) (mem_Icc.mp hk).1 hmp hc hx
    apply (logarithmic_row_norm_le_prefix lam l₃ K N m α x H H₁ _ hP hHH hp).trans
    nlinarith [mul_le_mul_of_nonneg_right hlog hP]
  · have he : Ioc ⌊H⌋₊ ⌊H₁⌋₊ = ∅ := Ioc_eq_empty_of_le (le_of_not_gt hHH)
    simp only [row, he, sum_empty, norm_zero]
    positivity

end LeanLab.Tolev2009.Decomp336a
