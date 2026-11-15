module

public import LeanLab.Tolev2009.Decomp286b
public import LeanLab.PNTPort.Vinogradov.Count

/-!
AI wrote this Lean code. Codex task310.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98.
Adapted to https://arxiv.org/abs/0902.2669 page 4 display 12.
All analytic leaves are proved. Assemblies are derived from them.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Decomp310a

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b

/-- The inner row after removing a m, Tolev 1999 page 86 display 64.
The product truncation and fixed residue are those of the sealed bilinear block. -/
noncomputable def row (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ)
    (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      b l * ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
    else 0

/-- Removing the first coefficient gives the row form of display 64. -/
theorem bilinear_eq_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) :
    bilinear lam l₃ K N α x M M₁ H H₁ a b =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * row lam l₃ K N α x H H₁ b m := by
  unfold bilinear row
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  split_ifs <;> ring

/-- The coefficient free majorant in display 64. No minor arc input is used. -/
theorem bilinear_norm_le_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) :
    ‖bilinear lam l₃ K N α x M M₁ H H₁ a b‖ ≤
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        ((tau5 m : ℝ) * Real.log N) * ‖row lam l₃ K N α x H H₁ b m‖ := by
  rw [bilinear_eq_rows]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro m hm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha m) (norm_nonneg _)

/-- The exact discrete Abel identity behind Tolev 1999 page 86 display 66.
It reduces each logarithmic row to constant rows with truncated upper endpoints.
No minor arc assumption or analytic row bound is used. -/
theorem logarithmic_row_by_parts (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ) (m : ℕ)
    (hHH : ⌊H⌋₊ < ⌊H₁⌋₊) :
    row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m =
      (Real.log ⌊H₁⌋₊ : ℂ) * row lam l₃ K N α x H H₁ (fun _ => 1) m -
      ∑ l ∈ Ioc ⌊H⌋₊ (⌊H₁⌋₊ - 1),
        ((Real.log (l + 1 : ℕ) : ℂ) - (Real.log l : ℂ)) *
          row lam l₃ K N α x H (l : ℝ) (fun _ => 1) m := by
  let c : ℕ → ℂ := fun l =>
    if ⌊H⌋₊ < l then
      if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
        ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
      else 0
    else 0
  have hG : ∀ t : ℕ, ∑ l ∈ range (t + 1), c l =
      row lam l₃ K N α x H (t : ℝ) (fun _ => 1) m := by
    intro t
    have hs : (range (t + 1)).filter (fun l => ⌊H⌋₊ < l) = Ioc ⌊H⌋₊ t := by
      ext l
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    simp only [c]
    rw [← sum_filter, hs]
    simp only [row, Nat.floor_natCast, one_mul]
  have hG0 : ∑ l ∈ range (⌊H⌋₊ + 1), c l = 0 := by
    rw [hG]
    simp only [row, Nat.floor_natCast, Ioc_self, sum_empty]
  have hh := sum_Ioc_by_parts (fun l : ℕ => (Real.log l : ℂ)) c hHH
  rw [hG0, smul_zero, sub_zero] at hh
  simp only [smul_eq_mul] at hh
  have hlhs : (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (Real.log l : ℂ) * c l) =
      row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m := by
    unfold row
    apply sum_congr rfl
    intro l hl
    simp only [c, ite_eq_left (mem_Ioc.mp hl).1]
    split_ifs <;> ring
  rw [hlhs] at hh
  simp_rw [hG] at hh
  simpa only [row, Nat.floor_natCast] using hh

/-- The geometric progression step of Tolev 1999 page 86 display 64 and page 72 Lemma 6.
The denominator is kept as the exact complex distance from one.
No torus distance comparison or averaged Diophantine estimate is asserted. -/
theorem progression_phase_bound (β θ : ℝ) (J : ℕ) (hθ : ee θ ≠ 1) :
    ‖∑ j ∈ range J, ee (β + (j : ℝ) * θ)‖ ≤
      min (J : ℝ) (2 / ‖ee θ - 1‖) := by
  have he : ∀ j : ℕ, ee (β + (j : ℝ) * θ) = ee β * ee θ ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [show β + ((j : ℝ) * θ + θ) = (β + (j : ℝ) * θ) + θ by ring, ee_add, ih, pow_succ]
      ring
  apply le_min
  · apply (norm_sum_le _ _).trans_eq
    simp only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have hs : (∑ j ∈ range J, ee (β + (j : ℝ) * θ)) = ee β * ∑ j ∈ range J, ee θ ^ j := by
      rw [mul_sum]
      exact sum_congr rfl (fun j hj => he j)
    rw [hs, norm_mul, norm_ee, one_mul, geom_sum_eq hθ J, norm_div]
    have hn : ‖ee θ ^ J - 1‖ ≤ 2 := by
      simpa only [norm_pow, norm_ee, one_pow, norm_one, one_add_one_eq_two] using
        norm_sub_le (ee θ ^ J) 1
    exact div_le_div_of_nonneg_right hn (norm_nonneg _)

open LeanLab.HeathBrown1985

/-- The reciprocal divisor moment used in Tolev 1999 page 72 Lemma 8 part iii.
At r equal to twelve it supplies the Cauchy factor in page 86 display 65. -/
theorem divisor_power_reciprocal (r N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n ≤ Hn N ^ (2 ^ r) := by
  induction r generalizing N with
  | zero => simp [Hn]
  | succ r ih =>
    have hh := LeanLab.Tolev2009.DivisorMoment.reciprocal_step N r (2 ^ r) (fun M hM => ih M)
    simpa only [pow_succ, Nat.mul_comm] using hh

open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

/-! ### The phase cap and its elementary properties -/

private theorem phcap_nonneg (α x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    0 ≤ (if ee (α * n) = 1 then 2 * x / n + 1
      else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) := by
  split_ifs <;> positivity

private theorem phcap_le_count (α x : ℝ) (n : ℕ) :
    (if ee (α * n) = 1 then 2 * x / n + 1
      else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) ≤ 2 * x / n + 1 := by
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The complex distance from one dominates four times the distance to the
nearest integer.  This is the constant conversion of Tolev display 65. -/
private theorem phcap_distance (t : ℝ) :
    4 * |t - round t| ≤ ‖ee t - 1‖ := by
  have h := LeanLab.PNTPort.LargeSieve.four_dist0_le t
  have hd : LeanLab.PNTPort.LargeSieve.dist0 t = |t - round t| := rfl
  rw [hd] at h
  have he : LeanLab.PNTPort.LargeSieve.e t = ee t := by
    unfold LeanLab.PNTPort.LargeSieve.e ee
    congr 1
    push_cast
    ring
  rwa [he] at h

/-- The phase cap is at most Vinogradov's `G` plus one. -/
private theorem phcap_le_G_add_one (α x : ℝ) (n : ℕ) :
    (if ee (α * n) = 1 then 2 * x / n + 1
      else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) ≤
      LeanLab.PNTPort.Vinogradov.G (2 * x / n) (α * n) + 1 := by
  by_cases hd : dist0 (α * n) = 0
  · rw [LeanLab.PNTPort.Vinogradov.G, if_pos hd]
    exact phcap_le_count α x n
  · have hdpos : 0 < dist0 (α * n) := lt_of_le_of_ne (dist0_nonneg _) (Ne.symm hd)
    have hdist : 4 * dist0 (α * n) ≤ ‖ee (α * n) - 1‖ := phcap_distance _
    have hden : 0 < ‖ee (α * n) - 1‖ := by linarith
    have he : ee (α * n) ≠ 1 := by
      intro hh
      simp [hh] at hden
    rw [if_neg he, LeanLab.PNTPort.Vinogradov.G, if_neg hd, ← min_add_add_right]
    apply le_min
    · exact min_le_left _ _
    · have hle : 2 / ‖ee (α * n) - 1‖ ≤ 1 / (2 * dist0 (α * n)) := by
        rw [div_le_div_iff₀ hden (by positivity)]
        nlinarith
      exact (min_le_right _ _).trans (hle.trans (by linarith))


/-! ### The single modulus progression sum -/

/-- The affine parametrization of the finite progression before Tolev display 65.
The progression sum is passed as a value with its defining equation, so that no
new definition enters the file. -/
private theorem prog_affine (l₃ k N m : ℕ) (α x H H₁ : ℝ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hcop : Nat.Coprime k l₃) (hx : 0 < x) (S : ℂ)
    (hS : S = ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
      (if (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧ (m * l) % k = l₃ % k
        then ee (α * (m * l : ℕ)) else 0)) :
    ∃ β : ℝ, ∃ J : ℕ,
      S = ∑ j ∈ range J, ee (β + (j : ℝ) * (α * (m * k : ℕ))) ∧
      (J : ℝ) ≤ 2 * x / (m * k : ℕ) + 1 := by
  classical
  let s := (Ioc ⌊H⌋₊ ⌊H₁⌋₊).filter (fun l =>
    (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
      (m * l) % k = l₃ % k)
  have he : S = ∑ l ∈ s, ee (α * (m * l : ℕ)) := by
    rw [hS]
    simp only [s, sum_filter]
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

/-- The geometric bound for one progression: the resonance and endpoint cases are
explicit, and the denominator is the exact complex distance from one. -/
private theorem prog_bound (l₃ k N m : ℕ) (α x H H₁ : ℝ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hcop : Nat.Coprime k l₃) (hx : 0 < x) (S : ℂ)
    (hS : S = ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
      (if (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧ (m * l) % k = l₃ % k
        then ee (α * (m * l : ℕ)) else 0)) :
    ‖S‖ ≤ (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
      else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
  obtain ⟨β, J, he, hJ⟩ := prog_affine l₃ k N m α x H H₁ hk hm hcop hx S hS
  rw [he]
  split_ifs with hθ
  · apply le_trans (norm_sum_le _ _)
    simpa only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one] using hJ
  · exact (progression_phase_bound β (α * (m * k : ℕ)) J hθ).trans
      (min_le_min hJ le_rfl)


/-- The constant row is bounded by the phase cap sum.  All bounded real weights
are removed by the triangle inequality; no minor arc input is used. -/
private theorem row_le_phase (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ)
    (hlam : ∀ k, |lam k| ≤ 1) (hm : 1 ≤ m) (hx : 0 < x) :
    ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤
      ∑ k ∈ Icc 1 K, (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
        else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
  classical
  let prog : ℕ → ℂ := fun k => ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
      (if (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧ (m * l) % k = l₃ % k
        then ee (α * (m * l : ℕ)) else 0)
  have hrow : row lam l₃ K N α x H H₁ (fun _ => 1) m =
      ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃), (lam k : ℂ) * prog k := by
    unfold row
    dsimp only [prog]
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
  calc ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖
      = ‖∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃), (lam k : ℂ) * prog k‖ := by
        rw [hrow]
    _ ≤ ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃), ‖(lam k : ℂ) * prog k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
          (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
            else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hkK, hkcop⟩ := mem_filter.mp hk
        have hk1 : 1 ≤ k := (mem_Icc.mp hkK).1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 : |lam k| * ‖prog k‖ ≤ 1 * ‖prog k‖ :=
          mul_le_mul_of_nonneg_right (hlam k) (norm_nonneg _)
        have h2 : ‖prog k‖ ≤ (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
            else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) :=
          prog_bound l₃ k N m α x H H₁ hk1 hm hkcop hx (prog k) rfl
        calc |lam k| * ‖prog k‖ ≤ 1 * ‖prog k‖ := h1
          _ = ‖prog k‖ := one_mul _
          _ ≤ _ := h2
    _ ≤ ∑ k ∈ Icc 1 K,
          (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
            else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun k _ _ => phcap_nonneg α x (m * k) hx.le)


/-- A uniform bound for all truncated constant rows transfers to the logarithmic
row by Abel summation: the norm step of Tolev display 66. -/
private theorem log_row_prefix (lam : ℕ → ℝ) (l₃ K N m : ℕ)
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

/-- Abel summation bounds the logarithmic row by eight `log N` times the phase
sum; the upper dyadic endpoint is controlled explicitly. -/
private theorem log_row_le_phase (lam : ℕ → ℝ) (l₃ K N m : ℕ)
    (α x M M₁ H H₁ : ℝ) (hlam : ∀ k, |lam k| ≤ 1)
    (hN : (3 : ℝ) ≤ N) (hx : 0 < x) (hxhi : x ≤ N)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) (hH : 0 < H) (hHH₁ : H ≤ H₁)
    (hH₁ : H₁ ≤ 2 * H) (hprod : M * H ≤ 2 * x)
    (hm : m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊) :
    ‖row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
      8 * Real.log N * ∑ k ∈ Icc 1 K,
        (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
          else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
  have hmp : 1 ≤ m := by have := (mem_Ioc.mp hm).1; omega
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hP : 0 ≤ ∑ k ∈ Icc 1 K,
      (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
        else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) :=
    sum_nonneg (fun k hk => phcap_nonneg α x (m * k) hx.le)
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
          ∑ k ∈ Icc 1 K, (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
            else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
      intro t ht htu
      exact row_le_phase lam l₃ K N m α x H (t : ℝ) hlam hmp hx
    apply (log_row_prefix lam l₃ K N m α x H H₁ _ hP hHH hp).trans
    nlinarith [mul_le_mul_of_nonneg_right hlog hP]
  · have he : Ioc ⌊H⌋₊ ⌊H₁⌋₊ = ∅ := Ioc_eq_empty_of_le (le_of_not_gt hHH)
    simp only [row, he, sum_empty, norm_zero]
    positivity


/-! ### The minor arc reduced denominator and the reciprocal phase sum -/

/-- Minor arcs exclude small reduced denominators, including the shifted interval
endpoints.  This is Decomp310b's `denominator_gt_Q`, restated inside this file. -/
private theorem priv_denominator_gt_Q (Q τ α : ℝ) (q a : ℕ)
    (hminor : α ∉ majorArcs Q τ) (hq : 1 ≤ q) (ha : a < q)
    (hcop : Nat.Coprime a q) (herr : |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * τ)) :
    Q < q := by
  by_contra hn
  have hqQ : (q : ℝ) ≤ Q := le_of_not_gt hn
  have hmem : q ∈ Icc 1 ⌊Q⌋₊ := mem_Icc.mpr ⟨hq, (Nat.le_floor hqQ)⟩
  apply hminor
  simp only [majorArcs, Set.mem_iUnion]
  refine ⟨q, hmem, a, ?_, ?_⟩
  · exact mem_filter.mpr ⟨mem_range.mpr ha, hcop⟩
  · rcases abs_le.mp herr with ⟨hl, hr⟩
    constructor <;> linarith

/-- The integer numerator form of the same exclusion. -/
private theorem priv_integer_denominator_gt_Q (Q τ α : ℝ) (q : ℕ) (a : ℤ)
    (hQ : 0 ≤ Q) (hτ : Q + 1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1 / τ) (1 - 1 / τ)) (hminor : α ∉ majorArcs Q τ)
    (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (herr : |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * τ)) : Q < q := by
  by_contra hn
  have hqQ : (q : ℝ) ≤ Q := le_of_not_gt hn
  have ht : 0 < τ := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : |(q : ℝ) * α - a| ≤ 1 / τ := by
    have hh := mul_le_mul_of_nonneg_left herr hqr.le
    rw [show (q : ℝ) * |α - (a : ℝ) / q| = |(q : ℝ) * α - a| by
      rw [← abs_of_pos hqr, ← abs_mul, abs_of_pos hqr]
      congr 1
      field_simp] at hh
    convert hh using 1
    field_simp
  have hlo := (abs_le.mp he).1
  have hhi := (abs_le.mp he).2
  have hlα := mul_lt_mul_of_pos_left hα.1 hqr
  have huα := mul_lt_mul_of_pos_left hα.2 hqr
  have hqτ : (q : ℝ) + 1 ≤ τ := by linarith
  have hl : (-1 : ℝ) < a := by
    have hh : (q : ℝ) / τ + 1 / τ ≤ 1 := by
      rw [← add_div, div_le_one ht]
      exact hqτ
    have hm : (q : ℝ) * (-1 / τ) = -(q : ℝ) / τ := by ring
    rw [hm, neg_div] at hlα
    linarith
  have hu : (a : ℝ) < q := by
    have hh : 1 / τ ≤ (q : ℝ) / τ := div_le_div_of_nonneg_right (by exact_mod_cast hq) ht.le
    have hm : (q : ℝ) * (1 - 1 / τ) = q - (q : ℝ) / τ := by ring
    rw [hm] at huα
    linarith
  have ha0 : 0 ≤ a := by exact_mod_cast (show (-1 : ℤ) < a by exact_mod_cast hl)
  have haq : a < (q : ℤ) := by exact_mod_cast hu
  have hac : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
  have hc : Nat.Coprime a.toNat q := by
    apply IsCoprime.natCoprime
    simpa only [hac] using hcop
  have haqr : a.toNat < q := by omega
  have her : |α - (a.toNat : ℝ) / q| ≤ 1 / ((q : ℝ) * τ) := by
    simpa only [show (a.toNat : ℝ) = (a : ℝ) by exact_mod_cast hac] using herr
  exact (not_lt_of_ge hqQ)
    (priv_denominator_gt_Q Q τ α q a.toNat hminor hq haqr hc her)

/-- Dirichlet approximation with both required error bounds and an integer
numerator, on the minor arcs. -/
private theorem priv_minor_arc_approximation (Q τ α : ℝ)
    (hQ : 0 ≤ Q) (hτ : Q + 1 ≤ τ) (ht : 1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1 / τ) (1 - 1 / τ)) (hminor : α ∉ majorArcs Q τ) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ Q < (q : ℝ) ∧ (q : ℝ) ≤ τ ∧
      IsCoprime a (q : ℤ) ∧
      |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * τ) ∧
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hfloor : 0 < ⌊τ⌋₊ := by
    have hh : 1 ≤ ⌊τ⌋₊ := Nat.le_floor (by simpa using ht)
    omega
  obtain ⟨r, herr, hr⟩ := Real.exists_rat_abs_sub_le_and_den_le α hfloor
  have hq : 1 ≤ r.den := Rat.pos r
  have hqt : (r.den : ℝ) ≤ τ :=
    (show (r.den : ℝ) ≤ ⌊τ⌋₊ by exact_mod_cast hr).trans (Nat.floor_le (by linarith))
  have htf : τ ≤ (⌊τ⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one τ).le
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast Rat.pos r
  have he : |α - (r.num : ℝ) / r.den| ≤ 1 / ((r.den : ℝ) * τ) := by
    rw [← Rat.cast_def]
    apply herr.trans
    apply one_div_le_one_div_of_le (mul_pos hqr (by linarith))
    nlinarith
  have he2 : |α - (r.num : ℝ) / r.den| ≤ 1 / (r.den : ℝ) ^ 2 := by
    apply he.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hqr)
    nlinarith
  exact ⟨r.num, r.den, hq,
    priv_integer_denominator_gt_Q Q τ α r.den r.num hQ hτ hα hminor hq r.isCoprime_num_den he,
    hqt, r.isCoprime_num_den, he, he2⟩

/-- The major arc parameters obey the separation condition from some point on. -/
private theorem priv_eventual_minor_arc_parameters (A : ℝ) (hA : 0 ≤ A) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧ Qof A N + 1 ≤ τof A N := by
  have he := (isLittleO_log_rpow_rpow_atTop (40 * A) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.mp he
  refine ⟨max X₀ (Real.exp 2), ?_⟩
  intro N hN
  have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := (Real.exp_pos 2).trans_le hNe
  have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hL0 : 0 < Real.log N := by linarith
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have hbound := hX (N : ℝ) ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _), abs_of_pos hN0] at hbound
  have hQsq : Qof A N ^ 2 = Real.log N ^ (40 * A) := by
    rw [Qof, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
    congr 1
    ring
  refine ⟨hL, ?_⟩
  unfold τof
  apply (le_div_iff₀ hQ0).mpr
  rw [← hQsq] at hbound
  nlinarith


/-- Tolev page 72 Lemma 7 part ii in the phase cap form: the reciprocal phase sum
at a good rational approximation. -/
private theorem priv_phase_sum_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ))
    {α x : ℝ} (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (hx : 0 ≤ x) (T : ℕ) :
    ∑ n ∈ Icc 1 T, (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) ≤
      12 * (2 * x / q + T + q) * (1 + Real.log q + Real.log T) + T := by
  calc
    _ ≤ ∑ n ∈ Icc 1 T, (G (2 * x / n) (α * n) + 1) :=
      sum_le_sum (fun n hn => phcap_le_G_add_one α x n)
    _ = (∑ n ∈ Icc 1 T, G (2 * x / n) (α * n)) + T := by
      rw [sum_add_distrib]
      simp
    _ ≤ _ := add_le_add (sum_G_div_le hq hcop hα T (by positivity : 0 ≤ 2 * x)) le_rfl

/-- The product cutoff keeps the full logarithmic saving in the Type I shell. -/
private theorem priv_shell_product_bound (A : ℝ) (N : ℕ) (x M H : ℝ)
    (hA : 10000 ≤ A) (hN : (1 : ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hx : 0 < x) (hxN : x ≤ N) (hM : 0 < M) (hH : 0 < H)
    (hMH : M * H ≤ 2 * x) (hHlo : x ^ ((249 : ℝ) / 500) ≤ H) :
    let T := ⌊2 * M⌋₊ * cutoff3 (10000 * A) N
    (T : ℝ) ≤ 4 * N * Real.log N ^ (-10000 * A) ∧
    (T : ℝ) ≤ N ∧
    (T : ℝ) ≤ 4 * N * Real.log N ^ (-20 * A) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hp : 0 < x ^ ((249 : ℝ) / 500) := Real.rpow_pos_of_pos hx _
  have hmp : M * x ^ ((249 : ℝ) / 500) ≤ 2 * x :=
    (mul_le_mul_of_nonneg_left hHlo hM.le).trans hMH
  have hm : M ≤ 2 * x ^ ((251 : ℝ) / 500) := by
    have hh : M ≤ 2 * x / x ^ ((249 : ℝ) / 500) := (le_div_iff₀ hp).mpr hmp
    convert hh using 1
    rw [mul_div_assoc]
    congr 1
    simpa only [show (1 : ℝ) - (249 : ℝ) / 500 = (251 : ℝ) / 500 by norm_num,
      Real.rpow_one] using Real.rpow_sub hx 1 ((249 : ℝ) / 500)
  have hmN : M ≤ 2 * (N : ℝ) ^ ((251 : ℝ) / 500) :=
    hm.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx.le hxN (by norm_num)) (by norm_num))
  have hf : (⌊2 * M⌋₊ : ℝ) ≤ 2 * M := Nat.floor_le (by positivity)
  have hk : (cutoff3 (10000 * A) N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-10000 * A) := by
    unfold cutoff3
    have hh := Nat.floor_le (show 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-(10000 * A))
      by positivity)
    simpa only [neg_mul] using hh
  have hfirst : ((⌊2 * M⌋₊ * cutoff3 (10000 * A) N : ℕ) : ℝ) ≤
      4 * (N : ℝ) * Real.log N ^ (-10000 * A) := by
    push_cast
    calc
      _ ≤ (2 * M) * ((N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-10000 * A)) :=
        mul_le_mul hf hk (Nat.cast_nonneg _) (by positivity)
      _ ≤ (2 * (2 * (N : ℝ) ^ ((251 : ℝ) / 500))) *
            ((N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-10000 * A)) := by
        gcongr
      _ = 4 * (N : ℝ) ^ ((1253 : ℝ) / 1500) * Real.log N ^ (-10000 * A) := by
        rw [show (1253 : ℝ) / 1500 = (251 : ℝ) / 500 + 1 / 3 by norm_num, Real.rpow_add hN0]
        ring
      _ ≤ _ := by
        have hh : (N : ℝ) ^ ((1253 : ℝ) / 1500) ≤ N := by
          convert Real.rpow_le_rpow_of_exponent_le hN (show (1253 : ℝ) / 1500 ≤ 1 by norm_num) using 1 <;> simp
        gcongr
  have hs : Real.log N ^ (-10000 * A) ≤ (1 : ℝ) / 4 := by
    calc
      _ ≤ Real.log N ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
      _ = 1 / 4 := by norm_num
  refine ⟨hfirst, ?_, ?_⟩
  · calc
      _ ≤ 4 * (N : ℝ) * Real.log N ^ (-10000 * A) := hfirst
      _ ≤ 4 * (N : ℝ) * (1 / 4) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  · apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)

/-- The rational approximation mass estimate with the exact third cutoff saving. -/
private theorem priv_phase_mass_from_approx (A : ℝ) (N T q : ℕ) (a : ℤ) (α x : ℝ)
    (hA : 0 ≤ A) (hN : 0 < (N : ℝ)) (hL : 2 ≤ Real.log N)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hTN : T ≤ N)
    (hTS : (T : ℝ) ≤ 4 * N * Real.log N ^ (-20 * A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q : ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q : ℤ)) (herr : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ∑ n ∈ Icc 1 T, (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) ≤
      256 * N * Real.log N ^ (1 - 20 * A) := by
  let s : ℝ := N * Real.log N ^ (-20 * A)
  have hL0 : 0 < Real.log N := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have ht : τof A N = s := by
    dsimp [τof, Qof, s]
    rw [show -20 * A = -(20 * A) by ring, Real.rpow_neg hL0.le, div_eq_mul_inv]
  have hqS : (q : ℝ) ≤ s := by rwa [ht] at hqτ
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqN : (q : ℝ) ≤ N := hqτ.trans (div_le_self hN.le hQ)
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hq0 hqN
  have hlogT : Real.log T ≤ Real.log N := by
    by_cases hT : T = 0
    · simp [hT]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast hTN)
  have hlog : 1 + Real.log q + Real.log T ≤ 3 * Real.log N := by linarith
  have hlog0 : 0 ≤ 1 + Real.log q + Real.log T := by positivity
  have hNq : (N : ℝ) / q ≤ s := by
    calc
      _ ≤ (N : ℝ) / Qof A N := div_le_div_of_nonneg_left hN.le hQ0 hqQ.le
      _ = s := ht
  have hxq : 2 * x / q ≤ 2 * s := by
    calc
      _ = 2 * (x / q) := by ring
      _ ≤ 2 * ((N : ℝ) / q) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hxN hq0.le) (by norm_num)
      _ ≤ 2 * s := mul_le_mul_of_nonneg_left hNq (by norm_num)
  have hT : (T : ℝ) ≤ 4 * s := by simpa only [s, mul_assoc] using hTS
  have hcoef : 2 * x / q + T + q ≤ 7 * s := by linarith
  have hm := priv_phase_sum_le hq hcop herr hx T
  apply hm.trans
  have hprod := mul_le_mul hcoef hlog hlog0 (by positivity : 0 ≤ 7 * s)
  have hbound : 12 * (2 * x / q + T + q) * (1 + Real.log q + Real.log T) + T ≤
      256 * s * Real.log N := by
    nlinarith [mul_nonneg hs (show 0 ≤ Real.log N - 1 by linarith)]
  apply hbound.trans_eq
  dsimp [s]
  rw [show (1 - 20 * A) = (-20 * A) + (1 : ℝ) by ring, Real.rpow_add hL0, Real.rpow_one]
  ring


/-! ### The divisor moment and the Cauchy step of display 65 -/

/-- Tolev page 72 Lemma 8 part iii for convolution powers of zeta.  This is
Decomp310b's `zeta_power_reciprocal`, restated inside this file. -/
private theorem priv_zeta_power_reciprocal (k N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) / n ≤ Hn N ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_div, zero_div, sum_ite_eq', pow_zero]
    split_ifs <;> norm_num
  | succ k ih =>
    have hpoint : ∀ n ∈ Icc 1 N,
        (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) / n =
          ∑ d ∈ Icc 1 N, if d ∣ n then (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) / n else 0 := by
      intro n hn
      rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.cast_sum, sum_div,
        divisors_eq_filter N n hn, sum_filter]
    have he : (∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) / n) =
        ∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) *
          ∑ n ∈ (Icc 1 N).filter (d ∣ ·), (n : ℝ)⁻¹ := by
      rw [sum_congr rfl hpoint, sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    rw [he]
    calc
      _ ≤ ∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) * (Hn N / d) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (sum_inv_multiples_le N d (mem_Icc.mp hd).1)
          (Nat.cast_nonneg _)
      _ = (∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) / d) * Hn N := by
        rw [sum_mul]
        apply sum_congr rfl
        intro d hd
        ring
      _ ≤ Hn N ^ k * Hn N := mul_le_mul_of_nonneg_right ih (Hn_nonneg N)
      _ = _ := (pow_succ _ _).symm

/-- A joint multiset has arbitrary prescribed marginals: the local factor
comparison behind Lemma 8 part i. -/
private theorem priv_multichoose_mul_le (k l e : ℕ) :
    Nat.multichoose k e * Nat.multichoose l e ≤ Nat.multichoose (k * l) e := by
  classical
  have hs : ∀ e, Function.Surjective (fun s : Sym (Fin k × Fin l) e =>
      (s.map Prod.fst, s.map Prod.snd)) := by
    intro e
    induction e with
    | zero =>
      intro st
      exact ⟨Sym.nil, Subsingleton.elim _ _⟩
    | succ e ih =>
      rintro ⟨s, t⟩
      obtain ⟨a, s, rfl⟩ := Sym.exists_eq_cons_of_succ s
      obtain ⟨b, t, rfl⟩ := Sym.exists_eq_cons_of_succ t
      obtain ⟨u, hu⟩ := ih (s, t)
      have hu1 : Sym.map Prod.fst u = s := congrArg Prod.fst hu
      have hu2 : Sym.map Prod.snd u = t := congrArg Prod.snd hu
      refine ⟨Sym.cons (a, b) u, ?_⟩
      apply Prod.ext
      · simp only [Sym.map_cons]
        rw [hu1]
      · simp only [Sym.map_cons]
        rw [hu2]
  have hc := Fintype.card_le_of_surjective _ (hs e)
  simpa only [Fintype.card_prod, Sym.card_sym_eq_multichoose, Fintype.card_fin] using hc

/-- The local ordered divisor count is a multiset count. -/
private theorem priv_zeta_power_prime_pow (k p e : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.zeta ^ (k + 1)) (p ^ e) = Nat.multichoose (k + 1) e := by
  induction k generalizing e with
  | zero =>
    simp [ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ hp.ne_zero), Nat.multichoose_one]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
    rw [show k + 1 + 1 + e - 1 = e + (k + 1) by omega]
    exact Nat.choose_symm_add.symm

/-- The finite convolution regrouping of display 65. -/
private theorem priv_convolution_reduction (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (L U K : ℕ) :
    ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, F (m * k) ≤
      ∑ n ∈ Icc 1 (U * K), (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n := by
  classical
  by_cases hU : U = 0
  · subst U; simp
  by_cases hK : K = 0
  · subst K; simp
  let T := U * K
  have hUT : U ≤ T := Nat.le_mul_of_pos_right U (Nat.pos_of_ne_zero hK)
  have hKT : K ≤ T := Nat.le_mul_of_pos_left K (Nat.pos_of_ne_zero hU)
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 T) :
      (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n =
        ∑ p ∈ (Ioc 0 T ×ˢ Ioc 0 T).filter (fun p : ℕ × ℕ => p.1 * p.2 = n),
          (tau5 p.1 : ℝ) * F n := by
    rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_succ, ArithmeticFunction.mul_apply,
      Nat.cast_sum, sum_mul]
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by have := (mem_Icc.mp hn).1; omega)
      (mem_Icc.mp hn).2]
    apply sum_congr rfl
    intro p hp
    have hp0 : p.2 ≠ 0 := by
      have := (mem_Ioc.mp (mem_product.mp (mem_filter.mp hp).1).2).1; omega
    simp [tau5, ArithmeticFunction.zeta_apply, hp0]
  have he : (∑ n ∈ Icc 1 T, (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n) =
      ∑ p ∈ (Ioc 0 T ×ˢ Ioc 0 T).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ T),
        (tau5 p.1 : ℝ) * F (p.1 * p.2) := by
    rw [sum_congr rfl hpoint]
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    have hpos : 0 < p.1 * p.2 :=
      Nat.mul_pos (mem_Ioc.mp (mem_product.mp hp).1).1 (mem_Ioc.mp (mem_product.mp hp).2).1
    simp only [sum_ite_eq, mem_Icc]
    by_cases hh : p.1 * p.2 ≤ T
    · simp [hh, show 1 ≤ p.1 * p.2 by omega]
    · simp [hh]
  simp_rw [mul_sum]
  rw [he, ← sum_product']
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hm, hk⟩ := mem_product.mp hp
    have hm' := mem_Ioc.mp hm
    have hk' := mem_Icc.mp hk
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨by omega, hm'.2.trans hUT⟩,
      mem_Ioc.mpr ⟨by omega, hk'.2.trans hKT⟩⟩, Nat.mul_le_mul hm'.2 hk'.2⟩
  · intro p hp hnot
    exact mul_nonneg (Nat.cast_nonneg _) (hF _)

/-- The joint multiset majorant for the squared sixth divisor coefficient. -/
private theorem priv_zeta6_sq_le_zeta36_nat (n : ℕ) :
    (ArithmeticFunction.zeta ^ 6) n ^ 2 ≤ (ArithmeticFunction.zeta ^ 36) n := by
  have hm6 : (ArithmeticFunction.zeta ^ 6).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.pow
  have hm36 : (ArithmeticFunction.zeta ^ 36).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.pow
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p e hp
    change (ArithmeticFunction.zeta ^ (5 + 1)) (p ^ e) ^ 2 ≤
      (ArithmeticFunction.zeta ^ (35 + 1)) (p ^ e)
    rw [priv_zeta_power_prime_pow 5 p e hp, priv_zeta_power_prime_pow 35 p e hp]
    simpa only [pow_two] using priv_multichoose_mul_le 6 6 e
  · intro a b ha hb hab hIa hIb
    change ((ArithmeticFunction.zeta ^ 6) (a * b)) ^ 2 ≤ (ArithmeticFunction.zeta ^ 36) (a * b)
    rw [hm6.map_mul_of_coprime hab, hm36.map_mul_of_coprime hab, mul_pow]
    exact Nat.mul_le_mul hIa hIb

/-- The same pointwise comparison after casting to real coefficients. -/
private theorem priv_zeta6_sq_le_zeta36 (n : ℕ) :
    (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) ^ 2 ≤
      (((ArithmeticFunction.zeta ^ 36) n : ℕ) : ℝ) :=
  by exact_mod_cast priv_zeta6_sq_le_zeta36_nat n

/-- The reciprocal squared sixth divisor moment in the scalar Cauchy step. -/
private theorem priv_zeta6_sq_reciprocal (N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) ^ 2 / n ≤
      Hn N ^ 36 := by
  apply le_trans (sum_le_sum (fun n hn =>
    div_le_div_of_nonneg_right (priv_zeta6_sq_le_zeta36 n) (Nat.cast_nonneg n)))
  exact priv_zeta_power_reciprocal 36 N

/-- The weighted finite Cauchy step of display 65, retaining the count one. -/
private theorem priv_weighted_phase_cauchy (a : ℕ → ℝ) (T : ℕ) (α x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Icc 1 T, a n * (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖))) ^ 2 ≤
      (∑ n ∈ Icc 1 T, (a n) ^ 2 / n) *
        ((2 * x + T) * ∑ n ∈ Icc 1 T, (if ee (α * n) = 1 then 2 * x / n + 1
          else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖))) := by
  let f : ℕ → ℝ := fun n => (a n) ^ 2 / n
  let g : ℕ → ℝ := fun n => (n : ℝ) * (if ee (α * n) = 1 then 2 * x / n + 1
      else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) ^ 2
  have hc : (∑ n ∈ Icc 1 T, a n * (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖))) ^ 2 ≤
      (∑ n ∈ Icc 1 T, f n) * (∑ n ∈ Icc 1 T, g n) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro n hn
      dsimp [f]
      positivity
    · intro n hn
      dsimp [g]
      positivity
    · intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)
      dsimp [f, g]
      apply le_of_eq
      field_simp
  have hg : (∑ n ∈ Icc 1 T, g n) ≤ (2 * x + T) * ∑ n ∈ Icc 1 T,
      (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.mp hn).1; omega)
    have hnT : (n : ℝ) ≤ T := by exact_mod_cast (mem_Icc.mp hn).2
    have hp := phcap_nonneg α x n hx
    have hcap : (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) - 1 ≤ 2 * x / n := by
      linarith [phcap_le_count α x n]
    have hcap' := (le_div_iff₀ hn0).mp hcap
    have hh : (n : ℝ) * (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) ≤ 2 * x + T := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hh hp
    dsimp [g]
    nlinarith
  exact hc.trans (mul_le_mul_of_nonneg_left hg (sum_nonneg (fun n hn => by dsimp [f]; positivity)))

/-- The finite rectangle bound after Cauchy and the proved coefficient moment. -/
private theorem priv_rectangle_phase_sq_le (L U K : ℕ) (α x : ℝ) (hx : 0 ≤ x) :
    (∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K,
        (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
          else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖))) ^ 2 ≤
      Hn (U * K) ^ 36 * ((2 * x + (U * K : ℕ)) *
        ∑ n ∈ Icc 1 (U * K), (if ee (α * n) = 1 then 2 * x / n + 1
          else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖))) := by
  have hconv := priv_convolution_reduction
    (fun n => (if ee (α * n) = 1 then 2 * x / n + 1
      else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)))
    (fun n => phcap_nonneg α x n hx) L U K
  have hconv' : ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K,
      (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
        else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) ≤
      ∑ n ∈ Icc 1 (U * K), (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) *
        (if ee (α * n) = 1 then 2 * x / n + 1
          else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) := by
    simpa only [Nat.cast_mul] using hconv
  have hpos : 0 ≤ ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K,
      (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
        else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
    apply sum_nonneg
    intro m hm
    apply mul_nonneg (Nat.cast_nonneg _)
    exact sum_nonneg (fun k hk => phcap_nonneg α x (m * k) hx)
  apply (pow_le_pow_left₀ hpos hconv' 2).trans
  apply (priv_weighted_phase_cauchy (fun n => (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ))
    (U * K) α x hx).trans
  apply mul_le_mul_of_nonneg_right (priv_zeta6_sq_reciprocal (U * K))
  exact mul_nonneg (by positivity)
    (sum_nonneg (fun n hn => phcap_nonneg α x n hx))


/-- The scalar Cauchy estimate fits the target exponent with an absolute constant. -/
private theorem priv_rectangle_phase_of_mass (A : ℝ) (N : ℕ) (α x : ℝ) (L U K : ℕ)
    (hA : 10000 ≤ A) (hN : 0 < N) (hL : 2 ≤ Real.log N)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hT : U * K ≤ N)
    (hmass : ∑ n ∈ Icc 1 (U * K), (if ee (α * n) = 1 then 2 * x / n + 1
        else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) ≤
      256 * (N : ℝ) * Real.log N ^ (1 - 20 * A)) :
    ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K,
        (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
          else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) ≤
      (2 : ℝ) ^ 30 * N * Real.log N ^ (328 - 4 * A) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLp : 0 < Real.log N := by linarith
  have hTc : (U * K : ℕ) ≤ (N : ℝ) := by exact_mod_cast hT
  have hlog : Real.log (U * K : ℕ) ≤ Real.log N := by
    by_cases ht0 : U * K = 0
    · simp only [ht0, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ht0) hTc
  have hH : Hn (U * K) ≤ 2 * Real.log N := (Hn_le _).trans (by linarith)
  have hHp : Hn (U * K) ^ 36 ≤ (2 * Real.log N) ^ 36 :=
    pow_le_pow_left₀ (Hn_nonneg _) hH 36
  have hcount : 2 * x + (U * K : ℕ) ≤ 3 * (N : ℝ) := by linarith
  have hmass0 : 0 ≤ ∑ n ∈ Icc 1 (U * K), (if ee (α * n) = 1 then 2 * x / n + 1
      else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) :=
    sum_nonneg (fun n hn => phcap_nonneg α x n hx)
  have hs := priv_rectangle_phase_sq_le L U K α x hx
  have hs' : (∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K,
      (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
        else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖))) ^ 2 ≤
      (2 * Real.log N) ^ 36 * (3 * (N : ℝ) * (256 * (N : ℝ) * Real.log N ^ (1 - 20 * A))) := by
    apply hs.trans
    apply mul_le_mul hHp _ (by positivity) (by positivity)
    exact mul_le_mul hcount hmass hmass0 (by positivity)
  have heq : (2 * Real.log N) ^ 36 * (3 * (N : ℝ) * (256 * (N : ℝ) * Real.log N ^ (1 - 20 * A))) =
      (768 * (2 : ℝ) ^ 36) * (N : ℝ) ^ 2 * Real.log N ^ (37 - 20 * A) := by
    rw [show (37 - 20 * A) = (36 : ℝ) + (1 - 20 * A) by ring, Real.rpow_add hLp,
      show Real.log N ^ (36 : ℝ) = Real.log N ^ (36 : ℕ) from Real.rpow_natCast _ 36]
    ring
  rw [heq] at hs'
  have hexp : Real.log N ^ (37 - 20 * A) ≤ Real.log N ^ (656 - 8 * A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hcoeff : 768 * (2 : ℝ) ^ 36 ≤ (2 : ℝ) ^ 60 := by norm_num
  have hb : (768 * (2 : ℝ) ^ 36) * (N : ℝ) ^ 2 * Real.log N ^ (37 - 20 * A) ≤
      (2 : ℝ) ^ 60 * (N : ℝ) ^ 2 * Real.log N ^ (656 - 8 * A) := by
    gcongr
  have hsq : ((2 : ℝ) ^ 30 * N * Real.log N ^ (328 - 4 * A)) ^ 2 =
      (2 : ℝ) ^ 60 * (N : ℝ) ^ 2 * Real.log N ^ (656 - 8 * A) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (Real.log N ^ (328 - 4 * A)) 2,
      ← Real.rpow_mul hLp.le]
    congr 1
    · norm_num
    · congr 1; ring
  have hB : 0 ≤ (2 : ℝ) ^ 30 * N * Real.log N ^ (328 - 4 * A) := by positivity
  have hh := hs'.trans hb
  rw [← hsq] at hh
  nlinarith

/-- The scalar phase average of display 65. -/
private theorem priv_phase_average :
    ∀ A : ℝ, 10 ^ 4 ≤ A →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N),
          α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M H : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → 0 < H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) *
            ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N),
              (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
                else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) ≤
              C * N * Real.log N ^ (328 - 4 * A) := by
  intro A hA
  obtain ⟨N₀, hN₀⟩ := priv_eventual_minor_arc_parameters A (by linarith)
  refine ⟨(2 : ℝ) ^ 30, N₀, by positivity, ?_⟩
  intro N hodd hNN α hα hminor x M H hxlo hxN hx hM hH hprodlo hprodhi hsize
  obtain ⟨hL, hτ⟩ := hN₀ N hNN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hQ : 0 ≤ Qof A N := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  obtain ⟨a, q, hq, hqQ, hqτ, hcop, herr, herr2⟩ :=
    priv_minor_arc_approximation (Qof A N) (τof A N) α hQ hτ (by linarith) hα hminor
  have hprod := priv_shell_product_bound A N x M H (by norm_num at hA ⊢; exact hA)
    hN1 hL (by linarith) hxN hM hH hprodhi hsize
  have hTN : ⌊2 * M⌋₊ * cutoff3 (10000 * A) N ≤ N := by exact_mod_cast hprod.2.1
  have hmass := priv_phase_mass_from_approx A N (⌊2 * M⌋₊ * cutoff3 (10000 * A) N) q a α x
    (by linarith) hNpos hL (by linarith) hxN hTN hprod.2.2 hq hqQ hqτ hcop herr2
  have hres := priv_rectangle_phase_of_mass A N α x ⌊M⌋₊ ⌊2 * M⌋₊ (cutoff3 (10000 * A) N)
    (by norm_num at hA ⊢; exact hA) (by exact_mod_cast hNpos) hL
    (by linarith) hxN hTN hmass
  norm_num only [show (10 : ℝ) ^ 4 = 10000 by norm_num] at *
  exact hres

/-- Tolev 1999 page 86 display 65, the unweighted inner progression sum.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. Proved. -/
theorem constant_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun _ => 1) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := priv_phase_average A hA
  refine ⟨C, max N₀ 3, hC, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by have := (le_max_right N₀ 3).trans hN; linarith)]
    exact Real.exp_one_lt_d9.le.trans (by have := (le_max_right N₀ 3).trans hN; linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N),
    (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
      else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖))
  have hP : ∀ m, 0 ≤ P m := fun m =>
    sum_nonneg (fun k hk => phcap_nonneg α x (m * k) (by linarith))
  have hr : ∀ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
      ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun _ => 1) m‖ ≤ P m := by
    intro m hm
    exact row_le_phase lam l₃ _ N m α x H H₁ hlam
      (by have := (mem_Ioc.mp hm).1; omega) (by linarith)
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have ht := mul_le_mul_of_nonneg_left (hr m hm)
        (show 0 ≤ (tau5 m : ℝ) * Real.log N by positivity)
      nlinarith
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m)))
        hL0.le
    _ ≤ Real.log N * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' hL0.le
    _ = C * N * Real.log N ^ (329 - 4 * A) := by
      rw [show (329 - 4 * A) = (1 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

/-- Tolev 1999 page 86 display 66, the Abel summation variant.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. Proved. -/
theorem logarithmic_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := priv_phase_average A hA
  refine ⟨8 * C, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N),
    (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
      else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖))
  have hP : ∀ m, 0 ≤ P m := fun m =>
    sum_nonneg (fun k hk => phcap_nonneg α x (m * k) (by linarith))
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have hrow := log_row_le_phase lam l₃ (cutoff3 (10 ^ 4 * A) N) N m α x M M₁ H H₁ hlam
        hN3 (by linarith) hxhi hM hM₁ hH hHH₁ hH₁ hprodhi hm
      calc (tau5 m : ℝ) * Real.log N *
            ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖
          ≤ (tau5 m : ℝ) * Real.log N * (8 * Real.log N * P m) :=
            mul_le_mul_of_nonneg_left hrow (by positivity)
        _ = 8 * Real.log N ^ 2 * ((tau5 m : ℝ) * P m) := by ring
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m)))
        (by positivity)
    _ ≤ (8 * Real.log N ^ 2) * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' (by positivity)
    _ = _ := by
      rw [show (330 - 4 * A) = (2 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_two]
      ring

/-- The exact sealed Type I statement follows from the two row majorants.
Derived from constant_rows and logarithmic_rows. -/
theorem typeI_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (b = (fun _ => 1) ∨ b = (fun l : ℕ => (Real.log l : ℂ))) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := constant_rows A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := logarithmic_rows A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize a b ha hb
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  apply (bilinear_norm_le_rows lam l₃ _ N α x M M₁ H H₁ a b ha).trans
  rcases hb with rfl | rfl
  · apply (h₁ N hodd hN₁ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · apply (h₂ N hodd hN₂ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)

end LeanLab.Tolev2009.Decomp310a
