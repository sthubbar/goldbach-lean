module

public import LeanLab.Tolev2009.PublishedTheorem
public import LeanLab.PNTPort.Vinogradov.Count
public import LeanLab.Tolev2009.Sup83Heath
public import LeanLab.Tolev2009.Sup83Group

/-!
AI wrote this Lean code. Claude route burst 2026-11-12, split of Decomp83.minor_arc_sup_leaf.
Binary Goldbach is open.
Source: Tolev 2009, arXiv 0902.2669, page 4 display 12, supremum half.
Written proof: Tolev 1999 pages 71 and 82 to 87, Lemmas 4 and 12.
This file is a verbatim port of the leaf part of Decomp286b, which cannot be
imported by Decomp83 because Decomp286b itself imports Decomp83.
Only the namespace and the imports differ. typeI_estimate and typeII_estimate
carry full proofs. Route burst 7: prime_decomposition is now PROVED through the copied
Decomp424 chain below, the copied inputs in Sup83Heath and the new grouping in Sup83Group.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Sup83Split

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic
open LeanLab.HeathBrown1985
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

/-- The number of ordered factorizations into five positive integers, tau5 in display 53. -/
noncomputable def tau5 (n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ 5) n

/-- The weighted bilinear block of Tolev 1999 pages 82 to 83 displays 53 and 54.
The phase is alpha times m times l and the congruence is ml equal to l3 modulo k.
The coprime divisor weight is exactly the already defined weight in L2Bound. -/
noncomputable def bilinear (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      a m * b l * ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
    else 0

/-- Tolev 1999 displays 53 and 54, the divisor coefficient at one is nonzero. -/
theorem tau5_one : tau5 1 = 1 := by
  norm_num [tau5, pow_succ, ArithmeticFunction.mul_apply_one]

/-- Tolev 1999 displays 53 and 54, a nonzero instance of the adapted block.
This checks the block definition and does not witness either uniform estimate. -/
theorem bilinear_nonzero :
    bilinear (fun k => if k = 1 then 1 else 0) 1 1 6 0 3 (1 / 2) 1 3 6
      (fun m => if m = 1 then 1 else 0) (fun _ => 1) = 3 := by
  norm_num [bilinear, L2Bound.weight, ee_zero, Finset.sum_Ioc_succ_top]

/-
### Type I estimate (Tolev 1999 page 86 displays 64 to 66), PORTED

Everything from here to `constant_rows` is copied from `LeanLab.Tolev2009.Decomp310a`,
whose `typeI_estimate` has the same statement as the leaf below.  That module imports this
file, so it cannot be imported here and the development is reproduced instead.  The single
definition `row` of the source is written out at every use site (no new definition is
allowed here); every declaration below is `private` because it is only needed here.
The new import `LeanLab.PNTPort.Vinogradov.Count` supplies the large sieve factor
`four_dist0_le` and Vinogradov's `G`; its closure is fully proved.
-/

/-- Removing the first coefficient gives the row form of display 64. -/
private theorem bilinear_eq_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) :
    bilinear lam l₃ K N α x M M₁ H H₁ a b =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (b) l * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0)) := by
  unfold bilinear
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  split_ifs <;> ring

/-- The coefficient free majorant in display 64. No minor arc input is used. -/
private theorem bilinear_norm_le_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) :
    ‖bilinear lam l₃ K N α x M M₁ H H₁ a b‖ ≤
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        ((tau5 m : ℝ) * Real.log N) * ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (b) l * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ := by
  rw [bilinear_eq_rows]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro m hm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha m) (norm_nonneg _)

/-- The exact discrete Abel identity behind Tolev 1999 page 86 display 66.
It reduces each logarithmic row to constant rows with truncated upper endpoints.
No minor arc assumption or analytic row bound is used. -/
private theorem logarithmic_row_by_parts (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ) (m : ℕ)
    (hHH : ⌊H⌋₊ < ⌊H₁⌋₊) :
    ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then ((Real.log l : ℂ)) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0)) =
      (Real.log ⌊H₁⌋₊ : ℂ) * ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0)) -
      ∑ l ∈ Ioc ⌊H⌋₊ (⌊H₁⌋₊ - 1),
        ((Real.log (l + 1 : ℕ) : ℂ) - (Real.log l : ℂ)) *
          ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊((l : ℝ))⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0)) := by
  let c : ℕ → ℂ := fun l =>
    if ⌊H⌋₊ < l then
      if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
        ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
      else 0
    else 0
  have hG : ∀ t : ℕ, ∑ l ∈ range (t + 1), c l =
      ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊((t : ℝ))⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0)) := by
    intro t
    have hs : (range (t + 1)).filter (fun l => ⌊H⌋₊ < l) = Ioc ⌊H⌋₊ t := by
      ext l
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    simp only [c]
    rw [← sum_filter, hs]
    simp only [Nat.floor_natCast, one_mul]
  have hG0 : ∑ l ∈ range (⌊H⌋₊ + 1), c l = 0 := by
    rw [hG]
    simp only [Nat.floor_natCast, Ioc_self, sum_empty]
  have hh := sum_Ioc_by_parts (fun l : ℕ => (Real.log l : ℂ)) c hHH
  rw [hG0, smul_zero, sub_zero] at hh
  simp only [smul_eq_mul] at hh
  have hlhs : (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (Real.log l : ℂ) * c l) =
      ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then ((Real.log l : ℂ)) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0)) := by
    apply sum_congr rfl
    intro l hl
    simp only [c, ite_eq_left (mem_Ioc.mp hl).1, one_mul]
    split_ifs <;> ring
  rw [hlhs] at hh
  simp_rw [hG] at hh
  simpa only [Nat.floor_natCast] using hh

/-- The geometric progression step of Tolev 1999 page 86 display 64 and page 72 Lemma 6.
The denominator is kept as the exact complex distance from one.
No torus distance comparison or averaged Diophantine estimate is asserted. -/
private theorem progression_phase_bound (β θ : ℝ) (J : ℕ) (hθ : ee θ ≠ 1) :
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


/-- The reciprocal divisor moment used in Tolev 1999 page 72 Lemma 8 part iii.
At r equal to twelve it supplies the Cauchy factor in page 86 display 65.
PORTED from LeanLab.Tolev2009.Decomp310a. -/
private theorem divisor_power_reciprocal (r N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n ≤ Hn N ^ (2 ^ r) := by
  induction r generalizing N with
  | zero => simp [Hn]
  | succ r ih =>
    have hh := LeanLab.Tolev2009.DivisorMoment.reciprocal_step N r (2 ^ r) (fun M hM => ih M)
    simpa only [pow_succ, Nat.mul_comm] using hh


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
    ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤
      ∑ k ∈ Icc 1 K, (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
        else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
  classical
  let prog : ℕ → ℂ := fun k => ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
      (if (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧ (m * l) % k = l₃ % k
        then ee (α * (m * l : ℕ)) else 0)
  have hrow : ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0)) =
      ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃), (lam k : ℂ) * prog k := by
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
  calc ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖
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
      ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊((t : ℝ))⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤ B) :
    ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then ((Real.log l : ℂ)) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤
      2 * Real.log ⌊H₁⌋₊ * B := by
  let U := ⌊H₁⌋₊
  let L := ⌊H⌋₊
  have hLU : L < U := hHH
  have hU : 1 ≤ U := by omega
  have htop : ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤ B := by
    simpa only [Nat.floor_natCast] using hp U hLU le_rfl
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
  have hfirst : ‖(Real.log ⌊H₁⌋₊ : ℂ) * ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤
      Real.log U * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg _)]
    exact mul_le_mul_of_nonneg_left htop (Real.log_natCast_nonneg _)
  have hsecond : ‖∑ l ∈ Ioc ⌊H⌋₊ (⌊H₁⌋₊ - 1),
        ((Real.log (l + 1 : ℕ) : ℂ) - (Real.log l : ℂ)) *
          ((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊((l : ℝ))⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤ Real.log U * B := by
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
    ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then ((Real.log l : ℂ)) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤
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
        ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊((t : ℝ))⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) (K) ((m) * l) : ℂ) else 0))‖ ≤
          ∑ k ∈ Icc 1 K, (if ee (α * (m * k : ℕ)) = 1 then 2 * x / (m * k : ℕ) + 1
            else min (2 * x / (m * k : ℕ) + 1) (2 / ‖ee (α * (m * k : ℕ)) - 1‖)) := by
      intro t ht htu
      exact row_le_phase lam l₃ K N m α x H (t : ℝ) hlam hmp hx
    apply (log_row_prefix lam l₃ K N m α x H H₁ _ hP hHH hp).trans
    nlinarith [mul_le_mul_of_nonneg_right hlog hP]
  · have he : Ioc ⌊H⌋₊ ⌊H₁⌋₊ = ∅ := Ioc_eq_empty_of_le (le_of_not_gt hHH)
    simp only [he, sum_empty, norm_zero]
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

/-- PORTED from LeanLab.Tolev2009.Decomp310a (same statement, proved there).
Tolev 1999 page 86 display 65, the unweighted inner progression sum.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. -/
private theorem constant_rows :
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
              ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) ((cutoff3 (10 ^ 4 * A) (N))) ((m) * l) : ℂ) else 0))‖ ≤
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
      ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then (1) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) ((cutoff3 (10 ^ 4 * A) (N))) ((m) * l) : ℂ) else 0))‖ ≤ P m := by
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

/-- PORTED from LeanLab.Tolev2009.Decomp310a (same statement, proved there).
Tolev 1999 page 86 display 66, the Abel summation variant.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. -/
private theorem logarithmic_rows :
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
              ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then ((Real.log l : ℂ)) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) ((cutoff3 (10 ^ 4 * A) (N))) ((m) * l) : ℂ) else 0))‖ ≤
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
            ‖((∑ l ∈ Ioc ⌊(H)⌋₊ ⌊(H₁)⌋₊, if (x) < ((m) * l : ℕ) ∧ ((m) * l : ℕ) ≤ 2 * (x) ∧ (m) * l ≤ (N) then ((Real.log l : ℂ)) * ee ((α) * ((m) * l : ℕ)) * (L2Bound.weight (lam) (l₃) ((cutoff3 (10 ^ 4 * A) (N))) ((m) * l) : ℂ) else 0))‖
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

/-- Tolev 1999 page 86 displays 64 to 66, the two Type I estimates.
Adapted to Tolev 2009 display 12 with a fixed residue and the smaller modulus cutoff.
The shell x is at least N times log N to minus 4A. The first coefficient is normalised.
Both b equal to one and b equal to log l are included.
PROVED by the ported development above (statements agree byte for byte with
`LeanLab.Tolev2009.Decomp310a.typeI_estimate`, whose axioms are propext, choice, Quot.sound). -/
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

set_option exponentiation.threshold 2048 in
set_option maxHeartbeats 4000000 in
/-- Tolev 1999 pages 83 to 86 displays 55 to 63, the Type II estimate.
The same fixed residue and shell adaptation is required as in typeI_estimate.
Only bilinear sums with both coefficients normalised by tau5 times log N occur. Proved. -/
theorem typeII_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  let phaseCap : ℝ → ℝ → ℕ → ℝ := fun α x n =>
    if ee (α * n) = 1 then 2 * x / n + 1 else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)
  let row : (ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → ℕ → ℂ :=
    fun lam l₃ K N α x H H₁ b m =>
      ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
        if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
          b l * ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ) else 0
  let energy : (ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → ℝ :=
    fun lam l₃ K N α x M M₁ H H₁ b =>
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖row lam l₃ K N α x H H₁ b m‖ ^ 2
  let indices : ℕ → ℕ → ℝ → ℝ → Finset (ℕ × ℕ) :=
    fun l₃ K H H₁ => Ioc ⌊H⌋₊ ⌊H₁⌋₊ ×ˢ (Icc 1 K).filter (fun k => Nat.Coprime k l₃)
  let atom : ℕ → ℕ → ℝ → ℝ → ℕ → ℕ × ℕ → ℂ := fun l₃ N α x m i =>
    if (x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
        (m * i.1) % i.2 = l₃ % i.2 then ee (α * (m * i.1 : ℕ)) else 0
  let correlation : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℕ × ℕ → ℕ × ℕ → ℂ :=
    fun l₃ N α x M M₁ i j =>
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, atom l₃ N α x m i * starRingEnd ℂ (atom l₃ N α x m j)
  let diagonal : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun l₃ K N α x M M₁ H H₁ =>
    ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
      if i.1 = j.1 then (tau5 i.1 : ℝ) * tau5 j.1 * ‖correlation l₃ N α x M M₁ i j‖ else 0
  let offDiagonal : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun l₃ K N α x M M₁ H H₁ =>
    ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
      if i.1 ≠ j.1 then (tau5 i.1 : ℝ) * tau5 j.1 * ‖correlation l₃ N α x M M₁ i j‖ else 0
  let divisorPhase : ℝ → ℝ → ℕ → ℝ := fun α X T =>
    ∑ n ∈ Icc 1 T, (n.divisors.card : ℝ) ^ 5 * phaseCap α X n

  have phaseCap_unfold : ∀ (α x : ℝ) (n : ℕ), phaseCap α x n =
    (if ee (α * n) = 1 then 2 * x / n + 1 else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)) := by
    intro α x n
    exact   rfl

  have phaseCap_nonneg : ∀ (α x : ℝ) (n : ℕ) (hx : 0 ≤ x), 0 ≤ phaseCap α x n := by
    intro α x n hx
 
    rw [phaseCap_unfold]; exact phcap_nonneg α x n hx

  have phaseCap_le_count : ∀ (α x : ℝ) (n : ℕ), phaseCap α x n ≤ 2 * x / n + 1 := by
    intro α x n
 
    rw [phaseCap_unfold]; exact phcap_le_count α x n

  have phaseCap_sum_le : ∀ {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ))
    {α x : ℝ} (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (hx : 0 ≤ x) (T : ℕ), ∑ n ∈ Icc 1 T, phaseCap α x n ≤
      12 * (2 * x / q + T + q) * (1 + Real.log q + Real.log T) + T := by
    intro q hq a hcop α x hα hx T
 
    simpa only [phaseCap_unfold] using priv_phase_sum_le hq hcop hα hx T

  have weighted_phase_cauchy : ∀ (a : ℕ → ℝ) (T : ℕ) (α x : ℝ) (hx : 0 ≤ x), (∑ n ∈ Icc 1 T, a n * phaseCap α x n) ^ 2 ≤
      (∑ n ∈ Icc 1 T, (a n) ^ 2 / n) *
        ((2 * x + T) * ∑ n ∈ Icc 1 T, phaseCap α x n) := by
    intro a T α x hx
 
    simpa only [phaseCap_unfold] using priv_weighted_phase_cauchy a T α x hx

  have bilinear_eq_rows : ∀ (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ), bilinear lam l₃ K N α x M M₁ H H₁ a b =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * row lam l₃ K N α x H H₁ b m := by
    intro lam l₃ K N α x M M₁ H H₁ a b
 
    unfold bilinear row
    apply sum_congr rfl
    intro m hm
    rw [mul_sum]
    apply sum_congr rfl
    intro l hl
    split_ifs <;> ring

  have zeta_power_sum : ∀ (k N : ℕ), ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) ≤
      (N : ℝ) * Hn N ^ k := by
    intro k N
 
    have hi : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
    have he : (∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ)) =
        ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) * ((N / n : ℕ) : ℝ) := by
      have hh := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (ArithmeticFunction.zeta ^ k) N
      simp only [ArithmeticFunction.natCoe_nat, ← pow_succ, ← hi, Nat.cast_id] at hh
      exact_mod_cast hh
    rw [he]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) * ((N : ℝ) / n) := by
        apply sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg _)
      _ = (N : ℝ) * ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) / n := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (priv_zeta_power_reciprocal k N) (Nat.cast_nonneg N)

  have multichoose_mul_le : ∀ (k l e : ℕ), Nat.multichoose k e * Nat.multichoose l e ≤ Nat.multichoose (k * l) e := by
    intro k l e
 
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

  have zeta_power_prime_pow : ∀ (k p e : ℕ) (hp : p.Prime), (ArithmeticFunction.zeta ^ (k + 1)) (p ^ e) = Nat.multichoose (k + 1) e := by
    intro k p e hp
 
    induction k generalizing e with
    | zero =>
      simp [ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ hp.ne_zero), Nat.multichoose_one]
    | succ k ih =>
      rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
      simp_rw [ih]
      rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
      rw [show k + 1 + 1 + e - 1 = e + (k + 1) by omega]
      exact Nat.choose_symm_add.symm

  have tau5_sq_le_zeta25 : ∀ (n : ℕ), tau5 n ^ 2 ≤ (ArithmeticFunction.zeta ^ 25) n := by
    intro n
 
    have hm5 : (ArithmeticFunction.zeta ^ 5).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
    have hm25 : (ArithmeticFunction.zeta ^ 25).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
    refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
    · simp [tau5]
    · intro p e hp
      change (ArithmeticFunction.zeta ^ (4 + 1)) (p ^ e) ^ 2 ≤
        (ArithmeticFunction.zeta ^ (24 + 1)) (p ^ e)
      rw [zeta_power_prime_pow 4 p e hp, zeta_power_prime_pow 24 p e hp]
      simpa only [pow_two] using multichoose_mul_le 5 5 e
    · intro a b ha hb hab hIa hIb
      change ((ArithmeticFunction.zeta ^ 5) (a * b)) ^ 2 ≤ (ArithmeticFunction.zeta ^ 25) (a * b)
      rw [hm5.map_mul_of_coprime hab, hm25.map_mul_of_coprime hab, mul_pow]
      exact Nat.mul_le_mul hIa hIb

  have coefficient_mass : ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 3 ≤ N →
      ∀ M M₁ : ℝ, 0 < M → M ≤ M₁ → M₁ ≤ 2 * M → M ≤ 2 * N →
      ∀ a : ℕ → ℂ, (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
        (∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ ^ 2) ≤
          D * M * Real.log N ^ (26 : ℕ) := by
 
    refine ⟨2 * 5 ^ (24 : ℕ), by positivity, ?_⟩
    intro N hN M M₁ hM hMM₁ hM₁ hMN a ha
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hL : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    have hL0 : 0 ≤ Real.log N := by linarith
    let R : ℕ := ⌊2 * M⌋₊
    have hR : (R : ℝ) ≤ 2 * M := Nat.floor_le (by positivity)
    have hRN : (R : ℝ) ≤ 4 * N := by nlinarith
    have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    have hlogR : Real.log R ≤ Real.log (4 : ℝ) + Real.log N := by
      rcases Nat.eq_zero_or_pos R with hz | hp
      · simp only [hz, Nat.cast_zero, Real.log_zero]
        have h4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
        positivity
      · rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (N : ℝ) ≠ 0)]
        exact Real.log_le_log (by exact_mod_cast hp) hRN
    have hH : Hn R ≤ 5 * Real.log N := (Hn_le R).trans (by linarith)
    have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Icc 1 R := by
      intro m hm
      rcases mem_Ioc.mp hm with ⟨hm0, hm1⟩
      exact mem_Icc.mpr ⟨by omega, hm1.trans (Nat.floor_le_floor hM₁)⟩
    have ht : ∀ m, ‖a m‖ ^ 2 ≤ (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) := by
      intro m
      have hτ : (tau5 m : ℝ) ^ 2 ≤ (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) := by
        exact_mod_cast tau5_sq_le_zeta25 m
      calc
        _ ≤ ((tau5 m : ℝ) * Real.log N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (ha m) 2
        _ = (tau5 m : ℝ) ^ 2 * Real.log N ^ (2 : ℕ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hτ (sq_nonneg _)
    calc
      _ ≤ ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
          (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) :=
        sum_le_sum (fun m hm => ht m)
      _ ≤ ∑ m ∈ Icc 1 R,
          (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => by positivity)
      _ = (∑ m ∈ Icc 1 R, (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ)) *
          Real.log N ^ (2 : ℕ) := by rw [sum_mul]
      _ ≤ ((R : ℝ) * Hn R ^ (24 : ℕ)) * Real.log N ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right (zeta_power_sum 24 R) (sq_nonneg _)
      _ ≤ ((2 * M) * (5 * Real.log N) ^ (24 : ℕ)) * Real.log N ^ (2 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul hR (pow_le_pow_left₀ (Hn_nonneg R) hH 24) (by positivity) (by positivity)
      _ = _ := by ring

  have lcm_fiber_divisor_bound : ∀ (h K : ℕ), ∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h),
      (p.1.divisors.card : ℝ) * p.2.divisors.card ≤ (h.divisors.card : ℝ) ^ 4 := by
    intro h K
 
    by_cases hh : h = 0
    · subst h
      have he : (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = 0) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        rcases mem_filter.mp hp with ⟨hp, he⟩
        rcases mem_product.mp hp with ⟨hp1, hp2⟩
        have h1 := (mem_Icc.mp hp1).1
        have h2 := (mem_Icc.mp hp2).1
        exact (Nat.lcm_ne_zero (by omega) (by omega)) he
      rw [he]
      norm_num
    · have hs : (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h) ⊆
          h.divisors ×ˢ h.divisors := by
        intro p hp
        have he := (mem_filter.mp hp).2
        apply mem_product.mpr
        constructor
        · exact Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_left p.1 p.2, hh⟩
        · exact Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_right p.1 p.2, hh⟩
      calc
        _ ≤ ∑ p ∈ h.divisors ×ˢ h.divisors, (p.1.divisors.card : ℝ) * p.2.divisors.card :=
          sum_le_sum_of_subset_of_nonneg hs (fun p hp hn => by positivity)
        _ ≤ ∑ p ∈ h.divisors ×ˢ h.divisors, (h.divisors.card : ℝ) ^ 2 := by
          apply sum_le_sum
          intro p hp
          have hp1 := (mem_product.mp hp).1
          have hp2 := (mem_product.mp hp).2
          have hd1 : (p.1.divisors.card : ℝ) ≤ h.divisors.card := by
            exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hh (Nat.dvd_of_mem_divisors hp1))
          have hd2 : (p.2.divisors.card : ℝ) ≤ h.divisors.card := by
            exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hh (Nat.dvd_of_mem_divisors hp2))
          simpa only [pow_two] using mul_le_mul hd1 hd2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = _ := by
          simp only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul]
          ring

  have lcm_divisor_sum : ∀ (K : ℕ), ∑ p ∈ Icc 1 K ×ˢ Icc 1 K,
      ((p.1.divisors.card : ℝ) * p.2.divisors.card) / Nat.lcm p.1 p.2 ≤
        LeanLab.HeathBrown1985.Hn (K * K) ^ (16 : ℕ) := by
    intro K
 
    have hm : ∀ p ∈ Icc 1 K ×ˢ Icc 1 K, Nat.lcm p.1 p.2 ∈ Icc 1 (K * K) := by
      intro p hp
      rcases mem_product.mp hp with ⟨hp1, hp2⟩
      rcases mem_Icc.mp hp1 with ⟨h1, h1K⟩
      rcases mem_Icc.mp hp2 with ⟨h2, h2K⟩
      apply mem_Icc.mpr
      constructor
      · exact Nat.lcm_pos (by omega) (by omega)
      · exact (Nat.lcm_le_mul h1 h2).trans (Nat.mul_le_mul h1K h2K)
    have hf := sum_fiberwise_of_maps_to hm
      (fun p : ℕ × ℕ => ((p.1.divisors.card : ℝ) * p.2.divisors.card) / Nat.lcm p.1 p.2)
    rw [← hf]
    calc
      _ = ∑ h ∈ Icc 1 (K * K),
          (∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h),
            (p.1.divisors.card : ℝ) * p.2.divisors.card) / h := by
        apply sum_congr rfl
        intro h hh
        rw [sum_div]
        apply sum_congr rfl
        intro p hp
        rw [(mem_filter.mp hp).2]
      _ ≤ ∑ h ∈ Icc 1 (K * K), (h.divisors.card : ℝ) ^ (4 : ℕ) / h := by
        apply sum_le_sum
        intro h hh
        exact div_le_div_of_nonneg_right (lcm_fiber_divisor_bound h K) (Nat.cast_nonneg h)
      _ ≤ _ := by simpa only [show (2 : ℕ) ^ 4 = 16 by norm_num] using divisor_power_reciprocal 4 (K * K)

  have energy_nonneg : ∀ (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) (b : ℕ → ℂ), 0 ≤ energy lam l₃ K N α x M M₁ H H₁ b := by
    intro lam l₃ K N α x M M₁ H H₁ b
 
    unfold energy
    positivity

  have bilinear_sq_le_energy : ∀ (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ), ‖bilinear lam l₃ K N α x M M₁ H H₁ a b‖ ^ 2 ≤
      (∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ ^ 2) * energy lam l₃ K N α x M M₁ H H₁ b := by
    intro lam l₃ K N α x M M₁ H H₁ a b
 
    rw [bilinear_eq_rows]
    have ht : ‖∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * row lam l₃ K N α x H H₁ b m‖ ≤
        ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ * ‖row lam l₃ K N α x H H₁ b m‖ := by
      simpa only [norm_mul] using
        (norm_sum_le (Ioc ⌊M⌋₊ ⌊M₁⌋₊) (fun m => a m * row lam l₃ K N α x H H₁ b m))
    exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
      (sum_mul_sq_le_sq_mul_sq _ _ _)

  have row_eq_atoms : ∀ (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ)
    (b : ℕ → ℂ) (m : ℕ), row lam l₃ K N α x H H₁ b m =
      ∑ i ∈ indices l₃ K H H₁, (b i.1 * (lam i.2 : ℂ)) * atom l₃ N α x m i := by
    intro lam l₃ K N α x H H₁ b m
 
    classical
    simp only [indices, sum_product, row, L2Bound.weight, sum_filter,
      Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, mul_sum]
    apply sum_congr rfl
    intro l hl
    by_cases hc : x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N
    · simp only [hc, ite_true, atom, true_and]
      apply sum_congr rfl
      intro k hk
      split_ifs <;> simp_all; ring
    · simp only [hc, ite_false, atom, false_and, mul_zero, ite_self, sum_const_zero]

  have energy_eq_gram : ∀ (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ), (energy lam l₃ K N α x M M₁ H H₁ b : ℂ) =
      ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
        (b i.1 * (lam i.2 : ℂ)) * starRingEnd ℂ (b j.1 * (lam j.2 : ℂ)) *
          correlation l₃ N α x M M₁ i j := by
    intro lam l₃ K N α x M M₁ H H₁ b
 
    have hpoint (m : ℕ) :
        ((‖row lam l₃ K N α x H H₁ b m‖ ^ 2 : ℝ) : ℂ) =
          ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
            (b i.1 * (lam i.2 : ℂ)) * starRingEnd ℂ (b j.1 * (lam j.2 : ℂ)) *
              (atom l₃ N α x m i * starRingEnd ℂ (atom l₃ N α x m j)) := by
      rw [row_eq_atoms, sq_norm_eq_mul_conj, map_sum, sum_mul_sum]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [map_mul]
      ring
    simp only [energy, Complex.ofReal_sum, hpoint, correlation, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm]

  have diagonal_add_offDiagonal : ∀ (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ), diagonal l₃ K N α x M M₁ H H₁ + offDiagonal l₃ K N α x M M₁ H H₁ =
      ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
        (tau5 i.1 : ℝ) * tau5 j.1 * ‖correlation l₃ N α x M M₁ i j‖ := by
    intro l₃ K N α x M M₁ H H₁
 
    classical
    simp only [diagonal, offDiagonal, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    by_cases h : i.1 = j.1 <;> simp [h]

  have energy_le_correlations : ∀ (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) (hlam : ∀ k, |lam k| ≤ 1) (hL : 0 ≤ Real.log N)
    (hb : ∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N), energy lam l₃ K N α x M M₁ H H₁ b ≤
      Real.log N ^ (2 : ℕ) *
        (diagonal l₃ K N α x M M₁ H H₁ + offDiagonal l₃ K N α x M M₁ H H₁) := by
    intro lam l₃ K N α x M M₁ H H₁ b hlam hL hb
 
    have hc (i : ℕ × ℕ) : ‖b i.1 * (lam i.2 : ℂ)‖ ≤ (tau5 i.1 : ℝ) * Real.log N := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hlam i.2) (norm_nonneg _)).trans (by simpa using hb i.1)
    have he := congrArg norm (energy_eq_gram lam l₃ K N α x M M₁ H H₁ b)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energy_nonneg ..)] at he
    rw [he, diagonal_add_offDiagonal, mul_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i hi
    rw [mul_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro j hj
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc
      _ ≤ (((tau5 i.1 : ℝ) * Real.log N) * ((tau5 j.1 : ℝ) * Real.log N)) *
          ‖correlation l₃ N α x M M₁ i j‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul (hc i) (hc j) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hL)
      _ = _ := by ring

  have correlation_eq_phase : ∀ (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ), correlation l₃ N α x M M₁ i j =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        if ((x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
            (m * i.1) % i.2 = l₃ % i.2) ∧
           ((x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
            (m * j.1) % j.2 = l₃ % j.2) then
          ee (α * m * ((i.1 : ℝ) - j.1)) else 0 := by
    intro l₃ N α x M M₁ i j
 
    classical
    unfold correlation
    apply sum_congr rfl
    intro m hm
    by_cases hi : (x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
        (m * i.1) % i.2 = l₃ % i.2
    · by_cases hj : (x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
          (m * j.1) % j.2 = l₃ % j.2
      · simp only [atom, hi, hj, and_self, ite_true, conj_ee]
        rw [← ee_add]
        congr 1
        push_cast
        ring
      · simp only [atom, hi, hj, true_and, ite_true, ite_false, map_zero, mul_zero]
    · simp only [atom, hi, false_and, ite_false, zero_mul]

  have correlation_diagonal : ∀ (l₃ N : ℕ) (α x M M₁ : ℝ) (l k₁ k₂ : ℕ), correlation l₃ N α x M M₁ (l, k₁) (l, k₂) =
      (((Ioc ⌊M⌋₊ ⌊M₁⌋₊).filter (fun m =>
        (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
          (m * l) % k₁ = l₃ % k₁ ∧ (m * l) % k₂ = l₃ % k₂)).card : ℂ) := by
    intro l₃ N α x M M₁ l k₁ k₂
 
    rw [correlation_eq_phase]
    simp only [sub_self, mul_zero, ee_zero, ← sum_filter,
      sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext m
    simp only [mem_filter]
    tauto

  have diagonal_independent : ∀ (l₃ K N : ℕ) (α β x M M₁ H H₁ : ℝ), diagonal l₃ K N α x M M₁ H H₁ = diagonal l₃ K N β x M M₁ H H₁ := by
    intro l₃ K N α β x M M₁ H H₁
 
    classical
    unfold diagonal
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    by_cases h : i.1 = j.1
    · simp only [h, ite_true]
      obtain ⟨l, k₁⟩ := i
      obtain ⟨l', k₂⟩ := j
      dsimp at h
      subst l'
      rw [correlation_diagonal, correlation_diagonal]
    · simp only [h, ite_false]

  have scalar_nonneg : ∀ (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ), 0 ≤ diagonal l₃ K N α x M M₁ H H₁ ∧
      0 ≤ offDiagonal l₃ K N α x M M₁ H H₁ := by
    intro l₃ K N α x M M₁ H H₁
 
    simp only [diagonal, offDiagonal]
    constructor <;>
      apply sum_nonneg <;> intro i hi <;> apply sum_nonneg <;> intro j hj <;>
      split_ifs <;> positivity

  have distance_sum_le : ∀ (S : Finset ℕ) (U l : ℕ) (hl : l ≤ U)
    (hS : ∀ j ∈ S, j ≤ U) (F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r), ∑ j ∈ S, (if l ≠ j then F (Nat.dist l j) else 0) ≤
      2*∑ r ∈ Icc 1 U, F r := by
    intro S U l hl hS F hF
 
    classical
    have hlow : ∑ j ∈ S.filter (fun j => j<l), F (l-j) ≤ ∑ r ∈ Icc 1 U, F r := by
      have hi : Set.InjOn (fun j => l-j) (S.filter (fun j => j<l)) := by
        intro a ha b hb he
        dsimp only at he
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        omega
      rw [← sum_image hi]
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hr
        have hj' := (mem_filter.mp hj).2
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      · intro r hr hnot
        exact hF r
    have hhigh : ∑ j ∈ S.filter (fun j => l<j), F (j-l) ≤ ∑ r ∈ Icc 1 U, F r := by
      have hi : Set.InjOn (fun j => j-l) (S.filter (fun j => l<j)) := by
        intro a ha b hb he
        dsimp only at he
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        omega
      rw [← sum_image hi]
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hr
        have hj' := mem_filter.mp hj
        have hjU := hS j hj'.1
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      · intro r hr hnot
        exact hF r
    have he : (∑ j ∈ S, if l ≠ j then F (Nat.dist l j) else 0) =
        (∑ j ∈ S.filter (fun j => j<l), F (l-j)) +
        (∑ j ∈ S.filter (fun j => l<j), F (j-l)) := by
      simp only [sum_filter,← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rcases lt_trichotomy j l with h|h|h
      · simp [show l≠j by omega,h,show ¬l<j by omega,Nat.dist_eq_sub_of_le_right h.le]
      · subst j; simp
      · simp [show l≠j by omega,h,show ¬j<l by omega,Nat.dist_eq_sub_of_le h.le]
    rw [he]
    linarith

  have shifted_square_bound : ∀ (S : Finset ℕ) (U : ℕ) (hS : ∀ j ∈ S, j ≤ U)
    (a F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r), ∑ l ∈ S, ∑ j ∈ S, (if l ≠ j then a l*a j*F (Nat.dist l j) else 0) ≤
      2*(∑ l ∈ S, a l^2)*(∑ r ∈ Icc 1 U, F r) := by
    intro S U hS a F hF
 
    classical
    let B := ∑ r ∈ Icc 1 U, F r
    have hsquare : ∀ l j : ℕ,
        2*(if l≠j then a l*a j*F (Nat.dist l j) else 0) ≤
          a l^2*(if l≠j then F (Nat.dist l j) else 0) +
          a j^2*(if l≠j then F (Nat.dist l j) else 0) := by
      intro l j
      split_ifs with h
      · nlinarith [mul_nonneg (sq_nonneg (a l-a j)) (hF (Nat.dist l j))]
      · simp
    have hs := sum_le_sum (s:=S) (fun l hl => sum_le_sum (s:=S) (fun j hj => hsquare l j))
    have hsym : (∑ l ∈ S, ∑ j ∈ S, a j^2*(if l≠j then F (Nat.dist l j) else 0)) =
        ∑ l ∈ S, ∑ j ∈ S, a l^2*(if l≠j then F (Nat.dist l j) else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro l hl
      apply sum_congr rfl
      intro j hj
      simp [ne_comm,Nat.dist_comm]
    simp only [sum_add_distrib,← mul_sum] at hs
    rw [hsym] at hs
    simp only [← mul_sum] at hs
    have hb : (∑ l ∈ S, a l^2*∑ j ∈ S, if l≠j then F (Nat.dist l j) else 0) ≤
        (∑ l ∈ S, a l^2)*(2*B) := by
      rw [sum_mul]
      apply sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (distance_sum_le S U l (hS l hl) hS F hF) (sq_nonneg _)
    dsimp [B] at hb
    nlinarith

  have lcm_sum_bound : ∀ (K : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0≤F n), ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, F (Nat.lcm k₁ k₂) ≤
      ∑ h ∈ Icc 1 (K*K), (h.divisors.card:ℝ)^4*F h := by
    intro K F hF
 
    have hm : ∀ p ∈ Icc 1 K ×ˢ Icc 1 K, Nat.lcm p.1 p.2 ∈ Icc 1 (K*K) := by
      intro p hp
      obtain ⟨hp₁,hp₂⟩ := mem_product.mp hp
      obtain ⟨h₁,h₁K⟩ := mem_Icc.mp hp₁
      obtain ⟨h₂,h₂K⟩ := mem_Icc.mp hp₂
      exact mem_Icc.mpr ⟨Nat.lcm_pos (by omega) (by omega),
        (Nat.lcm_le_mul h₁ h₂).trans (Nat.mul_le_mul h₁K h₂K)⟩
    calc
      _ ≤ ∑ p ∈ Icc 1 K ×ˢ Icc 1 K,
          (p.1.divisors.card:ℝ)*p.2.divisors.card*F (Nat.lcm p.1 p.2) := by
        rw [sum_product]
        apply sum_le_sum
        intro k₁ hk₁
        apply sum_le_sum
        intro k₂ hk₂
        have hc₁ : (1:ℝ)≤k₁.divisors.card := by
          exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp hk₁).1; omega))
        have hc₂ : (1:ℝ)≤k₂.divisors.card := by
          exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp hk₂).1; omega))
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:ℝ)≤(k₁.divisors.card:ℝ)*k₂.divisors.card by nlinarith) (hF _)
      _ = ∑ h ∈ Icc 1 (K*K),
          (∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2=h),
            (p.1.divisors.card:ℝ)*p.2.divisors.card)*F h := by
        rw [← sum_fiberwise_of_maps_to hm]
        apply sum_congr rfl
        intro h hh
        rw [sum_mul]
        apply sum_congr rfl
        intro p hp
        rw [(mem_filter.mp hp).2]
      _ ≤ _ := sum_le_sum (fun h hh => mul_le_mul_of_nonneg_right (lcm_fiber_divisor_bound h K) (hF h))

  have divisor_product_bound : ∀ (U V : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0≤F n), ∑ h ∈ Icc 1 V, (h.divisors.card:ℝ)^4*∑ r ∈ Icc 1 U, F (h*r) ≤
      ∑ n ∈ Icc 1 (U*V), (n.divisors.card:ℝ)^5*F n := by
    intro U V F hF
 
    classical
    have hm : ∀ p ∈ Icc 1 V ×ˢ Icc 1 U, p.1*p.2 ∈ Icc 1 (U*V) := by
      intro p hp
      obtain ⟨h₁,h₂⟩ := mem_product.mp hp
      obtain ⟨h₁p,h₁V⟩ := mem_Icc.mp h₁
      obtain ⟨h₂p,h₂U⟩ := mem_Icc.mp h₂
      exact mem_Icc.mpr ⟨by nlinarith,by nlinarith⟩
    have hf (n : ℕ) (hn : n ∈ Icc 1 (U*V)) :
        (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n),
          (p.1.divisors.card:ℝ)^4) ≤ (n.divisors.card:ℝ)^5 := by
      let s := (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n)
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      have hi : Set.InjOn (fun p : ℕ × ℕ => p.1) (s : Set (ℕ × ℕ)) := by
        intro p hp q hq he
        have hp' := mem_filter.mp hp
        have hq' := mem_filter.mp hq
        have hp0 : 0<p.1 := (mem_Icc.mp (mem_product.mp hp'.1).1).1
        apply Prod.ext he
        apply Nat.eq_of_mul_eq_mul_left hp0
        simpa only [he] using hp'.2.trans hq'.2.symm
      have hs : s.image Prod.fst ⊆ n.divisors := by
        intro h hh
        obtain ⟨p,hp,rfl⟩ := mem_image.mp hh
        have hp' := (mem_filter.mp hp).2
        exact Nat.mem_divisors.mpr ⟨hp' ▸ dvd_mul_right p.1 p.2,hn0⟩
      calc
        _ = ∑ h ∈ s.image Prod.fst, (h.divisors.card:ℝ)^4 := (sum_image hi).symm
        _ ≤ ∑ h ∈ n.divisors, (h.divisors.card:ℝ)^4 :=
          sum_le_sum_of_subset_of_nonneg hs (fun h hh hnot => by positivity)
        _ ≤ ∑ h ∈ n.divisors, (n.divisors.card:ℝ)^4 := by
          apply sum_le_sum
          intro h hh
          apply pow_le_pow_left₀ (Nat.cast_nonneg _)
          exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hn0 (Nat.dvd_of_mem_divisors hh))
        _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
    simp_rw [mul_sum]
    rw [← sum_product',← sum_fiberwise_of_maps_to hm]
    apply sum_le_sum
    intro n hn
    have he : (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n),
        (p.1.divisors.card:ℝ)^4*F (p.1*p.2)) =
        (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n),
          (p.1.divisors.card:ℝ)^4)*F n := by
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hf n hn) (hF n)

  have phaseCap_neg : ∀ (α X : ℝ) (n : ℕ), phaseCap (-α) X n = phaseCap α X n := by
    intro α X n
 
    have he : ee ((-α)*n) = starRingEnd ℂ (ee (α*n)) := by rw [conj_ee]; congr 1; ring
    have hn : ‖starRingEnd ℂ (ee (α*n))-1‖ = ‖ee (α*n)-1‖ := by
      rw [← map_one (starRingEnd ℂ),← map_sub,Complex.norm_conj]
      simp only [map_one]
    have hi : starRingEnd ℂ (ee (α*n))=1 ↔ ee (α*n)=1 := by
      constructor
      · intro h
        have ht := congrArg (starRingEnd ℂ) h
        simpa using ht
      · intro h
        simp [h]
    simp only [phaseCap,he,hi,hn]

  have phaseCap_distance : ∀ (α M : ℝ) (l j h : ℕ), phaseCap (α*((l:ℝ)-j)) M h = phaseCap (α*(Nat.dist l j:ℝ)) M h := by
    intro α M l j h
 
    rcases le_total j l with hj|hl
    · rw [Nat.dist_eq_sub_of_le_right hj,Nat.cast_sub hj]
    · rw [Nat.dist_eq_sub_of_le hl,Nat.cast_sub hl]
      have he : α*((l:ℝ)-j) = -(α*((j:ℝ)-l)) := by ring
      rw [he,phaseCap_neg]

  have phaseCap_product : ∀ (α M H : ℝ) (r h : ℕ)
    (hM : 0≤M) (hH : 0≤H) (hr : 1≤r) (hh : 1≤h) (hrH : (r:ℝ)≤2*H), phaseCap (α*r) M h ≤ phaseCap α (2*M*H) (r*h) := by
    intro α M H r h hM hH hr hh hrH
 
    have hrp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
    have hhp : (0:ℝ)<h := by exact_mod_cast (show 0<h by omega)
    have he : (α*r)*(h:ℝ) = α*(r*h:ℕ) := by push_cast; ring
    have hc : 2*M/h+1 ≤ 2*(2*M*H)/(r*h:ℕ)+1 := by
      apply add_le_add _ le_rfl
      rw [Nat.cast_mul,div_le_div_iff₀ hhp (mul_pos hrp hhp)]
      have ht := mul_le_mul_of_nonneg_left hrH (show 0≤2*M by positivity)
      have ht' := mul_le_mul_of_nonneg_right ht hhp.le
      nlinarith
    simp only [phaseCap,he]
    split_ifs
    · exact hc
    · exact min_le_min hc le_rfl

  have correlation_affine : ∀ (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ)
    (hi : 1 ≤ i.2) (hj : 1 ≤ j.2)
    (hci : Nat.Coprime i.2 l₃) (hcj : Nat.Coprime j.2 l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M), ∃ β : ℝ, ∃ J : ℕ,
      correlation l₃ N α x M M₁ i j =
        ∑ r ∈ range J, ee (β + (r : ℝ) *
          (α * (Nat.lcm i.2 j.2 : ℝ) * ((i.1 : ℝ) - j.1))) ∧
      (J : ℝ) ≤ 2 * M / Nat.lcm i.2 j.2 + 1 := by
    intro l₃ N α x M M₁ i j hi hj hci hcj hM hM₁
 
    classical
    let h := Nat.lcm i.2 j.2
    have hh : 0 < h := Nat.lcm_pos (by omega) (by omega)
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    let s := (Ioc ⌊M⌋₊ ⌊M₁⌋₊).filter (fun m =>
      ((x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
        (m * i.1) % i.2 = l₃ % i.2) ∧
      ((x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
        (m * j.1) % j.2 = l₃ % j.2))
    have he : correlation l₃ N α x M M₁ i j =
        ∑ m ∈ s, ee (α * m * ((i.1 : ℝ) - j.1)) := by
      rw [correlation_eq_phase, ← sum_filter]
    by_cases hne : s.Nonempty
    · let a := s.min' hne
      let b := s.max' hne
      have ha : a ∈ s := s.min'_mem hne
      have hb : b ∈ s := s.max'_mem hne
      have ha' := mem_filter.mp ha
      have hb' := mem_filter.mp hb
      have hab : a ≤ b := s.min'_le b hb
      have hki : Nat.Coprime i.2 i.1 := by
        have ht : Nat.Coprime i.2 (a * i.1) := by
          change Nat.gcd i.2 (a * i.1) = 1
          rw [Nat.gcd_rec, ha'.2.1.2, ← Nat.gcd_rec]
          exact hci
        exact ht.of_dvd_right (dvd_mul_left i.1 a)
      have hkj : Nat.Coprime j.2 j.1 := by
        have ht : Nat.Coprime j.2 (a * j.1) := by
          change Nat.gcd j.2 (a * j.1) = 1
          rw [Nat.gcd_rec, ha'.2.2.2, ← Nat.gcd_rec]
          exact hcj
        exact ht.of_dvd_right (dvd_mul_left j.1 a)
      have hmod : ∀ m ∈ s, a ≡ m [MOD h] := by
        intro m hm
        have hm' := mem_filter.mp hm
        apply Nat.mod_lcm
        · apply Nat.ModEq.cancel_left_of_coprime hki
          simpa only [Nat.mul_comm] using (show a * i.1 ≡ m * i.1 [MOD i.2] from
            ha'.2.1.2.trans hm'.2.1.2.symm)
        · apply Nat.ModEq.cancel_left_of_coprime hkj
          simpa only [Nat.mul_comm] using (show a * j.1 ≡ m * j.1 [MOD j.2] from
            ha'.2.2.2.trans hm'.2.2.2.symm)
      have hdiv : h ∣ b - a := (hmod b hb).dvd'
      have hbe : b = a + ((b - a) / h) * h := by
        rw [Nat.div_mul_cancel hdiv]
        omega
      let J := (b - a) / h + 1
      have hbetween : ∀ r < J, a ≤ a + r * h ∧ a + r * h ≤ b := by
        intro r hr
        dsimp [J] at hr
        constructor
        · omega
        · have ht := Nat.mul_le_mul_right h (show r ≤ (b - a) / h by omega)
          omega
      have hmem : ∀ r < J, a + r * h ∈ s := by
        intro r hr
        obtain ⟨hlo, hhi⟩ := hbetween r hr
        have ht : a ≡ a + r * h [MOD h] := by
          simp [Nat.ModEq, Nat.add_mod]
        have hti := (ht.of_dvd (Nat.dvd_lcm_left i.2 j.2)).mul_right i.1
        have htj := (ht.of_dvd (Nat.dvd_lcm_right i.2 j.2)).mul_right j.1
        apply mem_filter.mpr
        refine ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp ha'.1).1.trans_le hlo,
          hhi.trans (mem_Ioc.mp hb'.1).2⟩, ?_, ?_⟩
        · have hpi := Nat.mul_le_mul_right i.1 hlo
          have hqi := Nat.mul_le_mul_right i.1 hhi
          refine ⟨⟨ha'.2.1.1.1.trans_le (by exact_mod_cast hpi),
            (by exact_mod_cast hqi : (((a + r * h) * i.1 : ℕ) : ℝ) ≤ (b * i.1 : ℕ)).trans hb'.2.1.1.2.1,
            hqi.trans hb'.2.1.1.2.2⟩, hti.symm.trans ha'.2.1.2⟩
        · have hpj := Nat.mul_le_mul_right j.1 hlo
          have hqj := Nat.mul_le_mul_right j.1 hhi
          refine ⟨⟨ha'.2.2.1.1.trans_le (by exact_mod_cast hpj),
            (by exact_mod_cast hqj : (((a + r * h) * j.1 : ℕ) : ℝ) ≤ (b * j.1 : ℕ)).trans hb'.2.2.1.2.1,
            hqj.trans hb'.2.2.1.2.2⟩, htj.symm.trans ha'.2.2.2⟩
      have hs : s = (range J).image (fun r => a + r * h) := by
        ext m
        constructor
        · intro hm
          have ham : a ≤ m := s.min'_le m hm
          have hmb : m ≤ b := s.le_max' m hm
          have hdm : h ∣ m - a := (hmod m hm).dvd'
          refine mem_image.mpr ⟨(m - a) / h, mem_range.mpr ?_, ?_⟩
          · dsimp [J]
            exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : m - a ≤ b - a))
          · rw [Nat.div_mul_cancel hdm]
            omega
        · intro hm
          obtain ⟨r, hr, rfl⟩ := mem_image.mp hm
          exact hmem r (mem_range.mp hr)
      refine ⟨α * a * ((i.1 : ℝ) - j.1), J, ?_, ?_⟩
      · rw [he, hs, sum_image]
        · apply sum_congr rfl
          intro r hr
          congr 1
          push_cast
          ring
        · intro r hr r' hr' heq
          exact Nat.mul_right_cancel hh (Nat.add_left_cancel heq)
      · have hbpos : 0 < b := lt_of_lt_of_le (by have := (mem_Ioc.mp ha'.1).1; omega : 0 < a) hab
        have hM₁0 : 0 ≤ M₁ := by
          by_contra hn
          have hz := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hn))
          rw [hz] at hb'
          have := (mem_Ioc.mp hb'.1).2
          omega
        have hble : (b : ℝ) ≤ 2 * M :=
          (show (b : ℝ) ≤ ⌊M₁⌋₊ by exact_mod_cast (mem_Ioc.mp hb'.1).2).trans
            ((Nat.floor_le hM₁0).trans hM₁)
        have hbeR : (b : ℝ) = a + ((b - a) / h : ℕ) * (h : ℝ) := by exact_mod_cast hbe
        have hJR : (J : ℝ) = ((b - a) / h : ℕ) + 1 := by simp [J]
        have hnum : ((J : ℝ) - 1) * h ≤ 2 * M := by
          rw [hJR]
          nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
        have hquot := (le_div_iff₀ hhr).mpr hnum
        change (J : ℝ) ≤ 2 * M / h + 1
        linarith
    · refine ⟨0, 0, ?_, ?_⟩
      · rw [he, not_nonempty_iff_eq_empty.mp hne]
        simp
      · simp only [Nat.cast_zero]
        exact add_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) zero_le_one

  have correlation_bound : ∀ (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ)
    (hi : 1 ≤ i.2) (hj : 1 ≤ j.2)
    (hci : Nat.Coprime i.2 l₃) (hcj : Nat.Coprime j.2 l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M), ‖correlation l₃ N α x M M₁ i j‖ ≤
      phaseCap (α * ((i.1 : ℝ) - j.1)) M (Nat.lcm i.2 j.2) := by
    intro l₃ N α x M M₁ i j hi hj hci hcj hM hM₁
 
    obtain ⟨β, J, he, hJ⟩ := correlation_affine l₃ N α x M M₁ i j hi hj hci hcj hM hM₁
    have ht : α * (Nat.lcm i.2 j.2 : ℝ) * ((i.1 : ℝ) - j.1) =
        (α * ((i.1 : ℝ) - j.1)) * (Nat.lcm i.2 j.2 : ℝ) := by ring
    rw [he]
    simp only [ht]
    unfold phaseCap
    split_ifs with hθ
    · apply le_trans (norm_sum_le _ _)
      simpa only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one] using hJ
    · exact (progression_phase_bound β _ J hθ).trans (min_le_min hJ le_rfl)

  have correlation_diagonal_bound : ∀ (l₃ N : ℕ) (α x M M₁ : ℝ) (l k₁ k₂ : ℕ)
    (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (hc₁ : Nat.Coprime k₁ l₃) (hc₂ : Nat.Coprime k₂ l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M), ‖correlation l₃ N α x M M₁ (l, k₁) (l, k₂)‖ ≤
      2 * M / Nat.lcm k₁ k₂ + 1 := by
    intro l₃ N α x M M₁ l k₁ k₂ h₁ h₂ hc₁ hc₂ hM hM₁
 
    simpa [phaseCap, ee_zero] using
      correlation_bound l₃ N α x M M₁ (l, k₁) (l, k₂) h₁ h₂ hc₁ hc₂ hM hM₁

  have unweighted_lcm_sum : ∀ (K : ℕ), ∑ p ∈ Icc 1 K ×ˢ Icc 1 K, (1 : ℝ) / Nat.lcm p.1 p.2 ≤ Hn (K*K) ^ (16 : ℕ) := by
    intro K
 
    apply (sum_le_sum (fun p hp => ?_)).trans (lcm_divisor_sum K)
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    have hc₁ : (1 : ℝ) ≤ p.1.divisors.card := by
      exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp h₁).1; omega))
    have hc₂ : (1 : ℝ) ≤ p.2.divisors.card := by
      exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp h₂).1; omega))
    exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)

  have diagonal_eq : ∀ (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ), diagonal l₃ K N α x M M₁ H H₁ =
      ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2 *
        ∑ k₁ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        ∑ k₂ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
          ‖correlation l₃ N α x M M₁ (l,k₁) (l,k₂)‖ := by
    intro l₃ K N α x M M₁ H H₁
 
    classical
    simp only [diagonal, indices, sum_product]
    apply sum_congr rfl
    intro l hl
    rw [mul_sum]
    apply sum_congr rfl
    intro k₁ hk₁
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro k₂ hk₂
    simp only [sum_ite_eq, hl, ite_true, pow_two]

  have diagonal_le_separated : ∀ (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M), diagonal l₃ K N α x M M₁ H H₁ ≤
      (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2) *
        (2*M*Hn (K*K) ^ (16 : ℕ) + (K : ℝ)^2) := by
    intro l₃ K N α x M M₁ H H₁ hM hM₁
 
    classical
    rw [diagonal_eq, sum_mul]
    apply sum_le_sum
    intro l hl
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    calc
      _ ≤ ∑ k₁ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
          ∑ k₂ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
            (2*M / Nat.lcm k₁ k₂ + 1) := by
        apply sum_le_sum
        intro k₁ hk₁
        apply sum_le_sum
        intro k₂ hk₂
        exact correlation_diagonal_bound l₃ N α x M M₁ l k₁ k₂
          (mem_Icc.mp (mem_filter.mp hk₁).1).1 (mem_Icc.mp (mem_filter.mp hk₂).1).1
          (mem_filter.mp hk₁).2 (mem_filter.mp hk₂).2 hM hM₁
      _ ≤ ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, (2*M / Nat.lcm k₁ k₂ + 1) := by
        apply (sum_le_sum (fun k₁ hk₁ =>
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₂ hk₂ hnot => by positivity))).trans
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₁ hk₁ hnot =>
          sum_nonneg (fun k₂ hk₂ => by positivity))
      _ = 2*M*(∑ p ∈ Icc 1 K ×ˢ Icc 1 K, (1:ℝ) / Nat.lcm p.1 p.2) + (K:ℝ)^2 := by
        simp only [← sum_product', sum_add_distrib, sum_const, card_product,
          Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul, nsmul_eq_mul, mul_one, mul_sum]
        congr 1
        · apply sum_congr rfl
          intro p hp
          ring
        · ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (unweighted_lcm_sum K) (show 0 ≤ 2*M by positivity)) le_rfl

  have tau5_square_sum : ∀ (H H₁ : ℝ) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H), ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ)^2 ≤
      2*H*Hn ⌊2*H⌋₊ ^ (24 : ℕ) := by
    intro H H₁ hH hH₁
 
    have hs : Ioc ⌊H⌋₊ ⌊H₁⌋₊ ⊆ Icc 1 ⌊2*H⌋₊ := by
      intro l hl
      obtain ⟨hl0,hl1⟩ := mem_Ioc.mp hl
      exact mem_Icc.mpr ⟨by omega,hl1.trans (Nat.floor_le_floor hH₁)⟩
    calc
      _ ≤ ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (((ArithmeticFunction.zeta ^ 25) l : ℕ) : ℝ) := by
        apply sum_le_sum
        intro l hl
        exact_mod_cast tau5_sq_le_zeta25 l
      _ ≤ ∑ l ∈ Icc 1 ⌊2*H⌋₊, (((ArithmeticFunction.zeta ^ 25) l : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hs (fun l hl hnot => Nat.cast_nonneg _)
      _ ≤ (⌊2*H⌋₊ : ℝ) * Hn ⌊2*H⌋₊ ^ (24 : ℕ) := zeta_power_sum 24 _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)

  have diagonal_finite_bound : ∀ (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H), diagonal l₃ K N α x M M₁ H H₁ ≤
      (2*H*Hn ⌊2*H⌋₊ ^ (24 : ℕ)) *
        (2*M*Hn (K*K) ^ (16 : ℕ) + (K : ℝ)^2) := by
    intro l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
 
    exact (diagonal_le_separated l₃ K N α x M M₁ H H₁ hM hM₁).trans
      (mul_le_mul_of_nonneg_right (tau5_square_sum H H₁ hH hH₁) (by positivity))

  have diagonal_power_bound : ∀ (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hN : (1 : ℝ) ≤ N) (hL : 1 ≤ Real.log N)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H)
    (hMH : M*H ≤ 2*N) (hHlo : (N : ℝ)^((1:ℝ)/2000) ≤ H)
    (hK : (K : ℝ)^2 ≤ (N : ℝ)^((2:ℝ)/3))
    (hHm : Hn ⌊2*H⌋₊ ≤ 33*Real.log N)
    (hHk : Hn (K*K) ≤ 33*Real.log N), M * diagonal l₃ K N α x M M₁ H H₁ ≤
      (20 * 33^(40:ℕ)) * (N : ℝ)^((3999:ℝ)/2000) * Real.log N^(40:ℕ) := by
    intro l₃ K N α x M M₁ H H₁ hN hL hM hM₁ hH hH₁ hMH hHlo hK hHm hHk
 
    have hN0 : (0 : ℝ) < N := by linarith
    have hP : 0 < (N : ℝ)^((1:ℝ)/2000) := Real.rpow_pos_of_pos hN0 _
    have hML : M ≤ 2 * (N : ℝ)^((1999:ℝ)/2000) := by
      have hh : M ≤ 2*(N:ℝ)/(N:ℝ)^((1:ℝ)/2000) :=
        (le_div_iff₀ hP).mpr ((mul_le_mul_of_nonneg_left hHlo hM.le).trans hMH)
      convert hh using 1
      rw [mul_div_assoc]
      congr 1
      simpa only [show (1:ℝ)-(1:ℝ)/2000 = (1999:ℝ)/2000 by norm_num, Real.rpow_one] using
        Real.rpow_sub hN0 1 ((1:ℝ)/2000)
    have hKL : (K:ℝ)^2 ≤ (N:ℝ)^((1999:ℝ)/2000) :=
      hK.trans (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
    have hL0 : 0 ≤ Real.log N := by linarith
    have h33 : 1 ≤ 33*Real.log N := by linarith
    have h3316 : 1 ≤ (33*Real.log N)^(16:ℕ) := one_le_pow₀ h33
    have hbracket : 2*M*Hn (K*K)^(16:ℕ)+(K:ℝ)^2 ≤
        5*(N:ℝ)^((1999:ℝ)/2000)*(33*Real.log N)^(16:ℕ) := by
      have hh := pow_le_pow_left₀ (Hn_nonneg _) hHk 16
      have hb := mul_le_mul (mul_le_mul_of_nonneg_left hML (by norm_num : (0:ℝ)≤2)) hh
        (by positivity) (by positivity)
      have hk := mul_le_mul_of_nonneg_left h3316
        (Real.rpow_nonneg (Nat.cast_nonneg N) ((1999:ℝ)/2000))
      nlinarith
    have hHnon := Hn_nonneg ⌊2*H⌋₊
    have hf := diagonal_finite_bound l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
    calc
      _ ≤ M*((2*H*Hn ⌊2*H⌋₊^(24:ℕ))*(2*M*Hn (K*K)^(16:ℕ)+(K:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hf hM.le
      _ = 2*(M*H)*Hn ⌊2*H⌋₊^(24:ℕ)*(2*M*Hn (K*K)^(16:ℕ)+(K:ℝ)^2) := by ring
      _ ≤ 2*(2*(N:ℝ))*(33*Real.log N)^(24:ℕ)*
          (5*(N:ℝ)^((1999:ℝ)/2000)*(33*Real.log N)^(16:ℕ)) := by
        gcongr
      _ = _ := by
        rw [show (3999:ℝ)/2000 = 1+(1999:ℝ)/2000 by norm_num, Real.rpow_add hN0, Real.rpow_one]
        ring

  have harmonic_endpoint : ∀ (R N : ℕ) (hN : (0:ℝ) < N) (hL : 1 ≤ Real.log N)
    (hR : (R:ℝ) ≤ 2^(31:ℕ)*(N:ℝ)), Hn R ≤ 33*Real.log N := by
    intro R N hN hL hR
 
    have hlog2 : Real.log (2:ℝ) ≤ 1 := by
      have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    have hlogR : Real.log R ≤ 31+Real.log N := by
      by_cases hzero : R = 0
      · simp [hzero]
        linarith
      · have hRp : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero hzero
        have ht := Real.log_le_log hRp hR
        rw [Real.log_mul (by positivity : (2:ℝ)^(31:ℕ) ≠ 0) (ne_of_gt hN), Real.log_pow] at ht
        norm_num at ht
        linarith
    exact (Hn_le R).trans (by linarith)

  have eventual_diagonal_parameters : ∀ (A : ℝ), ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧
      Real.log N^(4*A) ≤ (N:ℝ)^((1:ℝ)/2) ∧
      Real.log N^(8*A-592) ≤ (N:ℝ)^((1:ℝ)/2000) := by
    intro A
 
    obtain ⟨X₁,h₁⟩ := Filter.eventually_atTop.mp
      ((isLittleO_log_rpow_rpow_atTop (4*A) (by norm_num : (0:ℝ)<1/2)).bound
        (by norm_num : (0:ℝ)<1))
    obtain ⟨X₂,h₂⟩ := Filter.eventually_atTop.mp
      ((isLittleO_log_rpow_rpow_atTop (8*A-592) (by norm_num : (0:ℝ)<1/2000)).bound
        (by norm_num : (0:ℝ)<1))
    refine ⟨max (max X₁ X₂) (Real.exp 2), ?_⟩
    intro N hN
    have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
    have hNp : (0:ℝ)<N := (Real.exp_pos 2).trans_le hNe
    have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hNp).mpr hNe
    have h₁' := h₁ (N:ℝ) ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
    have h₂' := h₂ (N:ℝ) ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), one_mul] at h₁' h₂'
    exact ⟨hL,h₁',h₂'⟩

  have diagonal_shell_parameters : ∀ (A : ℝ) (N : ℕ) (x H : ℝ)
    (hA : 0 ≤ A) (hN : (1:ℝ) ≤ N) (hL : 1 ≤ Real.log N)
    (hlog : Real.log N^(4*A) ≤ (N:ℝ)^((1:ℝ)/2))
    (hx : 0 < x) (hxlo : (N:ℝ)*Real.log N^(-4*A) ≤ x) (hxN : x ≤ N)
    (hHlo : x^((1:ℝ)/1000) ≤ H) (hHhi : H ≤ 2^(30:ℕ)*x^((1:ℝ)/3)), let K := cutoff3 (10000*A) N
    (N:ℝ)^((1:ℝ)/2000) ≤ H ∧
      (K:ℝ)^2 ≤ (N:ℝ)^((2:ℝ)/3) ∧
      Hn ⌊2*H⌋₊ ≤ 33*Real.log N ∧ Hn (K*K) ≤ 33*Real.log N := by
    intro A N x H hA hN hL hlog hx hxlo hxN hHlo hHhi
 
    have hNp : (0:ℝ)<N := by linarith
    have hLp : 0 < Real.log N := by linarith
    have hsquare : ((N:ℝ)^((1:ℝ)/2))^2 = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      norm_num
    have hs : (N:ℝ)^((1:ℝ)/2) ≤ (N:ℝ)*Real.log N^(-4*A) := by
      rw [show -4*A = -(4*A) by ring, Real.rpow_neg hLp.le, ← div_eq_mul_inv]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp _)).mpr
      exact (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hNp.le _)).trans_eq
        (by simpa only [pow_two] using hsquare)
    have hHlower : (N:ℝ)^((1:ℝ)/2000) ≤ H := by
      calc
        _ = ((N:ℝ)^((1:ℝ)/2))^((1:ℝ)/1000) := by
          rw [← Real.rpow_mul hNp.le]
          norm_num
        _ ≤ x^((1:ℝ)/1000) := Real.rpow_le_rpow (by positivity) (hs.trans hxlo) (by norm_num)
        _ ≤ H := hHlo
    have hNthird : (N:ℝ)^((1:ℝ)/3) ≤ N := by
      convert Real.rpow_le_rpow_of_exponent_le hN (show (1:ℝ)/3 ≤ 1 by norm_num) using 1 <;> simp
    have hHupper : H ≤ 2^(30:ℕ)*(N:ℝ) :=
      hHhi.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num))
        (by positivity)).trans (mul_le_mul_of_nonneg_left hNthird (by positivity)))
    let K := cutoff3 (10000*A) N
    have hK : (K:ℝ) ≤ (N:ℝ)^((1:ℝ)/3) := by
      have hf : (K:ℝ) ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)) :=
        Nat.floor_le (by positivity)
      have ht : Real.log N^(-(10000*A)) ≤ (1:ℝ) := Real.rpow_le_one_of_one_le_of_nonpos hL (by nlinarith)
      exact hf.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (mul_one _))
    have hKsq : (K:ℝ)^2 ≤ (N:ℝ)^((2:ℝ)/3) := by
      have ht := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
      convert ht using 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      norm_num
    refine ⟨hHlower,hKsq,?_,?_⟩
    · apply harmonic_endpoint _ N hNp hL
      have hHp : 0 < H := (Real.rpow_pos_of_pos hNp _).trans_le hHlower
      exact (Nat.floor_le (by positivity : 0 ≤ 2*H)).trans (by nlinarith)
    · apply harmonic_endpoint _ N hNp hL
      have ht : (N:ℝ)^((2:ℝ)/3) ≤ N := by
        convert Real.rpow_le_rpow_of_exponent_le hN (show (2:ℝ)/3 ≤ 1 by norm_num) using 1 <;> simp
      push_cast
      calc
        (K:ℝ)*(K:ℝ) = (K:ℝ)^2 := by ring
        _ ≤ (N:ℝ)^((2:ℝ)/3) := hKsq
        _ ≤ (N:ℝ) := ht
        _ ≤ _ := by nlinarith

  have diagonal_mean : ∀ A : ℝ, 10000 ≤ A → ∃ C N₀ : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ l₃ : ℕ, ∀ α x M M₁ H H₁ : ℝ,
        (N:ℝ)*Real.log N^(-4*A) ≤ x → x ≤ N → 2 < x →
        0 < M → M₁ ≤ 2*M → 0 < H → H₁ ≤ 2*H → M*H ≤ 2*x →
        x^((1:ℝ)/1000) ≤ H → H ≤ 2^(30:ℕ)*x^((1:ℝ)/3) →
        M * diagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁ ≤
          C*(N:ℝ)^2*Real.log N^(632-8*A) := by
 
    intro A hA
    obtain ⟨N₀,hparam⟩ := eventual_diagonal_parameters A
    refine ⟨20*33^(40:ℕ),max N₀ 3,by positivity,?_⟩
    intro N hN l₃ α x M M₁ H H₁ hxlo hxN hx hM hM₁ hH hH₁ hMH hHlo hHhi
    have hN3 : (3:ℝ) ≤ N := (le_max_right _ _).trans hN
    have hNp : (0:ℝ)<N := by linarith
    have hN1 : (1:ℝ) ≤ N := by linarith
    obtain ⟨hL,hlog,habs⟩ := hparam N ((le_max_left _ _).trans hN)
    have hLp : 0 < Real.log N := by linarith
    obtain ⟨hHlower,hK,hHm,hHk⟩ := diagonal_shell_parameters A N x H (by linarith) hN1
      (by linarith) hlog (by linarith) hxlo hxN hHlo hHhi
    have hpower := diagonal_power_bound l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁
      hN1 (by linarith) hM hM₁ hH hH₁ (hMH.trans (by linarith)) hHlower hK hHm hHk
    have hlogs : Real.log N^(40:ℕ) = Real.log N^(8*A-592)*Real.log N^(632-8*A) := by
      rw [← Real.rpow_add hLp, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hfactor : (N:ℝ)^((3999:ℝ)/2000)*Real.log N^(40:ℕ) ≤
        (N:ℝ)^2*Real.log N^(632-8*A) := by
      rw [hlogs, ← mul_assoc]
      calc
        _ ≤ ((N:ℝ)^((3999:ℝ)/2000)*(N:ℝ)^((1:ℝ)/2000))*Real.log N^(632-8*A) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg hNp.le _))
            (Real.rpow_nonneg hLp.le _)
        _ = _ := by
          rw [← Real.rpow_add hNp]
          norm_num
    apply hpower.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfactor
      (show (0:ℝ) ≤ 20*33^(40:ℕ) by positivity)

  have divisorPhase_nonneg : ∀ (α X : ℝ) (T : ℕ) (hX : 0 ≤ X), 0 ≤ divisorPhase α X T := by
    intro α X T hX
    exact   sum_nonneg (fun n hn => mul_nonneg (by positivity) (phaseCap_nonneg α X n hX))

  have divisorPhase_sq : ∀ (α X : ℝ) (T : ℕ) (hX : 0 ≤ X), divisorPhase α X T ^ 2 ≤ Hn T ^ (1024:ℕ) *
      ((2*X+T)*∑ n ∈ Icc 1 T, phaseCap α X n) := by
    intro α X T hX
 
    have hm : (∑ n ∈ Icc 1 T, ((n.divisors.card : ℝ)^5)^2 / n) ≤ Hn T^(1024:ℕ) := by
      simpa only [← pow_mul, show (5:ℕ)*2=10 by norm_num, show (2:ℕ)^10=1024 by norm_num] using
        divisor_power_reciprocal 10 T
    exact (weighted_phase_cauchy (fun n => (n.divisors.card:ℝ)^5) T α X hX).trans
      (mul_le_mul_of_nonneg_right hm
        (mul_nonneg (by positivity) (sum_nonneg (fun n hn => phaseCap_nonneg α X n hX))))

  have phase_mass_four : ∀ (A : ℝ) (N T q : ℕ) (a : ℤ) (α X : ℝ)
    (hA : 0 ≤ A) (hN : 0 < (N:ℝ)) (hL : 2 ≤ Real.log N)
    (hX : 0 ≤ X) (hXN : X ≤ 4*N) (hTN : T ≤ N)
    (hTS : (T:ℝ) ≤ 4*N*Real.log N^(-20*A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q:ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q:ℤ)) (herr : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2), ∑ n ∈ Icc 1 T, phaseCap α X n ≤ 512*N*Real.log N^(1-20*A) := by
    intro A N T q a α X hA hN hL hX hXN hTN hTS hq hqQ hqτ hcop herr
 
    let s : ℝ := N*Real.log N^(-20*A)
    have hLp : 0 < Real.log N := by linarith
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have hQ : 1 ≤ Qof A N := Real.one_le_rpow (by linarith) (by positivity)
    have hQp : 0 < Qof A N := by linarith
    have ht : τof A N = s := by
      dsimp [τof,Qof,s]
      rw [show -20*A=-(20*A) by ring,Real.rpow_neg hLp.le,div_eq_mul_inv]
    have hqS : (q:ℝ) ≤ s := by rwa [ht] at hqτ
    have hqp : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
    have hqN : (q:ℝ) ≤ N := hqτ.trans (div_le_self hN.le hQ)
    have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hqp hqN
    have hlogT : Real.log T ≤ Real.log N := by
      by_cases hT : T=0
      · simp [hT]; linarith
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast hTN)
    have hlogs : 1+Real.log q+Real.log T ≤ 3*Real.log N := by linarith
    have hlogs0 : 0 ≤ 1+Real.log q+Real.log T := by positivity
    have hNq : (N:ℝ)/q ≤ s := by
      calc
        _ ≤ (N:ℝ)/Qof A N := div_le_div_of_nonneg_left hN.le hQp hqQ.le
        _ = s := ht
    have hXq : 2*X/q ≤ 8*s := by
      calc
        _ ≤ 2*(4*(N:ℝ))/q := div_le_div_of_nonneg_right (by linarith) hqp.le
        _ = 8*((N:ℝ)/q) := by ring
        _ ≤ 8*s := mul_le_mul_of_nonneg_left hNq (by norm_num)
    have hT : (T:ℝ) ≤ 4*s := by simpa only [s,mul_assoc] using hTS
    have hc : 2*X/q+T+q ≤ 13*s := by linarith
    have hp := mul_le_mul hc hlogs hlogs0 (by positivity : 0≤13*s)
    have hm := phaseCap_sum_le hq hcop herr hX T
    apply hm.trans
    have hbound : 12*(2*X/q+T+q)*(1+Real.log q+Real.log T)+T ≤ 512*s*Real.log N := by
      nlinarith [mul_nonneg hs (show 0 ≤ Real.log N-1 by linarith)]
    apply hbound.trans_eq
    dsimp [s]
    rw [show 1-20*A=(-20*A)+(1:ℝ) by ring,Real.rpow_add hLp,Real.rpow_one]
    ring

  have divisorPhase_bound : ∀ (A : ℝ) (N T q : ℕ) (a : ℤ) (α X : ℝ)
    (hA : 0 ≤ A) (hN : (1:ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hX : 0 ≤ X) (hXN : X ≤ 4*N) (hTN : T ≤ N)
    (hTS : (T:ℝ) ≤ 4*N*Real.log N^(-20*A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q:ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q:ℤ)) (herr : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2), divisorPhase α X T ≤ 2^(520:ℕ)*N*Real.log N^(513-10*A) := by
    intro A N T q a α X hA hN hL hX hXN hTN hTS hq hqQ hqτ hcop herr
 
    have hNp : (0:ℝ)<N := by linarith
    have hLp : 0 < Real.log N := by linarith
    have hH : Hn T ≤ 2*Real.log N := by
      have hl : Real.log T ≤ Real.log N := by
        by_cases hz : T=0
        · simp [hz]; linarith
        · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hTN)
      exact (Hn_le T).trans (by linarith)
    have hm := phase_mass_four A N T q a α X hA hNp hL hX hXN hTN hTS hq hqQ hqτ hcop herr
    have hTp : (T:ℝ) ≤ N := by exact_mod_cast hTN
    have hc : 2*X+T ≤ 9*N := by linarith
    have hphase0 : 0 ≤ ∑ n ∈ Icc 1 T, phaseCap α X n :=
      sum_nonneg (fun n hn => phaseCap_nonneg α X n hX)
    have hb := (divisorPhase_sq α X T hX).trans
      (mul_le_mul (pow_le_pow_left₀ (Hn_nonneg T) hH 1024)
        (mul_le_mul hc hm (sum_nonneg (fun n hn => phaseCap_nonneg α X n hX)) (by positivity))
        (by positivity) (by positivity))
    have he : (2*Real.log N)^(1024:ℕ)*(9*N*(512*N*Real.log N^(1-20*A))) =
        (9*512*2^(1024:ℕ))*(N:ℝ)^2*Real.log N^(1025-20*A) := by
      rw [mul_pow,← Real.rpow_natCast (Real.log N) 1024]
      rw [show 1025-20*A=(1024:ℝ)+(1-20*A) by ring,Real.rpow_add hLp]
      ring
    rw [he] at hb
    have hpow : Real.log N^(1025-20*A) ≤ Real.log N^(1026-20*A) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hC : (9*512*2^(1024:ℕ):ℝ) ≤ (2^(520:ℕ):ℝ)^2 := by norm_num
    have hfin := hb.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hC (sq_nonneg (N:ℝ))) hpow
      (Real.rpow_nonneg hLp.le _) (by positivity))
    have ht : ((2^(520:ℕ):ℝ)^2*(N:ℝ)^2)*Real.log N^(1026-20*A) =
        (2^(520:ℕ)*N*Real.log N^(513-10*A))^2 := by
      have hsq : (Real.log N^(513-10*A))^(2:ℕ) = Real.log N^(1026-20*A) := by
        rw [← Real.rpow_mul_natCast hLp.le]
        congr 1
        push_cast
        ring
      rw [← hsq]
      ring
    rw [ht] at hfin
    exact (sq_le_sq₀ (divisorPhase_nonneg α X T hX) (by positivity)).mp hfin

  have phase_product_endpoint : ∀ (A : ℝ) (N : ℕ) (x H : ℝ)
    (hA : 10000 ≤ A) (hN : (1:ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hx : 0 < x) (hxN : x ≤ N) (hH : 0 < H)
    (hHhi : H ≤ 2^(30:ℕ)*x^((1:ℝ)/3)), let K := cutoff3 (10000*A) N
    let T := ⌊2*H⌋₊*(K*K)
    T ≤ N ∧ (T:ℝ) ≤ 4*N*Real.log N^(-20*A) := by
    intro A N x H hA hN hL hx hxN hH hHhi
 
    let K := cutoff3 (10000*A) N
    let T := ⌊2*H⌋₊*(K*K)
    have hNp : (0:ℝ)<N := by linarith
    have hLp : 0<Real.log N := by linarith
    have hHupper : H ≤ 2^(30:ℕ)*(N:ℝ)^((1:ℝ)/3) :=
      hHhi.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num)) (by positivity))
    have hK : (K:ℝ) ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)) := Nat.floor_le (by positivity)
    have hKsq : (K:ℝ)^2 ≤ (N:ℝ)^((2:ℝ)/3)*Real.log N^(-20000*A) := by
      calc
        _ ≤ ((N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)))^2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
        _ = _ := by
          have hn : ((N:ℝ)^((1:ℝ)/3))^(2:ℕ) = (N:ℝ)^((2:ℝ)/3) := by
            rw [← Real.rpow_mul_natCast hNp.le]
            norm_num
          have hl : (Real.log N^(-(10000*A)))^(2:ℕ) = Real.log N^(-20000*A) := by
            rw [← Real.rpow_mul_natCast hLp.le]
            congr 1
            push_cast
            ring
          rw [mul_pow,hn,hl]
    have hT : (T:ℝ) ≤ 2^(31:ℕ)*(N:ℝ)*Real.log N^(-20000*A) := by
      have hf : (⌊2*H⌋₊:ℝ) ≤ 2*H := Nat.floor_le (by positivity)
      calc
        (T:ℝ) = (⌊2*H⌋₊:ℝ)*(K:ℝ)^2 := by dsimp [T]; push_cast; ring
        _ ≤ (2*H)*((N:ℝ)^((2:ℝ)/3)*Real.log N^(-20000*A)) :=
          mul_le_mul hf hKsq (sq_nonneg _) (by positivity)
        _ ≤ (2*(2^(30:ℕ)*(N:ℝ)^((1:ℝ)/3)))*
            ((N:ℝ)^((2:ℝ)/3)*Real.log N^(-20000*A)) := by gcongr
        _ = 2^(31:ℕ)*((N:ℝ)^((1:ℝ)/3)*(N:ℝ)^((2:ℝ)/3))*Real.log N^(-20000*A) := by ring
        _ = _ := by rw [← Real.rpow_add hNp]; norm_num
    have hsmall : Real.log N^(-19980*A) ≤ (2:ℝ)^(-(31:ℝ)) := by
      calc
        _ ≤ Real.log N^(-(31:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
    have hbudget : (T:ℝ) ≤ (N:ℝ)*Real.log N^(-20*A) := by
      apply hT.trans
      rw [show -20000*A=(-20*A)+(-19980*A) by ring,Real.rpow_add hLp]
      calc
        _ = (2^(31:ℕ)*(N:ℝ)*Real.log N^(-20*A))*Real.log N^(-19980*A) := by ring
        _ ≤ (2^(31:ℕ)*(N:ℝ)*Real.log N^(-20*A))*(2:ℝ)^(-(31:ℝ)) :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = _ := by norm_num [Real.rpow_neg,Real.rpow_natCast]; ring
    have hone : Real.log N^(-20*A) ≤ (1:ℝ) :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by nlinarith)
    refine ⟨?_,?_⟩
    · exact_mod_cast hbudget.trans ((mul_le_mul_of_nonneg_left hone hNp.le).trans_eq (mul_one _))
    · exact hbudget.trans (by have := Real.rpow_nonneg hLp.le (-20*A); nlinarith)

  have finite_offDiagonal_reduction : ∀ (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H), offDiagonal l₃ K N α x M M₁ H H₁ ≤
      2*(∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ)^2) *
        divisorPhase α (2*M*H) (⌊2*H⌋₊*(K*K)) := by
    intro l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
 
    classical
    let S := Ioc ⌊H⌋₊ ⌊H₁⌋₊
    let U := ⌊2*H⌋₊
    let ks := (Icc 1 K).filter (fun k => Nat.Coprime k l₃)
    let X := 2*M*H
    let F : ℕ → ℝ := fun r => ∑ h ∈ Icc 1 (K*K), (h.divisors.card:ℝ)^4*phaseCap α X (h*r)
    have hX : 0≤X := by dsimp [X]; positivity
    have hF : ∀ r, 0≤F r := fun r => sum_nonneg (fun h hh =>
      mul_nonneg (by positivity) (phaseCap_nonneg α X (h*r) hX))
    have hS : ∀ l ∈ S, l≤U := fun l hl =>
      (mem_Ioc.mp hl).2.trans (Nat.floor_le_floor hH₁)
    have he : offDiagonal l₃ K N α x M M₁ H H₁ =
        ∑ l ∈ S, ∑ j ∈ S, if l≠j then (tau5 l:ℝ)*tau5 j*
          ∑ k₁ ∈ ks, ∑ k₂ ∈ ks, ‖correlation l₃ N α x M M₁ (l,k₁) (j,k₂)‖ else 0 := by
      simp only [offDiagonal,indices,sum_product]
      apply sum_congr rfl
      intro l hl
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      by_cases hn : l≠j
      · simp [hn,ks,mul_sum]
      · simp [hn,ks]
    have hpoint (l j : ℕ) (hl : l∈S) (hj : j∈S) (hne : l≠j) :
        (∑ k₁ ∈ ks, ∑ k₂ ∈ ks, ‖correlation l₃ N α x M M₁ (l,k₁) (j,k₂)‖) ≤
          F (Nat.dist l j) := by
      let r := Nat.dist l j
      have hr : 1≤r := by dsimp [r,Nat.dist]; omega
      have hrU : r≤U := by have hlU := hS l hl; have hjU := hS j hj; dsimp [r,Nat.dist]; omega
      have hrH : (r:ℝ)≤2*H :=
        (show (r:ℝ)≤U by exact_mod_cast hrU).trans (Nat.floor_le (by positivity))
      calc
        _ ≤ ∑ k₁ ∈ ks, ∑ k₂ ∈ ks, phaseCap α X (Nat.lcm k₁ k₂*r) := by
          apply sum_le_sum
          intro k₁ hk₁
          apply sum_le_sum
          intro k₂ hk₂
          have hk₁' := mem_filter.mp hk₁
          have hk₂' := mem_filter.mp hk₂
          have hk₁p := (mem_Icc.mp hk₁'.1).1
          have hk₂p := (mem_Icc.mp hk₂'.1).1
          have hh : 1≤Nat.lcm k₁ k₂ := Nat.lcm_pos (by omega) (by omega)
          calc
            _ ≤ phaseCap (α*((l:ℝ)-j)) M (Nat.lcm k₁ k₂) :=
              correlation_bound l₃ N α x M M₁ (l,k₁) (j,k₂) hk₁p hk₂p hk₁'.2 hk₂'.2 hM hM₁
            _ = phaseCap (α*r) M (Nat.lcm k₁ k₂) := phaseCap_distance α M l j _
            _ ≤ _ := by simpa only [Nat.mul_comm] using phaseCap_product α M H r (Nat.lcm k₁ k₂) hM.le hH.le hr hh hrH
        _ ≤ ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, phaseCap α X (Nat.lcm k₁ k₂*r) := by
          apply (sum_le_sum (fun k₁ hk₁ =>
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₂ hk₂ hnot => phaseCap_nonneg α X _ hX))).trans
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₁ hk₁ hnot =>
            sum_nonneg (fun k₂ hk₂ => phaseCap_nonneg α X _ hX))
        _ ≤ _ := lcm_sum_bound K (fun h => phaseCap α X (h*r)) (fun h => phaseCap_nonneg α X _ hX)
    have hfirst : offDiagonal l₃ K N α x M M₁ H H₁ ≤
        ∑ l ∈ S, ∑ j ∈ S, if l≠j then (tau5 l:ℝ)*tau5 j*F (Nat.dist l j) else 0 := by
      rw [he]
      apply sum_le_sum
      intro l hl
      apply sum_le_sum
      intro j hj
      by_cases hn : l≠j
      · simp only [ne_eq,hn,ite_true]
        exact mul_le_mul_of_nonneg_left (hpoint l j hl hj hn) (by positivity)
      · simp only [ne_eq,hn,ite_false,le_refl]
    have hsecond := shifted_square_bound S U hS (fun l => (tau5 l:ℝ)) F hF
    have hthird : (∑ r ∈ Icc 1 U, F r) ≤ divisorPhase α X (U*(K*K)) := by
      dsimp [F,divisorPhase]
      rw [sum_comm]
      simp only [← mul_sum]
      exact divisor_product_bound U (K*K) (fun n => phaseCap α X n) (fun n => phaseCap_nonneg α X n hX)
    exact (hfirst.trans hsecond).trans (mul_le_mul_of_nonneg_left hthird (by positivity))

  have offDiagonal_mean : ∀ A : ℝ, 10000 ≤ A → ∃ C N₀ : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ l₃ : ℕ,
        ∀ α ∈ Set.Ioo (-1/τof A N) (1-1/τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N:ℝ)*Real.log N^(-4*A) ≤ x → x ≤ N → 2 < x →
          0 < M → M₁ ≤ 2*M → 0 < H → H₁ ≤ 2*H → M*H ≤ 2*x →
          x^((1:ℝ)/1000) ≤ H → H ≤ 2^(30:ℕ)*x^((1:ℝ)/3) →
          M * offDiagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁ ≤
            C*(N:ℝ)^2*Real.log N^(632-8*A) := by
 
    intro A hA
    obtain ⟨N₁,hparam₁⟩ := priv_eventual_minor_arc_parameters A (by linarith)
    obtain ⟨N₂,hparam₂⟩ := eventual_diagonal_parameters A
    refine ⟨2^(523:ℕ)*33^(24:ℕ),max N₁ (max N₂ 3),by positivity,?_⟩
    intro N hN l₃ α hα hminor x M M₁ H H₁ hxlo hxN hx hM hM₁ hH hH₁ hMH hHlo hHhi
    have hN3 : (3:ℝ) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hNp : (0:ℝ)<N := by linarith
    have hN1 : (1:ℝ)≤N := by linarith
    obtain ⟨hL,hτ⟩ := hparam₁ N ((le_max_left _ _).trans hN)
    obtain ⟨_,hlog,_⟩ := hparam₂ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    have hLp : 0<Real.log N := by linarith
    have hQ : 0≤Qof A N := Real.rpow_nonneg (by linarith) _
    have hτ1 : 1≤τof A N := by linarith
    obtain ⟨a,q,hq,hqQ,hqt,hcop,_,herr⟩ :=
      priv_minor_arc_approximation (Qof A N) (τof A N) α hQ hτ hτ1 hα hminor
    let K := cutoff3 (10000*A) N
    let T := ⌊2*H⌋₊*(K*K)
    obtain ⟨hTN,hTS⟩ := phase_product_endpoint A N x H hA hN1 hL (by linarith) hxN hH hHhi
    have hX : 0≤2*M*H := by positivity
    have hXN : 2*M*H ≤ 4*N := by nlinarith
    have hphase := divisorPhase_bound A N T q a α (2*M*H) (by linarith) hN1 hL hX hXN
      hTN hTS hq hqQ hqt hcop herr
    obtain ⟨_,_,hHm,_⟩ := diagonal_shell_parameters A N x H (by linarith) hN1
      (by linarith) hlog (by linarith) hxlo hxN hHlo hHhi
    have hmass : (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l:ℝ)^2) ≤
        2*H*(33*Real.log N)^(24:ℕ) :=
      (tau5_square_sum H H₁ hH hH₁).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Hn_nonneg _) hHm 24)
          (by positivity))
    have hf := finite_offDiagonal_reduction l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
    have hb := hf.trans (mul_le_mul (mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ)≤2)) hphase
      (divisorPhase_nonneg α (2*M*H) T hX) (by positivity))
    have he : M*(2*(2*H*(33*Real.log N)^(24:ℕ))*(2^(520:ℕ)*N*Real.log N^(513-10*A))) =
        (2^(522:ℕ)*33^(24:ℕ))*(M*H)*N*Real.log N^(537-10*A) := by
      rw [mul_pow,show 537-10*A=(24:ℝ)+(513-10*A) by ring,Real.rpow_add hLp]
      simp only [Real.rpow_ofNat]
      ring
    have hsave : Real.log N^(537-10*A) ≤ Real.log N^(632-8*A) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hMHN : M*H ≤ 2*N := hMH.trans (by linarith)
    calc
      _ ≤ M*(2*(2*H*(33*Real.log N)^(24:ℕ))*(2^(520:ℕ)*N*Real.log N^(513-10*A))) :=
        mul_le_mul_of_nonneg_left hb hM.le
      _ = _ := he
      _ ≤ (2^(522:ℕ)*33^(24:ℕ))*(2*N)*N*Real.log N^(632-8*A) := by gcongr
      _ = _ := by ring

  have row_energy : ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ b : ℕ → ℂ,
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A) := by
 
    intro A hA l₃ hl₃
    have hA' : 10000 ≤ A := by norm_num at hA; exact hA
    obtain ⟨C₁,N₁,hC₁,h₁⟩ := diagonal_mean A hA'
    obtain ⟨C₂,N₂,hC₂,h₂⟩ := offDiagonal_mean A hA'
    refine ⟨C₁+C₂,max N₁ N₂,by positivity,?_⟩
    intro N hodd hN lam hlam α hα hminor x M M₁ H H₁ hxlo hxN hx
      hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hHlo hHhi b hb
    have hd := h₁ N ((le_max_left _ _).trans hN) l₃ α x M M₁ H H₁
      hxlo hxN hx hM hM₁ hH hH₁ hprodhi hHlo hHhi
    have ho := h₂ N ((le_max_right _ _).trans hN) l₃ α hα hminor x M M₁ H H₁
      hxlo hxN hx hM hM₁ hH hH₁ hprodhi hHlo hHhi
    have hN2 : (1:ℝ)<N := lt_of_lt_of_le (by linarith : (1:ℝ)<x) hxN
    have hLp : 0<Real.log N := Real.log_pos hN2
    norm_num only [show (10^4:ℝ)=10000 by norm_num]
    have he := mul_le_mul_of_nonneg_left
      (energy_le_correlations lam l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁ b hlam hLp.le hb) hM.le
    calc
      _ ≤ Real.log N^(2:ℕ)*(M*diagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁+
          M*offDiagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁) := by nlinarith [he]
      _ ≤ Real.log N^(2:ℕ)*(C₁*(N:ℝ)^2*Real.log N^(632-8*A)+
          C₂*(N:ℝ)^2*Real.log N^(632-8*A)) :=
        mul_le_mul_of_nonneg_left (add_le_add hd ho) (sq_nonneg _)
      _ = _ := by
        rw [show 634-8*A=(2:ℝ)+(632-8*A) by ring,Real.rpow_add hLp]
        simp only [Real.rpow_ofNat]
        ring
  intro A hA l₃ hl₃
  obtain ⟨D, hD, hm⟩ := coefficient_mass
  obtain ⟨C, N₀, hC, he⟩ := row_energy A hA l₃ hl₃
  refine ⟨D + C + 1, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi a b ha hb
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN3nat : 3 ≤ N := by exact_mod_cast hN3
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith : 1 ≤ x) (by norm_num : (0 : ℝ) ≤ 1 / 1000)).trans hlo
  have hMbound : M ≤ 2 * N := by nlinarith
  have hmass := hm N hN3nat M M₁ hM hMM₁ hM₁ hMbound a ha
  have henergy := he N hodd hN₀ lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi b hb
  have hE0 : 0 ≤ energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := by
    unfold energy
    positivity
  have hp : Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A) =
      (Real.log N ^ (330 - 4 * A)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL, ← Real.rpow_mul_natCast hL.le]
    congr 1
    ring
  have hs := (bilinear_sq_le_energy lam l₃ _ N α x M M₁ H H₁ a b).trans
    (mul_le_mul_of_nonneg_right hmass hE0)
  have hs' : ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ^ 2 ≤
      (D * C) * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 := by
    calc
      _ ≤ (D * M * Real.log N ^ (26 : ℕ)) *
          energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := hs
      _ = (D * Real.log N ^ (26 : ℕ)) *
          (M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b) := by ring
      _ ≤ (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = _ := by rw [show (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) =
          D * C * (N : ℝ) ^ 2 *
            (Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A)) by ring, hp]
  have hc : D * C ≤ (D + C + 1) ^ 2 := by nlinarith [sq_nonneg (D - C)]
  have hs'' := hs'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ)))
    (sq_nonneg (Real.log N ^ (330 - 4 * A))))
  have ht : (D + C + 1) ^ 2 * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 =
      ((D + C + 1) * N * Real.log N ^ (330 - 4 * A)) ^ 2 := by ring
  rw [ht] at hs''
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs''

section HeathPort

open LeanLab.Tolev2009.Sup83Heath

/-! ### Port of the Decomp424 chain, see Sup83Heath for the copied proved inputs -/

/-- Same statement as Decomp424a.grouped_annular_decomposition, PROVED here in route
burst 7 through Sup83Group.grouped_blocks: Heath Brown's identity on dyadic boxes, the
grouping into Type I and Type II blocks and the tau5 coefficient bounds.
Tolev 1999 page 71 Lemma 4 and page 83 displays 53 and 54.
Heath Brown 1982 pages 1367 to 1368 give the six variable dyadic subdivision and grouping.
The coefficient identity is already proved. This leaf only groups its explicit polynomial
on one annulus into normalized blocks. There is no outer shell or prime conversion. -/
theorem grouped_annular_decomposition :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 3 ≤ X₀ ∧ ∀ N : ℕ, 1 ≤ Real.log N →
      ∀ x : ℝ, X₀ ≤ x → x ≤ N →
      ∀ lam : ℕ → ℝ, ∀ l₃ K : ℕ, ∀ α : ℝ,
        ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (6 : ℕ) ∧
        ∃ M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
          Sup83Heath.annularHeathBrown lam l₃ K N α x =
            ∑ j : Fin J, c j * bilinear lam l₃ K N α x
              (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
          ∀ j : Fin J,
            ‖c j‖ ≤ C ∧
            0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
            0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
            x / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x ∧
            (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
            ((x ^ ((249 : ℝ) / 500) ≤ H j ∧
                (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
              (x ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) ∧
                ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  obtain ⟨C, X₀, hC, hX₀, h⟩ := Sup83Group.grouped_blocks
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro N hL x hx hxN lam l₃ K α
  set w : ℕ → ℂ := fun n => ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ) with hw
  obtain ⟨n, hn, J, hJ, c, M, M₁, H, H₁, a, b, hS, hb⟩ := h N hL x hx hxN w
  refine ⟨J, (Nat.cast_le.mpr hJ).trans hn, M, M₁, H, H₁, a, b, c, ?_, fun j => hb j⟩
  have h1 : Sup83Heath.annularHeathBrown lam l₃ K N α x =
      Sup83Group.annSum w N x
        (Sup83Heath.heathBrownPolynomial ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊) := by
    unfold Sup83Heath.annularHeathBrown Sup83Group.annSum
    apply sum_congr rfl
    intro n _
    split_ifs
    · simp only [hw, mul_assoc]
    · rfl
  rw [h1, hS]
  apply sum_congr rfl
  intro j _
  congr 1
  unfold bilinear Sup83Group.blockSum
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro l _
  split_ifs
  · simp only [hw, mul_assoc]
  · rfl

/-- COPY of Decomp424a.annular_decomposition, Tolev 1999 page 71 Lemma 4.
The annular von Mangoldt identity follows from the explicit polynomial grouping.
Uses grouped_annular_decomposition, now proved. The coefficient identity is proved. -/
theorem annular_decomposition :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 3 ≤ X₀ ∧ ∀ N : ℕ, 1 ≤ Real.log N →
      ∀ x : ℝ, X₀ ≤ x → x ≤ N →
      ∀ lam : ℕ → ℝ, ∀ l₃ K : ℕ, ∀ α : ℝ,
        ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (6 : ℕ) ∧
        ∃ M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
          Sup83Heath.annularMangoldt lam l₃ K N α x =
            ∑ j : Fin J, c j * bilinear lam l₃ K N α x
              (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
          ∀ j : Fin J,
            ‖c j‖ ≤ C ∧
            0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
            0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
            x / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x ∧
            (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
            ((x ^ ((249 : ℝ) / 500) ≤ H j ∧
                (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
              (x ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) ∧
                ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  obtain ⟨C, X₀, hC, hX₀, hgroup⟩ := grouped_annular_decomposition
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro N hL x hx hxN lam l₃ K α
  simpa only [annularMangoldt_eq_heathBrown lam l₃ K N α x (hX₀.trans hx)] using
    hgroup N hL x hx hxN lam l₃ K α


/-- COPY of Decomp424c.retained_identity, Tolev 1999 page 82 displays 52 to 54.
The full retained identity follows from the annular step and proved shell bookkeeping. -/
theorem retained_identity :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (7 : ℕ) ∧
          ∃ x M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
            retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α =
              ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
                (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
            ∀ j : Fin J,
              ‖c j‖ ≤ C ∧
              (N : ℝ) * Real.log N ^ (-4 * A) ≤ x j ∧ x j ≤ N ∧ 2 < x j ∧
              0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
              0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
              x j / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x j ∧
              (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
              ((x j ^ ((249 : ℝ) / 500) ≤ H j ∧
                  (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
                (x j ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x j ^ ((1 : ℝ) / 3) ∧
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  classical
  intro A hA l₃ hl₃
  obtain ⟨C, X₀, hC, hX₀, hann⟩ := annular_decomposition
  obtain ⟨N₀, hN₀⟩ := eventual_retained_radius A X₀ (by linarith)
  let d : ℝ := 1 / Real.log 2 + 2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨C * d + C, N₀, by positivity, ?_⟩
  intro N hodd hN lam hlam α
  obtain ⟨hL, hY⟩ := hN₀ N hN
  let y : ℝ := (N : ℝ) * Real.log N ^ (-4 * A)
  let t : ℕ := Nat.clog 2 N
  let r : Fin t → ℝ := fun i => y * 2 ^ (i : ℕ)
  have hy : 1 ≤ y := by dsimp [y]; linarith
  have hr : ∀ i : Fin t, y ≤ r i := by
    intro i
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
  have hall : ∀ i : Fin t,
      ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (6 : ℕ) ∧
      ∃ M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
        annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i) =
          ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i)
            (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
        ∀ j : Fin J,
          r i ≤ N ∧ ‖c j‖ ≤ C ∧
          0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
          0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
          (r i) / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * (r i) ∧
          (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
          (((r i) ^ ((249 : ℝ) / 500) ≤ H j ∧
              (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
            ((r i) ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * (r i) ^ ((1 : ℝ) / 3) ∧
              ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
    intro i
    by_cases hi : r i ≤ N
    · obtain ⟨J, hJ, M, M₁, H, H₁, a, b, c, he, hb⟩ :=
        hann N hL (r i) (hY.trans (hr i)) hi lam l₃ _ α
      exact ⟨J, hJ, M, M₁, H, H₁, a, b, c, he, fun j => ⟨hi, hb j⟩⟩
    · refine ⟨0, ?_, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
        Fin.elim0, Fin.elim0, Fin.elim0, ?_, fun j => Fin.elim0 j⟩
      · simpa using mul_nonneg hC (pow_nonneg (show 0 ≤ Real.log N by linarith) 6)
      · simpa using annularMangoldt_eq_zero lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i)
          (le_of_not_ge hi)
  choose Js hJs M M₁ H H₁ a b c he hb using hall
  let U := (i : Fin t) × Fin (Js i)
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  have hcard : (Fintype.card U : ℝ) = ∑ i : Fin t, (Js i : ℝ) := by
    simp [U, Fintype.card_sigma, Nat.cast_sum]
  refine ⟨Fintype.card U, ?_, (fun j => r (e.symm j).1),
    (fun j => M (e.symm j).1 (e.symm j).2), (fun j => M₁ (e.symm j).1 (e.symm j).2),
    (fun j => H (e.symm j).1 (e.symm j).2), (fun j => H₁ (e.symm j).1 (e.symm j).2),
    (fun j => a (e.symm j).1 (e.symm j).2), (fun j => b (e.symm j).1 (e.symm j).2),
    (fun j => c (e.symm j).1 (e.symm j).2), ?_, ?_⟩
  · calc
      (Fintype.card U : ℝ) = ∑ i : Fin t, (Js i : ℝ) := hcard
      _ ≤ ∑ i : Fin t, C * Real.log N ^ (6 : ℕ) := sum_le_sum (fun i _ => hJs i)
      _ = (t : ℝ) * (C * Real.log N ^ (6 : ℕ)) := by simp
      _ ≤ (d * Real.log N) * (C * Real.log N ^ (6 : ℕ)) :=
        mul_le_mul_of_nonneg_right (shell_count_le N hL) (by positivity)
      _ = (C * d) * Real.log N ^ (7 : ℕ) := by ring
      _ ≤ (C * d + C) * Real.log N ^ (7 : ℕ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hcover : (N : ℝ) ≤ y * 2 ^ t := by
      have hp : (N : ℝ) ≤ 2 ^ t := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) N
      exact hp.trans (le_mul_of_one_le_left (by positivity) hy)
    calc
      retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α =
          ∑ i : Fin t, annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i) := by
        change _ = ∑ i : Fin t, annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
          (y * 2 ^ (i : ℕ))
        exact (retainedMangoldt_eq_annuli A lam l₃ _ N t α hcover).trans
          (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
            annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (y * 2 ^ j)) t).symm
      _ = ∑ i : Fin t, ∑ j : Fin (Js i), c i j *
          bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i)
            (M i j) (M₁ i j) (H i j) (H₁ i j) (a i j) (b i j) := by simp_rw [he]
      _ = ∑ u : U, c u.1 u.2 * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r u.1)
            (M u.1 u.2) (M₁ u.1 u.2) (H u.1 u.2) (H₁ u.1 u.2) (a u.1 u.2) (b u.1 u.2) :=
        (Fintype.sum_sigma (fun u : U => c u.1 u.2 *
          bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r u.1)
            (M u.1 u.2) (M₁ u.1 u.2) (H u.1 u.2) (H₁ u.1 u.2) (a u.1 u.2) (b u.1 u.2))).symm
      _ = _ := (e.symm.sum_comp _).symm
  · intro j
    let u := e.symm j
    have hh := hb u.1 u.2
    exact ⟨hh.2.1.trans (by nlinarith [mul_nonneg hC hd]),
      hr u.1, hh.1, by linarith [hY.trans (hr u.1)], hh.2.2⟩

/-- Tolev 1999 page 71 Lemma 4 and page 82 display 52 followed by 53 and 54.
Apply Heath Brown's identity on dyadic shells, omitting the initial short segment.
The remainder includes that segment and the prime power conversion.
There are at most C log N to seven blocks after shell subdivision.
The source's tau5 coefficient constants are moved into the bounded scalars c.
Route burst 7: proof copied from Decomp424c.prime_decomposition; the grouping step
grouped_annular_decomposition above and the conversion error in Sup83Heath are proved. -/
theorem prime_decomposition :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (7 : ℕ) ∧
          ∃ r : ℂ, ‖r‖ ≤ C * N * Real.log N ^ (330 - 4 * A) ∧
          ∃ x M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
            Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α = r +
              ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
                (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
            ∀ j : Fin J,
              ‖c j‖ ≤ C ∧
              (N : ℝ) * Real.log N ^ (-4 * A) ≤ x j ∧ x j ≤ N ∧ 2 < x j ∧
              0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
              0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
              x j / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x j ∧
              (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
              ((x j ^ ((249 : ℝ) / 500) ≤ H j ∧
                  (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
                (x j ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x j ^ ((1 : ℝ) / 3) ∧
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := prime_power_and_initial_segment A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := retained_identity A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨J, hJ, x, M, M₁, H, H₁, a, b, c, he, hb⟩ := h₂ N hodd hN₂ lam hlam α
  refine ⟨J, ?_, Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α -
    retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α, ?_,
    x, M, M₁, H, H₁, a, b, c, ?_, ?_⟩
  · exact hJ.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (by positivity))
  · apply (h₁ N hodd hN₁ lam hlam α).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · rw [he]
    ring
  · intro j
    exact ⟨(hb j).1.trans (le_add_of_nonneg_left hC₁), (hb j).2⟩

end HeathPort

end LeanLab.Tolev2009.Sup83Split
