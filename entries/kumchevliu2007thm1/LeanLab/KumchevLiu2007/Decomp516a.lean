module

public import LeanLab.KumchevLiu2007.Decomp1534a
public import LeanLab.KumchevLiu2007.Decomp1534c
public import LeanLab.KumchevLiu2007.Decomp506a

/-!
Repair leaves for Kumchev and Liu, arXiv 0801.0130, P0088 pages 13 to 16.
Definitions are written as let expressions inside each leaf statement.
This file imports neither Decomp129 nor a module that imports it.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Task516a

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Chebyshev counting: on the interval `(X, X + H]` a set `S` on which `f`
exceeds `t` has at most the total mass of `f` divided by `t` elements. -/
private lemma cnt_mul_le_sum {S : ℕ → Prop} {X H t : ℝ} (f : ℕ → ℝ) (hX : 0 ≤ X)
    (hf : ∀ n, 0 ≤ f n) (hS : ∀ n : ℕ, X < (n : ℝ) → S n → t < f n) :
    (cntIoc S X H : ℝ) * t ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, f n := by
  classical
  set T := (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n)
  have hsub : T ⊆ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
    intro n hn
    obtain ⟨hr, hXn, _⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hX).mpr hXn, ?_⟩
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hcard : (cntIoc S X H : ℝ) * t = ∑ n ∈ T, t := by
    simp [cntIoc, T, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  calc ∑ n ∈ T, t ≤ ∑ n ∈ T, f n := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨_, hXn, hSn⟩ := Finset.mem_filter.mp hn
        exact (hS n hXn hSn).le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

/-- For `L` large in terms of `B` the truncation height `L ^ B` sits below
`exp (L ^ (3 / 4))`, which is the sieve level `exp (L ^ (1 - 1/4))` that the
mean square estimate of display 49 allows. Same argument as
`Decomp129.pow_le_sieveLevel` at `delta = 1/2`. -/
private lemma logrpow_le_exp_three_quarters (B : ℝ) (hB : 0 < B) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ X : ℝ, M ≤ Real.log X →
      Real.log X ^ B ≤ Real.exp (Real.log X ^ (3 / 4 : ℝ)) := by
  set s := (3 / 4 : ℝ) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; norm_num
  have hs34 : 2 * s = 3 / 4 := by rw [hs]; ring
  refine ⟨max 1 ((B / s) ^ (1 / s)), le_max_left _ _, ?_⟩
  intro X hX
  set L := Real.log X
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hX
  have hLpos : 0 < L := by linarith
  have hBs : 0 ≤ B / s := by positivity
  have hpow : B / s ≤ L ^ s := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hBs _) (le_trans (le_max_right _ _) hX) hs0.le
    rwa [one_div, Real.rpow_inv_rpow hBs hs0.ne'] at h
  have hlog : Real.log L ≤ L ^ s / s := Real.log_le_rpow_div hLpos.le hs0
  have hLs : 0 ≤ L ^ s := Real.rpow_nonneg hLpos.le _
  have hkey : B * Real.log L ≤ L ^ (3 / 4 : ℝ) := by
    have e : L ^ (3 / 4 : ℝ) = L ^ s * L ^ s := by
      rw [← Real.rpow_add hLpos]; congr 1; rw [hs]; norm_num
    rw [e]
    calc B * Real.log L ≤ B * (L ^ s / s) := mul_le_mul_of_nonneg_left hlog hB.le
      _ = B / s * L ^ s := by ring
      _ ≤ L ^ s * L ^ s := mul_le_mul_of_nonneg_right hpow hLs
  rw [Real.rpow_def_of_pos hLpos]
  apply Real.exp_le_exp.mpr
  linarith [mul_comm (Real.log L) B]

/-- LEAF. Page 14 display 48, the lower bound of P2 of n, P by
log P to the minus 1 on H2, together with Lemma 3.8 display 49 with y equal to H
and Chebyshev's inequality: S2 of n, P is at least c over log P for all but
O of H L to the minus A integers n in H2 in the interval X, X plus H.
CITED: Lemma 3.8 and display 48 are proved on pages 14 and 15. -/
theorem eq48_49_series_lower (A : ℝ) (hA : 0 < A) :
    let series2 (n : ℕ) (P : ℝ) : ℂ := ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ c C X0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          ‖series2 n (Real.log X ^ B)‖ < c / Real.log (Real.log X ^ B)) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  intro series2
  change ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ c C X0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          ‖Task506aTask129.series2 n (Real.log X ^ B)‖ < c / Real.log (Real.log X ^ B)) X H : ℝ) ≤
          C * H / Real.log X ^ A
  obtain ⟨c, Q0, hc, hQ0, hp⟩ := Task129a.P2_lower_explicit
  refine ⟨A + 3, by linarith, ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := by linarith
  obtain ⟨C, x0, hC, hx0, hm⟩ :=
    Task506aTask342e.lemma38_two_proved (max 2 (A + 2)) (1 / 4) (le_max_left _ _) (by norm_num)
  obtain ⟨M, hM1, hMP⟩ := logrpow_le_exp_three_quarters B hBpos
  refine ⟨c / 2, 8 * C / c ^ 2,
    max x0 (Real.exp (max M (max 2 Q0))), by positivity, by positivity,
    hx0.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have hxx0 : x0 ≤ X := (le_max_left _ _).trans hX
  have hX2 : 2 ≤ X := hx0.trans hxx0
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hLM : max M (max 2 Q0) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at h
  set L := Real.log X with hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hB1 : 1 ≤ B := by linarith
  set P := L ^ B with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hLpos B
  have hLP : L ≤ P := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 hB1
    simpa using h
  have hPQ0 : Q0 ≤ P := ((le_max_right _ _).trans ((le_max_right _ _).trans hLM)).trans hLP
  have hP2 : 2 ≤ P := hL2.trans hLP
  have hlogPpos : 0 < Real.log P := Real.log_pos (by linarith)
  have hcut3 : P ≤ Real.exp (L ^ (3 / 4 : ℝ)) := hMP X ((le_max_left _ _).trans hLM)
  have hcut : P ≤ Real.exp (L ^ (1 - (1 / 4 : ℝ))) := by
    simpa only [show (3 : ℝ) / 4 = 1 - 1 / 4 by norm_num] using hcut3
  have hlogPL : Real.log P ≤ L := by
    have h1 : Real.log P ≤ Real.log (Real.exp (L ^ (3 / 4 : ℝ))) := Real.log_le_log hPpos hcut3
    rw [Real.log_exp] at h1
    have h2 := Real.rpow_le_rpow_of_exponent_le hL1
      (show (3 : ℝ) / 4 ≤ 1 by norm_num)
    rw [Real.rpow_one] at h2
    exact h1.trans h2
  have hHpos : 0 < H := (Real.rpow_pos_of_pos hXpos _).trans_le hH
  have hlow : X ^ (1 / 4 : ℝ) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)).trans hH
  have hsum := hm X H P P hxx0 hlow hHX hPpos le_rfl hcut
  have hprod := hp P hPQ0
  have key : ∀ n : ℕ, X < (n : ℝ) →
      (InH2 n ∧ ‖Task506aTask129.series2 n P‖ < (c / 2) / Real.log P) →
      (c / 2 * L⁻¹) ^ 2 <
        ‖Task506aTask129.series2 n P - Task506aTask129b.product2 n P‖ ^ 2 := by
    rintro n _ ⟨hn, hs⟩
    have hpn := hprod n hn
    have htri := norm_sub_norm_le (Task506aTask129b.product2 n P) (Task506aTask129.series2 n P)
    have hd : c / 2 / Real.log P <
        ‖Task506aTask129.series2 n P - Task506aTask129b.product2 n P‖ := by
      rw [norm_sub_rev]
      change c / Real.log P ≤ ‖Task506aTask129b.product2 n P‖ at hpn
      have heq : c / Real.log P = 2 * (c / 2 / Real.log P) := by ring
      rw [heq] at hpn
      linarith only [hpn, htri, hs]
    have ht : c / 2 * L⁻¹ ≤ c / 2 / Real.log P := by
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by positivity) hlogPpos hlogPL
    exact (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr (ht.trans_lt hd)
  have hcheb := cnt_mul_le_sum (S := fun n => InH2 n ∧
      ‖Task506aTask129.series2 n P‖ < (c / 2) / Real.log P) (H := H)
    (fun n => ‖Task506aTask129.series2 n P - Task506aTask129b.product2 n P‖ ^ 2) hXpos.le
    (fun n => by positivity) key
  have hcnt := hcheb.trans hsum
  have ht : 0 < (c / 2 * L⁻¹) ^ 2 := by positivity
  have hinv : ((c / 2 * L⁻¹) ^ 2)⁻¹ = 4 / c ^ 2 * L ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    field_simp
    norm_num
  have b1 : H / P * L * L ^ (2 : ℝ) ≤ H * L ^ (-A) := by
    have heq : H / P * L * L ^ (2 : ℝ) = H * L ^ (-B + 1 + 2) := by
      rw [Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_neg hLpos.le, Real.rpow_one]
      dsimp [P]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hHpos.le
  have b2 : H / L ^ (max 2 (A + 2)) * L ^ (2 : ℝ) ≤ H * L ^ (-A) := by
    have heq : H / L ^ (max 2 (A + 2)) * L ^ (2 : ℝ) =
        H * L ^ (-max 2 (A + 2) + 2) := by
      rw [Real.rpow_add hLpos, Real.rpow_neg hLpos.le]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_max_right 2 (A + 2)])) hHpos.le
  have hfin : (cntIoc (fun n => InH2 n ∧
      ‖Task506aTask129.series2 n P‖ < (c / 2) / Real.log P) X H : ℝ) ≤
      C * (H / P * L + H / L ^ (max 2 (A + 2))) * (4 / c ^ 2 * L ^ (2 : ℝ)) := by
    rw [← hinv, ← div_eq_mul_inv, le_div_iff₀ ht]
    exact hcnt
  calc _ ≤ C * (H / P * L + H / L ^ (max 2 (A + 2))) * (4 / c ^ 2 * L ^ (2 : ℝ)) := hfin
    _ = 4 * C / c ^ 2 * (H / P * L * L ^ (2 : ℝ) +
        H / L ^ (max 2 (A + 2)) * L ^ (2 : ℝ)) := by ring
    _ ≤ 4 * C / c ^ 2 * (H * L ^ (-A) + H * L ^ (-A)) :=
      mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)
    _ = 8 * C / c ^ 2 * H / L ^ A := by rw [Real.rpow_neg hLpos.le]; ring

end LeanLab.KumchevLiu2007.Task516a
