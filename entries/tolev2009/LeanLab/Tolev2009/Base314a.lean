module

public import LeanLab.Tolev2009.ArcGeometry314
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
AI wrote this Lean code. Codex task314. Moved here by U-1626 with every statement and proof unchanged.
Binary Goldbach is open.
Source: Halupczok 2008 pages 7 to 11, the expansion into O1, O2 and O3.
The prime sum adaptation is explicit. This base holds the definitions and exact expansions only.
Progression346 and Integral314 import this base, so Decomp314a can import Decomp346a, b and c
without an import cycle. The namespace stays Decomp314a, so every declaration name is unchanged.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp314a
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286a

/-- Halupczok page 7, the main term of one progression polynomial. -/
noncomputable def approx (k l N q a : ℕ) (β : ℝ) : ℂ :=
  localSum k l q a / (k.totient : ℂ) * geometric N β

/-- Halupczok pages 7 to 8, the exact remainder for one prime polynomial. -/
noncomputable def residual (k l N q a : ℕ) (β : ℝ) : ℂ :=
  Sexp k l N ((a : ℝ) / q + β) - approx k l N q a β

/-- Halupczok page 8, the homogeneous part with j remainder factors. -/
noncomputable def homogeneous (j : ℕ) (b d : Fin 3 → ℂ) : ℂ :=
  if j = 1 then d 0 * b 1 * b 2 + b 0 * d 1 * b 2 + b 0 * b 1 * d 2
  else if j = 2 then d 0 * d 1 * b 2 + d 0 * b 1 * d 2 + b 0 * d 1 * d 2
  else if j = 3 then d 0 * d 1 * d 2 else 0

/-- Halupczok page 8, the signed integral contribution of degree j.
This retains the actual complex remainder instead of its O notation majorant. -/
noncomputable def errorTerm (j : ℕ) (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)),
      homogeneous j (fun i => approx (k i) (l i) N q a β)
        (fun i => residual (k i) (l i) N q a β) *
          ee (-((N : ℝ) * ((a : ℝ) / q + β)))).re

/-- Halupczok page 8, the finite algebra behind O1, O2 and O3. -/
theorem homogeneous_expansion (b d : Fin 3 → ℂ) :
    (∏ i, (b i + d i)) - ∏ i, b i =
      (homogeneous 1 b d + homogeneous 2 b d) + homogeneous 3 b d := by
  simp only [Fin.prod_univ_three, homogeneous]
  norm_num
  ring

/-- Halupczok page 7, the finite geometric polynomial is continuous. -/
theorem continuous_geometric (N : ℕ) : Continuous (geometric N) := by
  unfold geometric
  exact continuous_finsetSum _ (fun m _ => continuous_ee.comp (continuous_id.mul continuous_const))

/-- Halupczok page 8, every fixed homogeneous arc integrand is continuous. -/
theorem continuous_error_integrand (j : ℕ) (k l : Fin 3 → ℕ) (N q a : ℕ) :
    Continuous (fun β : ℝ => homogeneous j
      (fun i => approx (k i) (l i) N q a β)
      (fun i => residual (k i) (l i) N q a β) *
      ee (-((N : ℝ) * ((a : ℝ) / q + β)))) := by
  have hb (i : Fin 3) : Continuous (fun β : ℝ => approx (k i) (l i) N q a β) :=
    continuous_const.mul (continuous_geometric N)
  have hd (i : Fin 3) : Continuous (fun β : ℝ => residual (k i) (l i) N q a β) :=
    ((continuous_Sexp (k i) (l i) N).comp (continuous_const.add continuous_id)).sub (hb i)
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have he : Continuous (fun β : ℝ => ee (-((N : ℝ) * ((a : ℝ) / q + β)))) :=
    continuous_ee.comp (by fun_prop)
  unfold homogeneous
  split_ifs <;> fun_prop

/-- Halupczok page 8, the exact local integral expansion before any error estimate. -/
theorem local_arc_expansion (τ : ℝ) (k l : Fin 3 → ℕ) (N q a : ℕ) :
    (∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)),
      integrand k l N ((a : ℝ) / q + β)) =
      (ee (-((a : ℝ) * N / q)) * (∏ i, localSum (k i) (l i) q a) /
        (∏ i : Fin 3, ((k i).totient : ℂ))) * arcIntegral τ N q +
      ((∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)),
        homogeneous 1 (fun i => approx (k i) (l i) N q a β)
          (fun i => residual (k i) (l i) N q a β) * ee (-((N : ℝ) * ((a : ℝ) / q + β)))) +
       (∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)),
        homogeneous 2 (fun i => approx (k i) (l i) N q a β)
          (fun i => residual (k i) (l i) N q a β) * ee (-((N : ℝ) * ((a : ℝ) / q + β))))) +
      (∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)),
        homogeneous 3 (fun i => approx (k i) (l i) N q a β)
          (fun i => residual (k i) (l i) N q a β) * ee (-((N : ℝ) * ((a : ℝ) / q + β)))) := by
  let m : ℝ → ℂ := fun β =>
    (ee (-((a : ℝ) * N / q)) * (∏ i, localSum (k i) (l i) q a) /
      (∏ i : Fin 3, ((k i).totient : ℂ))) *
        (geometric N β ^ 3 * ee (-((N : ℝ) * β)))
  let e : ℕ → ℝ → ℂ := fun j β => homogeneous j
    (fun i => approx (k i) (l i) N q a β)
    (fun i => residual (k i) (l i) N q a β) * ee (-((N : ℝ) * ((a : ℝ) / q + β)))
  have hm : Continuous m := continuous_const.mul
    ((continuous_geometric N).pow 3 |>.mul (continuous_ee.comp (by fun_prop)))
  have he (j : ℕ) : Continuous (e j) := continuous_error_integrand j k l N q a
  have hpoly : (fun β => integrand k l N ((a : ℝ) / q + β)) =
      fun β => ((m β + e 1 β) + e 2 β) + e 3 β := by
    funext β
    have hphase : ee (-((N : ℝ) * ((a : ℝ) / q + β))) =
      ee (-((a : ℝ) * N / q)) * ee (-((N : ℝ) * β)) := by
      rw [← ee_add]
      congr 1
      ring
    simp only [integrand, m, e, homogeneous, residual, approx, Fin.prod_univ_three, hphase]
    norm_num
    ring
  rw [hpoly]
  rw [intervalIntegral.integral_add (f := fun β => m β + e 1 β + e 2 β) (g := e 3)
    (((hm.add (he 1)).add (he 2)).intervalIntegrable _ _) ((he 3).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add (f := fun β => m β + e 1 β) (g := e 2)
    ((hm.add (he 1)).intervalIntegrable _ _) ((he 2).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add (f := m) (g := e 1)
    (hm.intervalIntegrable _ _) ((he 1).intervalIntegrable _ _)]
  dsimp only [m]
  rw [intervalIntegral.integral_const_mul]
  simp only [arcIntegral, e]
  ring

/-- Tolev page 3, the prescribed major arcs are eventually complete and disjoint. -/
theorem major_arc_regime (A : ℝ) (hA : 10 ^ 4 ≤ A) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ Qof A N ∧ 2 * Qof A N < τof A N := by
  have he := (isLittleO_log_rpow_rpow_atTop (40 * A) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hl := Real.tendsto_log_atTop.eventually_ge_atTop 1
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (he.and hl)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨heN, hL⟩ := hN₀ N hN
  have hL0 : 0 < Real.log N := by linarith
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow hL (by linarith)
  have hQ0 : 0 < Qof A N := by linarith
  have hsq : (Qof A N) ^ 2 ≤ (1 / 4 : ℝ) * N := by
    have hr : (Qof A N) ^ 2 = Real.log N ^ (40 * A) := by
      unfold Qof
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    rw [hr]
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hL0.le _),
      abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)] using heN
  refine ⟨hQ, ?_⟩
  have hp : τof A N * Qof A N = N := by unfold τof; exact div_mul_cancel₀ _ hQ0.ne'
  by_contra hn
  have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hQ0.le
  nlinarith

/-- Halupczok page 8, split into rational arcs and expand the three factors.
No progression estimate is asserted. The threshold ensures disjoint full arcs. -/
theorem rational_arc_expansion :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ k l : Fin 3 → ℕ,
        RM (Qof A N) (τof A N) k l N - model (Qof A N) (τof A N) k l N =
          (errorTerm 1 (Qof A N) (τof A N) k l N +
            errorTerm 2 (Qof A N) (τof A N) k l N) +
              errorTerm 3 (Qof A N) (τof A N) k l N := by
  intro A hA
  obtain ⟨N₀, hN₀⟩ := major_arc_regime A hA
  refine ⟨N₀, fun N hN k l => ?_⟩
  obtain ⟨hQ, hτ⟩ := hN₀ N hN
  have hi := ArcGeometry314.integral_majorArcs (Qof A N) (τof A N)
    (integrand k l N) (continuous_integrand k l N) hQ hτ
  unfold RM
  rw [hi]
  simp_rw [local_arc_expansion]
  simp [model, errorTerm, ssTerm, sum_div, sum_mul, sum_add_distrib]
  ring

end LeanLab.Tolev2009.Decomp314a
