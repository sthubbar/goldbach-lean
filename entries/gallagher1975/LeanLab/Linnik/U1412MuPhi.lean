module

public import LeanLab.Linnik.U1394Lemma43Lower
public import LeanLab.PNTPort.BV.Helpers

/-!
Li-Liu, arXiv 2610.15784, Section 4, proof of Lemma 4.3, read by WebFetch on
arxiv.org/html/2610.15784, 2026-10-21: "Summing over these q gives
  R₁(0) ≥ (∑_{q ≤ P/T} μ(q)²/φ(q)) ∫_{-T/N}^{T/N} |S(β)|² dβ,  ∑_{q ≤ P/T} μ(q)²/φ(q) = log P + O_T(1)."

This file:
* `log_le_sum_mu_sq_div_totient`: for real `y > 0`, `log y ≤ ∑_{q ≤ y} μ(q)²/φ(q)`, the classical
  lower bound. NOT new to the lab: it is a two-line consequence of `log_le_sum_sqf`,
  PNTPort/LargeSieve/MontgomeryBT.lean, unit U-5551, already used in LiLiuLemma43.lean, and of
  `MuPhi.log_le_mu_phi_sum` at r = 1, RieselVaughan1983/MuPhiSum.lean, unit U-6712.
  Mathlib has neither.
* `log_sub_log_le_sum`: the paper's form, `log P - log T ≤ ∑_{q ≤ P/T} μ(q)²/φ(q)`, so the
  `O_T(1)` of the lower half is `-log T`, explicit.
* `sum_mu_sq_div_totient_le`: the upper bound `∑_{q ≤ y} μ(q)²/φ(q) ≤ 4 (1 + log y)`, from
  `PNTPort.BV.sum_inv_totient_le`. WEAKER than the classical `log y + O(1)`: the coefficient
  of `log y` is 4, not 1. The paper's argument uses only the lower half.
* `lemma43_lower_logP`: the lower half of display (36) in the paper's own normalisation,
  `R₁(0) ≥ (1 - ε) N log P` eventually, for any arc parameter `P = P(N) → ∞` with
  `P ≤ N^{1-κ}` and `2P² < N`; this replaces the `log(Q + 1)` of
  `U1394Lemma43Lower.lemma43_lower_one` by `log P`, through `log_sub_log_le_sum`'s floor step.
* `vacuity_logP`: `κ = 1/2`, `P(N) = N^{1/2}/2` meet the hypotheses.

Unit U-1412, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own step. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1412MuPhi

open Finset Real Filter ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve LeanLab.Linnik.LiLiuDisplay37

/-- **Classical lower bound.** For real `y > 0`, `log y ≤ ∑_{q ≤ y} μ(q)²/φ(q)`. -/
theorem log_le_sum_mu_sq_div_totient (y : ℝ) (hy : 0 < y) :
    Real.log y ≤ ∑ q ∈ Icc 1 ⌊y⌋₊, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) := by
  have h1 : Real.log y ≤ Real.log ((⌊y⌋₊ : ℝ) + 1) :=
    Real.log_le_log hy (Nat.lt_floor_add_one y).le
  have hlog := log_le_sum_sqf ⌊y⌋₊
  have hsqf : ∑ q ∈ (Icc 1 ⌊y⌋₊).filter Squarefree, ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) ≤
      ∑ q ∈ Icc 1 ⌊y⌋₊, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro q _
    split_ifs with h
    · rw [LeanLab.Linnik.LiLiuLemma43.mu_sq_div_totient_sqf h]
    · positivity
  exact h1.trans (hlog.trans hsqf)

/-- **The paper's form of the lower half.** For `P, T > 0`,
`log P - log T ≤ ∑_{q ≤ P/T} μ(q)²/φ(q)`: the `O_T(1)` is `-log T`. -/
theorem log_sub_log_le_sum (P T : ℝ) (hP : 0 < P) (hT : 0 < T) :
    Real.log P - Real.log T ≤ ∑ q ∈ Icc 1 ⌊P / T⌋₊, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) := by
  rw [← Real.log_div hP.ne' hT.ne']
  exact log_le_sum_mu_sq_div_totient _ (div_pos hP hT)

/-- **Upper bound, weaker than classical.** For `y ≥ 1`,
`∑_{q ≤ y} μ(q)²/φ(q) ≤ 4 (1 + log y)`. The classical form has coefficient 1 on `log y`. -/
theorem sum_mu_sq_div_totient_le (y : ℝ) (hy : 1 ≤ y) :
    ∑ q ∈ Icc 1 ⌊y⌋₊, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) ≤ 4 * (1 + Real.log y) := by
  have h1 : ∑ q ∈ Icc 1 ⌊y⌋₊, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) ≤
      ∑ q ∈ Icc 1 ⌊y⌋₊, (1 : ℝ) / q.totient := by
    apply Finset.sum_le_sum
    intro q _
    exact LeanLab.PNTPort.BV.sqfTot_le q
  have h2 : ∑ q ∈ Icc 1 ⌊y⌋₊, (1 : ℝ) / q.totient ≤ 4 * (1 + Real.log ⌊y⌋₊) := by
    -- the proof of `PNTPort.BV.sum_inv_totient_le`, which states only `∃ C`, with its C = 4
    have hH : ∑ j ∈ Icc 1 ⌊y⌋₊, (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log ⌊y⌋₊ := by
      have h := harmonic_le_one_add_log ⌊y⌋₊
      rw [harmonic_eq_sum_Icc] at h
      push_cast at h
      simpa [one_div] using h
    have step : ∀ m ∈ Icc 1 ⌊y⌋₊, (1 : ℝ) / m.totient =
        ∑ d ∈ m.divisors, (LeanLab.PNTPort.BV.sqfTot d / (d : ℝ)) * (1 / (((m / d : ℕ) : ℝ))) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm0 : m ≠ 0 := by omega
      have e : ∀ d ∈ m.divisors, (LeanLab.PNTPort.BV.sqfTot d / (d : ℝ)) *
          (1 / (((m / d : ℕ) : ℝ))) = LeanLab.PNTPort.BV.sqfTot d / (m : ℝ) := by
        intro d hd
        rw [Nat.mem_divisors] at hd
        have hd0 : d ≠ 0 := by rintro rfl; exact hm0 (Nat.eq_zero_of_zero_dvd hd.1)
        rw [Nat.cast_div hd.1 (by exact_mod_cast hd0)]
        have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
        have : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
        field_simp
      rw [Finset.sum_congr rfl e, ← Finset.sum_div, LeanLab.PNTPort.BV.inv_totient_eq hm0]
      ring
    rw [Finset.sum_congr rfl step]
    calc _ ≤ (∑ d ∈ Icc 1 ⌊y⌋₊, LeanLab.PNTPort.BV.sqfTot d / (d : ℝ)) *
            ∑ j ∈ Icc 1 ⌊y⌋₊, 1 / (j : ℝ) :=
          LeanLab.PNTPort.BV.sum_divisors_le_mul _ (fun d => LeanLab.PNTPort.BV.sqfTot d / (d : ℝ))
            (fun j => 1 / (j : ℝ))
            (fun n => by have := LeanLab.PNTPort.BV.sqfTot_nonneg n; positivity)
            (fun n => by positivity)
      _ ≤ 4 * (1 + Real.log ⌊y⌋₊) := by
          apply mul_le_mul (LeanLab.PNTPort.BV.sum_inv_mul_totient_le _) hH
            (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
  have h3 : Real.log ⌊y⌋₊ ≤ Real.log y := by
    have : (0 : ℝ) < ⌊y⌋₊ := by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
      exact_mod_cast this
    exact Real.log_le_log this (Nat.floor_le (by linarith))
  linarith

/-- **Lemma 4.3, lower half of (36), in the paper's normalisation `N log P`.** For `κ > 0`,
`0 < ε < 1` and any arc parameter `P(N) → ∞` with `P(N) ≤ N^{1-κ}` and `2P(N)² < N`
eventually, `R₁(0) ≥ (1 - ε) N log P(N)` for all large `N`. -/
theorem lemma43_lower_logP {κ : ℝ} (hκ : 0 < κ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (P : ℕ → ℝ) (hP : Tendsto P atTop atTop)
    (hPup : ∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ))
    (hP2 : ∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) :
    ∀ᶠ N : ℕ in atTop, (1 - ε) * N * Real.log (P N) ≤
      LeanLab.Linnik.LiLiuLemma43Int.R10 (primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N) logw (P N) N := by
  obtain ⟨T, hT1, hev⟩ := LeanLab.Linnik.U1394Lemma43Lower.lemma43_lower_one hκ (half_pos hε)
  have hT0 : 0 < T := by linarith
  set M : ℝ := (1 - ε / 2) * Real.log T / (ε / 2) with hM
  have hlogP : Tendsto (fun N => Real.log (P N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hP
  filter_upwards [hev, hPup, hP2, hP.eventually_ge_atTop T, hlogP.eventually_ge_atTop M]
    with N hN hup h2 hPT hlog
  have hPpos : 0 < P N := by linarith
  set Q : ℕ := ⌊P N / T⌋₊ with hQdef
  have hdiv : 1 ≤ P N / T := (one_le_div hT0).2 hPT
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hdiv)
  have hQle : (Q : ℝ) ≤ P N / T := Nat.floor_le (by linarith)
  have hQP : (Q : ℝ) ≤ P N := hQle.trans (div_le_self hPpos.le hT1)
  have hQT : (Q : ℝ) * T ≤ P N := (le_div_iff₀ hT0).1 hQle
  have hQM : Q ≤ ⌊(N : ℝ) ^ (1 - κ)⌋₊ := Nat.le_floor (hQP.trans hup)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2' : 2 * P N ^ 2 < T * N := by nlinarith
  have key := hN Q (P N) hQ1 hQM hQP hQT h2'
  have hl : Real.log (P N) - Real.log T ≤ Real.log ((Q : ℝ) + 1) := by
    rw [← Real.log_div hPpos.ne' hT0.ne']
    exact Real.log_le_log (div_pos hPpos hT0) (Nat.lt_floor_add_one _).le
  have hMle : (1 - ε / 2) * Real.log T ≤ (ε / 2) * Real.log (P N) := by
    have := (div_le_iff₀ (half_pos hε)).1 (hM ▸ hlog)
    linarith
  have h1 : (1 - ε) * Real.log (P N) ≤ (1 - ε / 2) * Real.log ((Q : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 1 - ε / 2)
    nlinarith
  calc (1 - ε) * N * Real.log (P N) = N * ((1 - ε) * Real.log (P N)) := by ring
    _ ≤ N * ((1 - ε / 2) * Real.log ((Q : ℝ) + 1)) := mul_le_mul_of_nonneg_left h1 hN0
    _ = (1 - ε / 2) * N * Real.log ((Q : ℝ) + 1) := by ring
    _ ≤ _ := key

/-- Vacuity: `κ = 1/2`, `P(N) = N^{1/2}/2` meet the hypotheses of `lemma43_lower_logP`. -/
theorem vacuity_logP :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) / 2) atTop atTop ∧
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (N : ℝ) ^ (1 - 1 / 2 : ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, 2 * ((N : ℝ) ^ (1 / 2 : ℝ) / 2) ^ 2 < N) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num)
  · refine Eventually.of_forall fun N => ?_
    have : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by positivity
    norm_num
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsq : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have : 2 * ((N : ℝ) ^ (1 / 2 : ℝ) / 2) ^ 2 = N / 2 := by
      rw [div_pow, hsq]; ring
    rw [this]
    linarith

/-- The two together: the lower half of (36) at `κ = 1/2`, `P = N^{1/2}/2`, `ε = 1/10`. -/
theorem lemma43_lower_logP_instance :
    ∀ᶠ N : ℕ in atTop, (1 - 1 / 10) * N * Real.log ((N : ℝ) ^ (1 / 2 : ℝ) / 2) ≤
      LeanLab.Linnik.LiLiuLemma43Int.R10 (primesIn ⌊(N : ℝ) ^ (1 - 1 / 2 : ℝ)⌋₊ N) logw
        ((N : ℝ) ^ (1 / 2 : ℝ) / 2) N :=
  lemma43_lower_logP (by norm_num) (by norm_num) (by norm_num) _ vacuity_logP.1
    vacuity_logP.2.1 vacuity_logP.2.2

end LeanLab.Linnik.U1412MuPhi
