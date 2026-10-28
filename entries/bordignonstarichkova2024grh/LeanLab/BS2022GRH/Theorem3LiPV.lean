module

public import LeanLab.BS2022GRH.Theorem3
public import LeanLab.BS2022GRH.LiPV

/-!
BS2022GRH, P0021: Theorem 3 and Corollary 1 with the principal value `li` and `U_N` defined,
so the two inputs `li(y) ≤ ∫₂^y dt/log t + 2` and `U_N ≥ 1` of `theorem3_of` are PROVED.

* `cbrt_ge_two`: `N^{1/3} ≥ 2` for `N ≥ X₂ ≥ exp(exp 15.85)`.
* `UN n = ∏_{p | n, p > 2} (p - 1)/(p - 2)`, the factor of Chen's theorem as in the standard
  explicit Chen literature; this display was not re-read from the paper in this run.
  `one_le_UN`: `U_N ≥ 1`.
* `theorem3_of_liPV`, `corollary1_of_liPV`: real `N`, `li = liPV (N^{1/3})`, CONDITIONAL ON
  Lemma 10, Theorems 5, 6, 7 and `U ≥ 1`.
* `theorem3_of_nat`, `corollary1_of_nat`: `N = n` a natural number, `U = UN n`,
  `li = liPV (n^{1/3})`, CONDITIONAL ON Lemma 10 and Theorems 5, 6, 7 only.

AI-written Lean code, Claude, run 20261019T0202Z-9877, unit U-0997. Checked only by the
Lean kernel. Binary Goldbach is OPEN; Chen's theorem itself is not in doubt.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real

/-- `N^{1/3} ≥ 2` for `N ≥ X₂ ≥ exp(exp 15.85)`. -/
lemma cbrt_ge_two {X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    2 ≤ N ^ (1 / 3 : ℝ) := by
  obtain ⟨hL, hN0⟩ := logN_ge hX hN
  rw [rpow_def_of_pos hN0]
  have := add_one_le_exp (log N * (1 / 3))
  linarith

/-- `U_N = ∏_{p | n, p > 2} (p - 1)/(p - 2)`. -/
noncomputable def UN (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2))

lemma one_le_UN (n : ℕ) : 1 ≤ UN n := by
  unfold UN
  have h : ∀ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    intro p hp
    have h2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.1 hp).2
    rw [le_div_iff₀ (by linarith)]; linarith
  exact Finset.one_le_prod₀ h

/-- **Theorem 3 with the principal value li, CONDITIONAL** ON Lemma 10, Theorems 5, 6, 7 at the
Section 5.4 parameters and `U ≥ 1`; the `li` input is PROVED. -/
theorem theorem3_of_liPV {pi2 S0 S6 SB U X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N)
    (hU : 1 ≤ U)
    (h10 : S0 - 1 / 2 * S6 - 1 / 2 * SB - 2 * N ^ (7 / 8 : ℝ) - N ^ (1 / 3 : ℝ) < pi2)
    (h5 : 8 * (U * N / log N ^ 2) * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N < S0)
    (h6 : S6 ≤ 8 * (U * N / log N ^ 2) * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ N)
    (h7 : SB ≤ U * N / log N ^ 2 * thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5)) (liPV (N ^ (1 / 3 : ℝ))) N) :
    4e-4 * (U * N / log N ^ 2) < pi2 :=
  theorem3_of hX hN hU (liPV_le (cbrt_ge_two hX hN)) h10 h5 h6 h7

/-- **Corollary 1 with the principal value li, CONDITIONAL** ON Lemma 10, Theorems 5, 6, 7 and
`U ≥ 1`: `π₂'(N) > 0`. -/
theorem corollary1_of_liPV {pi2 pi2' S0 S6 SB U X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂)
    (hN : X₂ ≤ N) (hU : 1 ≤ U)
    (h10 : S0 - 1 / 2 * S6 - 1 / 2 * SB - 2 * N ^ (7 / 8 : ℝ) - N ^ (1 / 3 : ℝ) < pi2)
    (h5 : 8 * (U * N / log N ^ 2) * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N < S0)
    (h6 : S6 ≤ 8 * (U * N / log N ^ 2) * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ N)
    (h7 : SB ≤ U * N / log N ^ 2 * thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5)) (liPV (N ^ (1 / 3 : ℝ))) N)
    (hC : pi2 - sqrt N - 1 ≤ pi2') :
    0 < pi2' :=
  corollary1_of hX hN hU (liPV_le (cbrt_ge_two hX hN)) h10 h5 h6 h7 hC

/-- **Theorem 3 for a natural number `N = n`, CONDITIONAL** ON Lemma 10 and Theorems 5, 6, 7 at
the Section 5.4 parameters only, with `U = U_n` and `li = liPV`. -/
theorem theorem3_of_nat {pi2 S0 S6 SB X₂ : ℝ} {n : ℕ} (hX : exp (exp 15.85) ≤ X₂)
    (hN : X₂ ≤ (n : ℝ))
    (h10 : S0 - 1 / 2 * S6 - 1 / 2 * SB - 2 * (n : ℝ) ^ (7 / 8 : ℝ) - (n : ℝ) ^ (1 / 3 : ℝ) < pi2)
    (h5 : 8 * (UN n * (n : ℝ) / log (n : ℝ) ^ 2) * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ (n : ℝ) < S0)
    (h6 : S6 ≤ 8 * (UN n * (n : ℝ) / log (n : ℝ) ^ 2) * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ (n : ℝ))
    (h7 : SB ≤ UN n * (n : ℝ) / log (n : ℝ) ^ 2 * thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * (n : ℝ) ^ (1 / 8 : ℝ))) ((n : ℝ) ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * (n : ℝ) ^ (1 / 8 : ℝ)) (sqrt (n : ℝ) / log (n : ℝ) ^ 5)) (liPV ((n : ℝ) ^ (1 / 3 : ℝ))) (n : ℝ)) :
    4e-4 * (UN n * (n : ℝ) / log (n : ℝ) ^ 2) < pi2 :=
  theorem3_of_liPV hX hN (one_le_UN n) h10 h5 h6 h7


end LeanLab.BS2022GRH
