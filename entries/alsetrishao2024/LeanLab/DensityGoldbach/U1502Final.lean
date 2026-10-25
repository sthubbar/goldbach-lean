module

public import LeanLab.DensityGoldbach.U1502Spec
public import LeanLab.DensityGoldbach.U1502Arc
public import LeanLab.DensityGoldbach.U1502Levels

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

`NuMajorant`, PROVED, from the lab's unconditional circle method inputs: `major_arc` at `A = 21`
(Siegel-Walfisz through `PNTPort.PsiChi.siegelWalfisz`), `minor_sup` through `U1478.twS_minor`,
and Mathlib's `ψ - θ ≪ √x`. Hence Alsetri-Shao Theorem 1.2 with no cited hypothesis:

* `nuMajorant : NuMajorant`, with `C = 2`;
* `greenLargeSpec : U1488.GreenLargeSpec`, the large spectrum bound for `0 ≤ f ≤ ν_b`;
* `alsetriShao_1_2 : AlsetriShao12`.

AI-written Lean code, Claude, 2026-10-23. Checked only by the Lean kernel. Binary Goldbach is
OPEN; Theorem 1.2 is a density statement about almost all even numbers.
-/

@[expose] public section

open Finset Real Filter
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1502

open LeanLab.DensityGoldbach.U1446 LeanLab.DensityGoldbach.U1478 LeanLab.DensityGoldbach.U1481
  LeanLab.DensityGoldbach.U1484

local notation "SV" => LeanLab.PNTPort.Vinogradov.S
local notation "VV" => LeanLab.PNTPort.Vinogradov.V

set_option maxHeartbeats 1600000 in
/-- **`NuMajorant`, PROVED.** -/
theorem nuMajorant : NuMajorant := by
  obtain ⟨c', hc', K, hK, hmajA⟩ := LeanLab.PNTPort.Vinogradov.major_arc 21 (by norm_num)
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C := max C₀ 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨2, by norm_num, 2, fun z hz b hb hcop => ?_⟩
  set W := primorial z with hWdef
  have hW2 : 2 ≤ W := two_le_primorial hz
  have hW1 : 1 ≤ W := by omega
  have hW : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hb1 : 1 ≤ b := one_le_b hW2 hcop
  have hz1 : 1 ≤ z := by omega
  obtain ⟨X₀, hX₀⟩ := asymp2 (W := W) hW1 hc' hK
  have e7 := ev_logpow 4 (s := 1) one_pos (show 0 < 16 * C ^ 2 * (W : ℝ) by positivity)
  obtain ⟨x₁, hx₁⟩ := (e7.and (eventually_ge_atTop (Real.exp 4))).exists_forall_of_atTop
  refine ⟨max X₀ (max ⌈x₁⌉₊ 2), fun N _ hNp hN T hT1 _ s hs => ?_⟩
  have hNX₀ : X₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNx₁ : x₁ ≤ (N : ℝ) := Nat.ceil_le.1 (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) hN)
  have hN1 : 1 ≤ N := hNp.one_lt.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hlogpow, he4N⟩ := hx₁ N hNx₁
  rw [Real.rpow_one] at hlogpow
  set lN := Real.log N with hlN
  have hlN4 : 4 ≤ lN := by
    rw [hlN, ← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) he4N
  have hlN0 : 0 < lN := by linarith
  -- the point `r = s.val`
  set r := s.val with hrdef
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact absurd ((ZMod.val_eq_zero s).1 h) hs
    · exact h
  have hrN : r < N := ZMod.val_lt s
  -- the length `X ≥ N`
  set X := Xc W b N with hXdef
  have hNX : N ≤ X := by
    have : 1 * (N - 1) ≤ W * (N - 1) := Nat.mul_le_mul_right _ hW1
    simp only [X, Xc]; omega
  have hXr : (N : ℝ) ≤ X := by exact_mod_cast hNX
  have hXle : (X : ℝ) ≤ W * N := Xc_le hb hN1
  obtain ⟨hP1, hQ2, hQX, he4, hWP, hMb, hEn, hE⟩ := hX₀ X (le_trans hNX₀ hNX)
  set ℓ := Real.log X with hℓ
  have hℓN : lN ≤ ℓ := Real.log_le_log hNr hXr
  have hℓ0 : 0 < ℓ := by linarith
  -- uniform major arc error
  have hmaj' : ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ W * P2 X → IsCoprime a (q : ℤ) →
      ∀ β : ℝ, |β| ≤ 1 / ((Q2 X : ℝ) + 1) →
        ‖SV X (a / q + β) - gμ q * VV X β‖ ≤ Emaj2 W X K c' := by
    intro a q hq hqP hcop' β hβ
    have hqr : (q : ℝ) ≤ ((W * P2 X : ℕ) : ℝ) := by exact_mod_cast hqP
    exact (hmajA _ he4 q hq (hqr.trans hWP) a hcop' β).trans (major_err_le2 hK hq hqr hβ)
  have hcases := twS_cases (z := z) (b := b) (N := N) (r := r) hz1 hcop hP1 (by omega) hQX
    hmaj' hEn
  -- the normalisation `A₀ = φ(W)/(W² N)`
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  have hφW := totient_le_real W
  set A₀ := (Nat.totient W : ℝ) / (W ^ 2 * N) with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hAX1 : A₀ * X ≤ 1 := by
    rw [hA₀, div_mul_eq_mul_div, div_le_one (by positivity)]
    calc (Nat.totient W : ℝ) * X ≤ W * (W * N) :=
          mul_le_mul hφW hXle (Nat.cast_nonneg _) hWr.le
      _ = W ^ 2 * N := by ring
  have hX3 : A₀ * (X / ℓ ^ 3) ≤ 1 / ℓ ^ 3 := by
    rw [show A₀ * (X / ℓ ^ 3) = A₀ * X * (1 / ℓ ^ 3) by ring]
    exact mul_le_of_le_one_left (by positivity) hAX1
  have hPhi0 := PhiT_nonneg (N := N) T s
  have hT0 : 0 ≤ 2 / Real.sqrt T := by positivity
  -- the twisted term
  have htw : A₀ * ‖twS W b N r‖ ≤ 2 / ℓ ^ 3 + (2 / Real.sqrt T + PhiT N T s) := by
    rcases hcases with hmin | ⟨ρ2, β, t, hcp, hβ, hrel, hbd⟩
    · have : A₀ * ‖twS W b N r‖ ≤ A₀ * (X / ℓ ^ 3) + A₀ * (X / ℓ ^ 3) := by
        have := mul_le_mul_of_nonneg_left hmin hA₀0
        have h1 : A₀ * (W * Mb X (P2 X) (Q2 X)) ≤ A₀ * (X / ℓ ^ 3) :=
          mul_le_mul_of_nonneg_left hMb hA₀0
        have h2 : A₀ * (W * Emaj2 W X K c') ≤ A₀ * (X / ℓ ^ 3) :=
          mul_le_mul_of_nonneg_left hE hA₀0
        linarith
      have : 2 / ℓ ^ 3 = 1 / ℓ ^ 3 + 1 / ℓ ^ 3 := by ring
      linarith
    · -- the Farey point and the geometric sum
      have hrel' : -((r : ℝ) / N) = (W : ℝ) * (ρ2 : ℝ) + t + W * β := by
        have hWne : (primorial z : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (primorial_pos z).ne'
        rw [← hrel]; field_simp
      obtain ⟨a, ha, hd⟩ := farey_point ρ2 W hcp ((r : ℝ) / N) β t hrel'
      have hQr : (2 : ℝ) ≤ Q2 X := by exact_mod_cast hQ2
      have hβ2 : |β| < 1 / 2 := by
        calc |β| ≤ 1 / ((Q2 X : ℝ) + 1) := hβ
          _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
          _ < 1 / 2 := by norm_num
      have hV := V_div_le_psi X W N hW hN1 hXle β ((r : ℝ) / N - (a : ℝ) / ρ2.den) hβ2 hd
      have hg := gmu_psi_le T hT1 s ρ2.den a ρ2.pos ha
      have hth : thetaN N s = (r : ℝ) / N := rfl
      rw [hth] at hg
      have hmain : A₀ * ((W : ℝ) / Nat.totient W * ‖gμ ρ2.den‖ * ‖VV X β‖) =
          ‖gμ ρ2.den‖ * (‖VV X β‖ / (W * N)) := by
        rw [hA₀]; field_simp
      have h1 : A₀ * ((W : ℝ) / Nat.totient W * ‖gμ ρ2.den‖ * ‖VV X β‖) ≤
          2 / Real.sqrt T + PhiT N T s := by
        rw [hmain]
        exact (mul_le_mul_of_nonneg_left hV (norm_nonneg _)).trans hg
      have h2 : A₀ * (W * Emaj2 W X K c') ≤ 1 / ℓ ^ 3 :=
        (mul_le_mul_of_nonneg_left hE hA₀0).trans hX3
      have h3 : 0 ≤ 1 / ℓ ^ 3 := by positivity
      calc A₀ * ‖twS W b N r‖
          ≤ A₀ * ((W : ℝ) / Nat.totient W * ‖gμ ρ2.den‖ * ‖VV X β‖ + W * Emaj2 W X K c') :=
            mul_le_mul_of_nonneg_left hbd hA₀0
        _ = A₀ * ((W : ℝ) / Nat.totient W * ‖gμ ρ2.den‖ * ‖VV X β‖) +
              A₀ * (W * Emaj2 W X K c') := mul_add _ _ _
        _ ≤ (2 / Real.sqrt T + PhiT N T s) + 1 / ℓ ^ 3 := add_le_add h1 h2
        _ ≤ 2 / ℓ ^ 3 + (2 / Real.sqrt T + PhiT N T s) := by
            have : 2 / ℓ ^ 3 = 1 / ℓ ^ 3 + 1 / ℓ ^ 3 := by ring
            linarith
  -- the `ψ - θ` term
  have hpsi : (Nat.totient W : ℝ) / (W * N) * (Chebyshev.psi X - Chebyshev.theta X) ≤
      1 / (4 * lN ^ 2) := by
    have hε : 0 < 1 / (4 * lN ^ 2) := by positivity
    have hNc : C ^ 2 * W / (1 / (4 * lN ^ 2)) ^ 2 ≤ (N : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      calc C ^ 2 * W = 16 * C ^ 2 * W * lN ^ 4 * (1 / (4 * lN ^ 2)) ^ 2 := by field_simp; ring
        _ ≤ N * (1 / (4 * lN ^ 2)) ^ 2 :=
            mul_le_mul_of_nonneg_right hlogpow (by positivity)
    have hsq := sqrt_err hC hε W N hNc
    have hpt : Chebyshev.psi X - Chebyshev.theta X ≤ C * Real.sqrt (W * N) := by
      refine (hC₀ _).trans ?_
      have hs : Real.sqrt X ≤ Real.sqrt (W * N) := Real.sqrt_le_sqrt hXle
      have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
      rcases le_or_gt C₀ 0 with h0 | h0
      · nlinarith [Real.sqrt_nonneg ((W : ℝ) * N)]
      · calc C₀ * Real.sqrt X ≤ C * Real.sqrt X :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
          _ ≤ C * Real.sqrt (W * N) := mul_le_mul_of_nonneg_left hs hC.le
    have hfac : (Nat.totient W : ℝ) / (W * N) ≤ 1 / N := by
      rw [div_le_div_iff₀ (by positivity) hNr]; nlinarith
    have hpt0 : 0 ≤ Chebyshev.psi X - Chebyshev.theta X := sub_nonneg.2 (Chebyshev.theta_le_psi _)
    calc (Nat.totient W : ℝ) / (W * N) * (Chebyshev.psi X - Chebyshev.theta X)
        ≤ 1 / N * (C * Real.sqrt (W * N)) := mul_le_mul hfac hpt hpt0 (by positivity)
      _ ≤ 1 / N * (1 / (4 * lN ^ 2) * N) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 1 / (4 * lN ^ 2) := by field_simp
  -- assemble
  have hhat := hat_vs_twS hW hb hb1 s
  have hup := (abs_le.1 hhat).2
  have hℓ3 : 2 / ℓ ^ 3 ≤ 1 / (2 * lN ^ 2) := by
    have h1 : 2 / ℓ ^ 3 ≤ 2 / lN ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hlN0.le hℓN 3)
    have h2 : 2 / lN ^ 3 ≤ 1 / (2 * lN ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have e1 : 1 / Real.log N ^ 2 = 1 / (2 * lN ^ 2) + 1 / (4 * lN ^ 2) + 1 / (4 * lN ^ 2) := by
    rw [← hlN]; field_simp; ring
  rw [e1]
  have : ‖hatE N (nuW W b N) s‖ ≤ A₀ * ‖twS W b N r‖ +
      (Nat.totient W : ℝ) / (W * N) * (Chebyshev.psi X - Chebyshev.theta X) := by
    rw [hA₀]; linarith
  have h14 : 0 ≤ 1 / (4 * lN ^ 2) := by positivity
  linarith

/-- **The large spectrum bound for the majorant class, PROVED.** -/
theorem greenLargeSpec : LeanLab.DensityGoldbach.U1488.GreenLargeSpec :=
  largeSpec_of_majorant nuMajorant

/-- **Alsetri-Shao 2024, Theorem 1.2, PROVED**, no cited hypothesis: for `A` a set of primes with
lower relative density above `1/2` in every reduced class, almost all even numbers are a sum of
two elements of `A`. -/
theorem alsetriShao_1_2 : AlsetriShao12 := alsetriShao_1_2_U1502 nuMajorant

end LeanLab.DensityGoldbach.U1502
