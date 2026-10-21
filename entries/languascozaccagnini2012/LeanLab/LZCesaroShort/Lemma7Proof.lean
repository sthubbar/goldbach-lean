module

public import LeanLab.LZCesaroShort.Statements
public import LeanLab.PNTPort.ExplicitPsi1.Nontrivial

/-!
# P0058 Lemma 7, proved

Lab proof, unit U-5321, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
no cited input. Languasco-Zaccagnini Lemma 7, `Σ_{n ≤ M} (ψ(n) - n) = -Σ_ρ M^{ρ+1}/(ρ(ρ+1)) + O(M)`
for real `M > 1`, follows from the lab's explicit formula for `ψ₁(x)/x`,
`PNTPort.ExplicitPsi1.explicit_formula_psi1_bound`, since `Σ_{n ≤ M} ψ(n)` and
`ψ₁(M) = M Σ Λ(k) max(0, 1 - k/M)` differ by at most `ψ(M) = O(M)`.
This proves the statement the cited `lz_lemma7` takes on trust. Binary Goldbach is open.
-/

@[expose] public section


open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section
namespace LeanLab.LZCesaroShort

lemma psi_nat (n : ℕ) : ψ (n : ℝ) = ∑ k ∈ range (n + 1), Λ k := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, range_eq_Ico]
  rfl

/-- `Σ_{n=1}^{N} (ψ(n) - n) = Σ_{k ≤ N} Λ(k)(N + 1 - k) - N(N + 1)/2`. -/
lemma sum_psi_sub (N : ℕ) : ∑ n ∈ Icc 1 N, (ψ (n : ℝ) - n) =
    ∑ k ∈ range (N + 1), Λ k * ((N : ℝ) + 1 - k) - (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, psi_nat,
      sum_range_succ (fun k => Λ k * (((N + 1 : ℕ) : ℝ) + 1 - k)) (N + 1)]
    have : ∑ k ∈ range (N + 1), Λ k * (((N + 1 : ℕ) : ℝ) + 1 - k) =
        ∑ k ∈ range (N + 1), Λ k * ((N : ℝ) + 1 - k) + ∑ k ∈ range (N + 1), Λ k := by
      rw [← sum_add_distrib]; congr 1; funext k; push_cast; ring
    rw [this, sum_range_succ (fun k => Λ k) (N + 1)]
    push_cast
    ring

/-- `Σ Λ(k) w₁(k/M) = Σ_{k ≤ ⌊M⌋} Λ(k)(1 - k/M)`. -/
lemma tsum_w1 {M : ℝ} (hM : 0 < M) :
    ∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / M) =
      ((∑ k ∈ range (⌊M⌋₊ + 1), Λ k * (1 - k / M) : ℝ) : ℂ) := by
  rw [tsum_eq_sum (s := range (⌊M⌋₊ + 1))]
  · push_cast
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hkM : (k : ℝ) ≤ M := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hk)
      (Nat.floor_le hM.le)
    rw [PNTPort.ZetaZeros.w1_eq (by rw [div_le_one hM]; exact hkM)]
    push_cast; ring
  · intro k hk
    rw [mem_range, not_lt] at hk
    have hkM : M ≤ k := by
      have := Nat.lt_floor_add_one M
      have h2 : ((⌊M⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2; linarith
    rw [PNTPort.ZetaZeros.w1_eq_zero (by rw [le_div_iff₀ hM]; linarith)]
    simp

/-- The zero sum of Lemma 7 is `M` times the zero sum of the explicit formula. -/
lemma zeroSum_eq {M : ℝ} (hM : 0 < M) :
    zeroSum (fun ρ => (M : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) =
      (M : ℂ) * ∑' ρ : PNTPort.ExplicitPsi1.Zall, PNTPort.ExplicitPsi1.zterm M ρ := by
  rw [← tsum_mul_left]
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have e : (∑' ρ : PNTPort.ExplicitPsi1.Zall, (M : ℂ) * PNTPort.ExplicitPsi1.zterm M ρ) =
      ∑' ρ : NontrivialZero, (M : ℂ) * PNTPort.ExplicitPsi1.zterm M ρ.1 := by
    rw [PNTPort.ExplicitPsi1.Zall_eq]; rfl
  rw [e, zeroSum]
  apply tsum_congr
  intro ρ
  simp only [PNTPort.ExplicitPsi1.zterm]
  rw [cpow_add _ _ hM0, cpow_one]
  ring

/-- **Languasco-Zaccagnini Lemma 7**, unconditional, now proved. -/
theorem lz_lemma7_proved : Lemma7 := by
  obtain ⟨K, hK⟩ := PNTPort.ExplicitPsi1.explicit_formula_psi1_bound
  set d0 : ℂ := deriv riemannZeta 0 / riemannZeta 0
  refine ⟨1 / 2 + ‖d0‖ + |K| + (Real.log 4 + 4), fun M hM => ?_⟩
  have hM0 : 0 < M := by linarith
  set N := ⌊M⌋₊ with hN
  have hNM : (N : ℝ) ≤ M := Nat.floor_le hM0.le
  have hMN : M < N + 1 := Nat.lt_floor_add_one M
  set P : ℝ := ∑ k ∈ range (N + 1), Λ k with hP
  set S : ℝ := ∑ k ∈ range (N + 1), Λ k * (1 - k / M) with hS
  set Z := ∑' ρ : PNTPort.ExplicitPsi1.Zall, PNTPort.ExplicitPsi1.zterm M ρ
  have hb := hK M hM0
  rw [tsum_w1 hM0] at hb
  -- the sum of `ψ(n) - n` in terms of `S`
  have hA : ∑ n ∈ Icc 1 N, (ψ (n : ℝ) - n) =
      M * S + ((N : ℝ) + 1 - M) * P - (N : ℝ) * (N + 1) / 2 := by
    rw [sum_psi_sub, hS, hP, mul_sum, mul_sum]
    rw [← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro k _
    field_simp
    ring
  rw [hA, zeroSum_eq hM0]
  set E : ℂ := (S : ℂ) - (M / 2 - d0 - Z) with hE
  have key : (((M * S + ((N : ℝ) + 1 - M) * P - (N : ℝ) * (N + 1) / 2 : ℝ)) : ℂ) + (M : ℂ) * Z =
      (((M ^ 2 - (N : ℝ) * (N + 1)) / 2 : ℝ) : ℂ) - (M : ℂ) * d0 + (M : ℂ) * E +
        (((N : ℝ) + 1 - M) * P : ℝ) := by
    rw [hE]; push_cast; ring
  rw [key]
  have hP0 : 0 ≤ P := sum_nonneg fun k _ => ArithmeticFunction.vonMangoldt_nonneg
  have hPle : P ≤ (Real.log 4 + 4) * M := by
    rw [hP, ← psi_nat]
    exact (Chebyshev.psi_le_const_mul_self (by positivity)).trans (by gcongr)
  have h1 : ‖((((M ^ 2 - (N : ℝ) * (N + 1)) / 2 : ℝ)) : ℂ)‖ ≤ 1 / 2 * M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  have h2 : ‖(M : ℂ) * d0‖ = ‖d0‖ * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0]; ring
  have h3 : ‖(M : ℂ) * E‖ ≤ |K| * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0]
    have hr : M ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM.le (by norm_num)
    have hr0 : 0 ≤ M ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hM0.le _
    have : ‖E‖ ≤ |K| := by
      refine hb.trans ?_
      calc K * M ^ (-1 / 2 : ℝ) ≤ |K| * M ^ (-1 / 2 : ℝ) := by
            gcongr; exact le_abs_self K
        _ ≤ |K| * 1 := by gcongr
        _ = |K| := mul_one _
    nlinarith [norm_nonneg E]
  have h4 : ‖((((N : ℝ) + 1 - M) * P : ℝ) : ℂ)‖ ≤ (Real.log 4 + 4) * M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0,
      abs_of_nonneg (by linarith)]
    calc ((N : ℝ) + 1 - M) * P ≤ 1 * P := by gcongr; linarith
      _ ≤ (Real.log 4 + 4) * M := by linarith
  calc ‖((((M ^ 2 - (N : ℝ) * (N + 1)) / 2 : ℝ)) : ℂ) - (M : ℂ) * d0 + (M : ℂ) * E +
        ((((N : ℝ) + 1 - M) * P : ℝ) : ℂ)‖
      ≤ ‖((((M ^ 2 - (N : ℝ) * (N + 1)) / 2 : ℝ)) : ℂ)‖ + ‖(M : ℂ) * d0‖ + ‖(M : ℂ) * E‖ +
        ‖((((N : ℝ) + 1 - M) * P : ℝ) : ℂ)‖ := by
        have a1 := norm_add_le ((((M ^ 2 - (N : ℝ) * (N + 1)) / 2 : ℝ) : ℂ) - (M : ℂ) * d0 +
          (M : ℂ) * E) ((((N : ℝ) + 1 - M) * P : ℝ) : ℂ)
        have a2 := norm_add_le ((((M ^ 2 - (N : ℝ) * (N + 1)) / 2 : ℝ) : ℂ) - (M : ℂ) * d0)
          ((M : ℂ) * E)
        have a3 := norm_sub_le ((((M ^ 2 - (N : ℝ) * (N + 1)) / 2 : ℝ) : ℂ)) ((M : ℂ) * d0)
        linarith
    _ ≤ 1 / 2 * M + ‖d0‖ * M + |K| * M + (Real.log 4 + 4) * M := by
        rw [h2]; linarith
    _ = (1 / 2 + ‖d0‖ + |K| + (Real.log 4 + 4)) * M := by ring

end LeanLab.LZCesaroShort

