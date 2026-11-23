module

public import LeanLab.PNTPort.PsiChi.ZeroHyp
public import LeanLab.PNTPort.BV.Characters

/-!
# From the smoothed sum back to `ψ(X, χ)`

Lab proof, unit U-5207, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics, no
cited input.

`unsmooth_le`: for `X > 0` and `0 < ε < 1`,
`‖ψ(X, χ) - ∑ χ(n) Λ(n) Smooth1 F ε (n/X)‖ ≤ ψ(X(1 + 2ε)) - ψ(X(1 - ε))`, since the weight is `1`
below `X(1 - ε)`, `0` above `X(1 + 2ε)` and in `[0, 1]` between; `ψ(X, χ)` is `BV.psiChi`.
-/

@[expose] public section


open Set Function Filter Complex Real Finset

open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

namespace LeanLab.PNTPort.PsiChi

lemma psi_sub_eq {a b : ℝ} (hab : a ≤ b) :
    Chebyshev.psi b - Chebyshev.psi a = ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n := by
  unfold Chebyshev.psi
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hab)]
  ring

theorem unsmooth_le {SmoothingF : ℝ → ℝ}
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {X ε : ℝ} (hX : 0 < X) (εpos : 0 < ε)
    (ε1 : ε < 1) :
    ‖BV.psiChi X χ - ∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 SmoothingF ε (n / X)‖ ≤
      Chebyshev.psi (X * (1 + 2 * ε)) - Chebyshev.psi (X * (1 - ε)) := by
  obtain ⟨c₁, -, hc₁, hbelow⟩ := Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, -, hc₂, habove⟩ := Smooth1Properties_above suppSmoothingF
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set w : ℕ → ℝ := fun n ↦ Smooth1 SmoothingF ε (n / X) with hw
  have w_one : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X * (1 - ε) → w n = 1 := by
    intro n hn h
    refine hbelow ε _ εpos (by positivity) ?_
    have hle : Real.log 2 * ε ≤ ε := by nlinarith
    have := mul_le_mul_of_nonneg_left hle hX.le
    rw [div_le_iff₀ hX, hc₁]; nlinarith
  have w_zero : ∀ n : ℕ, X * (1 + 2 * ε) ≤ n → w n = 0 := by
    intro n h
    refine habove ε _ ⟨εpos, ε1⟩ ?_
    have hle : 2 * Real.log 2 * ε ≤ 2 * ε := by nlinarith
    have := mul_le_mul_of_nonneg_left hle hX.le
    rw [le_div_iff₀ hX, hc₂]; nlinarith
  have w_nonneg : ∀ n : ℕ, 0 < n → 0 ≤ w n := fun n hn ↦
    Smooth1Nonneg SmoothingFpos (by positivity) εpos
  have w_le : ∀ n : ℕ, 0 < n → w n ≤ 1 := fun n hn ↦
    Smooth1LeOne SmoothingFpos mass_one εpos (by positivity)
  set a := ⌊X * (1 - ε)⌋₊ with ha
  set b := ⌊X * (1 + 2 * ε)⌋₊ with hb
  set S := Finset.range (b + ⌊X⌋₊ + 1) with hS
  set f : ℕ → ℂ := fun n ↦ χ (n : ZMod N) * Λ n * w n with hf
  -- the tsum is a finite sum over `S`
  have htsum : ∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 SmoothingF ε (n / X) = ∑ n ∈ S, f n := by
    apply tsum_eq_sum
    intro n hn
    rw [hS, Finset.mem_range, not_lt] at hn
    have : X * (1 + 2 * ε) ≤ n := by
      have h1 := Nat.lt_floor_add_one (X * (1 + 2 * ε))
      have h2 : ((b + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : b + 1 ≤ n)
      push_cast at h2; rw [← hb] at h1; linarith
    show χ (n : ZMod N) * Λ n * ((w n : ℝ) : ℂ) = 0
    rw [w_zero n this]; simp
  -- `ψ(X, χ)` as a sum over `S`
  set g : ℕ → ℂ := fun n ↦ if 1 ≤ n ∧ n ≤ ⌊X⌋₊ then (Λ n : ℂ) * χ (n : ZMod N) else 0 with hg
  have hpsi : BV.psiChi X χ = ∑ n ∈ S, g n := by
    unfold BV.psiChi
    rw [hg, ← Finset.sum_filter]
    congr 1
    ext n; simp only [Finset.mem_Icc, Finset.mem_filter, hS, Finset.mem_range]; omega
  rw [htsum, hpsi, ← Finset.sum_sub_distrib]
  set h : ℕ → ℝ := fun n ↦ if a < n ∧ n ≤ b then Λ n else 0 with hh
  have hpt : ∀ n ∈ S, ‖g n - f n‖ ≤ h n := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hg, hf, hh]
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    by_cases h1 : n ≤ a
    · have hnX : (n : ℝ) ≤ X * (1 - ε) := by
        have := Nat.floor_le (show 0 ≤ X * (1 - ε) by nlinarith)
        have h' : (n : ℝ) ≤ a := by exact_mod_cast h1
        rw [← ha] at this; linarith
      have hnX' : n ≤ ⌊X⌋₊ := Nat.le_floor (by nlinarith)
      have : g n - f n = 0 := by
        have hif : (1 ≤ n ∧ n ≤ ⌊X⌋₊) := ⟨hn, hnX'⟩
        simp only [hg, hf, if_pos hif, w_one n hn hnX]; push_cast; ring
      rw [this, norm_zero]
      simp only [hh]; split_ifs <;> linarith
    by_cases h2 : b < n
    · have hnX : X * (1 + 2 * ε) ≤ n := by
        have h1' := Nat.lt_floor_add_one (X * (1 + 2 * ε))
        have h2' : ((b + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : b + 1 ≤ n)
        push_cast at h2'; rw [← hb] at h1'; linarith
      have hnX' : ¬ (1 ≤ n ∧ n ≤ ⌊X⌋₊) := by
        rintro ⟨-, h3⟩
        have h4 : (n : ℝ) ≤ X := (Nat.le_floor_iff hX.le).mp h3
        nlinarith
      have : g n - f n = 0 := by
        simp only [hg, hf, if_neg hnX', w_zero n hnX]; push_cast; ring
      rw [this, norm_zero]
      simp only [hh]; split_ifs <;> linarith
    push_neg at h1 h2
    simp only [hh, if_pos (And.intro h1 h2)]
    have hw0 := w_nonneg n hn
    have hw1 := w_le n hn
    have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    simp only [hg, hf]
    split_ifs
    · have e : (Λ n : ℂ) * χ (n : ZMod N) - χ (n : ZMod N) * Λ n * (w n : ℂ) =
          (Λ n : ℂ) * χ (n : ZMod N) * ((1 - w n : ℝ) : ℂ) := by push_cast; ring
      rw [e, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hΛ, abs_of_nonneg (by linarith)]
      calc Λ n * ‖χ (n : ZMod N)‖ * (1 - w n) ≤ Λ n * 1 * 1 := by gcongr <;> linarith
        _ = Λ n := by ring
    · rw [zero_sub, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ, abs_of_nonneg hw0]
      calc ‖χ (n : ZMod N)‖ * Λ n * w n ≤ 1 * Λ n * 1 := by gcongr
        _ = Λ n := by ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
  rw [psi_sub_eq (by nlinarith), hh, ← Finset.sum_filter]
  apply le_of_eq
  congr 1
  ext n
  simp only [Finset.mem_filter, hS, Finset.mem_range, Finset.mem_Ioc]
  omega

end LeanLab.PNTPort.PsiChi
