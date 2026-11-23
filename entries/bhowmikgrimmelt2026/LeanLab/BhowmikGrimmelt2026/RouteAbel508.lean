module

public import Mathlib

/-!
ROUTE for `oscillatory_zero_modes508`, part one: partial summation against a monotone weight.
Source: P0029 page 15 display 4.6, the partial summation step, in its discrete form, and the
dyadic halving that sums the blocks. No analytic input.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Discrete Abel identity with tail sums `Z m = ∑ n ∈ Ico m B, u n`, by downward induction. -/
theorem abel_identity_aux508 (w : ℕ → ℝ) (u : ℕ → ℂ) (B : ℕ) :
    ∀ k a : ℕ, a + k + 1 = B →
      ∑ n ∈ Finset.Ico a B, (w n : ℂ) * u n
        = (w a : ℂ) * ∑ n ∈ Finset.Ico a B, u n
          + ∑ m ∈ Finset.Ico a (B - 1),
              ((w (m + 1) : ℂ) - (w m : ℂ)) * ∑ n ∈ Finset.Ico (m + 1) B, u n := by
  intro k
  induction k with
  | zero =>
    intro a ha
    have hB : B = a + 1 := by omega
    subst hB
    simp
  | succ k ih =>
    intro a ha
    have h1 : a < B := by omega
    have h2 : a < B - 1 := by omega
    have ih' := ih (a + 1) (by omega)
    rw [Finset.sum_eq_sum_Ico_succ_bot h1, Finset.sum_eq_sum_Ico_succ_bot h1 (f := u),
      Finset.sum_eq_sum_Ico_succ_bot h2, ih']
    ring

/-- Telescoping of consecutive differences over `Ico a b`. -/
theorem telescope_aux508 (w : ℕ → ℝ) (a : ℕ) :
    ∀ b : ℕ, a ≤ b → ∑ m ∈ Finset.Ico a b, (w (m + 1) - w m) = w b - w a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

/-- P0029 page 15 display 4.6, partial summation with a nonnegative nondecreasing
weight. If every tail sum of `u` over `[m, b]` with `a ≤ m` has norm at most `V`, then the
weighted sum over `[a, b]` has norm at most `w b * V`. -/
theorem abel_monotone_weight508 (w : ℕ → ℝ) (u : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) (V : ℝ)
    (hw0 : ∀ n ∈ Finset.Icc a b, 0 ≤ w n)
    (hmono : ∀ n ∈ Finset.Ico a b, w n ≤ w (n + 1))
    (hV : ∀ m ∈ Finset.Icc a b, ‖∑ n ∈ Finset.Icc m b, u n‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc a b, (w n : ℂ) * u n‖ ≤ w b * V := by
  have hIcc : ∀ m : ℕ, Finset.Icc m b = Finset.Ico m (b + 1) := by
    intro m; ext x; simp
  have hV' : ∀ m ∈ Finset.Icc a b, ‖∑ n ∈ Finset.Ico m (b + 1), u n‖ ≤ V := by
    intro m hm; rw [← hIcc m]; exact hV m hm
  have hid := abel_identity_aux508 w u (b + 1) (b - a) a (by omega)
  rw [hIcc a, hid]
  simp only [Nat.add_sub_cancel]
  have ha0 : 0 ≤ w a := hw0 a (Finset.mem_Icc.mpr ⟨le_refl a, hab⟩)
  have t1 : ‖(w a : ℂ) * ∑ n ∈ Finset.Ico a (b + 1), u n‖ ≤ w a * V := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hV' a (Finset.mem_Icc.mpr ⟨le_refl a, hab⟩)) ha0
  have t2 : ‖∑ m ∈ Finset.Ico a b,
      ((w (m + 1) : ℂ) - (w m : ℂ)) * ∑ n ∈ Finset.Ico (m + 1) (b + 1), u n‖
      ≤ ∑ m ∈ Finset.Ico a b, (w (m + 1) - w m) * V := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro m hm
    have hm' := Finset.mem_Ico.mp hm
    have hd : 0 ≤ w (m + 1) - w m := sub_nonneg.mpr (hmono m hm)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left
      (hV' (m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) hd
  rw [← Finset.sum_mul, telescope_aux508 w a b hab] at t2
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ w a * V + (w b - w a) * V := add_le_add t1 t2
    _ = w b * V := by ring

/-- The numerical inequality `(3/4)^τ ≤ 7/8` for `τ ≥ 1/2`. -/
theorem three_quarters_rpow_aux508 {τ : ℝ} (hτ : 1 / 2 ≤ τ) : (3 / 4 : ℝ) ^ τ ≤ 7 / 8 := by
  have h1 : (3 / 4 : ℝ) ^ τ ≤ (3 / 4 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hτ
  have h2 : (3 / 4 : ℝ) ^ (1 / 2 : ℝ) ≤ 7 / 8 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    norm_num
  exact h1.trans h2

/-- P0029 page 15 display 4.6, the blocks of the partial summation summed by halving.
If every sum of `u` over an interval `[p, q]` inside a block `[N, 2N - 1]` below `M0` has norm
at most `V`, then the sum of `n ^ σ * u n` over `1 ≤ n < M` is at most `8 * M ^ τ * V` for
every `M ≤ M0`, where `τ` is any exponent with `σ ≤ τ` and `1 / 2 ≤ τ`. The power weight
makes the blocks a geometric series, so no logarithm is lost. -/
theorem halving_weighted_sum508 (u : ℕ → ℂ) {σ τ V : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ)
    (hτ : 1 / 2 ≤ τ) (hV0 : 0 ≤ V) (M0 : ℕ)
    (hV : ∀ N p q : ℕ, 1 ≤ N → N ≤ p → p ≤ q → q + 1 ≤ 2 * N → q < M0 →
      ‖∑ n ∈ Finset.Icc p q, u n‖ ≤ V) :
    ∀ M : ℕ, M ≤ M0 →
      ‖∑ n ∈ Finset.Ico 1 M, (((n : ℝ) ^ σ : ℝ) : ℂ) * u n‖ ≤ 8 * (M : ℝ) ^ τ * V := by
  have hτ0 : 0 ≤ τ := by linarith
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM
    have hMτ : 0 ≤ (M : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg M) τ
    rcases Nat.lt_or_ge M 2 with hlt | hge
    · have he : Finset.Ico 1 M = ∅ := Finset.Ico_eq_empty (by omega)
      rw [he, Finset.sum_empty, norm_zero]
      positivity
    · obtain ⟨h, hh⟩ : ∃ h : ℕ, h = (M + 1) / 2 := ⟨_, rfl⟩
      have hh1 : 1 ≤ h := by omega
      have hhM : h < M := by omega
      have hM2 : M ≤ 2 * h := by omega
      have h2h : 2 * h ≤ M + 1 := by omega
      have hsplit := Finset.sum_Ico_consecutive
        (fun n : ℕ => (((n : ℝ) ^ σ : ℝ) : ℂ) * u n) hh1 hhM.le
      have hIco : Finset.Ico h M = Finset.Icc h (M - 1) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [← hsplit, hIco]
      have hA := ih h hhM (by omega)
      have hB := abel_monotone_weight508 (fun n : ℕ => (n : ℝ) ^ σ) u h (M - 1) (by omega) V
        (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) σ)
        (fun n _ => Real.rpow_le_rpow (Nat.cast_nonneg n) (by push_cast; linarith) hσ)
        (fun m hm => by
          have hm' := Finset.mem_Icc.mp hm
          exact hV h m (M - 1) hh1 hm'.1 hm'.2 (by omega) (by omega))
      have hM1 : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M - 1)
      have hM1le : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
      have hw : ((M - 1 : ℕ) : ℝ) ^ σ ≤ (M : ℝ) ^ τ :=
        (Real.rpow_le_rpow_of_exponent_le hM1 hστ).trans
          (Real.rpow_le_rpow (by linarith) hM1le hτ0)
      have hB' : ‖∑ n ∈ Finset.Icc h (M - 1), (((n : ℝ) ^ σ : ℝ) : ℂ) * u n‖
          ≤ (M : ℝ) ^ τ * V := hB.trans (mul_le_mul_of_nonneg_right hw hV0)
      have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hge
      have hhr : (h : ℝ) ≤ 3 / 4 * (M : ℝ) := by
        have : (2 : ℝ) * (h : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast h2h
        linarith
      have hhτ : (h : ℝ) ^ τ ≤ 7 / 8 * (M : ℝ) ^ τ := by
        calc (h : ℝ) ^ τ ≤ (3 / 4 * (M : ℝ)) ^ τ :=
              Real.rpow_le_rpow (Nat.cast_nonneg h) hhr hτ0
          _ = (3 / 4 : ℝ) ^ τ * (M : ℝ) ^ τ :=
              Real.mul_rpow (by norm_num) (Nat.cast_nonneg M)
          _ ≤ 7 / 8 * (M : ℝ) ^ τ :=
              mul_le_mul_of_nonneg_right (three_quarters_rpow_aux508 hτ) hMτ
      have hA' : 8 * (h : ℝ) ^ τ * V ≤ 7 * (M : ℝ) ^ τ * V := by
        have := mul_le_mul_of_nonneg_right hhτ hV0
        nlinarith
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ 8 * (h : ℝ) ^ τ * V + (M : ℝ) ^ τ * V := add_le_add hA hB'
        _ ≤ 8 * (M : ℝ) ^ τ * V := by linarith

end LeanLab.BhowmikGrimmelt2026
