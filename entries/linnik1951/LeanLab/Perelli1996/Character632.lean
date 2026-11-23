module

public import LeanLab.Perelli1996.Kernel
public import LeanLab.PNTPort.BV.Helpers
public import LeanLab.PNTPort.Gallagher.Basic

/-!
Perelli 1996, pages 484 and 485, equations 18 through 25.
Elementary primitive character reduction and numerical consequences.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Decomp88
open Finset Real
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

/-- Page 485 equation 25. The density exponent simplifies exactly. -/
theorem density_exponent_identity (k ε σ : ℝ) :
    2 * σ - 1 + 12 * (5 / 6 - k * ε / 2) * (1 - σ) / 5 =
      1 - (6 * k * ε / 5) * (1 - σ) := by ring

/-- Page 485 equation 25. A good character rectangle yields logarithmic decay. -/
theorem density_exponent_decay (N k ε D σ : ℝ) (hN : 1 < N)
    (hk : 0 < k) (hε : 0 < ε)
    (hσ : σ ≤ 1 - (5 * D / (6 * k * ε)) *
      (Real.log (Real.log N) / Real.log N)) :
    N ^ (2 * σ - 1 + 12 * (5 / 6 - k * ε / 2) * (1 - σ) / 5) ≤
      N * Real.log N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have hc : 0 < 6 * k * ε / 5 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hσ hc.le
  have hid : (6 * k * ε / 5) * (5 * D / (6 * k * ε)) = D := by
    field_simp
  have hexp : 1 - (6 * k * ε / 5) * (1 - σ) ≤
      1 - D * (Real.log (Real.log N) / Real.log N) := by
    have heq : (6 * k * ε / 5) *
        (1 - (5 * D / (6 * k * ε)) *
          (Real.log (Real.log N) / Real.log N)) =
        6 * k * ε / 5 - D * (Real.log (Real.log N) / Real.log N) := by
      calc
        _ = 6 * k * ε / 5 - ((6 * k * ε / 5) *
          (5 * D / (6 * k * ε))) * (Real.log (Real.log N) / Real.log N) := by ring
        _ = _ := by rw [hid]
    rw [heq] at hmul
    linarith
  rw [density_exponent_identity]
  apply (Real.rpow_le_rpow_of_exponent_le hN.le hexp).trans_eq
  have heq : Real.log N * (1 - D * (Real.log (Real.log N) / Real.log N)) =
      Real.log N + Real.log (Real.log N) * (-D) := by
    field_simp
    ring
  rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hL, heq,
    Real.exp_add, Real.exp_log hN0]
/-- Page 485 equation 25. The full logarithmic prefactor is absorbed. -/
theorem density_good_character_saving (N k ε B d σ : ℝ)
    (hN : Real.exp 1 ≤ N) (hk : 0 < k) (hε : 0 < ε)
    (hd : d ≤ (12 * k - 1) * B)
    (hσ : σ ≤ 1 - (10 * B / ε) *
      (Real.log (Real.log N) / Real.log N)) :
    Real.log N ^ d *
      N ^ (2 * σ - 1 + 12 * (5 / 6 - k * ε / 2) * (1 - σ) / 5) ≤
      N * Real.log N ^ (-B) := by
  have hN1 : 1 < N := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hN
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) hN
  have hL0 : 0 < Real.log N := by linarith
  have hcoef : 5 * (12 * k * B) / (6 * k * ε) = 10 * B / ε := by field_simp; ring
  have hs := density_exponent_decay N k ε (12 * k * B) σ hN1 hk hε
    (by simpa only [hcoef] using hσ)
  calc
    _ ≤ Real.log N ^ d * (N * Real.log N ^ (-(12 * k * B))) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hL0.le _)
    _ = N * Real.log N ^ (d - 12 * k * B) := by
      rw [sub_eq_add_neg, Real.rpow_add hL0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hN0.le
/-- Page 484 equation 20. Numerical exclusion of small bad moduli. -/
theorem bad_modulus_lower_of_gap (L q c A δ : ℝ) (hL : 1 ≤ L)
    (hq : 0 < q) (hc : 0 < c) (hδ : 0 < δ)
    (hlog : A * Real.log L ≤ c / 4 * L ^ (1 / 5 : ℝ))
    (hgap : c / max (q ^ δ) (2 * L ^ (4 / 5 : ℝ)) ≤ A * Real.log L / L) :
    L ^ (1 / (2 * δ)) ≤ q := by
  have hL0 : 0 < L := by linarith
  have hpow : 0 < L ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hden : 0 < max (q ^ δ) (2 * L ^ (4 / 5 : ℝ)) :=
    (Real.rpow_pos_of_pos hq δ).trans_le (le_max_left _ _)
  apply le_of_not_gt
  intro hsmall
  have hqpow := Real.rpow_le_rpow hq.le hsmall.le hδ.le
  have he : 1 / (2 * δ) * δ = (1 / 2 : ℝ) := by field_simp
  rw [← Real.rpow_mul hL0.le, he] at hqpow
  have hpowle : L ^ (1 / 2 : ℝ) ≤ L ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hmax : max (q ^ δ) (2 * L ^ (4 / 5 : ℝ)) ≤ 2 * L ^ (4 / 5 : ℝ) := by
    apply max_le _ le_rfl
    linarith [hqpow.trans hpowle]
  have hmain : c * L ≤ A * Real.log L * max (q ^ δ) (2 * L ^ (4 / 5 : ℝ)) :=
    (div_le_div_iff₀ hden hL0).mp hgap
  have hb : A * Real.log L * max (q ^ δ) (2 * L ^ (4 / 5 : ℝ)) ≤
      (c / 4 * L ^ (1 / 5 : ℝ)) * (2 * L ^ (4 / 5 : ℝ)) := by
    apply mul_le_mul hlog hmax hden.le
    positivity
  have hid : (c / 4 * L ^ (1 / 5 : ℝ)) * (2 * L ^ (4 / 5 : ℝ)) = c / 2 * L := by
    calc
      _ = c / 2 * (L ^ (1 / 5 : ℝ) * L ^ (4 / 5 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hL0]; norm_num
  rw [hid] at hb
  nlinarith [mul_pos hc hL0]
/-- Page 484 equation 20, from the numerical gap supplied by equation 19. -/
theorem bad_modulus_lower (c A δ : ℝ) (hc : 0 < c) (hA : 0 < A) (hδ : 0 < δ) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N q t : ℝ, N₀ ≤ N → 0 < q → |t| ≤ N →
      c / max (q ^ δ) (Real.log (|t| + 1) ^ (4 / 5 : ℝ)) ≤
        A * Real.log (Real.log N) / Real.log N →
      Real.log N ^ (1 / (2 * δ)) ≤ q := by
  have hb := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).bound
    (show 0 < c / (4 * A) by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max 3 (Real.exp (max 1 X)), le_max_left _ _, ?_⟩
  intro N q t hN hq ht hgap
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hLX : max 1 X ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos (max 1 X)) ((le_max_right _ _).trans hN)
    simpa using hh
  have hL1 : 1 ≤ Real.log N := (le_max_left _ _).trans hLX
  have hL0 : 0 < Real.log N := by linarith
  have hlog := hX (Real.log N) ((le_max_right _ _).trans hLX)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
  have hlog' : A * Real.log (Real.log N) ≤ c / 4 * Real.log N ^ (1 / 5 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog hA.le
    calc
      _ ≤ A * (c / (4 * A) * Real.log N ^ (1 / 5 : ℝ)) := hh
      _ = _ := by field_simp
  have hheight : Real.log (|t| + 1) ^ (4 / 5 : ℝ) ≤
      2 * Real.log N ^ (4 / 5 : ℝ) := by
    have ht0 : 0 < |t| + 1 := by positivity
    have htN : |t| + 1 ≤ N ^ (2 : ℕ) := by nlinarith
    have hlogs := Real.log_le_log ht0 htN
    rw [Real.log_pow] at hlogs
    norm_num at hlogs
    have hr := Real.rpow_le_rpow (Real.log_nonneg (by linarith [abs_nonneg t]))
      hlogs (by norm_num : (0 : ℝ) ≤ 4 / 5)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL0.le] at hr
    have htwo : (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (4 / 5 : ℝ) ≤ 1)
    exact hr.trans (mul_le_mul_of_nonneg_right htwo (by positivity))
  have hden : 0 < max (q ^ δ) (Real.log (|t| + 1) ^ (4 / 5 : ℝ)) :=
    (Real.rpow_pos_of_pos hq δ).trans_le (le_max_left _ _)
  have hden' : max (q ^ δ) (Real.log (|t| + 1) ^ (4 / 5 : ℝ)) ≤
      max (q ^ δ) (2 * Real.log N ^ (4 / 5 : ℝ)) := max_le_max_left _ hheight
  apply bad_modulus_lower_of_gap (Real.log N) q c A δ hL1 hq hc hδ hlog'
  exact (div_le_div_of_nonneg_left hc.le hden hden').trans hgap
/-- Page 484 equations 18 through 20. Real parts in both regions force large q. -/
theorem bad_rectangle_modulus_lower (c A δ : ℝ) (hc : 0 < c)
    (hA : 0 < A) (hδ : 0 < δ) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N q t β : ℝ, N₀ ≤ N → 0 < q → |t| ≤ N →
      1 - A * Real.log (Real.log N) / Real.log N ≤ β →
      β ≤ 1 - c / max (q ^ δ) (Real.log (|t| + 1) ^ (4 / 5 : ℝ)) →
      Real.log N ^ (1 / (2 * δ)) ≤ q := by
  obtain ⟨N₀, hN₀, h⟩ := bad_modulus_lower c A δ hc hA hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N q t β hN hq ht hβ hreg
  exact h N q t hN hq ht (by linarith)

/-- Page 484 equation 19. A classical fixed logarithmic width is insufficient
for every fixed positive good rectangle coefficient. This is numerical only. -/
theorem classical_width_lt_good_width (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∃ N₀ : ℝ, 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      c / Real.log N < A * Real.log (Real.log N) / Real.log N := by
  let N₀ := Real.exp (Real.exp (c / A + 1))
  have he : 0 < Real.exp (c / A + 1) := Real.exp_pos _
  refine ⟨N₀, Real.one_lt_exp_iff.mpr he, ?_⟩
  intro N hN
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hLN : Real.exp (c / A + 1) ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos _) hN
    simpa only [N₀, Real.log_exp] using hh
  have hL : 0 < Real.log N := he.trans_le hLN
  have hLL : c / A + 1 ≤ Real.log (Real.log N) := by
    have hh := Real.log_le_log he hLN
    simpa only [Real.log_exp] using hh
  apply (div_lt_div_iff_of_pos_right hL).mpr
  have hh := mul_le_mul_of_nonneg_left hLL hA.le
  have hcancel : A * (c / A + 1) = c + A := by field_simp
  rw [hcancel] at hh
  linarith


/-- Page 484 before equation 18. Removing the imprimitive Euler factors costs
only the von Mangoldt weight on integers not coprime to the full modulus. -/
theorem twisted_primitive_error (M q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (η : ℝ) :
    ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
      (∑ n ∈ range (M + 1),
        (Λ n : ℂ) * χ.primitiveCharacter n * Kernel.e ((n : ℝ) * η))‖ ≤
      LeanLab.PNTPort.BV.psiBad (M : ℝ) q := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hterm (n : ℕ) :
      ‖(Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η) -
        (Λ n : ℂ) * χ.primitiveCharacter n * Kernel.e ((n : ℝ) * η)‖ ≤
      if Nat.Coprime n q then 0 else Λ n := by
    by_cases hn : Nat.Coprime n q
    · have heq := χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
      simp only [Int.cast_natCast] at heq
      rw [ite_eq_left hn, heq, sub_self, norm_zero]
    · have hnu : ¬ IsUnit (n : ZMod q) := fun h => hn ((ZMod.isUnit_iff_coprime n q).1 h)
      rw [ite_eq_right hn, MulChar.map_nonunit _ hnu, mul_zero, zero_mul,
        zero_sub, norm_neg, norm_mul, norm_mul]
      have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      simp only [Kernel.e, Complex.norm_exp, Complex.mul_re, Complex.I_re,
        Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
        sub_zero, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hΛ]
      exact mul_le_of_le_one_right hΛ (DirichletCharacter.norm_le_one _ _)
  calc
    _ ≤ ∑ n ∈ range (M + 1),
        ‖(Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η) -
          (Λ n : ℂ) * χ.primitiveCharacter n * Kernel.e ((n : ℝ) * η)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range (M + 1), if Nat.Coprime n q then 0 else Λ n :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = _ := by
      unfold LeanLab.PNTPort.BV.psiBad
      rw [Nat.floor_natCast]
      simp only [Finset.sum_filter]
      have hr : range (M + 1) = insert 0 (Icc 1 M) := by ext n; simp; omega
      rw [hr, Finset.sum_insert (by simp)]
      simp
/-- Page 484 before equation 18. The primitive reduction error has logarithmic size. -/
theorem twisted_primitive_error_le_log (M q : ℕ) [NeZero q] (hM : 1 ≤ M)
    (χ : DirichletCharacter ℂ q) (η : ℝ) :
    ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
      (∑ n ∈ range (M + 1),
        (Λ n : ℂ) * χ.primitiveCharacter n * Kernel.e ((n : ℝ) * η))‖ ≤
      Real.log q / Real.log 2 * Real.log M := by
  exact (twisted_primitive_error M q χ η).trans
    (LeanLab.PNTPort.BV.psiBad_le (by exact_mod_cast hM)
      (Nat.pos_of_ne_zero (NeZero.ne q)))

/-- Pages 484 and 485, the Gallagher step cited through Perelli and Pintz 1993
page 47 equation 21. The principal subtraction is a constant coefficient δ.
The integer window version retains the existing inclusive zero endpoint. -/
theorem character_gallagher_reduction (M L q : ℕ) (hL : 0 < L)
    (χ : DirichletCharacter ℂ q) (δ : ℂ) :
    (∫ η in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
      ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
        δ * Kernel.T 0 (M + 1) η‖ ^ 2) ≤
      (Real.pi / (2 * L)) ^ 2 * ∑ m ∈ range (M + 1 + L),
        ‖LeanLab.PNTPort.Gallagher.win
          (fun n => (Λ n : ℂ) * χ n - δ) (M + 1) L m‖ ^ 2 := by
  have h := LeanLab.PNTPort.Gallagher.gallagher
    (fun n => (Λ n : ℂ) * χ n - δ) (M + 1) L hL
  simpa only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
    Kernel.T, Nat.zero_add, LeanLab.PNTPort.LargeSieve.e, Kernel.e] using h


/-- Page 484 definition of W. Induction preserves the principal character condition. -/
theorem primitiveCharacter_eq_one_iff (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) : χ.primitiveCharacter = 1 ↔ χ = 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  constructor
  · intro h
    apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
    have hp := χ.primitiveCharacter_isPrimitive
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  · intro h
    subst χ
    exact DirichletCharacter.primitiveCharacter_one

/-- Page 484 equation 19, from Prachar page 295 equation 6.4.
The iterated logarithm in Prachar's height denominator is absorbed by four fifths. -/
theorem prachar_height_absorption :
    ∃ X₀ : ℝ, Real.exp 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      Real.log x ^ (3 / 4 : ℝ) * Real.log (Real.log x) ^ (3 / 4 : ℝ) ≤
        Real.log x ^ (4 / 5 : ℝ) := by
  have hb := (isLittleO_log_rpow_rpow_atTop (3 / 4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 20)).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hb
  refine ⟨Real.exp (max 1 Y), Real.exp_le_exp.mpr (le_max_left _ _), ?_⟩
  intro x hx
  have hL : max 1 Y ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    simpa using h
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hL
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans hL)
  have h := hY (Real.log x) ((le_max_right _ _).trans hL)
  simp only [Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hL1) _),
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at h
  calc
    _ ≤ Real.log x ^ (3 / 4 : ℝ) * Real.log x ^ (1 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hL0.le _)
    _ = _ := by
      rw [← Real.rpow_add hL0]
      congr 1
      norm_num


/-- Pages 484 and 485 through Perelli and Pintz 1993 page 47 equation 21.
Gallagher's finite reduction holds on the exact real Farey arc radius.
The integer coefficient window is rounded down from q Q over two. -/
theorem character_gallagher_real_order (M q : ℕ) (hq : 0 < q)
    (Q : ℝ) (hQ : 0 < Q) (horder : 2 ≤ (q : ℝ) * Q)
    (χ : DirichletCharacter ℂ q) (δ : ℂ) :
    ∃ L : ℕ, 0 < L ∧ (q : ℝ) * Q / 4 ≤ L ∧ (L : ℝ) ≤ (q : ℝ) * Q / 2 ∧
      (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
        ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
          δ * Kernel.T 0 (M + 1) η‖ ^ 2) ≤
        (4 * Real.pi ^ 2 / ((q : ℝ) * Q) ^ 2) *
          ∑ m ∈ range (M + 1 + L),
            ‖LeanLab.PNTPort.Gallagher.win
              (fun n => (Λ n : ℂ) * χ n - δ) (M + 1) L m‖ ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqQ : 0 < (q : ℝ) * Q := mul_pos hq0 hQ
  let L : ℕ := ⌊(q : ℝ) * Q / 2⌋₊
  have hL1 : 1 ≤ L := by
    apply Nat.le_floor
    norm_num
    linarith
  have hL : 0 < L := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hLup : (L : ℝ) ≤ (q : ℝ) * Q / 2 := Nat.floor_le (by positivity)
  have hfloor : (q : ℝ) * Q / 2 < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLlow : (q : ℝ) * Q / 4 ≤ (L : ℝ) := by
    by_cases hsmall : (q : ℝ) * Q ≤ 4
    · have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast hL1
      linarith
    · linarith
  refine ⟨L, hL, hLlow, hLup, ?_⟩
  have hrad : 1 / ((q : ℝ) * Q) ≤ 1 / (2 * (L : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hc : Continuous (fun η : ℝ =>
      ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
        δ * Kernel.T 0 (M + 1) η‖ ^ 2) := by
    unfold Kernel.T Kernel.e
    fun_prop
  have hi :
      (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
        ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
          δ * Kernel.T 0 (M + 1) η‖ ^ 2) ≤
      (∫ η in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
        ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
          δ * Kernel.T 0 (M + 1) η‖ ^ 2) := by
    apply intervalIntegral.integral_mono_interval (neg_le_neg hrad) (by linarith [one_div_pos.mpr hqQ]) hrad
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    · exact hc.intervalIntegrable _ _
  have hcoeff : (Real.pi / (2 * L)) ^ 2 ≤ 4 * Real.pi ^ 2 / ((q : ℝ) * Q) ^ 2 := by
    have hh : Real.pi / (2 * L) ≤ 2 * Real.pi / ((q : ℝ) * Q) := by
      apply (div_le_div_iff₀ (by positivity) hqQ).mpr
      have hp := mul_le_mul_of_nonneg_left hLlow (show 0 ≤ 4 * Real.pi by positivity)
      nlinarith
    have hs := pow_le_pow_left₀ (show 0 ≤ Real.pi / (2 * L) by positivity) hh 2
    convert hs using 1 <;> ring
  exact hi.trans ((character_gallagher_reduction M L q hL χ δ).trans
    (mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

end
end LeanLab.Perelli1996.Decomp88
