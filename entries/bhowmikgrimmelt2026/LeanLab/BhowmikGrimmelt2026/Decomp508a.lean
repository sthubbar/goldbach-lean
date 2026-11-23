module

public import LeanLab.BhowmikGrimmelt2026.Decomp502a
public import LeanLab.BhowmikGrimmelt2026.PrimePowerMinor451
public import LeanLab.BhowmikGrimmelt2026.ZeroBoundLeaf150

/-!
Elementary steps for the sharp character major arc expansion.
Source: P0029 pages 11 and 12, displays 3.4 through 3.7.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Every noncoprime prime power through X divides q to the floor base two logarithm of X. -/
theorem noncoprime_prime_power_dvd508 {n q X : ℕ} (hn : IsPrimePow n)
    (hnX : n ≤ X) (hcop : ¬ Nat.Coprime n q) : n ∣ q ^ Nat.log 2 X := by
  obtain ⟨p, k, hp, hk, rfl⟩ := ((isPrimePow_nat_iff n).mp hn)
  have hpd : p ∣ q := by
    by_contra h
    exact hcop (Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr h))
  have hkX : k ≤ Nat.log 2 X :=
    Nat.le_log_of_pow_le (by norm_num) ((Nat.pow_le_pow_left hp.two_le k).trans hnX)
  exact (pow_dvd_pow_of_dvd hpd k).trans (pow_dvd_pow _ hkX)

/-- The total noncoprime Mangoldt mass has a logarithmic divisor majorant. -/
theorem noncoprime_mangoldt_mass508 {q X : ℕ} (hq : 1 ≤ q) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n) ≤ (Nat.log 2 X : ℝ) * Real.log q := by
  classical
  have hq0 : q ^ Nat.log 2 X ≠ 0 := pow_ne_zero _ (by omega)
  calc
    _ = ∑ n ∈ ((Finset.Icc 1 X).filter (fun n => ¬ Nat.Coprime n q)).filter
        (fun n => IsPrimePow n), ArithmeticFunction.vonMangoldt n := by
      symm
      apply Finset.sum_filter_of_ne
      intro n hn
      exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
    _ ≤ ∑ n ∈ (q ^ Nat.log 2 X).divisors, ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn, hpp⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn, hcop⟩ := Finset.mem_filter.mp hn
        exact Nat.mem_divisors.mpr
          ⟨noncoprime_prime_power_dvd508 hpp (Finset.mem_Icc.mp hn).2 hcop, hq0⟩
      · intro n _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by rw [ArithmeticFunction.vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

/-- The integer square root loses at most a factor four after squaring. -/
theorem sqrt_truncation_scale508 {X : ℕ} (hX : 1 ≤ X) :
    (X : ℝ) ≤ 4 * (Nat.sqrt X : ℝ) ^ 2 := by
  have hQ : 1 ≤ Nat.sqrt X := Nat.sqrt_pos.mpr (by omega)
  have hh := Nat.lt_succ_sqrt' X
  have h : X < (Nat.sqrt X + 1) ^ 2 := by exact hh
  have hr : (X : ℝ) < ((Nat.sqrt X : ℝ) + 1) ^ 2 := by exact_mod_cast h
  have hQr : (1 : ℝ) ≤ Nat.sqrt X := by exact_mod_cast hQ
  nlinarith

/-- The arc scale q times one plus beta X is at most five times the truncation. -/
theorem arc_frequency_scale508 {X q : ℕ} (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Nat.sqrt X) {β : ℝ}
    (hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X)) :
    (q : ℝ) * (1 + |β| * X) ≤ 5 * Nat.sqrt X := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hQp : (0 : ℝ) < Nat.sqrt X := by
    exact_mod_cast (hq.trans hqQ)
  have hb : (q : ℝ) * Nat.sqrt X * |β| ≤ 1 := by
    apply (le_div_iff₀ (mul_pos hqp hQp)).mp at hβ
    nlinarith only [hβ]
  have hx := sqrt_truncation_scale508 hX
  have hqR : (q : ℝ) ≤ Nat.sqrt X := by exact_mod_cast hqQ
  have hmul := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg X)
  apply (mul_le_mul_iff_left₀ hQp).mp
  nlinarith only [hx, hmul, mul_le_mul_of_nonneg_right hqR hQp.le]

/-- The Gauss factor and oscillatory square root together cost one quarter power. -/
theorem gauss_arc_scale508 {X q : ℕ} (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Nat.sqrt X) {β : ℝ}
    (hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X)) :
    Real.sqrt q * Real.sqrt (1 + |β| * X) ≤
      Real.sqrt 5 * (X : ℝ) ^ (1 / 4 : ℝ) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg q)]
  have hs := Real.sqrt_le_sqrt (arc_frequency_scale508 hX hq hqQ hβ)
  have hQ : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' X
  calc
    _ ≤ Real.sqrt (5 * Nat.sqrt X) := hs
    _ ≤ Real.sqrt (5 * Real.sqrt X) := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hQ (by norm_num))
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
      simp_rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul (Nat.cast_nonneg X)]
      norm_num

/-- The omitted nonunit mass is logarithmic squared when q is at most X. -/
theorem noncoprime_mangoldt_log508 {q n X : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (hnX : n ≤ X) (hqX : q ≤ X) :
    (∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ Nat.Coprime m q),
      ArithmeticFunction.vonMangoldt m) ≤ Real.log X ^ 2 / Real.log 2 := by
  have hX : (1 : ℝ) ≤ X := by exact_mod_cast (hq.trans hqX)
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX
  have hqlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hlogq : Real.log (q : ℝ) ≤ Real.log X := Real.log_le_log
    (by exact_mod_cast (by omega : 0 < q)) (by exact_mod_cast hqX)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnatlog : (Nat.log 2 n : ℝ) ≤ Real.log X / Real.log 2 := by
    have hh : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
      simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb n 2
    exact hh.trans (div_le_div_of_nonneg_right (Real.log_le_log
      (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnX)) hlog2.le)
  calc
    _ ≤ (Nat.log 2 n : ℝ) * Real.log q := noncoprime_mangoldt_mass508 hq
    _ ≤ (Real.log X / Real.log 2) * Real.log X :=
      mul_le_mul hnatlog hlogq hqlog (by positivity)
    _ = _ := by ring
/-- The induced character differs only at summation variables not coprime to the new modulus. -/
theorem character_changeLevel_sum508 {r q : ℕ} (hd : r ∣ q)
    (χ : DirichletCharacter ℂ r) (s : Finset ℕ) (c : ℕ → ℂ) :
    ‖(∑ n ∈ s, c n * DirichletCharacter.changeLevel hd χ (n : ZMod q)) -
      ∑ n ∈ s, c n * χ (n : ZMod r)‖ ≤
        ∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q), ‖c n‖ := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hcop : Nat.Coprime n q
  · have he : DirichletCharacter.changeLevel hd χ (n : ZMod q) = χ (n : ZMod r) := by
      simpa only [Int.cast_natCast] using DirichletCharacter.changeLevel_eq_cast_of_dvd'
        χ hd (Nat.isCoprime_iff_coprime.mpr hcop)
    simp [hcop, he]
  · have he : DirichletCharacter.changeLevel hd χ (n : ZMod q) = 0 :=
      MulChar.map_nonunit _ (fun h => hcop ((ZMod.isUnit_iff_coprime n q).mp h))
    simp only [hcop, not_false_eq_true, ite_true, he, mul_zero, zero_sub, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

/-- The sharp induced Chebyshev sum changes by at most the nonunit Mangoldt mass. -/
theorem psi_changeLevel_bound508 {r q : ℕ} (hd : r ∣ q)
    (χ : DirichletCharacter ℂ r) (n X : ℕ) (hq : 1 ≤ q)
    (hn : 1 ≤ n) (hnX : n ≤ X) (hqX : q ≤ X) :
    ‖(∑ n ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt n : ℂ) *
        DirichletCharacter.changeLevel hd χ (n : ZMod q)) -
      ∑ n ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt n : ℂ) *
        χ (n : ZMod r)‖ ≤ Real.log X ^ 2 / Real.log 2 := by
  have hb := character_changeLevel_sum508 hd χ (Finset.range (n + 1))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  have he : (∑ n ∈ (Finset.range (n + 1)).filter (fun n => ¬ Nat.Coprime n q),
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖) =
      ∑ n ∈ (Finset.Icc 1 n).filter (fun n => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n := by
    simp_rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    symm
    apply Finset.sum_subset
    · intro n hn
      obtain ⟨hn, hcop⟩ := Finset.mem_filter.mp hn
      have hh := Finset.mem_Icc.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcop⟩
    · intro n hn hnot
      obtain ⟨hn, hcop⟩ := Finset.mem_filter.mp hn
      have h0 : n = 0 := by
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn hnot
        omega
      subst n
      simp
  rw [he] at hb
  exact hb.trans (noncoprime_mangoldt_log508 hq hn hnX hqX)

/-- Removing Euler factors adds no zeros in the open right half plane. -/
theorem character_euler_factor_ne508 {r : ℕ} (χ : DirichletCharacter ℂ r)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 - χ (p : ZMod r) * (p : ℂ) ^ (-s) ≠ 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hn : ‖χ (p : ZMod r) * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
    calc
      _ ≤ 1 * (p : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right
        (DirichletCharacter.norm_le_one χ _) (by positivity)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  intro hz
  have hh : χ (p : ZMod r) * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [hh, norm_one] at hn
  exact (lt_irrefl 1) hn

/-- The complete imprimitive Euler product is nonzero in the open right half plane. -/
theorem character_euler_product_ne508 {r : ℕ} (χ : DirichletCharacter ℂ r)
    (q : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∏ p ∈ q.primeFactors, (1 - χ (p : ZMod r) * (p : ℂ) ^ (-s))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact character_euler_factor_ne508 χ (Nat.prime_of_mem_primeFactors hp) hs

/-- Inducing a character preserves every zero in the open critical strip. -/
theorem character_zero_changeLevel508 {r q : ℕ} [NeZero r] [NeZero q]
    (hd : r ∣ q) (χ : DirichletCharacter ℂ r) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ) s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 := by
  have hs : s ≠ 1 := by intro h; simp [h] at hs1
  rw [DirichletCharacter.LFunction_changeLevel hd χ (Or.inr hs),
    mul_eq_zero, or_iff_left (character_euler_product_ne508 χ q hs0)]

/-- Inducing a character preserves analytic multiplicities in the open critical strip. -/
theorem character_mult_changeLevel508 {r q : ℕ} [NeZero r] [NeZero q]
    (hd : r ∣ q) (χ : DirichletCharacter ℂ r) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mult (DirichletCharacter.changeLevel hd χ) s = mult χ s := by
  let P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors,
    (1 - χ (p : ZMod r) * (p : ℂ) ^ (-z))
  have hs : s ≠ 1 := by intro h; simp [h] at hs1
  have hP : AnalyticAt ℂ P s := by
    apply Finset.analyticAt_fun_prod
    intro p hp
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hps : (p : ℂ) ∈ Complex.slitPlane := Complex.natCast_mem_slitPlane.mpr
      (Nat.prime_of_mem_primeFactors hp).ne_zero
    fun_prop
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
    apply DifferentiableOn.analyticAt (s := {1}ᶜ) _
      (isOpen_compl_singleton.mem_nhds hs)
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have he : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ) =ᶠ[nhds s]
      (fun z => DirichletCharacter.LFunction χ z * P z) := by
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact DirichletCharacter.LFunction_changeLevel hd χ (Or.inr hz)
  unfold mult analyticOrderNatAt
  congr 1
  rw [analyticOrderAt_congr he]
  change analyticOrderAt (DirichletCharacter.LFunction χ * P) s = _
  have hP0 : P s ≠ 0 := character_euler_product_ne508 χ q hs0
  have hPo : analyticOrderAt P s = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hP0)
  rw [analyticOrderAt_mul hL hP, hPo, add_zero]

/-- The real rational phase agrees with the standard additive character. -/
theorem rational_phase508 {q : ℕ} [NeZero q] (a : ℤ) (n : ℕ) :
    ee ((n : ℝ) * a / q) = ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) := by
  rw [show (a : ZMod q) * (n : ZMod q) = ((a * (n : ℤ) : ℤ) : ZMod q) by push_cast; rfl,
    ZMod.stdAddChar_coe]
  unfold ee
  congr 1
  push_cast
  ring

/-- Character inversion includes exactly the coprime summation variables. -/
theorem rational_character508 {q : ℕ} [NeZero q] (a : ℤ)
    (ha : IsUnit (a : ZMod q)) (n : ℕ) :
    (if Nat.Coprime n q then ee ((n : ℝ) * a / q) else 0) =
      (1 / (Nat.totient q : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        tauConj χ * χ (a : ZMod q) * χ (n : ZMod q) := by
  classical
  by_cases hn : Nat.Coprime n q
  · rw [ite_eq_left hn, rational_phase508]
    have hx := ha.mul ((ZMod.isUnit_iff_coprime n q).mpr hn)
    have hh := gauss_character_inversion504
      ((a : ZMod q) * (n : ZMod q)) hx
    have he (x : ZMod q) : ee ((x.val : ℝ) / q) = ZMod.stdAddChar x := by
      rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
      unfold ee
      congr 1
      push_cast
      ring
    rw [he] at hh
    simpa only [map_mul, mul_assoc] using hh
  · rw [ite_eq_right hn]
    have hn' : ¬ IsUnit (n : ZMod q) := fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h)
    simp [MulChar.map_nonunit _ hn']

/-- Finite character inversion preserves arbitrary coefficients and the nonunit restriction. -/
theorem finite_character_expansion508 {q : ℕ} [NeZero q] (a : ℤ)
    (ha : IsUnit (a : ZMod q)) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ n ∈ s.filter (fun n => Nat.Coprime n q), c n * ee ((n : ℝ) * a / q)) =
      (1 / (Nat.totient q : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        tauConj χ * χ (a : ZMod q) * ∑ n ∈ s, c n * χ (n : ZMod q) := by
  classical
  rw [Finset.sum_filter]
  calc
    _ = ∑ n ∈ s, c n * (if Nat.Coprime n q then ee ((n : ℝ) * a / q) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ n ∈ s, c n * ((1 / (Nat.totient q : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q, tauConj χ * χ (a : ZMod q) * χ (n : ZMod q)) := by
      simp_rw [rational_character508 a ha]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- The principal character supplies exactly the Mobius main term. -/
theorem character_main508 {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (u : ℂ) :
    (1 / (Nat.totient q : ℂ)) *
      (∑ χ : DirichletCharacter ℂ q, tauConj χ * χ a * (if χ = 1 then u else 0)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * u := by
  classical
  simp [tau_principal504, MulChar.one_apply ha, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- A bound for each character error passes through the exact main term subtraction. -/
theorem character_error_assembly508 {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (f : DirichletCharacter ℂ q → ℂ) (u : ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ χ, ‖f χ - (if χ = 1 then u else 0)‖ ≤ B) :
    ‖(1 / (Nat.totient q : ℂ)) * (∑ χ : DirichletCharacter ℂ q, tauConj χ * χ a * f χ) -
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * u‖ ≤
      Real.sqrt q * B := by
  rw [← character_main508 a ha u, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  exact character_error_bound504 a _ hB hf

/-- Exact rational character expansion of the sharp prime sum with its nonunit correction. -/
theorem sharp_rational_character_identity508 {q : ℕ} [NeZero q]
    (a : ℤ) (ha : IsUnit (a : ZMod q)) (X : ℕ) (β : ℝ) :
    Ssum X ((a : ℝ) / q + β) =
      (1 / (Nat.totient q : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        tauConj χ * χ (a : ZMod q) *
          (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) *
            χ (n : ZMod q) * ee ((n : ℝ) * β)) +
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ Nat.Coprime n q),
        (ArithmeticFunction.vonMangoldt n : ℂ) * ee ((n : ℝ) * ((a : ℝ) / q + β)) := by
  classical
  have he (n : ℕ) : ((ArithmeticFunction.vonMangoldt n : ℂ) * ee ((n : ℝ) * β)) *
      ee ((n : ℝ) * a / q) = (ArithmeticFunction.vonMangoldt n : ℂ) *
        ee ((n : ℝ) * ((a : ℝ) / q + β)) := by
    rw [mul_assoc, ← ee_add150]
    congr 2
    ring
  have hc := finite_character_expansion508 a ha (Finset.Icc 1 X)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * ee ((n : ℝ) * β))
  simp_rw [he] at hc
  have hterm (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.vonMangoldt n : ℂ) * ee ((n : ℝ) * β)) * χ (n : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * ee ((n : ℝ) * β) := by
    apply Finset.sum_congr rfl
    intro n hn
    ring
  simp_rw [hterm] at hc
  rw [Ssum_eq150, ← hc]
  exact (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 X)
    (fun n => Nat.Coprime n q)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
      ee ((n : ℝ) * ((a : ℝ) / q + β)))).symm

/-- The rational sharp error reduces to character errors and the explicit nonunit mass. -/
theorem sharp_rational_character_bound508 {q : ℕ} [NeZero q]
    (a : ℤ) (ha : IsUnit (a : ZMod q)) {X : ℕ} (hqX : q ≤ X) (β : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hchar : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) *
        χ (n : ZMod q) * ee ((n : ℝ) * β)) -
          (if χ = 1 then TX150 X β else 0)‖ ≤ B) :
    ‖Ssum X ((a : ℝ) / q + β) -
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β‖ ≤
        Real.sqrt q * B + Real.log X ^ 2 / Real.log 2 := by
  classical
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hX : 1 ≤ X := hq.trans hqX
  have hc := character_error_assembly508 (a : ZMod q) ha
    (fun χ => ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) *
      χ (n : ZMod q) * ee ((n : ℝ) * β)) (TX150 X β) hB hchar
  have hn : ‖∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ Nat.Coprime n q),
      (ArithmeticFunction.vonMangoldt n : ℂ) * ee ((n : ℝ) * ((a : ℝ) / q + β))‖ ≤
        Real.log X ^ 2 / Real.log 2 := by
    apply (norm_sum_le _ _).trans
    simp_rw [norm_mul, norm_ee150, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact noncoprime_mangoldt_log508 hq hX (le_refl X) hqX
  rw [sharp_rational_character_identity508 a ha]
  have he (x y z : ℂ) : x + y - z = (x - z) + y := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hc hn)

/-- The Mangoldt convolution vanishes before two positive prime powers can sum. -/
theorem r2_small_zero508 {N : ℕ} (hN : N ≤ 2) : r2 N = 0 := by
  have hvm (m : ℕ) (hm : m ≤ 1) : ArithmeticFunction.vonMangoldt m = 0 := by
    interval_cases m <;> simp
  unfold r2
  apply Finset.sum_eq_zero
  intro x hx
  have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases h1 : x.1 ≤ 1
  · rw [hvm _ h1, zero_mul]
  · rw [hvm x.2 (by omega), mul_zero]

/-- The finite boundary needed for the repaired prime power estimate. -/
theorem small_even_goldbach508 {N : ℕ} (hN : Even N) (h4 : 4 ≤ N) (h16 : N < 16) :
    IsGoldbachSum N := by
  interval_cases N <;> norm_num at hN
  · exact ⟨2, 2, by decide, by decide, rfl⟩
  · exact ⟨3, 3, by decide, by decide, rfl⟩
  · exact ⟨3, 5, by decide, by decide, rfl⟩
  · exact ⟨3, 7, by decide, by decide, rfl⟩
  · exact ⟨5, 7, by decide, by decide, rfl⟩
  · exact ⟨3, 11, by decide, by decide, rfl⟩

/-- A bounded constant weight does not identify the prime sums at cutoffs N and X. -/
theorem bounded_prime_cutoff_mismatch508 :
    (∑ n ∈ (Finset.range 2).filter Nat.Prime,
      ((ArithmeticFunction.vonMangoldt n * (1 : ℝ) : ℝ) : ℂ) * ee (0 * n)) ≠
    (∑ n ∈ (Finset.range 3).filter Nat.Prime,
      ((ArithmeticFunction.vonMangoldt n * (1 : ℝ) : ℝ) : ℂ) * ee (0 * n)) := by
  have h1 : (Finset.range 2).filter Nat.Prime = ∅ := by decide
  have h2 : (Finset.range 3).filter Nat.Prime = {2} := by decide
  rw [h1, h2]
  simp only [Finset.sum_empty, Finset.sum_singleton, mul_one, zero_mul]
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have he : ee 0 = 1 := by simp [ee]
  rw [he, mul_one]
  exact Ne.symm (by exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne')

section

open MeasureTheory
attribute [local instance] Classical.propDecidable
/-- A weight vanishing above one permits extension of the prime cutoff. -/
theorem prime_cutoff_eq508 {ϕ : ℝ → ℝ} (hsupp : ∀ x, 1 ≤ x → ϕ x = 0)
    {N X : ℕ} (hN : 1 ≤ N) (hNX : N ≤ X) (α : ℝ) :
    (∑ n ∈ (Finset.range (X + 1)).filter Nat.Prime,
      ((ArithmeticFunction.vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) =
      primeSphi451 ϕ N α := by
  classical
  simp only [primeSphi451, apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hn).trans_le (by omega)), hp⟩
  · intro n hn hnot
    obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hn
    have hnN : N < n := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hp⟩)
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have hscale : 1 ≤ (n : ℝ) / N :=
      (le_div_iff₀ hNp).mpr (by simpa using (show (N : ℝ) ≤ n by exact_mod_cast hnN.le))
    rw [hsupp _ hscale]
    simp

/-- With the paper's upper support condition the prime cutoff defect has the existing budget. -/
theorem nonprime_defect_with_support508 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (hsupp : ∀ x, 1 ≤ x → ϕ x = 0)
    {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter Nat.Prime,
              ((ArithmeticFunction.vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2) ≤
      192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
  classical
  let W : ℕ → ℝ → ℂ := fun N α =>
    if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else ee (-(N * α))
  have hW (N : ℕ) (α : ℝ) : ‖W N α‖ ≤ 1 := by
    dsimp [W]
    split_ifs
    · simp
    · rw [norm_ee150]
  have h := prime_power_family_log5_451 hM hbound hX W hW
  convert h using 1
  apply Finset.sum_congr rfl
  intro N hN
  simp_rw [prime_cutoff_eq508 hsupp (Finset.mem_Icc.mp hN).1 (Finset.mem_Icc.mp hN).2]
  congr 2
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α <;> simp [W, hm]

end

/-- P0029 pages 11 and 12. Estimate only the explicit formula remainder after Abel summation. -/
theorem abel_remainder_bound508 (r : ℕ → ℂ) (X : ℕ) (β B : ℝ)
    (hB : ∀ n ≤ X, ‖r n‖ ≤ B) :
    ‖r X * ee ((X : ℝ) * β) -
      ∑ n ∈ Finset.range X, r n *
        (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
      B * (1 + (X : ℝ) * ‖ee β - 1‖) := by
  have hstep (n : ℕ) :
      ‖ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)‖ = ‖ee β - 1‖ := by
    rw [show (((n + 1 : ℕ) : ℝ) * β) = (n : ℝ) * β + β by push_cast; ring,
      ee_add150]
    rw [show ee ((n : ℝ) * β) * ee β - ee ((n : ℝ) * β) =
      ee ((n : ℝ) * β) * (ee β - 1) by ring, norm_mul, norm_ee150, one_mul]
  calc
    _ ≤ ‖r X * ee ((X : ℝ) * β)‖ +
        ‖∑ n ∈ Finset.range X, r n *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ := norm_sub_le _ _
    _ ≤ B + (X : ℝ) * (B * ‖ee β - 1‖) := by
      apply add_le_add
      · simpa only [norm_mul, norm_ee150, mul_one] using hB X le_rfl
      · refine (norm_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ _n ∈ Finset.range X, B * ‖ee β - 1‖ := by
            apply Finset.sum_le_sum
            intro n hn
            rw [norm_mul, hstep]
            exact mul_le_mul_of_nonneg_right (hB n (by have := Finset.mem_range.mp hn; omega))
              (norm_nonneg _)
          _ = _ := by simp
    _ = B * (1 + (X : ℝ) * ‖ee β - 1‖) := by ring

/-- The Gauss cost of the remainder variation is at most square root X on an assigned arc. -/
theorem remainder_arc_scale508 {X q : ℕ} (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Nat.sqrt X) {β : ℝ}
    (hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X)) :
    Real.sqrt q * (1 + (X : ℝ) * ‖ee β - 1‖) ≤
      10 * Real.pi * Real.sqrt X := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : Real.sqrt q ≤ (q : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr hqR)
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hQ : (Nat.sqrt X : ℝ) ≤ Real.sqrt X :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' X)
  calc
    _ ≤ (q : ℝ) * (1 + (X : ℝ) * (2 * Real.pi * |β|)) := by
      apply mul_le_mul hs _ (by positivity) (by positivity)
      exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left (norm_ee_sub_one_le502 β)
        (Nat.cast_nonneg X))
    _ ≤ 2 * Real.pi * ((q : ℝ) * (1 + |β| * X)) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr hpi)]
    _ ≤ 2 * Real.pi * (5 * Nat.sqrt X) :=
      mul_le_mul_of_nonneg_left (arc_frequency_scale508 hX hq hqQ hβ) (by positivity)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hQ (show 0 ≤ 10 * Real.pi by positivity)]

/-- A bounded sharp explicit formula remainder fits the square root X arc budget. -/
theorem gauss_remainder_arc508 (r : ℕ → ℂ) {X q : ℕ} (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Nat.sqrt X) {β B : ℝ}
    (hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X)) (hB : 0 ≤ B)
    (hr : ∀ n ≤ X, ‖r n‖ ≤ B) :
    Real.sqrt q * ‖r X * ee ((X : ℝ) * β) -
      ∑ n ∈ Finset.range X, r n *
        (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
      10 * Real.pi * B * Real.sqrt X := by
  calc
    _ ≤ Real.sqrt q * (B * (1 + (X : ℝ) * ‖ee β - 1‖)) :=
      mul_le_mul_of_nonneg_left (abel_remainder_bound508 r X β B hr) (Real.sqrt_nonneg _)
    _ = B * (Real.sqrt q * (1 + (X : ℝ) * ‖ee β - 1‖)) := by ring
    _ ≤ B * (10 * Real.pi * Real.sqrt X) :=
      mul_le_mul_of_nonneg_left (remainder_arc_scale508 hX hq hqQ hβ) hB
    _ = _ := by ring

/-- P0029 page 11 display 3.5, the finite sharp zero primitive. -/
noncomputable def zeroPartial508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) (n : ℕ) : ℂ :=
  ∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((n : ℂ) ^ ρ / ρ)

/-- P0029 page 15 display 4.6, finite zero modes retained inside Abel summation. -/
noncomputable def zeroTwist508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) (X : ℕ) (β : ℝ) : ℂ :=
  ∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
    ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
      (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))

/-- P0029 page 11 display 3.5, the sharp remainder after retaining every listed zero. -/
noncomputable def sharpRemainder508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) (n : ℕ) : ℂ :=
  psiCharacter502 χ n - (if χ = 1 then (n : ℂ) else 0) + zeroPartial508 χ Z n

/-- Mathlib finite summation by parts applied to the linear principal primitive. -/
theorem linear_main_abel508 (X : ℕ) (u : ℕ → ℂ) :
    (X : ℂ) * u X - ∑ n ∈ Finset.range X, (n : ℂ) * (u (n + 1) - u n) =
      ∑ n ∈ Finset.Icc 1 X, u n := by
  let f : ℕ → ℂ := fun n => if n = 0 then 0 else 1
  have hf (n : ℕ) : (∑ m ∈ Finset.range (n + 1), f m) = (n : ℂ) := by
    rw [Finset.sum_range_succ']
    simp [f]
  have h := Finset.sum_range_by_parts' f u (X + 1)
  simp_rw [hf] at h
  have he : (∑ n ∈ Finset.range (X + 1), f n * u n) =
      ∑ n ∈ Finset.Icc 1 X, u n := by
    rw [Finset.sum_range_eq_add_Ico _ (by omega)]
    simp only [f, ite_eq_left rfl, zero_mul, zero_add, Finset.Ico_add_one_right_eq_Icc]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ite_eq_right (by have := (Finset.mem_Icc.mp hn).1; omega), one_mul]
  simpa only [Nat.add_sub_cancel, smul_eq_mul, he] using h.symm

/-- The sum of the individual zero mode Abel expressions is exact before norms. -/
theorem zero_abel_identity508 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : Finset ℂ) (X : ℕ) (β : ℝ) :
    zeroPartial508 χ Z X * ee ((X : ℝ) * β) -
      ∑ n ∈ Finset.range X, zeroPartial508 χ Z n *
        (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)) = zeroTwist508 χ Z X β := by
  have h := finite_mode_abel504 Z (fun ρ => (mult χ ρ : ℂ))
    (fun ρ n => (n : ℂ) ^ ρ / ρ) (fun _ => 0) (fun n => ee ((n : ℝ) * β)) X
  simpa [zeroPartial508, zeroTwist508] using h

/-- A nontrivial zero list makes the sharp remainder vanish at the zero endpoint. -/
theorem sharp_remainder_zero508 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, 0 < ρ.re) : sharpRemainder508 χ Z 0 = 0 := by
  have hz : zeroPartial508 χ Z 0 = 0 := by
    unfold zeroPartial508
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := by intro h; simpa [h] using hZ ρ hρ
    simp [Complex.zero_cpow hρ0]
  simp [sharpRemainder508, psiCharacter502, hz]
/-- P0029 page 15 display 4.6, exact separation of principal, zero and remainder modes. -/
theorem sharp_character_mode_identity508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) (X : ℕ) (β : ℝ) :
    (∑ n ∈ Finset.range (X + 1),
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) * ee ((n : ℝ) * β)) -
        (if χ = 1 then TX150 X β else 0) =
      (sharpRemainder508 χ Z X * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, sharpRemainder508 χ Z n *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))) - zeroTwist508 χ Z X β := by
  rw [psi_twist_abel502, ← zero_abel_identity508]
  have hm := linear_main_abel508 X (fun n => ee ((n : ℝ) * β))
  change _ = TX150 X β at hm
  unfold sharpRemainder508
  split_ifs with h
  · simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linear_combination hm
  · simp only [sub_zero, add_mul, Finset.sum_add_distrib]
    ring
/-- P0029 page 15 display 4.6, the zero mode norm and the proved remainder budget. -/
theorem sharp_character_mode_bound508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) {X : ℕ} (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Nat.sqrt X) {β B : ℝ}
    (hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X)) (hB : 0 ≤ B)
    (hr : ∀ n ≤ X, ‖sharpRemainder508 χ Z n‖ ≤ B) :
    Real.sqrt q * ‖(∑ n ∈ Finset.range (X + 1),
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) * ee ((n : ℝ) * β)) -
        (if χ = 1 then TX150 X β else 0)‖ ≤
      Real.sqrt q * ‖zeroTwist508 χ Z X β‖ + 10 * Real.pi * B * Real.sqrt X := by
  rw [sharp_character_mode_identity508]
  have hrb := gauss_remainder_arc508 (sharpRemainder508 χ Z) hX hq hqQ hβ hB hr
  calc
    _ ≤ Real.sqrt q * (‖sharpRemainder508 χ Z X * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, sharpRemainder508 χ Z n *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ +
          ‖zeroTwist508 χ Z X β‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.sqrt_nonneg _)
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg (q : ℝ)]

/-- P0029 pages 11 and 15, rational assembly after the zero modes are separated. -/
theorem sharp_rational_mode_reduction508 {q : ℕ} [NeZero q]
    (a : ℤ) (ha : IsUnit (a : ZMod q)) {X : ℕ} (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Nat.sqrt X) {β B D : ℝ}
    (hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X)) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hmode : ∀ χ : DirichletCharacter ℂ q, ∃ Z : Finset ℂ,
      (∀ n ≤ X, ‖sharpRemainder508 χ Z n‖ ≤ B) ∧ ‖zeroTwist508 χ Z X β‖ ≤ D) :
    ‖Ssum X ((a : ℝ) / q + β) -
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β‖ ≤
      Real.sqrt q * D + 10 * Real.pi * B * Real.sqrt X + Real.log X ^ 2 / Real.log 2 := by
  classical
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hR : 0 ≤ 10 * Real.pi * B * Real.sqrt X :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hB) (Real.sqrt_nonneg _)
  have hc : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) *
        χ (n : ZMod q) * ee ((n : ℝ) * β)) -
          (if χ = 1 then TX150 X β else 0)‖ ≤
            D + (10 * Real.pi * B * Real.sqrt X) / Real.sqrt q := by
    intro χ
    obtain ⟨Z, hr, hz⟩ := hmode χ
    have hb := sharp_character_mode_bound508 χ Z hX hq hqQ hβ hB hr
    have he : (∑ n ∈ Finset.range (X + 1),
        ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) * ee ((n : ℝ) * β)) =
      ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * ee ((n : ℝ) * β) := by
      rw [Finset.sum_range_eq_add_Ico _ (by omega)]
      simp [Finset.Ico_add_one_right_eq_Icc]
    rw [he] at hb
    have hb' := hb.trans (add_le_add (mul_le_mul_of_nonneg_left hz hs.le) le_rfl)
    calc
      _ ≤ (Real.sqrt q * D + 10 * Real.pi * B * Real.sqrt X) / Real.sqrt q :=
        (le_div_iff₀ hs).mpr (by by_cases hχ : χ = 1 <;> simpa only [hχ, ite_true, ite_false, mul_comm] using hb')
      _ = _ := by field_simp [ne_of_gt hs]
  have hb := sharp_rational_character_bound508 a ha
    (hqQ.trans (Nat.sqrt_le_self X)) β (add_nonneg hD (div_nonneg hR hs.le)) hc
  calc
    _ ≤ _ := hb
    _ = _ := by field_simp [ne_of_gt hs]

/-- P0029 page 12, explicit absorption of the logarithmic remainder into a positive power. -/
theorem log_sq_power_budget508 {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    Real.log x ^ 2 ≤ (2 / ε) ^ 2 * x ^ ε := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h := Real.log_le_rpow_div hxp.le (half_pos hε)
  have hp : (x ^ (ε / 2)) ^ 2 = x ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (x ^ (ε / 2) / (ε / 2)) ^ 2 := by
      exact pow_le_pow_left₀ (Real.log_nonneg hx) h 2
    _ = _ := by rw [div_pow, hp]; field_simp
/-- P0029 page 12, the remainder square root fits every admissible zero exponent. -/
theorem sqrt_log_power_budget508 {x Θ ε : ℝ} (hx : 1 ≤ x)
    (hΘ : 1 / 2 ≤ Θ) (hε : 0 < ε) :
    Real.sqrt x * Real.log x ^ 2 ≤ (2 / ε) ^ 2 * x ^ (Θ + ε) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc
    _ ≤ Real.sqrt x * ((2 / ε) ^ 2 * x ^ ε) :=
      mul_le_mul_of_nonneg_left (log_sq_power_budget508 hx hε) (Real.sqrt_nonneg _)
    _ = (2 / ε) ^ 2 * x ^ ((1 / 2 : ℝ) + ε) := by
      rw [Real.rpow_add hxp, Real.sqrt_eq_rpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (sq_nonneg _)

/-- SPLIT piece 2 of `zeroBound_lower150`. P0029 Section 3, page 9, Theorem 3.1:
"every zero of every Dirichlet L-function" includes the modulus one character,
whose L-function is the Riemann zeta function. PROVED from Mathlib.
AI wrote the Lean code. -/
theorem LFunction_modOne_eq_zeta150 (s : ℂ) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s := by
  rw [DirichletCharacter.LFunction_modOne_eq]

/-- SPLIT piece 3 of `zeroBound_lower150`. P0029 Section 3, page 9, hypothesis of
Theorem 3.1 applied to the modulus one character: a zeta zero in the strip
`0 < Re s < 1` has real part at most Θ. PROVED. AI wrote the Lean code. -/
theorem zeroBound_zeta_zero150 {Θ : ℝ} (hZ : ZeroBound Θ) {s : ℂ}
    (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) : s.re ≤ Θ := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  exact hZ 1 (1 : DirichletCharacter ℂ 1) s (by rw [LFunction_modOne_eq_zeta150]; exact hs) h0 h1

/-- LEAF, now SPLIT. Page 12, the best possible zero bound is at least one half.
Derived from the cited Hardy 1914 critical line zero, `hardy_critical_line_zero150`,
and the modulus one case of the zero bound hypothesis, `zeroBound_zeta_zero150`.
CONDITIONAL ON `hardy_critical_line_zero150`, which is OPEN. -/
theorem zeroBound_lower150 {Θ : ℝ} (hZ : ZeroBound Θ) : 1 / 2 ≤ Θ := by
  obtain ⟨t, ht⟩ := hardy_critical_line_zero150
  have hre : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 := by simp
  have h := zeroBound_zeta_zero150 hZ ht (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rwa [hre] at h

-- The sealed oscillatory and sharp arc declarations are proved in SharpArc673.lean.

end LeanLab.BhowmikGrimmelt2026
