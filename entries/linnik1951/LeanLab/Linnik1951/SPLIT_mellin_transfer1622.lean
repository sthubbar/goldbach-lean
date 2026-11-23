module

public import LeanLab.Linnik1951.SPLIT1622_mellin

/-!
Split of mellin_transfer1622 into three leaves. The transfer of the character
prime sum to a Mellin integral is cut into three independent steps: the line
bound of the coefficient under the zero hypothesis, the prime power expansion of
the logarithm, and the size of the part of that expansion carrying powers of
exponent at least two. The assembly at the end has no placeholder proof and does not use
mellin_transfer1622.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951



private lemma exp_neg_mul_sq_le1622 {c x y : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp (-(c * y ^ 2)) ≤ Real.exp (-(c * x ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ c * (y - x) * (y + x) :=
    mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hxy)) (by linarith)
  nlinarith [h]

/-- The Gaussian majorant `x ↦ exp (-(c x^2))` is antitone on the nonnegative
half line for a positive `c`. -/

private lemma exp_neg_mul_sq_antitone1622 {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun x : ℝ => Real.exp (-(c * x ^ 2))) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only
  exact exp_neg_mul_sq_le1622 hc hx hxy

private lemma summable_exp_neg_mul_sq1622 {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-(c * (n : ℝ) ^ 2))) :=
  (exp_neg_mul_sq_antitone1622 hc).summable_of_integrableOn_Ioi_zero
    (by simpa only [neg_mul] using (integrable_exp_neg_mul_sq hc).integrableOn)
    (fun t _ => (Real.exp_pos _).le)

/-- Summing the Gaussian factor over the primes costs at most half the Gaussian
integral. The primes are a subset of the positive integers, so the sum over the
lattice points below the curve is bounded by the integral test. -/

private lemma tsum_exp_prime_gauss1622 {c : ℝ} (hc : 0 < c) :
    (∑' p : Nat.Primes, Real.exp (-(c * ((p : ℕ) : ℝ) ^ 2))) ≤
      Real.sqrt (Real.pi / c) / 2 := by
  classical
  have hanti := exp_neg_mul_sq_antitone1622 hc
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ Real.exp (-(c * t ^ 2)) :=
    fun t _ => (Real.exp_pos _).le
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-(c * x ^ 2))) (Set.Ioi 0) :=
    by simpa only [neg_mul] using (integrable_exp_neg_mul_sq hc).integrableOn
  have hsum : Summable (fun n : ℕ => Real.exp (-(c * (n : ℝ) ^ 2))) :=
    summable_exp_neg_mul_sq1622 hc
  set g1 : ℕ → ℝ := fun n => if 1 ≤ n then Real.exp (-(c * (n : ℝ) ^ 2)) else 0 with g1def
  have hg1nn : ∀ n, 0 ≤ g1 n := by
    intro n; simp only [g1def]; split_ifs <;> positivity
  have hg1_le : ∀ n, g1 n ≤ Real.exp (-(c * (n : ℝ) ^ 2)) := by
    intro n; simp only [g1def]; split_ifs with h <;> (first | exact le_rfl | positivity)
  have hsum_g1 : Summable g1 := Summable.of_nonneg_of_le hg1nn hg1_le hsum
  -- the prime sum is the sum of `g1` over the primes
  have h1 : (∑' p : Nat.Primes, Real.exp (-(c * ((p : ℕ) : ℝ) ^ 2)))
      = ∑' p : {n : ℕ // n.Prime}, g1 (p : ℕ) := by
    apply tsum_congr
    intro p
    simp only [g1def, ite_eq_left p.property.one_le]
  -- `g1` is the Gaussian sequence with its value at zero removed
  have hg1eq : (fun n : ℕ => g1 n) = fun n : ℕ =>
      if n = 0 then (0 : ℝ) else Real.exp (-(c * (n : ℝ) ^ 2)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [g1def]
    · simp only [g1def, ite_eq_left (show 1 ≤ n from h), ite_eq_right h.ne']
  have hsum' : Summable (fun n : ℕ =>
      if n = 0 then (0 : ℝ) else Real.exp (-(c * (n : ℝ) ^ 2))) := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs with h <;> (first | positivity | exact le_rfl)) hsum
  have hshift : (∑' n : ℕ, g1 n) = ∑' k : ℕ, Real.exp (-(c * (((k + 1 : ℕ) : ℝ)) ^ 2)) := by
    rw [hg1eq, hsum'.tsum_eq_zero_add]
    simp only [ite_true, zero_add, Nat.succ_ne_zero, ite_false]
  calc (∑' p : Nat.Primes, Real.exp (-(c * ((p : ℕ) : ℝ) ^ 2)))
      = ∑' p : {n : ℕ // n.Prime}, g1 (p : ℕ) := h1
    _ ≤ ∑' n : ℕ, g1 n :=
        hsum_g1.tsum_subtype_le g1 {n : ℕ | Nat.Prime n} hg1nn
    _ = ∑' k : ℕ, Real.exp (-(c * (((k + 1 : ℕ) : ℝ)) ^ 2)) := hshift
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(c * x ^ 2)) :=
        AntitoneOn.tsum_add_one_le_integral hanti hint hnonneg
    _ = Real.sqrt (Real.pi / c) / 2 := by
        simpa only [neg_mul] using integral_gaussian_Ioi c


private lemma norm_inv_add_two1622 (k : ℕ) :
    ‖((k : ℂ) + 2)⁻¹‖ = ((k : ℝ) + 2)⁻¹ := by
  rw [norm_inv]
  congr 1
  have h : ((k : ℂ) + 2) = (((k : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The exponential factor of the `(p, k)` term is at most the Gaussian factor
with the exponent `p^2 2^k`, since `p` is at least two. -/

private lemma exp_factor_le1622 (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (hp : 2 ≤ p) (k : ℕ) :
    Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) ≤
      Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) := by
  apply Real.exp_le_exp.mpr
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2k : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hp2 k
  have hkey : (p : ℝ) ^ (k + 2) = (p : ℝ) ^ k * (p : ℝ) ^ 2 := by rw [pow_add]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [neg_le_neg_iff, hkey]
  apply div_le_div_of_nonneg_right _ hNpos.le
  rw [mul_comm ((p : ℝ) ^ 2) ((2 : ℝ) ^ k)]
  exact mul_le_mul_of_nonneg_right h2k (by positivity)


private lemma chi_nat_norm_le_one1622 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (m : ℕ) : ‖χ m‖ ≤ 1 := by
  have := DirichletCharacter.norm_le_one χ (m : ZMod q)
  simpa using this

private lemma norm_term_le1622 (N : ℕ) (hN : 1 ≤ N) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (α : ℝ) (p : ℕ) (hp : 2 ≤ p) (k : ℕ) :
    ‖(((k : ℂ) + 2)⁻¹ * χ (p ^ (k + 2)) *
        (Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * ((p : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
      ≤ ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) := by
  have h1 : ‖((k : ℂ) + 2)⁻¹‖ = ((k : ℝ) + 2)⁻¹ := norm_inv_add_two1622 k
  have h2 : ‖χ (p ^ (k + 2))‖ ≤ 1 := by
    simpa [Nat.cast_pow] using chi_nat_norm_le_one1622 χ (p ^ (k + 2))
  have h3 : ‖((Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) : ℝ) : ℂ)‖ =
      Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h4 : ‖Complex.exp ((-(2 * Real.pi * α * ((p : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hA : (0 : ℝ) ≤ ((k : ℝ) + 2)⁻¹ := by positivity
  have hE : (0 : ℝ) < Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) := Real.exp_pos _
  have hstep : ((k : ℝ) + 2)⁻¹ * ‖χ (p ^ (k + 2))‖ *
      Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) * 1 ≤
        ((k : ℝ) + 2)⁻¹ * 1 * Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) * 1 := by
    gcongr
  calc ‖(((k : ℂ) + 2)⁻¹ * χ (p ^ (k + 2)) *
        (Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * ((p : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
      = ((k : ℝ) + 2)⁻¹ * ‖χ (p ^ (k + 2))‖ *
          Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) * 1 := by
        rw [norm_mul, norm_mul, norm_mul, h1, h3, h4]
    _ ≤ ((k : ℝ) + 2)⁻¹ * 1 * Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) * 1 := hstep
    _ = ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) := by ring
    _ ≤ ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (exp_factor_le1622 N hN p hp k) (by positivity)

private lemma sqrt_pow1622 {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = (Real.sqrt x) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

/-- The square root of the `k`-th power of two is at least the `k`-th power of
three quarters. -/
private lemma sqrt_halves1622 (N k : ℕ) :
    Real.sqrt (Real.pi * (N : ℝ) / 2 ^ k) ≤
      Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hpos : (0 : ℝ) < Real.pi * (N : ℝ) := by positivity
  have hkey : (1 : ℝ) / 2 ^ k ≤ (9 / 16 : ℝ) ^ k := by
    have h1 : (1 : ℝ) / 2 ^ k = ((2 : ℝ)⁻¹) ^ k := by rw [one_div, ← inv_pow]
    rw [h1]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) k
  have hR : (Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k) ^ 2
      = Real.pi * (N : ℝ) * (9 / 16 : ℝ) ^ k := by
    rw [mul_pow, Real.sq_sqrt hpos.le, ← pow_mul, mul_comm k 2, pow_mul,
      show ((3 : ℝ) / 4) ^ 2 = 9 / 16 by norm_num]
  have hsq : Real.pi * (N : ℝ) / 2 ^ k ≤
      (Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k) ^ 2 := by
    rw [hR]
    have h1 : Real.pi * (N : ℝ) / 2 ^ k = Real.pi * (N : ℝ) * ((1 : ℝ) / 2 ^ k) := by
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hkey hpos.le
  calc Real.sqrt (Real.pi * (N : ℝ) / 2 ^ k)
      ≤ Real.sqrt ((Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k :=
        Real.sqrt_sq (by positivity)

/-- The Gaussian square root at `N` is at most twice the square root of `N`. -/
private lemma sqrt_pi_mul_le1622 (N : ℕ) :
    Real.sqrt (Real.pi * (N : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpi4 : Real.pi ≤ (2 : ℝ) ^ 2 := by
    rw [show ((2 : ℝ)) ^ 2 = 4 by norm_num]
    exact Real.pi_lt_four.le
  have hpi2 : Real.sqrt Real.pi ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt hpi4
  rw [Real.sqrt_mul Real.pi_pos.le]
  exact mul_le_mul_of_nonneg_right hpi2 (Real.sqrt_nonneg _)

/-- Each `k`-th term of the prime power majorant, after the prime sum, is at most
`sqrt N` times the `k`-th power of three quarters. -/
private lemma kterm_bound1622 (N k : ℕ) :
    ((k : ℝ) + 2)⁻¹ * (Real.sqrt (Real.pi * (N : ℝ) / 2 ^ k) / 2) ≤
      Real.sqrt (N : ℝ) * (3 / 4 : ℝ) ^ k := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hinv : ((k : ℝ) + 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hd : Real.sqrt (Real.pi * (N : ℝ) / 2 ^ k) / 2 ≤
      (Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k) / 2 :=
    div_le_div_of_nonneg_right (sqrt_halves1622 N k) (by norm_num)
  have h1 : ((k : ℝ) + 2)⁻¹ * (Real.sqrt (Real.pi * (N : ℝ) / 2 ^ k) / 2) ≤
      1 * ((Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k) / 2) :=
    mul_le_mul hinv hd (by positivity) (by norm_num)
  have h2 : 1 * ((Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k) / 2) ≤
      Real.sqrt (N : ℝ) * (3 / 4 : ℝ) ^ k := by
    have h3 : Real.sqrt (Real.pi * (N : ℝ)) / 2 ≤ Real.sqrt (N : ℝ) := by
      have := sqrt_pi_mul_le1622 N
      linarith
    have h4 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k := by positivity
    calc 1 * ((Real.sqrt (Real.pi * (N : ℝ)) * (3 / 4 : ℝ) ^ k) / 2)
        = (Real.sqrt (Real.pi * (N : ℝ)) / 2) * (3 / 4 : ℝ) ^ k := by ring
      _ ≤ Real.sqrt (N : ℝ) * (3 / 4 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h3 h4
  linarith [h1, h2]

/-- The `k`-series of the majorant of the prime power sum is summable: it is
dominated by a geometric series with ratio `exp (-(p^2 / N))`. -/
private lemma summable_majorant_k1622 (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (hp : 2 ≤ p) :
    Summable (fun k : ℕ => ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have H : (0 : ℝ) < (2 : ℝ) := by norm_num
    have H2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hu : (0 : ℝ) < (p : ℝ) ^ 2 / (N : ℝ) := by positivity
  set Q : ℝ := Real.exp (-((p : ℝ) ^ 2 / (N : ℝ))) with hQ
  have hQnn : (0 : ℝ) ≤ Q := (Real.exp_pos _).le
  have hQ1 : Q < 1 := by
    rw [hQ, Real.exp_lt_one_iff]
    linarith
  have hbound : ∀ k : ℕ, ((k : ℝ) + 2)⁻¹ *
      Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) ≤ Q ^ k := by
    intro k
    have hinv : ((k : ℝ) + 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      have H : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hkN : (k : ℝ) ≤ (2 : ℝ) ^ k := by
      have h := Nat.lt_two_pow_self (n := k)
      have h2 : (k : ℝ) ≤ (((2 : ℕ) ^ k : ℕ) : ℝ) := by exact_mod_cast h.le
      simpa using h2
    have h2 : Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) ≤ Q ^ k := by
      rw [hQ, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have heq : (p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ) = (2 : ℝ) ^ k * ((p : ℝ) ^ 2 / (N : ℝ)) := by
        ring
      rw [heq]
      have hmul : (k : ℝ) * ((p : ℝ) ^ 2 / (N : ℝ)) ≤
          (2 : ℝ) ^ k * ((p : ℝ) ^ 2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hkN hu.le
      have hgoal : (k : ℝ) * -((p : ℝ) ^ 2 / (N : ℝ)) =
          -((↑k) * ((p : ℝ) ^ 2 / (N : ℝ))) := by ring
      rw [hgoal]
      linarith [hmul]
    calc ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))
        ≤ 1 * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
      _ ≤ 1 * Q ^ k := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = Q ^ k := one_mul _
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one hQnn hQ1) (fun k => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbound k)

/-- The `k`-series of the majorant is at most `N / p^2`. -/
private lemma tsum_majorant_le1622 (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (hp : 2 ≤ p) :
    (∑' k : ℕ, ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))) ≤
      (N : ℝ) / ((p : ℝ) ^ 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hu : (0 : ℝ) < (p : ℝ) ^ 2 / (N : ℝ) := by positivity
  set Q : ℝ := Real.exp (-((p : ℝ) ^ 2 / (N : ℝ))) with hQ
  have hQnn : (0 : ℝ) ≤ Q := (Real.exp_pos _).le
  have hQpos : (0 : ℝ) < Q := Real.exp_pos _
  have hQ1 : Q < 1 := by
    rw [hQ, Real.exp_lt_one_iff]
    linarith
  have hbound : ∀ k : ℕ, ((k : ℝ) + 2)⁻¹ *
      Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) ≤ Q ^ (k + 1) := by
    intro k
    have hinv : ((k : ℝ) + 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      have H : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hkN : (((k + 1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ k := by
      have h := Nat.lt_two_pow_self (n := k)
      have h2 : (k + 1 : ℝ) ≤ (((2 : ℕ) ^ k : ℕ) : ℝ) := by exact_mod_cast h
      simpa using h2
    have h2 : Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) ≤ Q ^ (k + 1) := by
      rw [hQ, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have heq : (p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ) = (2 : ℝ) ^ k * ((p : ℝ) ^ 2 / (N : ℝ)) := by
        ring
      rw [heq]
      have hmul : (((k + 1 : ℕ)) : ℝ) * ((p : ℝ) ^ 2 / (N : ℝ)) ≤
          (2 : ℝ) ^ k * ((p : ℝ) ^ 2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hkN hu.le
      linarith [hmul]
    calc ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))
        ≤ 1 * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
      _ ≤ 1 * Q ^ (k + 1) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = Q ^ (k + 1) := one_mul _
  have hgeom : (∑' k : ℕ, Q ^ (k + 1)) = Q * (1 - Q)⁻¹ := by
    have hshift : (fun k : ℕ => Q ^ (k + 1)) = fun k : ℕ => Q * Q ^ k := by
      funext k; ring
    rw [hshift, tsum_mul_left, tsum_geometric_of_lt_one hQnn hQ1]
  have hQle : (p : ℝ) ^ 2 / (N : ℝ) * Q ≤ 1 - Q := by
    have h := Real.add_one_le_exp ((p : ℝ) ^ 2 / (N : ℝ))
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-((p : ℝ) ^ 2 / (N : ℝ)))).le
    have hexp : Real.exp (-((p : ℝ) ^ 2 / (N : ℝ))) * Real.exp ((p : ℝ) ^ 2 / (N : ℝ)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    rw [hQ]
    nlinarith [hmul, hexp]
  have hpos : (0 : ℝ) < 1 - Q := by linarith
  have hkey : Q * (1 - Q)⁻¹ ≤ 1 / ((p : ℝ) ^ 2 / (N : ℝ)) := by
    rw [le_div_iff₀ hu]
    have h3 : (p : ℝ) ^ 2 / (N : ℝ) * (Q * (1 - Q)⁻¹) ≤ 1 := by
      have h4 := mul_le_mul_of_nonneg_right hQle (le_of_lt (inv_pos.mpr hpos))
      have h5 : (1 - Q) * (1 - Q)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      calc (p : ℝ) ^ 2 / (N : ℝ) * (Q * (1 - Q)⁻¹)
          = ((p : ℝ) ^ 2 / (N : ℝ) * Q) * (1 - Q)⁻¹ := by ring
        _ ≤ (1 - Q) * (1 - Q)⁻¹ := h4
        _ = 1 := h5
    calc Q * (1 - Q)⁻¹ * ((p : ℝ) ^ 2 / (N : ℝ))
        = (p : ℝ) ^ 2 / (N : ℝ) * (Q * (1 - Q)⁻¹) := by ring
      _ ≤ 1 := h3
  have hgeomSummable : Summable (fun k : ℕ => Q ^ (k + 1)) :=
    (summable_geometric_of_lt_one hQnn hQ1).comp_injective (fun a b hab => by simpa using hab)
  calc (∑' k : ℕ, ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))))
      ≤ ∑' k : ℕ, Q ^ (k + 1) :=
        Summable.tsum_le_tsum hbound (summable_majorant_k1622 N hN p hp) hgeomSummable
    _ = Q * (1 - Q)⁻¹ := hgeom
    _ ≤ 1 / ((p : ℝ) ^ 2 / (N : ℝ)) := hkey
    _ = (N : ℝ) / ((p : ℝ) ^ 2) := by rw [one_div, inv_div]

/-- The `k`-sums of the majorant are summable over the primes, by comparison
with `N / p^2`. -/
private lemma summable_tsum_majorant1622 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : Nat.Primes =>
      ∑' k : ℕ, ((k : ℝ) + 2)⁻¹ * Real.exp (-(((p : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))) := by
  have hsq : Summable (fun p : Nat.Primes => (N : ℝ) / (((p : ℕ)) : ℝ) ^ 2) := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => (N : ℝ) * ((1 : ℝ) / ((n : ℝ) ^ 2))) := h1.mul_left _
    have h3 : Summable (fun p : Nat.Primes => (N : ℝ) * ((1 : ℝ) / ((((p : ℕ)) : ℝ) ^ 2))) :=
      h2.comp_injective Nat.Primes.coe_nat_injective
    exact h3.congr (fun p => by rw [div_eq_mul_one_div]; ring)
  exact Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => tsum_majorant_le1622 N hN (p : ℕ) p.property.two_le) hsq

/-- For each `k` the majorant is summable over the primes, by comparison with an
inverse square. -/
private lemma summable_majorant_p1622 (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      ((k : ℝ) + 2)⁻¹ * Real.exp (-(((p : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsum : Summable (fun p : Nat.Primes => ((N : ℝ) / (2 : ℝ) ^ k) / (((p : ℕ)) : ℝ) ^ 2) := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => ((N : ℝ) / (2 : ℝ) ^ k) * ((1 : ℝ) / ((n : ℝ) ^ 2))) :=
      h1.mul_left _
    have h3 : Summable (fun p : Nat.Primes =>
        ((N : ℝ) / (2 : ℝ) ^ k) * ((1 : ℝ) / ((((p : ℕ)) : ℝ) ^ 2))) :=
      h2.comp_injective Nat.Primes.coe_nat_injective
    exact h3.congr (fun p => by rw [div_eq_mul_one_div]; ring)
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (hsum.mul_left ((k : ℝ) + 2)⁻¹)
  have hp2 : (0 : ℝ) < (((p : ℕ)) : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by exact_mod_cast p.property.two_le
    nlinarith
  have hv : (0 : ℝ) < (((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ) := by positivity
  have hexp : Real.exp (-((((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) ≤
      1 / ((((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)) := by
    have hle : (((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ) ≤
        Real.exp ((((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)) := by
      have h := Real.add_one_le_exp ((((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))
      linarith
    have := (inv_le_inv₀ (Real.exp_pos ((((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) hv).mpr hle
    simpa [Real.exp_neg, one_div] using this
  calc ((k : ℝ) + 2)⁻¹ * Real.exp (-((((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))
      ≤ ((k : ℝ) + 2)⁻¹ * (1 / ((((p : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = ((k : ℝ) + 2)⁻¹ * (((N : ℝ) / (2 : ℝ) ^ k) / (((p : ℕ)) : ℝ) ^ 2) := by
        field_simp

/-- The prime sum of the majorant at a fixed `k` is at most the Gaussian bound. -/
private lemma tsum_majorant_p_le1622 (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    (∑' p : Nat.Primes, ((k : ℝ) + 2)⁻¹ *
        Real.exp (-(((p : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))))
      ≤ ((k : ℝ) + 2)⁻¹ * (Real.sqrt (Real.pi * (N : ℝ) / (2 : ℝ) ^ k) / 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hc : (0 : ℝ) < (2 : ℝ) ^ k / (N : ℝ) := by positivity
  have hgauss := tsum_exp_prime_gauss1622 hc
  have hrewrite : ∀ p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ)))
      = Real.exp (-((2 : ℝ) ^ k / (N : ℝ) * (((p : ℕ)) : ℝ) ^ 2)) := by
    intro p
    congr 2
    ring
  have hsumexp : Summable (fun p : Nat.Primes =>
      Real.exp (-((2 : ℝ) ^ k / (N : ℝ) * (((p : ℕ)) : ℝ) ^ 2))) := by
    have h := (summable_majorant_p1622 N hN k).mul_left ((k : ℝ) + 2)
    refine h.congr (fun p => ?_)
    have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
    rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]
    exact hrewrite p
  have heq : (∑' p : Nat.Primes, ((k : ℝ) + 2)⁻¹ *
        Real.exp (-(((p : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))))
      = (∑' p : Nat.Primes, ((k : ℝ) + 2)⁻¹ *
        Real.exp (-((2 : ℝ) ^ k / (N : ℝ) * (((p : ℕ)) : ℝ) ^ 2))) := by
    apply tsum_congr
    intro p
    rw [hrewrite p]
  rw [heq, tsum_mul_left]
  have hpi : Real.pi / ((2 : ℝ) ^ k / (N : ℝ)) = Real.pi * (N : ℝ) / (2 : ℝ) ^ k := by
    field_simp
  rw [hpi] at hgauss
  exact mul_le_mul_of_nonneg_left hgauss (by positivity)

/-- The prime power tail is at most four times the square root of `N`. The
exponential damping at the prime powers makes every inner series summable, the
prime sums are bounded by the Gaussian integral, and the remaining series in the
exponent is geometric with ratio three quarters. -/
private lemma prime_power_tail_bound1622 (N : ℕ) (hN : 1 ≤ N) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (α : ℝ) :
    ‖∑' p : Nat.Primes, ∑' k : ℕ,
        (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
            Complex.exp
              ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
      ≤ 4 * Real.sqrt (N : ℝ) := by
  classical
  set M : ℕ → ℕ → ℝ := fun p k =>
    ((k : ℝ) + 2)⁻¹ * Real.exp (-((p : ℝ) ^ 2 * (2 : ℝ) ^ k / (N : ℝ))) with hM
  set F : ℕ → ℕ → ℂ := fun p k =>
    (((k : ℂ) + 2)⁻¹ * χ (p ^ (k + 2)) *
      (Real.exp (-((p : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * ((p : ℝ) ^ (k + 2))) : ℝ) * Complex.I)) with hF
  have hnorm : ∀ (p : ℕ) (hp : 2 ≤ p) (k : ℕ), ‖F p k‖ ≤ M p k := by
    intro p hp k
    simp only [hM, hF]
    exact norm_term_le1622 N hN χ α p hp k
  have hMnn : ∀ p k, 0 ≤ M p k := by
    intro p k
    simp only [hM]
    positivity
  -- summability of the inner series
  have hFs : ∀ p : Nat.Primes, Summable (fun k : ℕ => F (p : ℕ) k) := by
    intro p
    exact Summable.of_norm_bounded (summable_majorant_k1622 N hN (p : ℕ) p.property.two_le)
      (fun k => hnorm (p : ℕ) p.property.two_le k)
  -- the inner bound in terms of the majorant
  have hinner : ∀ p : Nat.Primes, ‖∑' k : ℕ, F (p : ℕ) k‖ ≤ ∑' k : ℕ, M (p : ℕ) k := by
    intro p
    refine le_trans (norm_tsum_le_tsum_norm (hFs p).norm) ?_
    exact Summable.tsum_le_tsum (fun k => hnorm (p : ℕ) p.property.two_le k)
      (hFs p).norm (summable_majorant_k1622 N hN (p : ℕ) p.property.two_le)
  -- summability of the outer series
  have hMs : Summable (fun p : Nat.Primes => ∑' k : ℕ, M (p : ℕ) k) :=
    summable_tsum_majorant1622 N hN
  have hFout : Summable (fun p : Nat.Primes => ∑' k : ℕ, F (p : ℕ) k) :=
    Summable.of_norm_bounded hMs hinner
  have hstep1 : ‖∑' p : Nat.Primes, ∑' k : ℕ, F (p : ℕ) k‖ ≤
      ∑' p : Nat.Primes, ∑' k : ℕ, M (p : ℕ) k :=
    le_trans (norm_tsum_le_tsum_norm hFout.norm)
      (Summable.tsum_le_tsum hinner hFout.norm hMs)
  -- swap the two sums
  have hprod : Summable (Function.uncurry (fun (p : Nat.Primes) (k : ℕ) => M (p : ℕ) k)) := by
    rw [show Function.uncurry (fun (p : Nat.Primes) (k : ℕ) => M (p : ℕ) k)
        = fun x : Nat.Primes × ℕ => M (x.1 : ℕ) x.2 from rfl]
    exact (summable_prod_of_nonneg
      (f := fun x : Nat.Primes × ℕ => M (x.1 : ℕ) x.2) (fun x => hMnn _ _)).mpr
      ⟨fun p => summable_majorant_k1622 N hN (p : ℕ) p.property.two_le, hMs⟩
  have hswap : (∑' p : Nat.Primes, ∑' k : ℕ, M (p : ℕ) k)
      = ∑' k : ℕ, ∑' p : Nat.Primes, M (p : ℕ) k :=
    (Summable.tsum_comm hprod).symm
  -- the `k`-series is geometric
  have hkbd : ∀ k : ℕ, (∑' p : Nat.Primes, M (p : ℕ) k) ≤ Real.sqrt (N : ℝ) * (3 / 4 : ℝ) ^ k := by
    intro k
    have h1 : (∑' p : Nat.Primes, M (p : ℕ) k) ≤
        ((k : ℝ) + 2)⁻¹ * (Real.sqrt (Real.pi * (N : ℝ) / (2 : ℝ) ^ k) / 2) := by
      simp only [hM]
      exact tsum_majorant_p_le1622 N hN k
    have h2 := kterm_bound1622 N k
    linarith
  have hksum : Summable (fun k : ℕ => ∑' p : Nat.Primes, M (p : ℕ) k) := by
    refine Summable.of_nonneg_of_le (fun k => by
      exact tsum_nonneg (fun p => hMnn _ _)) hkbd ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hfinal : (∑' k : ℕ, ∑' p : Nat.Primes, M (p : ℕ) k) ≤ 4 * Real.sqrt (N : ℝ) := by
    have hcmp := Summable.tsum_le_tsum hkbd hksum
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        (Real.sqrt (N : ℝ)))
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)] at hcmp
    have h34 : ((1 : ℝ) - 3 / 4)⁻¹ = 4 := by norm_num
    rw [h34] at hcmp
    calc (∑' k : ℕ, ∑' p : Nat.Primes, M (p : ℕ) k)
        ≤ Real.sqrt (N : ℝ) * 4 := hcmp
      _ = 4 * Real.sqrt (N : ℝ) := by ring
  calc ‖∑' p : Nat.Primes, ∑' k : ℕ, F (p : ℕ) k‖
      ≤ ∑' p : Nat.Primes, ∑' k : ℕ, M (p : ℕ) k := hstep1
    _ = ∑' k : ℕ, ∑' p : Nat.Primes, M (p : ℕ) k := hswap
    _ ≤ 4 * Real.sqrt (N : ℝ) := hfinal

/-- LEAF. Prime power tail step. The part of the prime power sum with exponents at
least two, summed over all primes and all such exponents, is at most a constant
times the square root of N. The exponential damping at the powers is what makes
the sum absolutely convergent. No zero hypothesis, no character estimate and no
Mellin integral occur here. -/
theorem prime_power_tail1622 :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
        ‖∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
          ≤ B * Real.sqrt N := by
  refine ⟨8, by norm_num, 4, ?_⟩
  intro N hN q _ hq χ α
  have hN1 : 1 ≤ N := by omega
  have hb := prime_power_tail_bound1622 N hN1 χ α
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  linarith

end LeanLab.Linnik1951
