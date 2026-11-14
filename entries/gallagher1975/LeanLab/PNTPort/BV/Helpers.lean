module

public import Mathlib

/-!
lab proof, AI wrote this file, known mathematics, no cited input
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset Real ArithmeticFunction

/-- `Σ_{n ≤ x, (n, q) > 1} Λ(n)`. -/
noncomputable def psiBad (x : ℝ) (q : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), Λ n

theorem psiBad_nonneg (x : ℝ) (q : ℕ) : 0 ≤ psiBad x q :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

lemma card_primeFactors_mul_log_two_le {q : ℕ} (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have h1 : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h2 : ((2 : ℝ)) ^ q.primeFactors.card ≤ q := by exact_mod_cast h1
  have := Real.log_le_log (by positivity) h2
  rwa [Real.log_pow] at this

theorem psiBad_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    psiBad x q ≤ Real.log q / Real.log 2 * Real.log x := by
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  set D := ∏ p ∈ q.primeFactors, p ^ (Nat.log p N) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  -- step 1: psiBad ≤ log D
  have step1 : psiBad x q ≤ Real.log D := by
    unfold psiBad
    rw [← vonMangoldt_sum, ← Finset.sum_filter_ne_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨hn1, hnN⟩, hcop⟩, hΛ⟩ := hn
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
      have hpq : p ∣ q := by
        by_contra h
        exact hcop (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr h))
      have hpm : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, by omega⟩
      have hkl : k ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hnN
      rw [Nat.mem_divisors]
      exact ⟨(pow_dvd_pow p hkl).trans (Finset.dvd_prod_of_mem _ hpm), hD0⟩
    · intro _ _ _; exact vonMangoldt_nonneg
  -- step 2: log D ≤ #pf * log N
  have step2 : Real.log D ≤ q.primeFactors.card * Real.log N := by
    rw [hD, Nat.cast_prod, Real.log_prod]
    · rw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      apply Real.log_le_log
      · have := hp'.pos; positivity
      · exact_mod_cast Nat.pow_log_le_self p (by omega)
    · intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have := hp'.pos
      positivity
  have hlogN : Real.log N ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le (by linarith))
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    exact card_primeFactors_mul_log_two_le hq
  have hq0 : 0 ≤ Real.log q / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) (Real.log_nonneg (by norm_num))
  calc psiBad x q ≤ q.primeFactors.card * Real.log N := step1.trans step2
    _ ≤ Real.log q / Real.log 2 * Real.log N := by gcongr
    _ ≤ Real.log q / Real.log 2 * Real.log x := by gcongr

theorem log_rpow_le_rpow (a ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
    Real.log x ^ a ≤ K * x ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt a 0 with ha | ha
  · refine ⟨Real.log 2 ^ a, Real.rpow_pos_of_pos hl2 a, fun x hx => ?_⟩
    have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h1 : Real.log x ^ a ≤ Real.log 2 ^ a :=
      Real.rpow_le_rpow_of_nonpos hl2 hlx ha
    have h2 : 1 ≤ x ^ ε := Real.one_le_rpow (by linarith) hε.le
    have h3 : 0 < Real.log 2 ^ a := Real.rpow_pos_of_pos hl2 a
    nlinarith
  · have hεa : 0 < ε / a := div_pos hε ha
    refine ⟨1 / (ε / a) ^ a, by positivity, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h1 : Real.log x ≤ x ^ (ε / a) / (ε / a) := Real.log_le_rpow_div hx0 hεa
    have h2 : Real.log x ^ a ≤ (x ^ (ε / a) / (ε / a)) ^ a :=
      Real.rpow_le_rpow hlog0 h1 ha.le
    rw [Real.div_rpow (by positivity) hεa.le, ← Real.rpow_mul hx0,
      div_mul_cancel₀ ε ha.ne'] at h2
    calc Real.log x ^ a ≤ x ^ ε / (ε / a) ^ a := h2
      _ = 1 / (ε / a) ^ a * x ^ ε := by ring

theorem log_rpow_le_sqrt (a : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
    Real.log x ^ a ≤ K * Real.sqrt x := by
  obtain ⟨K, hK, h⟩ := log_rpow_le_rpow a (1 / 2) (by norm_num)
  refine ⟨K, hK, fun x hx => ?_⟩
  rw [Real.sqrt_eq_rpow]
  exact h x hx

lemma rpow_le_mul_exp (B c : ℝ) (hB : 0 < B) (hc : 0 < c) : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
    t ^ B ≤ K * Real.exp (c * t) := by
  set n := ⌈B⌉₊
  refine ⟨1 + n.factorial / c ^ n, by positivity, fun t ht => ?_⟩
  have hexp1 : 1 ≤ Real.exp (c * t) := Real.one_le_exp (by positivity)
  have hK1 : 1 ≤ 1 + n.factorial / c ^ n := by
    have : 0 ≤ (n.factorial : ℝ) / c ^ n := by positivity
    linarith
  rcases le_or_gt t 1 with ht1 | ht1
  · have : t ^ B ≤ 1 := Real.rpow_le_one ht ht1 hB.le
    nlinarith
  · have h1 : t ^ B ≤ t ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1.le (Nat.le_ceil B)
    rw [Real.rpow_natCast] at h1
    have h2 := Real.pow_div_factorial_le_exp (c * t) (by positivity) n
    have hcn : 0 < c ^ n := by positivity
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have h3 : t ^ n ≤ n.factorial / c ^ n * Real.exp (c * t) := by
      rw [mul_pow, div_le_iff₀ hf] at h2
      rw [div_mul_eq_mul_div, le_div_iff₀ hcn]
      nlinarith
    have : 0 ≤ Real.exp (c * t) := (Real.exp_pos _).le
    nlinarith

theorem exp_neg_sqrt_log_le (c : ℝ) (hc : 0 < c) (A : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ K / Real.log x ^ A := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt A 0 with hA | hA
  · refine ⟨Real.log 2 ^ A, Real.rpow_pos_of_pos hl2 A, fun x hx => ?_⟩
    have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hpos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos (by linarith) A
    have h1 : Real.log x ^ A ≤ Real.log 2 ^ A := Real.rpow_le_rpow_of_nonpos hl2 hlx hA
    have h2 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg (Real.log x)])
    rw [le_div_iff₀ hpos]
    nlinarith [Real.exp_pos (-c * Real.sqrt (Real.log x))]
  · obtain ⟨K, hK, h⟩ := rpow_le_mul_exp (2 * A) c (by linarith) hc
    refine ⟨K, hK, fun x hx => ?_⟩
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    set t := Real.sqrt (Real.log x) with ht
    have ht0 : 0 < t := Real.sqrt_pos.mpr hlx
    have hL : Real.log x ^ A = t ^ (2 * A) := by
      rw [Real.rpow_mul ht0.le, ht, Real.rpow_two, Real.sq_sqrt hlx.le]
    rw [hL, le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)]
    have h1 := h t ht0.le
    have h2 : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-c * t) := Real.exp_pos _
    nlinarith

/-! ### The sum of `1 / φ(m)` -/

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- `g(d) = μ(d)² / φ(d)`. -/
noncomputable def sqfTot : ArithmeticFunction ℝ :=
  ⟨fun n => ((μ n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ), by simp⟩

lemma sqfTot_apply (n : ℕ) : sqfTot n = ((μ n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ) := rfl

lemma sqfTot_nonneg (n : ℕ) : 0 ≤ sqfTot n := by
  rw [sqfTot_apply]; positivity

lemma sqfTot_le (n : ℕ) : sqfTot n ≤ 1 / (n.totient : ℝ) := by
  rw [sqfTot_apply]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := abs_moebius_le_one (n := n)
  have h' : |((μ n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
  have := sq_abs ((μ n : ℤ) : ℝ)
  nlinarith [abs_nonneg ((μ n : ℤ) : ℝ)]

lemma sqfTot_mult : sqfTot.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [sqfTot_apply], fun {m n} _ _ hmn => ?_⟩
  simp only [sqfTot_apply]
  rw [isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  rw [mul_pow, mul_div_mul_comm]

/-- `n / φ(n)`. -/
noncomputable def idTot : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) / (n.totient : ℝ), by simp⟩

lemma idTot_mult : idTot.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [idTot], fun {m n} _ _ hmn => ?_⟩
  simp only [idTot, coe_mk]
  rw [Nat.totient_mul hmn]
  push_cast
  rw [mul_div_mul_comm]

lemma idTot_eq : idTot = sqfTot * (ζ : ArithmeticFunction ℝ) := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ idTot_mult _
    (sqfTot_mult.mul isMultiplicative_zeta.natCast)]
  intro p i hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  rcases i with _ | k
  · simp [idTot, sqfTot_apply]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : ∀ j ∈ Finset.range k, sqfTot (p ^ (j + 1 + 1)) = 0 := by
      intro j _
      rw [sqfTot_apply, moebius_apply_prime_pow hp (by omega)]
      simp
    rw [Finset.sum_eq_zero hz]
    simp only [idTot, coe_mk, sqfTot_apply, zero_add, pow_one, pow_zero,
      moebius_apply_prime hp, Nat.totient_prime hp, Nat.totient_prime_pow hp (by omega : 0 < k + 1)]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp2 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le]; simp
    simp only [Nat.add_sub_cancel, Nat.totient_one, moebius_apply_one]
    push_cast
    rw [hp2]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring

lemma inv_totient_eq {m : ℕ} (hm : m ≠ 0) :
    1 / (m.totient : ℝ) = (1 / (m : ℝ)) * ∑ d ∈ m.divisors, sqfTot d := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f m) idTot_eq
  simp only [idTot, coe_mk, coe_mul_zeta_apply] at h
  rw [← h]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp

/-- Swapping a Dirichlet sum. -/
lemma sum_divisors_le_mul (Q : ℕ) (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    ∑ m ∈ Icc 1 Q, ∑ d ∈ m.divisors, a d * b (m / d) ≤
      (∑ d ∈ Icc 1 Q, a d) * ∑ j ∈ Icc 1 Q, b j := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  set S := (Icc 1 Q ×ˢ Icc 1 Q).filter (fun x : ℕ × ℕ => x.1 * x.2 ≤ Q)
  have hmaps : ∀ x ∈ S, x.1 * x.2 ∈ Icc 1 Q := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx ⊢
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hx.2⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun x => a x.1 * b x.2)
  have key : ∀ m ∈ Icc 1 Q, ∑ d ∈ m.divisors, a d * b (m / d) =
      ∑ x ∈ S with x.1 * x.2 = m, a x.1 * b x.2 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [← Nat.sum_divisorsAntidiagonal (fun i j => a i * b j)]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ⟨d, j⟩
    simp only [Nat.mem_divisorsAntidiagonal, S, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at h1; omega)
      have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at h1; omega)
      have hdm : d ≤ m := h1 ▸ Nat.le_mul_of_pos_right d hj
      have hjm : j ≤ m := h1 ▸ Nat.le_mul_of_pos_left j hd
      refine ⟨⟨⟨⟨hd, by omega⟩, ⟨hj, by omega⟩⟩, by omega⟩, h1⟩
    · rintro ⟨_, h⟩
      exact ⟨h, by omega⟩
  rw [Finset.sum_congr rfl key, hfib]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro x _ _
  exact mul_nonneg (ha _) (hb _)

lemma sum_inv_mul_totient_le (Q : ℕ) :
    ∑ m ∈ Icc 1 Q, sqfTot m / m ≤ 4 := by
  have hsq : ∑ j ∈ Icc 1 Q, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (Q + 1)
    have hI : Ioo 0 (Q + 1) = Icc 1 Q := by
      ext n; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
    rw [hI] at h
    simpa [one_div] using h
  have step : ∀ m ∈ Icc 1 Q, sqfTot m / m ≤
      ∑ d ∈ m.divisors, (sqfTot d / (d : ℝ) ^ 2) * (1 / (((m / d : ℕ) : ℝ)) ^ 2) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have e : ∀ d ∈ m.divisors, (sqfTot d / (d : ℝ) ^ 2) * (1 / (((m / d : ℕ) : ℝ)) ^ 2) =
        sqfTot d / (m : ℝ) ^ 2 := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hd0 : d ≠ 0 := by rintro rfl; exact hm0 (Nat.eq_zero_of_zero_dvd hd.1)
      rw [Nat.cast_div hd.1 (by exact_mod_cast hd0)]
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
      field_simp
    rw [Finset.sum_congr rfl e, ← Finset.sum_div]
    have h1 : sqfTot m / m ≤ (1 / (m.totient : ℝ)) / m :=
      div_le_div_of_nonneg_right (sqfTot_le m) hmR.le
    rw [inv_totient_eq hm0] at h1
    refine h1.trans (le_of_eq ?_)
    field_simp
  calc ∑ m ∈ Icc 1 Q, sqfTot m / m
      ≤ ∑ m ∈ Icc 1 Q, ∑ d ∈ m.divisors,
          (sqfTot d / (d : ℝ) ^ 2) * (1 / (((m / d : ℕ) : ℝ)) ^ 2) := Finset.sum_le_sum step
    _ ≤ (∑ d ∈ Icc 1 Q, sqfTot d / (d : ℝ) ^ 2) * ∑ j ∈ Icc 1 Q, 1 / ((j : ℝ)) ^ 2 :=
        sum_divisors_le_mul Q (fun d => sqfTot d / (d : ℝ) ^ 2) (fun j => 1 / ((j : ℝ)) ^ 2)
          (fun n => by have := sqfTot_nonneg n; positivity) (fun n => by positivity)
    _ ≤ 2 * 2 := by
        apply mul_le_mul _ hsq (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
        refine le_trans (Finset.sum_le_sum fun d hd => ?_) hsq
        rw [Finset.mem_Icc] at hd
        have h1 := sqfTot_le d
        have ht : (1 : ℝ) ≤ d.totient := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by simp; omega)
        have h2 : sqfTot d ≤ 1 := h1.trans (by rw [div_le_one (by linarith)]; exact ht)
        apply div_le_div_of_nonneg_right h2 (by positivity)
    _ = 4 := by norm_num

theorem sum_inv_totient_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
    ∑ m ∈ Icc 1 Q, (1 : ℝ) / m.totient ≤ C * (1 + Real.log Q) := by
  refine ⟨4, by norm_num, fun Q => ?_⟩
  have hH : ∑ j ∈ Icc 1 Q, (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log Q := by
    have h := harmonic_le_one_add_log Q
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  have step : ∀ m ∈ Icc 1 Q, (1 : ℝ) / m.totient =
      ∑ d ∈ m.divisors, (sqfTot d / (d : ℝ)) * (1 / (((m / d : ℕ) : ℝ))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    have e : ∀ d ∈ m.divisors, (sqfTot d / (d : ℝ)) * (1 / (((m / d : ℕ) : ℝ))) =
        sqfTot d / (m : ℝ) := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hd0 : d ≠ 0 := by rintro rfl; exact hm0 (Nat.eq_zero_of_zero_dvd hd.1)
      rw [Nat.cast_div hd.1 (by exact_mod_cast hd0)]
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
      field_simp
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, inv_totient_eq hm0]
    ring
  rw [Finset.sum_congr rfl step]
  calc _ ≤ (∑ d ∈ Icc 1 Q, sqfTot d / (d : ℝ)) * ∑ j ∈ Icc 1 Q, 1 / (j : ℝ) :=
        sum_divisors_le_mul Q (fun d => sqfTot d / (d : ℝ)) (fun j => 1 / (j : ℝ))
          (fun n => by have := sqfTot_nonneg n; positivity) (fun n => by positivity)
    _ ≤ 4 * (1 + Real.log Q) := by
        apply mul_le_mul (sum_inv_mul_totient_le Q) hH
          (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)

end LeanLab.PNTPort.BV
