module

public import LeanLab.Tolev2009.Decomp310a
public import LeanLab.Tolev2009.Decomp336a

/-!
AI wrote this Lean code. Lean Lab prover, mistralhigh/labs-leanstral-1-5-1, task151.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 72 and 83 to 86.
The Type II proof separates the coefficient moment from the row energy.
The coefficient moment is proved. The row energy input is proved.
The assembly is derived from row_energy only.
-/

@[expose] public section

open Finset Real ComplexConjugate

namespace LeanLab.Tolev2009.Decomp310b

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a

/-- The squared inner row sum before the correlation expansion on page 83. -/
noncomputable def energy (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) : ℝ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖row lam l₃ K N α x H H₁ b m‖ ^ 2

/-- The exact finite Cauchy step on page 83 preceding display 55. -/
theorem bilinear_sq_le_energy (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) :
    ‖bilinear lam l₃ K N α x M M₁ H H₁ a b‖ ^ 2 ≤
      (∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ ^ 2) * energy lam l₃ K N α x M M₁ H H₁ b := by
  rw [bilinear_eq_rows]
  have ht : ‖∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * row lam l₃ K N α x H H₁ b m‖ ≤
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ * ‖row lam l₃ K N α x H H₁ b m‖ := by
    simpa only [norm_mul] using
      (norm_sum_le (Ioc ⌊M⌋₊ ⌊M₁⌋₊) (fun m => a m * row lam l₃ K N α x H H₁ b m))
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (sum_mul_sq_le_sq_mul_sq _ _ _)

/-- The finite correlation expansion on Tolev 1999 page 83 before display 55.
The phase depends on the difference of the two second variables.
This identity uses no coefficient estimate or minor arc input. -/
theorem energy_eq_correlations (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) :
    (energy lam l₃ K N α x M M₁ H H₁ b : ℂ) =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ∑ l₁ ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, ∑ l₂ ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
        if (x < (m * l₁ : ℕ) ∧ (m * l₁ : ℕ) ≤ 2 * x ∧ m * l₁ ≤ N) ∧
            (x < (m * l₂ : ℕ) ∧ (m * l₂ : ℕ) ≤ 2 * x ∧ m * l₂ ≤ N) then
          b l₁ * conj (b l₂) *
            ((L2Bound.weight lam l₃ K (m * l₁) * L2Bound.weight lam l₃ K (m * l₂) : ℝ) : ℂ) *
            ee (α * m * ((l₁ : ℝ) - l₂))
        else 0 := by
  simp only [energy, Complex.ofReal_sum]
  apply sum_congr rfl
  intro m hm
  rw [sq_norm_eq_mul_conj]
  simp only [row, map_sum]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro l₁ hl₁
  apply sum_congr rfl
  intro l₂ hl₂
  by_cases h₁ : x < (m * l₁ : ℕ) ∧ (m * l₁ : ℕ) ≤ 2 * x ∧ m * l₁ ≤ N
  · by_cases h₂ : x < (m * l₂ : ℕ) ∧ (m * l₂ : ℕ) ≤ 2 * x ∧ m * l₂ ≤ N
    · simp only [h₁, h₂, and_self, ite_true, map_mul, Complex.conj_ofReal, conj_ee,
        Complex.ofReal_mul]
      have he : ee (α * (m * l₁ : ℕ)) * ee (-(α * (m * l₂ : ℕ))) =
          ee (α * m * ((l₁ : ℝ) - l₂)) := by
        rw [← ee_add]
        congr 1
        push_cast
        ring
      calc
        _ = b l₁ * conj (b l₂) *
            ((L2Bound.weight lam l₃ K (m * l₁) : ℂ) * L2Bound.weight lam l₃ K (m * l₂)) *
            (ee (α * (m * l₁ : ℕ)) * ee (-(α * (m * l₂ : ℕ)))) := by ring
        _ = _ := by rw [he]
    · simp only [h₁, h₂, true_and, and_false, ite_true, ite_false, map_zero, mul_zero]
  · simp only [h₁, false_and, ite_false, zero_mul]

/-- The exclusion part of Tolev 1999 page 85 display 62.
A reduced approximation inside a major arc radius has denominator above Q on the minor arcs.
This does not assert existence of a rational approximation. -/
theorem denominator_gt_Q (Q τ α : ℝ) (q a : ℕ)
    (hminor : α ∉ majorArcs Q τ) (hq : 1 ≤ q) (ha : a < q)
    (hcop : Nat.Coprime a q) (herr : |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * τ)) :
    Q < q := by
  by_contra hn
  have hqQ : (q : ℝ) ≤ Q := le_of_not_gt hn
  have hmem : q ∈ Icc 1 ⌊Q⌋₊ := mem_Icc.mpr ⟨hq, (Nat.le_floor hqQ)⟩
  apply hminor
  simp only [majorArcs, Set.mem_iUnion]
  refine ⟨q, hmem, a, ?_, ?_⟩
  · exact mem_filter.mpr ⟨mem_range.mpr ha, hcop⟩
  · rcases abs_le.mp herr with ⟨hl, hr⟩
    constructor <;> linarith

/-- The shell adaptation of Tolev 1999 page 85 displays 61 and 62.
This is the algebraic saving once the denominator bounds have been supplied.
It does not assert existence of a rational approximation. -/
theorem denominator_ratios (A : ℝ) (N : ℕ) (x q : ℝ)
    (hN : 0 < N) (hL : 0 < Real.log N)
    (hqQ : Qof A N ≤ q) (hqt : q ≤ τof A N)
    (hx : (N : ℝ) * Real.log N ^ (-4 * A) ≤ x) :
    1 / q ≤ Real.log N ^ (-(20 * A)) ∧ q / x ≤ Real.log N ^ (-(16 * A)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ : 0 < Qof A N := Real.rpow_pos_of_pos hL _
  have hx0 : 0 < x := (mul_pos hNr (Real.rpow_pos_of_pos hL _)).trans_le hx
  constructor
  · have hb := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hQ hqQ
    simpa only [Qof, one_div, Real.rpow_neg hL.le] using hb
  · apply (div_le_iff₀ hx0).mpr
    have ht : τof A N = ((N : ℝ) * Real.log N ^ (-4 * A)) * Real.log N ^ (-(16 * A)) := by
      calc
        _ = (N : ℝ) * Real.log N ^ (-(20 * A)) := by
          rw [τof, Qof, Real.rpow_neg hL.le, div_eq_mul_inv]
        _ = _ := by
          rw [mul_assoc, ← Real.rpow_add hL]
          congr 1
          ring
    calc
      q ≤ τof A N := hqt
      _ = _ := ht
      _ ≤ x * Real.log N ^ (-(16 * A)) :=
        mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hL.le _)
      _ = _ := by ring

open LeanLab.HeathBrown1985

/-- The elementary reciprocal mean of the ordered divisor function.
Tolev 1999 page 72 Lemma 8, the convolution count used for part i. -/
theorem zeta_power_reciprocal (k N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) / n ≤ Hn N ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_div, zero_div, sum_ite_eq', pow_zero]
    split_ifs <;> norm_num
  | succ k ih =>
    have hpoint : ∀ n ∈ Icc 1 N,
        (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) / n =
          ∑ d ∈ Icc 1 N, if d ∣ n then (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) / n else 0 := by
      intro n hn
      rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.cast_sum, sum_div,
        divisors_eq_filter N n hn, sum_filter]
    have he : (∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) / n) =
        ∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) *
          ∑ n ∈ (Icc 1 N).filter (d ∣ ·), (n : ℝ)⁻¹ := by
      rw [sum_congr rfl hpoint, sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    rw [he]
    calc
      _ ≤ ∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) * (Hn N / d) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (sum_inv_multiples_le N d (mem_Icc.mp hd).1)
          (Nat.cast_nonneg _)
      _ = (∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) / d) * Hn N := by
        rw [sum_mul]
        apply sum_congr rfl
        intro d hd
        ring
      _ ≤ Hn N ^ k * Hn N := mul_le_mul_of_nonneg_right ih (Hn_nonneg N)
      _ = _ := (pow_succ _ _).symm

/-- The ordinary mean of a convolution power of zeta follows from reciprocal counting.
Tolev 1999 page 72 Lemma 8, the ordered divisor average behind part i. -/
theorem zeta_power_sum (k N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) ≤
      (N : ℝ) * Hn N ^ k := by
  have hi : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  have he : (∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ)) =
      ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) * ((N / n : ℕ) : ℝ) := by
    have hh := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (ArithmeticFunction.zeta ^ k) N
    simp only [ArithmeticFunction.natCoe_nat, ← pow_succ, ← hi, Nat.cast_id] at hh
    exact_mod_cast hh
  rw [he]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) * ((N : ℝ) / n) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg _)
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) / n := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (zeta_power_reciprocal k N) (Nat.cast_nonneg N)

/-- A joint multiset has arbitrary prescribed marginals of the same cardinality.
This counting inequality is the local factor comparison for Tolev 1999 page 72 Lemma 8 part i. -/
theorem multichoose_mul_le (k l e : ℕ) :
    Nat.multichoose k e * Nat.multichoose l e ≤ Nat.multichoose (k * l) e := by
  classical
  have hs : ∀ e, Function.Surjective (fun s : Sym (Fin k × Fin l) e =>
      (s.map Prod.fst, s.map Prod.snd)) := by
    intro e
    induction e with
    | zero =>
      intro st
      exact ⟨Sym.nil, Subsingleton.elim _ _⟩
    | succ e ih =>
      rintro ⟨s, t⟩
      obtain ⟨a, s, rfl⟩ := Sym.exists_eq_cons_of_succ s
      obtain ⟨b, t, rfl⟩ := Sym.exists_eq_cons_of_succ t
      obtain ⟨u, hu⟩ := ih (s, t)
      have hu1 : Sym.map Prod.fst u = s := congrArg Prod.fst hu
      have hu2 : Sym.map Prod.snd u = t := congrArg Prod.snd hu
      refine ⟨Sym.cons (a, b) u, ?_⟩
      apply Prod.ext
      · simp only [Sym.map_cons]
        rw [hu1]
      · simp only [Sym.map_cons]
        rw [hu2]
  have hc := Fintype.card_le_of_surjective _ (hs e)
  simpa only [Fintype.card_prod, Sym.card_sym_eq_multichoose, Fintype.card_fin] using hc

/-- The local ordered divisor count is a multiset count.
This identifies the convolution power used in Tolev 1999 page 72 Lemma 8. -/
theorem zeta_power_prime_pow (k p e : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.zeta ^ (k + 1)) (p ^ e) = Nat.multichoose (k + 1) e := by
  induction k generalizing e with
  | zero =>
    simp [ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ hp.ne_zero), Nat.multichoose_one]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
    rw [show k + 1 + 1 + e - 1 = e + (k + 1) by omega]
    exact Nat.choose_symm_add.symm

/-- Tau5 squared is bounded pointwise by the 25th convolution power of zeta.
This is the elementary majorant for the squared moment in Tolev 1999 page 72 Lemma 8 part i. -/
theorem tau5_sq_le_zeta25 (n : ℕ) : tau5 n ^ 2 ≤ (ArithmeticFunction.zeta ^ 25) n := by
  have hm5 : (ArithmeticFunction.zeta ^ 5).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  have hm25 : (ArithmeticFunction.zeta ^ 25).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp [tau5]
  · intro p e hp
    change (ArithmeticFunction.zeta ^ (4 + 1)) (p ^ e) ^ 2 ≤
      (ArithmeticFunction.zeta ^ (24 + 1)) (p ^ e)
    rw [zeta_power_prime_pow 4 p e hp, zeta_power_prime_pow 24 p e hp]
    simpa only [pow_two] using multichoose_mul_le 5 5 e
  · intro a b ha hb hab hIa hIb
    change ((ArithmeticFunction.zeta ^ 5) (a * b)) ^ 2 ≤ (ArithmeticFunction.zeta ^ 25) (a * b)
    rw [hm5.map_mul_of_coprime hab, hm25.map_mul_of_coprime hab, mul_pow]
    exact Nat.mul_le_mul hIa hIb

/-- Tolev 1999 page 72 Lemma 8 part i with k equal to five,
and page 83 before display 55. This is a coefficient moment without a phase,
a modulus, a residue, a minor arc or a second coefficient.
The absolute constant two times five to the 24th is supplied. -/
theorem coefficient_mass :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 3 ≤ N →
      ∀ M M₁ : ℝ, 0 < M → M ≤ M₁ → M₁ ≤ 2 * M → M ≤ 2 * N →
      ∀ a : ℕ → ℂ, (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
        (∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ ^ 2) ≤
          D * M * Real.log N ^ (26 : ℕ) := by
  refine ⟨2 * 5 ^ (24 : ℕ), by positivity, ?_⟩
  intro N hN M M₁ hM hMM₁ hM₁ hMN a ha
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 ≤ Real.log N := by linarith
  let R : ℕ := ⌊2 * M⌋₊
  have hR : (R : ℝ) ≤ 2 * M := Nat.floor_le (by positivity)
  have hRN : (R : ℝ) ≤ 4 * N := by nlinarith
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogR : Real.log R ≤ Real.log (4 : ℝ) + Real.log N := by
    rcases Nat.eq_zero_or_pos R with hz | hp
    · simp only [hz, Nat.cast_zero, Real.log_zero]
      have h4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
      positivity
    · rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (N : ℝ) ≠ 0)]
      exact Real.log_le_log (by exact_mod_cast hp) hRN
  have hH : Hn R ≤ 5 * Real.log N := (Hn_le R).trans (by linarith)
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Icc 1 R := by
    intro m hm
    rcases mem_Ioc.mp hm with ⟨hm0, hm1⟩
    exact mem_Icc.mpr ⟨by omega, hm1.trans (Nat.floor_le_floor hM₁)⟩
  have ht : ∀ m, ‖a m‖ ^ 2 ≤ (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) := by
    intro m
    have hτ : (tau5 m : ℝ) ^ 2 ≤ (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) := by
      exact_mod_cast tau5_sq_le_zeta25 m
    calc
      _ ≤ ((tau5 m : ℝ) * Real.log N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (ha m) 2
      _ = (tau5 m : ℝ) ^ 2 * Real.log N ^ (2 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hτ (sq_nonneg _)
  calc
    _ ≤ ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) :=
      sum_le_sum (fun m hm => ht m)
    _ ≤ ∑ m ∈ Icc 1 R,
        (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => by positivity)
    _ = (∑ m ∈ Icc 1 R, (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ)) *
        Real.log N ^ (2 : ℕ) := by rw [sum_mul]
    _ ≤ ((R : ℝ) * Hn R ^ (24 : ℕ)) * Real.log N ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (zeta_power_sum 24 R) (sq_nonneg _)
    _ ≤ ((2 * M) * (5 * Real.log N) ^ (24 : ℕ)) * Real.log N ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hR (pow_le_pow_left₀ (Hn_nonneg R) hH 24) (by positivity) (by positivity)
    _ = _ := by ring


/-- Tolev 1999 page 84 display 57, the elementary lcm fiber majorant. -/
theorem lcm_fiber_divisor_bound (h K : ℕ) :
    ∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h),
      (p.1.divisors.card : ℝ) * p.2.divisors.card ≤ (h.divisors.card : ℝ) ^ 4 := by
  by_cases hh : h = 0
  · subst h
    have he : (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = 0) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      rcases mem_filter.mp hp with ⟨hp, he⟩
      rcases mem_product.mp hp with ⟨hp1, hp2⟩
      have h1 := (mem_Icc.mp hp1).1
      have h2 := (mem_Icc.mp hp2).1
      exact (Nat.lcm_ne_zero (by omega) (by omega)) he
    rw [he]
    norm_num
  · have hs : (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h) ⊆
        h.divisors ×ˢ h.divisors := by
      intro p hp
      have he := (mem_filter.mp hp).2
      apply mem_product.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_left p.1 p.2, hh⟩
      · exact Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_right p.1 p.2, hh⟩
    calc
      _ ≤ ∑ p ∈ h.divisors ×ˢ h.divisors, (p.1.divisors.card : ℝ) * p.2.divisors.card :=
        sum_le_sum_of_subset_of_nonneg hs (fun p hp hn => by positivity)
      _ ≤ ∑ p ∈ h.divisors ×ˢ h.divisors, (h.divisors.card : ℝ) ^ 2 := by
        apply sum_le_sum
        intro p hp
        have hp1 := (mem_product.mp hp).1
        have hp2 := (mem_product.mp hp).2
        have hd1 : (p.1.divisors.card : ℝ) ≤ h.divisors.card := by
          exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hh (Nat.dvd_of_mem_divisors hp1))
        have hd2 : (p.2.divisors.card : ℝ) ≤ h.divisors.card := by
          exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hh (Nat.dvd_of_mem_divisors hp2))
        simpa only [pow_two] using mul_le_mul hd1 hd2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul]
        ring

/-- Tolev 1999 page 84 display 58, in a stronger harmonic form.
This proves the lcm sum that occurs in the Type II diagonal term. -/
theorem lcm_divisor_sum (K : ℕ) :
    ∑ p ∈ Icc 1 K ×ˢ Icc 1 K,
      ((p.1.divisors.card : ℝ) * p.2.divisors.card) / Nat.lcm p.1 p.2 ≤
        LeanLab.HeathBrown1985.Hn (K * K) ^ (16 : ℕ) := by
  have hm : ∀ p ∈ Icc 1 K ×ˢ Icc 1 K, Nat.lcm p.1 p.2 ∈ Icc 1 (K * K) := by
    intro p hp
    rcases mem_product.mp hp with ⟨hp1, hp2⟩
    rcases mem_Icc.mp hp1 with ⟨h1, h1K⟩
    rcases mem_Icc.mp hp2 with ⟨h2, h2K⟩
    apply mem_Icc.mpr
    constructor
    · exact Nat.lcm_pos (by omega) (by omega)
    · exact (Nat.lcm_le_mul h1 h2).trans (Nat.mul_le_mul h1K h2K)
  have hf := sum_fiberwise_of_maps_to hm
    (fun p : ℕ × ℕ => ((p.1.divisors.card : ℝ) * p.2.divisors.card) / Nat.lcm p.1 p.2)
  rw [← hf]
  calc
    _ = ∑ h ∈ Icc 1 (K * K),
        (∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h),
          (p.1.divisors.card : ℝ) * p.2.divisors.card) / h := by
      apply sum_congr rfl
      intro h hh
      rw [sum_div]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ ∑ h ∈ Icc 1 (K * K), (h.divisors.card : ℝ) ^ (4 : ℕ) / h := by
      apply sum_le_sum
      intro h hh
      exact div_le_div_of_nonneg_right (lcm_fiber_divisor_bound h K) (Nat.cast_nonneg h)
    _ ≤ _ := by simpa only [show (2 : ℕ) ^ 4 = 16 by norm_num] using divisor_power_reciprocal 4 (K * K)

/-- Helper: energy is nonnegative. -/
theorem energy_nonneg (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) (b : ℕ → ℂ) :
    0 ≤ energy lam l₃ K N α x M M₁ H H₁ b := by
  unfold energy
  positivity

section Port

set_option exponentiation.threshold 2048
set_option quotPrecheck false

open LeanLab.Tolev2009.Decomp336a
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve

/-! ## The lane definitions, written out at every use site -/

local notation "IND[" l₃:max "," K:max "," H:max "," H₁:max "]" =>
  (Ioc ⌊H⌋₊ ⌊H₁⌋₊ ×ˢ (Icc 1 K).filter (fun k => Nat.Coprime k l₃))

local notation "ATM[" l₃:max "," N:max "," α:max "," x:max "," m:max "," i:max "]" =>
  (if (x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
      (m * i.1) % i.2 = l₃ % i.2 then ee (α * (m * i.1 : ℕ)) else 0)

local notation "CORR[" l₃:max "," N:max "," α:max "," x:max "," M:max "," M₁:max "," i:max "," j:max "]" =>
  (∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
    ATM[ l₃, N, α, x, m, i ] * conj (ATM[ l₃, N, α, x, m, j ]))

local notation "DIAG[" l₃:max "," K:max "," N:max "," α:max "," x:max "," M:max "," M₁:max "," H:max "," H₁:max "]" =>
  (∑ i ∈ IND[ l₃, K, H, H₁ ], ∑ j ∈ IND[ l₃, K, H, H₁ ],
    if i.1 = j.1 then
      (tau5 i.1 : ℝ) * tau5 j.1 * ‖CORR[ l₃, N, α, x, M, M₁, i, j ]‖ else 0)

local notation "ODIAG[" l₃:max "," K:max "," N:max "," α:max "," x:max "," M:max "," M₁:max "," H:max "," H₁:max "]" =>
  (∑ i ∈ IND[ l₃, K, H, H₁ ], ∑ j ∈ IND[ l₃, K, H, H₁ ],
    if i.1 ≠ j.1 then
      (tau5 i.1 : ℝ) * tau5 j.1 * ‖CORR[ l₃, N, α, x, M, M₁, i, j ]‖ else 0)

local notation "DPH[" α:max "," X:max "," T:max "]" =>
  (∑ n ∈ Icc 1 T, (n.divisors.card : ℝ) ^ 5 * phaseCap α X n)

/-! ## Scalar phase estimates re-derived from `Decomp336b` -/

/-- The geometric cap retains its endpoint count, Tolev page 86 display 65. -/
private theorem phaseCap_le_count (α x : ℝ) (n : ℕ) : phaseCap α x n ≤ 2 * x / n + 1 := by
  unfold phaseCap
  split_ifs
  · rfl
  · exact min_le_left _ _

/-- The weighted finite Cauchy step in display 65, retaining the count one. -/
private theorem weighted_phase_cauchy (a : ℕ → ℝ) (T : ℕ) (α x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Icc 1 T, a n * phaseCap α x n) ^ 2 ≤
      (∑ n ∈ Icc 1 T, (a n) ^ 2 / n) *
        ((2 * x + T) * ∑ n ∈ Icc 1 T, phaseCap α x n) := by
  let f : ℕ → ℝ := fun n => (a n) ^ 2 / n
  let g : ℕ → ℝ := fun n => (n : ℝ) * phaseCap α x n ^ 2
  have hc : (∑ n ∈ Icc 1 T, a n * phaseCap α x n) ^ 2 ≤
      (∑ n ∈ Icc 1 T, f n) * (∑ n ∈ Icc 1 T, g n) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro n hn
      dsimp [f]
      positivity
    · intro n hn
      dsimp [g]
      positivity
    · intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)
      dsimp [f, g]
      apply le_of_eq
      field_simp
  have hg : (∑ n ∈ Icc 1 T, g n) ≤ (2 * x + T) * ∑ n ∈ Icc 1 T, phaseCap α x n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.mp hn).1; omega)
    have hnT : (n : ℝ) ≤ T := by exact_mod_cast (mem_Icc.mp hn).2
    have hp := phaseCap_nonneg α x n hx
    have hcap : phaseCap α x n - 1 ≤ 2 * x / n := by linarith [phaseCap_le_count α x n]
    have hcap' := (le_div_iff₀ hn0).mp hcap
    have hh : (n : ℝ) * phaseCap α x n ≤ 2 * x + T := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hh hp
    dsimp [g]
    nlinarith
  exact hc.trans (mul_le_mul_of_nonneg_left hg (sum_nonneg (fun n hn => by dsimp [f]; positivity)))

/-- The exact complex cap is at most the standard nearest integer cap plus one. -/
private theorem phaseCap_le_G_add_one (α x : ℝ) (n : ℕ) :
    phaseCap α x n ≤ LeanLab.PNTPort.Vinogradov.G (2 * x / n) (α * n) + 1 := by
  by_cases hd : dist0 (α * n) = 0
  · rw [LeanLab.PNTPort.Vinogradov.G, if_pos hd]
    exact phaseCap_le_count α x n
  · have hdpos : 0 < dist0 (α * n) := lt_of_le_of_ne (dist0_nonneg _) (Ne.symm hd)
    have hdist : 4 * dist0 (α * n) ≤ ‖ee (α * n) - 1‖ := distance_comparison _
    have hden : 0 < ‖ee (α * n) - 1‖ := by linarith
    have he : ee (α * n) ≠ 1 := by
      intro hh
      simp [hh] at hden
    have hdiv : 2 / ‖ee (α * n) - 1‖ ≤ 1 / (2 * dist0 (α * n)) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
    rw [phaseCap, if_neg he, LeanLab.PNTPort.Vinogradov.G, if_neg hd, ← min_add_add_right]
    apply le_min
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hdiv.trans (by linarith))

/-- The rational approximation reciprocal sum in Tolev page 72 Lemma 7 part ii. -/
private theorem phaseCap_sum_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ))
    {α x : ℝ} (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (hx : 0 ≤ x) (T : ℕ) :
    ∑ n ∈ Icc 1 T, phaseCap α x n ≤
      12 * (2 * x / q + T + q) * (1 + Real.log q + Real.log T) + T := by
  calc
    _ ≤ ∑ n ∈ Icc 1 T, (LeanLab.PNTPort.Vinogradov.G (2 * x / n) (α * n) + 1) :=
      sum_le_sum (fun n hn => phaseCap_le_G_add_one α x n)
    _ = (∑ n ∈ Icc 1 T, LeanLab.PNTPort.Vinogradov.G (2 * x / n) (α * n)) + T := by
      rw [sum_add_distrib]
      simp
    _ ≤ _ := add_le_add (sum_G_div_le hq hcop hα T (by positivity : 0 ≤ 2 * x)) le_rfl

/-- Minor arcs exclude small reduced denominators, including the shifted interval endpoints. -/
private theorem integer_denominator_gt_Q (Q τ α : ℝ) (q : ℕ) (a : ℤ)
    (hQ : 0 ≤ Q) (hτ : Q + 1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1 / τ) (1 - 1 / τ)) (hminor : α ∉ majorArcs Q τ)
    (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (herr : |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * τ)) : Q < q := by
  by_contra hn
  have hqQ : (q : ℝ) ≤ Q := le_of_not_gt hn
  have ht : 0 < τ := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : |(q : ℝ) * α - a| ≤ 1 / τ := by
    have hh := mul_le_mul_of_nonneg_left herr hqr.le
    rw [show (q : ℝ) * |α - (a : ℝ) / q| = |(q : ℝ) * α - a| by
      rw [← abs_of_pos hqr, ← abs_mul, abs_of_pos hqr]
      congr 1
      field_simp] at hh
    convert hh using 1
    field_simp
  have hlo := (abs_le.mp he).1
  have hhi := (abs_le.mp he).2
  have hlα := mul_lt_mul_of_pos_left hα.1 hqr
  have huα := mul_lt_mul_of_pos_left hα.2 hqr
  have hqτ : (q : ℝ) + 1 ≤ τ := by linarith
  have hl : (-1 : ℝ) < a := by
    have hh : (q : ℝ) / τ + 1 / τ ≤ 1 := by
      rw [← add_div, div_le_one ht]
      exact hqτ
    have hm : (q : ℝ) * (-1 / τ) = -(q : ℝ) / τ := by ring
    rw [hm, neg_div] at hlα
    linarith
  have hu : (a : ℝ) < q := by
    have hh : 1 / τ ≤ (q : ℝ) / τ := div_le_div_of_nonneg_right (by exact_mod_cast hq) ht.le
    have hm : (q : ℝ) * (1 - 1 / τ) = q - (q : ℝ) / τ := by ring
    rw [hm] at huα
    linarith
  have ha0 : 0 ≤ a := by exact_mod_cast (show (-1 : ℤ) < a by exact_mod_cast hl)
  have haq : a < (q : ℤ) := by exact_mod_cast hu
  have hac : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
  have hc : Nat.Coprime a.toNat q := by
    apply IsCoprime.natCoprime
    simpa only [hac] using hcop
  have haqr : a.toNat < q := by omega
  have her : |α - (a.toNat : ℝ) / q| ≤ 1 / ((q : ℝ) * τ) := by
    simpa only [show (a.toNat : ℝ) = (a : ℝ) by exact_mod_cast hac] using herr
  exact (not_lt_of_ge hqQ) (denominator_gt_Q Q τ α q a.toNat hminor hq haqr hc her)

/-- Dirichlet approximation with both required error bounds and an integer numerator. -/
private theorem minor_arc_reduced_approximation (Q τ α : ℝ)
    (hQ : 0 ≤ Q) (hτ : Q + 1 ≤ τ) (ht : 1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1 / τ) (1 - 1 / τ)) (hminor : α ∉ majorArcs Q τ) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ Q < (q : ℝ) ∧ (q : ℝ) ≤ τ ∧
      IsCoprime a (q : ℤ) ∧
      |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * τ) ∧
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hfloor : 0 < ⌊τ⌋₊ := by
    have hh : 1 ≤ ⌊τ⌋₊ := (Nat.le_floor (by simpa using ht))
    omega
  obtain ⟨r, herr, hr⟩ := Real.exists_rat_abs_sub_le_and_den_le α hfloor
  have hq : 1 ≤ r.den := Rat.pos r
  have hqt : (r.den : ℝ) ≤ τ :=
    (show (r.den : ℝ) ≤ ⌊τ⌋₊ by exact_mod_cast hr).trans (Nat.floor_le (by linarith))
  have htf : τ ≤ (⌊τ⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one τ).le
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast Rat.pos r
  have he : |α - (r.num : ℝ) / r.den| ≤ 1 / ((r.den : ℝ) * τ) := by
    rw [← Rat.cast_def]
    apply herr.trans
    apply one_div_le_one_div_of_le (mul_pos hqr (by linarith))
    nlinarith
  have he2 : |α - (r.num : ℝ) / r.den| ≤ 1 / (r.den : ℝ) ^ 2 := by
    apply he.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hqr)
    nlinarith
  exact ⟨r.num, r.den, hq,
    integer_denominator_gt_Q Q τ α r.den r.num hQ hτ hα hminor hq r.isCoprime_num_den he,
    hqt, r.isCoprime_num_den, he, he2⟩

/-- The major arc parameters obey the separation condition for all sufficiently large N. -/
private theorem eventual_minor_arc_parameters (A : ℝ) (hA : 0 ≤ A) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧ Qof A N + 1 ≤ τof A N := by
  have he := (isLittleO_log_rpow_rpow_atTop (40 * A) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.mp he
  refine ⟨max X₀ (Real.exp 2), ?_⟩
  intro N hN
  have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := (Real.exp_pos 2).trans_le hNe
  have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hL0 : 0 < Real.log N := by linarith
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have hbound := hX (N : ℝ) ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _), abs_of_pos hN0] at hbound
  have hQsq : Qof A N ^ 2 = Real.log N ^ (40 * A) := by
    rw [Qof, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
    congr 1
    ring
  refine ⟨hL, ?_⟩
  unfold τof
  apply (le_div_iff₀ hQ0).mpr
  rw [← hQsq] at hbound
  nlinarith

/-- The rational approximation mass estimate with the exact third cutoff savings. -/
private theorem phase_mass_from_approx (A : ℝ) (N T q : ℕ) (a : ℤ) (α x : ℝ)
    (hA : 0 ≤ A) (hN : 0 < (N : ℝ)) (hL : 2 ≤ Real.log N)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hTN : T ≤ N)
    (hTS : (T : ℝ) ≤ 4 * N * Real.log N ^ (-20 * A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q : ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q : ℤ)) (herr : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ∑ n ∈ Icc 1 T, phaseCap α x n ≤ 256 * N * Real.log N ^ (1 - 20 * A) := by
  let s : ℝ := N * Real.log N ^ (-20 * A)
  have hL0 : 0 < Real.log N := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have ht : τof A N = s := by
    dsimp [τof, Qof, s]
    rw [show -20 * A = -(20 * A) by ring, Real.rpow_neg hL0.le, div_eq_mul_inv]
  have hqS : (q : ℝ) ≤ s := by rwa [ht] at hqτ
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqN : (q : ℝ) ≤ N := hqτ.trans (div_le_self hN.le hQ)
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hq0 hqN
  have hlogT : Real.log T ≤ Real.log N := by
    by_cases hT : T = 0
    · simp [hT]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast hTN)
  have hlog : 1 + Real.log q + Real.log T ≤ 3 * Real.log N := by linarith
  have hlog0 : 0 ≤ 1 + Real.log q + Real.log T := by positivity
  have hNq : (N : ℝ) / q ≤ s := by
    calc
      _ ≤ (N : ℝ) / Qof A N := div_le_div_of_nonneg_left hN.le hQ0 hqQ.le
      _ = s := ht
  have hxq : 2 * x / q ≤ 2 * s := by
    calc
      _ = 2 * (x / q) := by ring
      _ ≤ 2 * ((N : ℝ) / q) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hxN hq0.le) (by norm_num)
      _ ≤ 2 * s := mul_le_mul_of_nonneg_left hNq (by norm_num)
  have hT : (T : ℝ) ≤ 4 * s := by simpa only [s, mul_assoc] using hTS
  have hcoef : 2 * x / q + T + q ≤ 7 * s := by linarith
  have hm := phaseCap_sum_le hq hcop herr hx T
  apply hm.trans
  have hprod := mul_le_mul hcoef hlog hlog0 (by positivity : 0 ≤ 7 * s)
  have hbound : 12 * (2 * x / q + T + q) * (1 + Real.log q + Real.log T) + T ≤
      256 * s * Real.log N := by
    nlinarith [mul_nonneg hs (show 0 ≤ Real.log N - 1 by linarith)]
  apply hbound.trans_eq
  dsimp [s]
  rw [show (1 - 20 * A) = (-20 * A) + (1 : ℝ) by ring, Real.rpow_add hL0, Real.rpow_one]
  ring

/-! ## Decomp341a: the finite Gram reduction of display 55 -/

/-- Expanding the divisor weight gives the coefficient and atom row on page 83. -/
private theorem row_eq_atoms (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ)
    (b : ℕ → ℂ) (m : ℕ) :
    row lam l₃ K N α x H H₁ b m =
      ∑ i ∈ IND[ l₃, K, H, H₁ ], (b i.1 * (lam i.2 : ℂ)) * ATM[ l₃, N, α, x, m, i ] := by
  classical
  simp only [sum_product, row, L2Bound.weight, sum_filter,
    Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, mul_sum]
  apply sum_congr rfl
  intro l hl
  by_cases hc : x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N
  · simp only [hc, ite_true, true_and]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> simp_all <;> ring
  · simp only [hc, ite_false, false_and, mul_zero, ite_self, sum_const_zero]

/-- The exact Gram expansion before Tolev 1999 display 55. -/
private theorem energy_eq_gram (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) :
    (energy lam l₃ K N α x M M₁ H H₁ b : ℂ) =
      ∑ i ∈ IND[ l₃, K, H, H₁ ], ∑ j ∈ IND[ l₃, K, H, H₁ ],
        (b i.1 * (lam i.2 : ℂ)) * conj (b j.1 * (lam j.2 : ℂ)) *
          CORR[ l₃, N, α, x, M, M₁, i, j ] := by
  have hpoint (m : ℕ) :
      ((‖row lam l₃ K N α x H H₁ b m‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ IND[ l₃, K, H, H₁ ], ∑ j ∈ IND[ l₃, K, H, H₁ ],
          (b i.1 * (lam i.2 : ℂ)) * conj (b j.1 * (lam j.2 : ℂ)) *
            (ATM[ l₃, N, α, x, m, i ] * conj (ATM[ l₃, N, α, x, m, j ])) := by
    rw [row_eq_atoms, sq_norm_eq_mul_conj, map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [map_mul]
    ring
  simp only [energy, Complex.ofReal_sum, hpoint, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]

/-- The scalar diagonal and off diagonal sum partition is exact. -/
private theorem diagonal_add_offDiagonal (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) :
    DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] +
        ODIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] =
      ∑ i ∈ IND[ l₃, K, H, H₁ ], ∑ j ∈ IND[ l₃, K, H, H₁ ],
        (tau5 i.1 : ℝ) * tau5 j.1 * ‖CORR[ l₃, N, α, x, M, M₁, i, j ]‖ := by
  classical
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  by_cases h : i.1 = j.1 <;> simp [h]

/-- The coefficient free energy majorant in Tolev 1999 page 83 display 55. -/
private theorem energy_le_correlations (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) (hlam : ∀ k, |lam k| ≤ 1) (hL : 0 ≤ Real.log N)
    (hb : ∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) :
    energy lam l₃ K N α x M M₁ H H₁ b ≤
      Real.log N ^ (2 : ℕ) *
        (DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] +
          ODIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ]) := by
  have hc (i : ℕ × ℕ) : ‖b i.1 * (lam i.2 : ℂ)‖ ≤ (tau5 i.1 : ℝ) * Real.log N := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hlam i.2) (norm_nonneg _)).trans (by simpa using hb i.1)
  have he := congrArg norm (energy_eq_gram lam l₃ K N α x M M₁ H H₁ b)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energy_nonneg ..)] at he
  rw [he, diagonal_add_offDiagonal, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc
    _ ≤ (((tau5 i.1 : ℝ) * Real.log N) * ((tau5 j.1 : ℝ) * Real.log N)) *
        ‖CORR[ l₃, N, α, x, M, M₁, i, j ]‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (hc i) (hc j) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hL)
    _ = _ := by ring

/-- The Gram kernel is the progression V of Tolev 1999 page 83 display 55. -/
private theorem correlation_eq_phase (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ) :
    CORR[ l₃, N, α, x, M, M₁, i, j ] =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        if ((x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
            (m * i.1) % i.2 = l₃ % i.2) ∧
           ((x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
            (m * j.1) % j.2 = l₃ % j.2) then
          ee (α * m * ((i.1 : ℝ) - j.1)) else 0 := by
  classical
  apply sum_congr rfl
  intro m hm
  by_cases hi : (x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
      (m * i.1) % i.2 = l₃ % i.2
  · by_cases hj : (x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
        (m * j.1) % j.2 = l₃ % j.2
    · simp only [hi, hj, and_self, ite_true, conj_ee]
      rw [← ee_add]
      congr 1
      push_cast
      ring
    · simp only [hi, hj, true_and, ite_true, ite_false, map_zero, mul_zero]
  · simp only [hi, false_and, ite_false, zero_mul]

/-- For equal second variables the phase vanishes and V is a cardinality. -/
private theorem correlation_diagonal (l₃ N : ℕ) (α x M M₁ : ℝ) (l k₁ k₂ : ℕ) :
    CORR[ l₃, N, α, x, M, M₁, (l, k₁), (l, k₂) ] =
      (((Ioc ⌊M⌋₊ ⌊M₁⌋₊).filter (fun m =>
        (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
          (m * l) % k₁ = l₃ % k₁ ∧ (m * l) % k₂ = l₃ % k₂)).card : ℂ) := by
  rw [correlation_eq_phase]
  simp only [sub_self, mul_zero, ee_zero, ← sum_filter,
    sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext m
  simp only [mem_filter]
  tauto

/-- The diagonal scalar sum is independent of alpha, as used in display 56. -/
private theorem diagonal_independent (l₃ K N : ℕ) (α β x M M₁ H H₁ : ℝ) :
    DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] = DIAG[ l₃, K, N, β, x, M, M₁, H, H₁ ] := by
  classical
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  obtain ⟨l, k₁⟩ := i
  obtain ⟨l', k₂⟩ := j
  by_cases h : l = l'
  · subst h
    simp only [ite_true]
    rw [correlation_diagonal, correlation_diagonal]
  · simp only [h, ite_false]

/-- Both scalar pieces in the source correlation split are nonnegative. -/
private theorem scalar_nonneg (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) :
    0 ≤ DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] ∧
      0 ≤ ODIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] := by
  constructor <;>
    apply sum_nonneg <;> intro i hi <;> apply sum_nonneg <;> intro j hj <;>
    split_ifs <;> positivity

/-! ## Shifted coefficient counting (Shifted341) -/

/-- At each positive distance a fixed integer has at most two partners. -/
private theorem distance_sum_le (S : Finset ℕ) (U l : ℕ) (hl : l ≤ U)
    (hS : ∀ j ∈ S, j ≤ U) (F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r) :
    ∑ j ∈ S, (if l ≠ j then F (Nat.dist l j) else 0) ≤
      2 * ∑ r ∈ Icc 1 U, F r := by
  classical
  have hlow : ∑ j ∈ S.filter (fun j => j < l), F (l - j) ≤ ∑ r ∈ Icc 1 U, F r := by
    have hi : Set.InjOn (fun j => l - j) (S.filter (fun j => j < l)) := by
      intro a ha b hb he
      dsimp only at he
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      omega
    rw [← sum_image hi]
    apply sum_le_sum_of_subset_of_nonneg
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      have hj' := (mem_filter.mp hj).2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro r hr hnot
      exact hF r
  have hhigh : ∑ j ∈ S.filter (fun j => l < j), F (j - l) ≤ ∑ r ∈ Icc 1 U, F r := by
    have hi : Set.InjOn (fun j => j - l) (S.filter (fun j => l < j)) := by
      intro a ha b hb he
      dsimp only at he
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      omega
    rw [← sum_image hi]
    apply sum_le_sum_of_subset_of_nonneg
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      have hj' := mem_filter.mp hj
      have hjU := hS j hj'.1
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro r hr hnot
      exact hF r
  have he : (∑ j ∈ S, if l ≠ j then F (Nat.dist l j) else 0) =
      (∑ j ∈ S.filter (fun j => j < l), F (l - j)) +
      (∑ j ∈ S.filter (fun j => l < j), F (j - l)) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rcases lt_trichotomy j l with h | h | h
    · simp [show l ≠ j by omega, h, show ¬ l < j by omega, Nat.dist_eq_sub_of_le_right h.le]
    · subst j; simp
    · simp [show l ≠ j by omega, h, show ¬ j < l by omega, Nat.dist_eq_sub_of_le h.le]
  rw [he]
  linarith

/-- The shifted coefficient mass is bounded by twice its square moment. -/
private theorem shifted_square_bound (S : Finset ℕ) (U : ℕ) (hS : ∀ j ∈ S, j ≤ U)
    (a F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r) :
    ∑ l ∈ S, ∑ j ∈ S, (if l ≠ j then a l * a j * F (Nat.dist l j) else 0) ≤
      2 * (∑ l ∈ S, a l ^ 2) * (∑ r ∈ Icc 1 U, F r) := by
  classical
  let B := ∑ r ∈ Icc 1 U, F r
  have hsquare : ∀ l j : ℕ,
      2 * (if l ≠ j then a l * a j * F (Nat.dist l j) else 0) ≤
        a l ^ 2 * (if l ≠ j then F (Nat.dist l j) else 0) +
        a j ^ 2 * (if l ≠ j then F (Nat.dist l j) else 0) := by
    intro l j
    split_ifs with h
    · nlinarith [mul_nonneg (sq_nonneg (a l - a j)) (hF (Nat.dist l j))]
    · simp
  have hs := sum_le_sum (s := S) (fun l hl => sum_le_sum (s := S) (fun j hj => hsquare l j))
  have hsym : (∑ l ∈ S, ∑ j ∈ S, a j ^ 2 * (if l ≠ j then F (Nat.dist l j) else 0)) =
      ∑ l ∈ S, ∑ j ∈ S, a l ^ 2 * (if l ≠ j then F (Nat.dist l j) else 0) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro j hj
    simp [ne_comm, Nat.dist_comm]
  simp only [sum_add_distrib, ← mul_sum] at hs
  rw [hsym] at hs
  simp only [← mul_sum] at hs
  have hb : (∑ l ∈ S, a l ^ 2 * ∑ j ∈ S, if l ≠ j then F (Nat.dist l j) else 0) ≤
      (∑ l ∈ S, a l ^ 2) * (2 * B) := by
    rw [sum_mul]
    apply sum_le_sum
    intro l hl
    exact mul_le_mul_of_nonneg_left (distance_sum_le S U l (hS l hl) hS F hF) (sq_nonneg _)
  dsimp [B] at hb
  nlinarith

/-! ## Product regrouping (Product341) -/

/-- The lcm fiber reduction in Tolev 1999 displays 57 and 59. -/
private theorem lcm_sum_bound (K : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, F (Nat.lcm k₁ k₂) ≤
      ∑ h ∈ Icc 1 (K * K), (h.divisors.card : ℝ) ^ 4 * F h := by
  have hm : ∀ p ∈ Icc 1 K ×ˢ Icc 1 K, Nat.lcm p.1 p.2 ∈ Icc 1 (K * K) := by
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := mem_product.mp hp
    obtain ⟨h₁, h₁K⟩ := mem_Icc.mp hp₁
    obtain ⟨h₂, h₂K⟩ := mem_Icc.mp hp₂
    exact mem_Icc.mpr ⟨Nat.lcm_pos (by omega) (by omega),
      (Nat.lcm_le_mul h₁ h₂).trans (Nat.mul_le_mul h₁K h₂K)⟩
  calc
    _ ≤ ∑ p ∈ Icc 1 K ×ˢ Icc 1 K,
        (p.1.divisors.card : ℝ) * p.2.divisors.card * F (Nat.lcm p.1 p.2) := by
      rw [sum_product]
      apply sum_le_sum
      intro k₁ hk₁
      apply sum_le_sum
      intro k₂ hk₂
      have hc₁ : (1 : ℝ) ≤ k₁.divisors.card := by
        exact_mod_cast card_pos.mpr
          (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp hk₁).1; omega))
      have hc₂ : (1 : ℝ) ≤ k₂.divisors.card := by
        exact_mod_cast card_pos.mpr
          (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp hk₂).1; omega))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ (k₁.divisors.card : ℝ) * k₂.divisors.card by nlinarith) (hF _)
    _ = ∑ h ∈ Icc 1 (K * K),
        (∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h),
          (p.1.divisors.card : ℝ) * p.2.divisors.card) * F h := by
      rw [← sum_fiberwise_of_maps_to hm]
      apply sum_congr rfl
      intro h hh
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ _ := sum_le_sum (fun h hh =>
      mul_le_mul_of_nonneg_right (lcm_fiber_divisor_bound h K) (hF h))

/-- The product regrouping in Tolev 1999 page 85 between displays 60 and 61. -/
private theorem divisor_product_bound (U V : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    ∑ h ∈ Icc 1 V, (h.divisors.card : ℝ) ^ 4 * ∑ r ∈ Icc 1 U, F (h * r) ≤
      ∑ n ∈ Icc 1 (U * V), (n.divisors.card : ℝ) ^ 5 * F n := by
  classical
  have hm : ∀ p ∈ Icc 1 V ×ˢ Icc 1 U, p.1 * p.2 ∈ Icc 1 (U * V) := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := mem_product.mp hp
    obtain ⟨h₁p, h₁V⟩ := mem_Icc.mp h₁
    obtain ⟨h₂p, h₂U⟩ := mem_Icc.mp h₂
    exact mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩
  have hf (n : ℕ) (hn : n ∈ Icc 1 (U * V)) :
      (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1 * p.2 = n),
        (p.1.divisors.card : ℝ) ^ 4) ≤ (n.divisors.card : ℝ) ^ 5 := by
    let s := (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1 * p.2 = n)
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hi : Set.InjOn (fun p : ℕ × ℕ => p.1) (s : Set (ℕ × ℕ)) := by
      intro p hp q hq he
      have hp' := mem_filter.mp hp
      have hq' := mem_filter.mp hq
      have hp0 : 0 < p.1 := (mem_Icc.mp (mem_product.mp hp'.1).1).1
      apply Prod.ext he
      apply Nat.eq_of_mul_eq_mul_left hp0
      simpa only [he] using hp'.2.trans hq'.2.symm
    have hs : s.image Prod.fst ⊆ n.divisors := by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hh
      have hp' := (mem_filter.mp hp).2
      exact Nat.mem_divisors.mpr ⟨hp' ▸ dvd_mul_right p.1 p.2, hn0⟩
    calc
      _ = ∑ h ∈ s.image Prod.fst, (h.divisors.card : ℝ) ^ 4 := (sum_image hi).symm
      _ ≤ ∑ h ∈ n.divisors, (h.divisors.card : ℝ) ^ 4 :=
        sum_le_sum_of_subset_of_nonneg hs (fun h hh hnot => by positivity)
      _ ≤ ∑ h ∈ n.divisors, (n.divisors.card : ℝ) ^ 4 := by
        apply sum_le_sum
        intro h hh
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hn0 (Nat.dvd_of_mem_divisors hh))
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  simp_rw [mul_sum]
  rw [← sum_product', ← sum_fiberwise_of_maps_to hm]
  apply sum_le_sum
  intro n hn
  have he : (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1 * p.2 = n),
      (p.1.divisors.card : ℝ) ^ 4 * F (p.1 * p.2)) =
      (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1 * p.2 = n),
        (p.1.divisors.card : ℝ) ^ 4) * F n := by
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [(mem_filter.mp hp).2]
  rw [he]
  exact mul_le_mul_of_nonneg_right (hf n hn) (hF n)

/-! ## Phase cap manipulations (Caps341) -/

/-- Negating the frequency preserves the progression cap used in display 59. -/
private theorem phaseCap_neg (α X : ℝ) (n : ℕ) : phaseCap (-α) X n = phaseCap α X n := by
  have he : ee ((-α) * n) = conj (ee (α * n)) := by rw [conj_ee]; congr 1; ring
  have hn : ‖conj (ee (α * n)) - 1‖ = ‖ee (α * n) - 1‖ := by
    rw [← map_one (starRingEnd ℂ), ← map_sub, Complex.norm_conj]
    simp only [map_one]
  have hi : conj (ee (α * n)) = 1 ↔ ee (α * n) = 1 := by
    constructor
    · intro h
      have ht := congrArg conj h
      simpa using ht
    · intro h
      simp [h]
  simp only [phaseCap, he, hi, hn]

/-- A signed second variable difference can be replaced by its natural distance. -/
private theorem phaseCap_distance (α M : ℝ) (l j h : ℕ) :
    phaseCap (α * ((l : ℝ) - j)) M h = phaseCap (α * (Nat.dist l j : ℝ)) M h := by
  rcases le_total j l with hj | hl
  · rw [Nat.dist_eq_sub_of_le_right hj, Nat.cast_sub hj]
  · rw [Nat.dist_eq_sub_of_le hl, Nat.cast_sub hl]
    have he : α * ((l : ℝ) - j) = -(α * ((j : ℝ) - l)) := by ring
    rw [he, phaseCap_neg]

/-- Enlarge the progression count to the difference times lcm product. -/
private theorem phaseCap_product (α M H : ℝ) (r h : ℕ)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hr : 1 ≤ r) (hh : 1 ≤ h) (hrH : (r : ℝ) ≤ 2 * H) :
    phaseCap (α * r) M h ≤ phaseCap α (2 * M * H) (r * h) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hhp : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have he : (α * r) * (h : ℝ) = α * (r * h : ℕ) := by push_cast; ring
  have hc : 2 * M / h + 1 ≤ 2 * (2 * M * H) / (r * h : ℕ) + 1 := by
    apply add_le_add _ le_rfl
    rw [Nat.cast_mul, div_le_div_iff₀ hhp (mul_pos hrp hhp)]
    have ht := mul_le_mul_of_nonneg_left hrH (show 0 ≤ 2 * M by positivity)
    have ht' := mul_le_mul_of_nonneg_right ht hhp.le
    nlinarith
  simp only [phaseCap, he]
  split_ifs
  · exact hc
  · exact min_le_min hc le_rfl

/-! ## Progressions341: the two-congruence progression -/

/-- The affine progression for V on Tolev 1999 pages 83 to 84. -/
private theorem correlation_affine (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ)
    (hi : 1 ≤ i.2) (hj : 1 ≤ j.2)
    (hci : Nat.Coprime i.2 l₃) (hcj : Nat.Coprime j.2 l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) :
    ∃ β : ℝ, ∃ J : ℕ,
      CORR[ l₃, N, α, x, M, M₁, i, j ] =
        ∑ r ∈ range J, ee (β + (r : ℝ) *
          (α * (Nat.lcm i.2 j.2 : ℝ) * ((i.1 : ℝ) - j.1))) ∧
      (J : ℝ) ≤ 2 * M / Nat.lcm i.2 j.2 + 1 := by
  classical
  let h := Nat.lcm i.2 j.2
  have hh : 0 < h := Nat.lcm_pos (by omega) (by omega)
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  let s := (Ioc ⌊M⌋₊ ⌊M₁⌋₊).filter (fun m =>
    ((x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
      (m * i.1) % i.2 = l₃ % i.2) ∧
    ((x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
      (m * j.1) % j.2 = l₃ % j.2))
  have he : CORR[ l₃, N, α, x, M, M₁, i, j ] =
      ∑ m ∈ s, ee (α * m * ((i.1 : ℝ) - j.1)) := by
    rw [correlation_eq_phase, ← sum_filter]
  by_cases hne : s.Nonempty
  · let a := s.min' hne
    let b := s.max' hne
    have ha : a ∈ s := s.min'_mem hne
    have hb : b ∈ s := s.max'_mem hne
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    have hab : a ≤ b := s.min'_le b hb
    have hki : Nat.Coprime i.2 i.1 := by
      have ht : Nat.Coprime i.2 (a * i.1) := by
        change Nat.gcd i.2 (a * i.1) = 1
        rw [Nat.gcd_rec, ha'.2.1.2, ← Nat.gcd_rec]
        exact hci
      exact ht.of_dvd_right (dvd_mul_left i.1 a)
    have hkj : Nat.Coprime j.2 j.1 := by
      have ht : Nat.Coprime j.2 (a * j.1) := by
        change Nat.gcd j.2 (a * j.1) = 1
        rw [Nat.gcd_rec, ha'.2.2.2, ← Nat.gcd_rec]
        exact hcj
      exact ht.of_dvd_right (dvd_mul_left j.1 a)
    have hmod : ∀ m ∈ s, a ≡ m [MOD h] := by
      intro m hm
      have hm' := mem_filter.mp hm
      apply Nat.mod_lcm
      · apply Nat.ModEq.cancel_left_of_coprime hki
        simpa only [Nat.mul_comm] using (show a * i.1 ≡ m * i.1 [MOD i.2] from
          ha'.2.1.2.trans hm'.2.1.2.symm)
      · apply Nat.ModEq.cancel_left_of_coprime hkj
        simpa only [Nat.mul_comm] using (show a * j.1 ≡ m * j.1 [MOD j.2] from
          ha'.2.2.2.trans hm'.2.2.2.symm)
    have hdiv : h ∣ b - a := (hmod b hb).dvd'
    have hbe : b = a + ((b - a) / h) * h := by
      rw [Nat.div_mul_cancel hdiv]
      omega
    let J := (b - a) / h + 1
    have hbetween : ∀ r < J, a ≤ a + r * h ∧ a + r * h ≤ b := by
      intro r hr
      dsimp [J] at hr
      constructor
      · omega
      · have ht := Nat.mul_le_mul_right h (show r ≤ (b - a) / h by omega)
        omega
    have hmem : ∀ r < J, a + r * h ∈ s := by
      intro r hr
      obtain ⟨hlo, hhi⟩ := hbetween r hr
      have ht : a ≡ a + r * h [MOD h] := by
        simp [Nat.ModEq, Nat.add_mod]
      have hti := (ht.of_dvd (Nat.dvd_lcm_left i.2 j.2)).mul_right i.1
      have htj := (ht.of_dvd (Nat.dvd_lcm_right i.2 j.2)).mul_right j.1
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp ha'.1).1.trans_le hlo,
        hhi.trans (mem_Ioc.mp hb'.1).2⟩, ?_, ?_⟩
      · have hpi := Nat.mul_le_mul_right i.1 hlo
        have hqi := Nat.mul_le_mul_right i.1 hhi
        refine ⟨⟨ha'.2.1.1.1.trans_le (by exact_mod_cast hpi),
          (by exact_mod_cast hqi : (((a + r * h) * i.1 : ℕ) : ℝ) ≤ (b * i.1 : ℕ)).trans
            hb'.2.1.1.2.1,
          hqi.trans hb'.2.1.1.2.2⟩, hti.symm.trans ha'.2.1.2⟩
      · have hpj := Nat.mul_le_mul_right j.1 hlo
        have hqj := Nat.mul_le_mul_right j.1 hhi
        refine ⟨⟨ha'.2.2.1.1.trans_le (by exact_mod_cast hpj),
          (by exact_mod_cast hqj : (((a + r * h) * j.1 : ℕ) : ℝ) ≤ (b * j.1 : ℕ)).trans
            hb'.2.2.1.2.1,
          hqj.trans hb'.2.2.1.2.2⟩, htj.symm.trans ha'.2.2.2⟩
    have hs : s = (range J).image (fun r => a + r * h) := by
      ext m
      constructor
      · intro hm
        have ham : a ≤ m := s.min'_le m hm
        have hmb : m ≤ b := s.le_max' m hm
        have hdm : h ∣ m - a := (hmod m hm).dvd'
        refine mem_image.mpr ⟨(m - a) / h, mem_range.mpr ?_, ?_⟩
        · dsimp [J]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : m - a ≤ b - a))
        · rw [Nat.div_mul_cancel hdm]
          omega
      · intro hm
        obtain ⟨r, hr, rfl⟩ := mem_image.mp hm
        exact hmem r (mem_range.mp hr)
    refine ⟨α * a * ((i.1 : ℝ) - j.1), J, ?_, ?_⟩
    · rw [he, hs, sum_image]
      · apply sum_congr rfl
        intro r hr
        congr 1
        push_cast
        ring
      · intro r hr r' hr' heq
        exact Nat.mul_right_cancel hh (Nat.add_left_cancel heq)
    · have hbpos : 0 < b := lt_of_lt_of_le (by have := (mem_Ioc.mp ha'.1).1; omega : 0 < a) hab
      have hM₁0 : 0 ≤ M₁ := by
        by_contra hn
        have hz := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hn))
        rw [hz] at hb'
        have := (mem_Ioc.mp hb'.1).2
        omega
      have hble : (b : ℝ) ≤ 2 * M :=
        (show (b : ℝ) ≤ ⌊M₁⌋₊ by exact_mod_cast (mem_Ioc.mp hb'.1).2).trans
          ((Nat.floor_le hM₁0).trans hM₁)
      have hbeR : (b : ℝ) = a + ((b - a) / h : ℕ) * (h : ℝ) := by exact_mod_cast hbe
      have hJR : (J : ℝ) = ((b - a) / h : ℕ) + 1 := by simp [J]
      have hnum : ((J : ℝ) - 1) * h ≤ 2 * M := by
        rw [hJR]
        nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
      have hquot := (le_div_iff₀ hhr).mpr hnum
      change (J : ℝ) ≤ 2 * M / h + 1
      linarith
  · refine ⟨0, 0, ?_, ?_⟩
    · rw [he, not_nonempty_iff_eq_empty.mp hne]
      simp
    · simp only [Nat.cast_zero]
      exact add_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) zero_le_one

/-- The geometric bound for V before Tolev 1999 display 56. -/
private theorem correlation_bound (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ)
    (hi : 1 ≤ i.2) (hj : 1 ≤ j.2)
    (hci : Nat.Coprime i.2 l₃) (hcj : Nat.Coprime j.2 l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) :
    ‖CORR[ l₃, N, α, x, M, M₁, i, j ]‖ ≤
      phaseCap (α * ((i.1 : ℝ) - j.1)) M (Nat.lcm i.2 j.2) := by
  obtain ⟨β, J, he, hJ⟩ := correlation_affine l₃ N α x M M₁ i j hi hj hci hcj hM hM₁
  have ht : α * (Nat.lcm i.2 j.2 : ℝ) * ((i.1 : ℝ) - j.1) =
      (α * ((i.1 : ℝ) - j.1)) * (Nat.lcm i.2 j.2 : ℝ) := by ring
  rw [he]
  simp only [ht]
  unfold phaseCap
  split_ifs with hθ
  · apply le_trans (norm_sum_le _ _)
    simpa only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one] using hJ
  · exact (progression_phase_bound β _ J hθ).trans (min_le_min hJ le_rfl)

/-- The diagonal count bound before Tolev 1999 display 56. -/
private theorem correlation_diagonal_bound (l₃ N : ℕ) (α x M M₁ : ℝ) (l k₁ k₂ : ℕ)
    (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (hc₁ : Nat.Coprime k₁ l₃) (hc₂ : Nat.Coprime k₂ l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) :
    ‖CORR[ l₃, N, α, x, M, M₁, (l, k₁), (l, k₂) ]‖ ≤
      2 * M / Nat.lcm k₁ k₂ + 1 := by
  simpa [phaseCap, ee_zero] using
    correlation_bound l₃ N α x M M₁ (l, k₁) (l, k₂) h₁ h₂ hc₁ hc₂ hM hM₁

/-! ## Diagonal341: display 56 -/

/-- Dropping the positive divisor weights in display 58 preserves its bound. -/
private theorem unweighted_lcm_sum (K : ℕ) :
    ∑ p ∈ Icc 1 K ×ˢ Icc 1 K, (1 : ℝ) / Nat.lcm p.1 p.2 ≤ Hn (K * K) ^ (16 : ℕ) := by
  apply (sum_le_sum (fun p hp => ?_)).trans (lcm_divisor_sum K)
  obtain ⟨h₁, h₂⟩ := mem_product.mp hp
  have hc₁ : (1 : ℝ) ≤ p.1.divisors.card := by
    exact_mod_cast card_pos.mpr
      (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp h₁).1; omega))
  have hc₂ : (1 : ℝ) ≤ p.2.divisors.card := by
    exact_mod_cast card_pos.mpr
      (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp h₂).1; omega))
  exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)

/-- The exact diagonal regrouping before Tolev 1999 display 56. -/
private theorem diagonal_eq (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) :
    DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] =
      ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2 *
        ∑ k₁ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        ∑ k₂ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
          ‖CORR[ l₃, N, α, x, M, M₁, (l, k₁), (l, k₂) ]‖ := by
  classical
  simp only [sum_product]
  apply sum_congr rfl
  intro l hl
  rw [mul_sum]
  apply sum_congr rfl
  intro k₁ hk₁
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro k₂ hk₂
  simp only [sum_ite_eq, hl, ite_true, pow_two]

/-- The diagonal progression bound with its lcm sum and endpoint count separated. -/
private theorem diagonal_le_separated (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) :
    DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] ≤
      (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2) *
        (2 * M * Hn (K * K) ^ (16 : ℕ) + (K : ℝ) ^ 2) := by
  classical
  rw [diagonal_eq, sum_mul]
  apply sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ k₁ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        ∑ k₂ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
          (2 * M / Nat.lcm k₁ k₂ + 1) := by
      apply sum_le_sum
      intro k₁ hk₁
      apply sum_le_sum
      intro k₂ hk₂
      exact correlation_diagonal_bound l₃ N α x M M₁ l k₁ k₂
        (mem_Icc.mp (mem_filter.mp hk₁).1).1 (mem_Icc.mp (mem_filter.mp hk₂).1).1
        (mem_filter.mp hk₁).2 (mem_filter.mp hk₂).2 hM hM₁
    _ ≤ ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, (2 * M / Nat.lcm k₁ k₂ + 1) := by
      apply (sum_le_sum (fun k₁ hk₁ =>
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun k₂ hk₂ hnot => by positivity))).trans
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₁ hk₁ hnot =>
        sum_nonneg (fun k₂ hk₂ => by positivity))
    _ = 2 * M * (∑ p ∈ Icc 1 K ×ˢ Icc 1 K, (1 : ℝ) / Nat.lcm p.1 p.2) + (K : ℝ) ^ 2 := by
      simp only [← sum_product', sum_add_distrib, sum_const, card_product,
        Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul, nsmul_eq_mul, mul_one, mul_sum]
      congr 1
      · apply sum_congr rfl
        intro p hp
        ring
      · ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (unweighted_lcm_sum K) (show 0 ≤ 2 * M by positivity)) le_rfl

/-- The unweighted tau5 square mean in the diagonal part of display 56. -/
private theorem tau5_square_sum (H H₁ : ℝ) (hH : 0 < H) (hH₁ : H₁ ≤ 2 * H) :
    ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2 ≤
      2 * H * Hn ⌊2 * H⌋₊ ^ (24 : ℕ) := by
  have hs : Ioc ⌊H⌋₊ ⌊H₁⌋₊ ⊆ Icc 1 ⌊2 * H⌋₊ := by
    intro l hl
    obtain ⟨hl0, hl1⟩ := mem_Ioc.mp hl
    exact mem_Icc.mpr ⟨by omega, hl1.trans (Nat.floor_le_floor hH₁)⟩
  calc
    _ ≤ ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (((ArithmeticFunction.zeta ^ 25) l : ℕ) : ℝ) := by
      apply sum_le_sum
      intro l hl
      exact_mod_cast tau5_sq_le_zeta25 l
    _ ≤ ∑ l ∈ Icc 1 ⌊2 * H⌋₊, (((ArithmeticFunction.zeta ^ 25) l : ℕ) : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hs (fun l hl hnot => Nat.cast_nonneg _)
    _ ≤ (⌊2 * H⌋₊ : ℝ) * Hn ⌊2 * H⌋₊ ^ (24 : ℕ) := zeta_power_sum 24 _
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)

/-- A fully explicit finite diagonal bound for Tolev 1999 display 56. -/
private theorem diagonal_finite_bound (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) (hH : 0 < H) (hH₁ : H₁ ≤ 2 * H) :
    DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] ≤
      (2 * H * Hn ⌊2 * H⌋₊ ^ (24 : ℕ)) *
        (2 * M * Hn (K * K) ^ (16 : ℕ) + (K : ℝ) ^ 2) := by
  exact (diagonal_le_separated l₃ K N α x M M₁ H H₁ hM hM₁).trans
    (mul_le_mul_of_nonneg_right (tau5_square_sum H H₁ hH hH₁) (by positivity))

/-! ## Decomp341b: the diagonal mean, display 56 -/

/-- The polynomial saving in the diagonal term of Tolev 1999 display 56. -/
private theorem diagonal_power_bound (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hN : (1 : ℝ) ≤ N) (hL : 1 ≤ Real.log N)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) (hH : 0 < H) (hH₁ : H₁ ≤ 2 * H)
    (hMH : M * H ≤ 2 * N) (hHlo : (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ H)
    (hK : (K : ℝ) ^ 2 ≤ (N : ℝ) ^ ((2 : ℝ) / 3))
    (hHm : Hn ⌊2 * H⌋₊ ≤ 33 * Real.log N)
    (hHk : Hn (K * K) ≤ 33 * Real.log N) :
    M * DIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] ≤
      (20 * 33 ^ (40 : ℕ)) * (N : ℝ) ^ ((3999 : ℝ) / 2000) * Real.log N ^ (40 : ℕ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hP : 0 < (N : ℝ) ^ ((1 : ℝ) / 2000) := Real.rpow_pos_of_pos hN0 _
  have hML : M ≤ 2 * (N : ℝ) ^ ((1999 : ℝ) / 2000) := by
    have hh : M ≤ 2 * (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      (le_div_iff₀ hP).mpr ((mul_le_mul_of_nonneg_left hHlo hM.le).trans hMH)
    convert hh using 1
    rw [mul_div_assoc]
    congr 1
    simpa only [show (1 : ℝ) - (1 : ℝ) / 2000 = (1999 : ℝ) / 2000 by norm_num, Real.rpow_one] using
      Real.rpow_sub hN0 1 ((1 : ℝ) / 2000)
  have hKL : (K : ℝ) ^ 2 ≤ (N : ℝ) ^ ((1999 : ℝ) / 2000) :=
    hK.trans (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
  have hL0 : 0 ≤ Real.log N := by linarith
  have h33 : 1 ≤ 33 * Real.log N := by linarith
  have h3316 : 1 ≤ (33 * Real.log N) ^ (16 : ℕ) := one_le_pow₀ h33
  have hbracket : 2 * M * Hn (K * K) ^ (16 : ℕ) + (K : ℝ) ^ 2 ≤
      5 * (N : ℝ) ^ ((1999 : ℝ) / 2000) * (33 * Real.log N) ^ (16 : ℕ) := by
    have hh := pow_le_pow_left₀ (Hn_nonneg _) hHk 16
    have hb := mul_le_mul (mul_le_mul_of_nonneg_left hML (by norm_num : (0 : ℝ) ≤ 2)) hh
      (by positivity) (by positivity)
    have hk := mul_le_mul_of_nonneg_left h3316
      (Real.rpow_nonneg (Nat.cast_nonneg N) ((1999 : ℝ) / 2000))
    nlinarith
  have hHnon := Hn_nonneg ⌊2 * H⌋₊
  have hf := diagonal_finite_bound l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
  calc
    _ ≤ M * ((2 * H * Hn ⌊2 * H⌋₊ ^ (24 : ℕ)) *
        (2 * M * Hn (K * K) ^ (16 : ℕ) + (K : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hf hM.le
    _ = 2 * (M * H) * Hn ⌊2 * H⌋₊ ^ (24 : ℕ) *
        (2 * M * Hn (K * K) ^ (16 : ℕ) + (K : ℝ) ^ 2) := by ring
    _ ≤ 2 * (2 * (N : ℝ)) * (33 * Real.log N) ^ (24 : ℕ) *
        (5 * (N : ℝ) ^ ((1999 : ℝ) / 2000) * (33 * Real.log N) ^ (16 : ℕ)) := by
      gcongr
    _ = _ := by
      rw [show (3999 : ℝ) / 2000 = 1 + (1999 : ℝ) / 2000 by norm_num, Real.rpow_add hN0,
        Real.rpow_one]
      ring

/-- Harmonic sums at these polynomial endpoints have one logarithmic loss. -/
private theorem harmonic_endpoint (R N : ℕ) (hN : (0 : ℝ) < N) (hL : 1 ≤ Real.log N)
    (hR : (R : ℝ) ≤ 2 ^ (31 : ℕ) * (N : ℝ)) : Hn R ≤ 33 * Real.log N := by
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogR : Real.log R ≤ 31 + Real.log N := by
    by_cases hzero : R = 0
    · simp [hzero]
      linarith
    · have hRp : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero hzero
      have ht := Real.log_le_log hRp hR
      rw [Real.log_mul (by positivity : (2 : ℝ) ^ (31 : ℕ) ≠ 0) (ne_of_gt hN), Real.log_pow] at ht
      norm_num at ht
      linarith
  exact (Hn_le R).trans (by linarith)

/-- The two logarithmic powers needed for diagonal absorption are eventually small. -/
private theorem eventual_diagonal_parameters (A : ℝ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧
      Real.log N ^ (4 * A) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
      Real.log N ^ (8 * A - 592) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000) := by
  obtain ⟨X₁, h₁⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (4 * A) (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (by norm_num : (0 : ℝ) < 1))
  obtain ⟨X₂, h₂⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (8 * A - 592) (by norm_num : (0 : ℝ) < 1 / 2000)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨max (max X₁ X₂) (Real.exp 2), ?_⟩
  intro N hN
  have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
  have hNp : (0 : ℝ) < N := (Real.exp_pos 2).trans_le hNe
  have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hNp).mpr hNe
  have h₁' := h₁ (N : ℝ) ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
  have h₂' := h₂ (N : ℝ) ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), one_mul] at h₁' h₂'
  exact ⟨hL, h₁', h₂'⟩

/-- The sealed Type II shell gives the parameters used by the diagonal power bound. -/
private theorem diagonal_shell_parameters (A : ℝ) (N : ℕ) (x H : ℝ)
    (hA : 0 ≤ A) (hN : (1 : ℝ) ≤ N) (hL : 1 ≤ Real.log N)
    (hlog : Real.log N ^ (4 * A) ≤ (N : ℝ) ^ ((1 : ℝ) / 2))
    (hx : 0 < x) (hxlo : (N : ℝ) * Real.log N ^ (-4 * A) ≤ x) (hxN : x ≤ N)
    (hHlo : x ^ ((1 : ℝ) / 1000) ≤ H) (hHhi : H ≤ 2 ^ (30 : ℕ) * x ^ ((1 : ℝ) / 3)) :
    let K := cutoff3 (10000 * A) N
    (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ H ∧
      (K : ℝ) ^ 2 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) ∧
      Hn ⌊2 * H⌋₊ ≤ 33 * Real.log N ∧ Hn (K * K) ≤ 33 * Real.log N := by
  have hNp : (0 : ℝ) < N := by linarith
  have hLp : 0 < Real.log N := by linarith
  have hsquare : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    norm_num
  have hs : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) * Real.log N ^ (-4 * A) := by
    rw [show -4 * A = -(4 * A) by ring, Real.rpow_neg hLp.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp _)).mpr
    exact (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hNp.le _)).trans_eq
      (by simpa only [pow_two] using hsquare)
  have hHlower : (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ H := by
    calc
      _ = ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 1000) := by
        rw [← Real.rpow_mul hNp.le]
        norm_num
      _ ≤ x ^ ((1 : ℝ) / 1000) := Real.rpow_le_rpow (by positivity) (hs.trans hxlo) (by norm_num)
      _ ≤ H := hHlo
  have hNthird : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ N := by
    convert Real.rpow_le_rpow_of_exponent_le hN (show (1 : ℝ) / 3 ≤ 1 by norm_num) using 1 <;> simp
  have hHupper : H ≤ 2 ^ (30 : ℕ) * (N : ℝ) :=
    hHhi.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num))
      (by positivity)).trans (mul_le_mul_of_nonneg_left hNthird (by positivity)))
  let K := cutoff3 (10000 * A) N
  have hK : (K : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have hf : (K : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-(10000 * A)) :=
      Nat.floor_le (by positivity)
    have ht : Real.log N ^ (-(10000 * A)) ≤ (1 : ℝ) :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by nlinarith)
    exact hf.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (mul_one _))
  have hKsq : (K : ℝ) ^ 2 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
    have ht := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
    convert ht using 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    norm_num
  refine ⟨hHlower, hKsq, ?_, ?_⟩
  · apply harmonic_endpoint _ N hNp hL
    have hHp : 0 < H := (Real.rpow_pos_of_pos hNp _).trans_le hHlower
    exact (Nat.floor_le (by positivity : 0 ≤ 2 * H)).trans (by nlinarith)
  · apply harmonic_endpoint _ N hNp hL
    have ht : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ N := by
      convert Real.rpow_le_rpow_of_exponent_le hN (show (2 : ℝ) / 3 ≤ 1 by norm_num) using 1 <;> simp
    push_cast
    calc
      (K : ℝ) * (K : ℝ) = (K : ℝ) ^ 2 := by ring
      _ ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := hKsq
      _ ≤ (N : ℝ) := ht
      _ ≤ _ := by nlinarith

/-- The diagonal scalar term has the required logarithmic saving. -/
private theorem diagonal_mean :
    ∀ A : ℝ, 10000 ≤ A → ∃ C N₀ : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ l₃ : ℕ, ∀ α x M M₁ H H₁ : ℝ,
        (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
        0 < M → M₁ ≤ 2 * M → 0 < H → H₁ ≤ 2 * H → M * H ≤ 2 * x →
        x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ (30 : ℕ) * x ^ ((1 : ℝ) / 3) →
        M * DIAG[ l₃, (cutoff3 (10000 * A) N), N, α, x, M, M₁, H, H₁ ] ≤
          C * (N : ℝ) ^ 2 * Real.log N ^ (632 - 8 * A) := by
  intro A hA
  obtain ⟨N₀, hparam⟩ := eventual_diagonal_parameters A
  refine ⟨20 * 33 ^ (40 : ℕ), max N₀ 3, by positivity, ?_⟩
  intro N hN l₃ α x M M₁ H H₁ hxlo hxN hx hM hM₁ hH hH₁ hMH hHlo hHhi
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  obtain ⟨hL, hlog, habs⟩ := hparam N ((le_max_left _ _).trans hN)
  have hLp : 0 < Real.log N := by linarith
  obtain ⟨hHlower, hK, hHm, hHk⟩ := diagonal_shell_parameters A N x H (by linarith) hN1
    (by linarith) hlog (by linarith) hxlo hxN hHlo hHhi
  have hpower := diagonal_power_bound l₃ (cutoff3 (10000 * A) N) N α x M M₁ H H₁
    hN1 (by linarith) hM hM₁ hH hH₁ (hMH.trans (by linarith)) hHlower hK hHm hHk
  have hlogs : Real.log N ^ (40 : ℕ) = Real.log N ^ (8 * A - 592) * Real.log N ^ (632 - 8 * A) := by
    rw [← Real.rpow_add hLp, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hfactor : (N : ℝ) ^ ((3999 : ℝ) / 2000) * Real.log N ^ (40 : ℕ) ≤
      (N : ℝ) ^ 2 * Real.log N ^ (632 - 8 * A) := by
    rw [hlogs, ← mul_assoc]
    calc
      _ ≤ ((N : ℝ) ^ ((3999 : ℝ) / 2000) * (N : ℝ) ^ ((1 : ℝ) / 2000)) *
          Real.log N ^ (632 - 8 * A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg hNp.le _))
          (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        rw [← Real.rpow_add hNp]
        norm_num
  apply hpower.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfactor
    (show (0 : ℝ) ≤ 20 * 33 ^ (40 : ℕ) by positivity)

/-! ## OffDiagonal341: displays 60 to 62 -/

/-- The scalar phase moment is nonnegative at a nonnegative upper shell. -/
private theorem divisorPhase_nonneg (α X : ℝ) (T : ℕ) (hX : 0 ≤ X) :
    0 ≤ DPH[ α, X, T ] :=
  sum_nonneg (fun n hn => mul_nonneg (by positivity) (phaseCap_nonneg α X n hX))

/-- The reciprocal divisor moment Cauchy bound in the adaptation of display 61. -/
private theorem divisorPhase_sq (α X : ℝ) (T : ℕ) (hX : 0 ≤ X) :
    DPH[ α, X, T ] ^ 2 ≤ Hn T ^ (1024 : ℕ) *
      ((2 * X + T) * ∑ n ∈ Icc 1 T, phaseCap α X n) := by
  have hm : (∑ n ∈ Icc 1 T, ((n.divisors.card : ℝ) ^ 5) ^ 2 / n) ≤ Hn T ^ (1024 : ℕ) := by
    simpa only [← pow_mul, show (5 : ℕ) * 2 = 10 by norm_num, show (2 : ℕ) ^ 10 = 1024 by norm_num]
      using divisor_power_reciprocal 10 T
  exact (weighted_phase_cauchy (fun n => (n.divisors.card : ℝ) ^ 5) T α X hX).trans
    (mul_le_mul_of_nonneg_right hm
      (mul_nonneg (by positivity) (sum_nonneg (fun n hn => phaseCap_nonneg α X n hX))))

/-- The unweighted reciprocal phase sum for an upper shell at most four N. -/
private theorem phase_mass_four (A : ℝ) (N T q : ℕ) (a : ℤ) (α X : ℝ)
    (hA : 0 ≤ A) (hN : 0 < (N : ℝ)) (hL : 2 ≤ Real.log N)
    (hX : 0 ≤ X) (hXN : X ≤ 4 * N) (hTN : T ≤ N)
    (hTS : (T : ℝ) ≤ 4 * N * Real.log N ^ (-20 * A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q : ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q : ℤ)) (herr : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ∑ n ∈ Icc 1 T, phaseCap α X n ≤ 512 * N * Real.log N ^ (1 - 20 * A) := by
  let s : ℝ := N * Real.log N ^ (-20 * A)
  have hLp : 0 < Real.log N := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow (by linarith) (by positivity)
  have hQp : 0 < Qof A N := by linarith
  have ht : τof A N = s := by
    dsimp [τof, Qof, s]
    rw [show -20 * A = -(20 * A) by ring, Real.rpow_neg hLp.le, div_eq_mul_inv]
  have hqS : (q : ℝ) ≤ s := by rwa [ht] at hqτ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqN : (q : ℝ) ≤ N := hqτ.trans (div_le_self hN.le hQ)
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hqp hqN
  have hlogT : Real.log T ≤ Real.log N := by
    by_cases hT : T = 0
    · simp [hT]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast hTN)
  have hlogs : 1 + Real.log q + Real.log T ≤ 3 * Real.log N := by linarith
  have hlogs0 : 0 ≤ 1 + Real.log q + Real.log T := by positivity
  have hNq : (N : ℝ) / q ≤ s := by
    calc
      _ ≤ (N : ℝ) / Qof A N := div_le_div_of_nonneg_left hN.le hQp hqQ.le
      _ = s := ht
  have hXq : 2 * X / q ≤ 8 * s := by
    calc
      _ ≤ 2 * (4 * (N : ℝ)) / q := div_le_div_of_nonneg_right (by linarith) hqp.le
      _ = 8 * ((N : ℝ) / q) := by ring
      _ ≤ 8 * s := mul_le_mul_of_nonneg_left hNq (by norm_num)
  have hT : (T : ℝ) ≤ 4 * s := by simpa only [s, mul_assoc] using hTS
  have hc : 2 * X / q + T + q ≤ 13 * s := by linarith
  have hp := mul_le_mul hc hlogs hlogs0 (by positivity : 0 ≤ 13 * s)
  have hm := phaseCap_sum_le hq hcop herr hX T
  apply hm.trans
  have hbound : 12 * (2 * X / q + T + q) * (1 + Real.log q + Real.log T) + T ≤
      512 * s * Real.log N := by
    nlinarith [mul_nonneg hs (show 0 ≤ Real.log N - 1 by linarith)]
  apply hbound.trans_eq
  dsimp [s]
  rw [show 1 - 20 * A = (-20 * A) + (1 : ℝ) by ring, Real.rpow_add hLp, Real.rpow_one]
  ring

/-- The weighted scalar phase sum has ample logarithmic saving. -/
private theorem divisorPhase_bound (A : ℝ) (N T q : ℕ) (a : ℤ) (α X : ℝ)
    (hA : 0 ≤ A) (hN : (1 : ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hX : 0 ≤ X) (hXN : X ≤ 4 * N) (hTN : T ≤ N)
    (hTS : (T : ℝ) ≤ 4 * N * Real.log N ^ (-20 * A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q : ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q : ℤ)) (herr : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    DPH[ α, X, T ] ≤ 2 ^ (520 : ℕ) * N * Real.log N ^ (513 - 10 * A) := by
  have hNp : (0 : ℝ) < N := by linarith
  have hLp : 0 < Real.log N := by linarith
  have hH : Hn T ≤ 2 * Real.log N := by
    have hl : Real.log T ≤ Real.log N := by
      by_cases hz : T = 0
      · simp [hz]; linarith
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hTN)
    exact (Hn_le T).trans (by linarith)
  have hm := phase_mass_four A N T q a α X hA hNp hL hX hXN hTN hTS hq hqQ hqτ hcop herr
  have hTp : (T : ℝ) ≤ N := by exact_mod_cast hTN
  have hc : 2 * X + T ≤ 9 * N := by linarith
  have hphase0 : 0 ≤ ∑ n ∈ Icc 1 T, phaseCap α X n :=
    sum_nonneg (fun n hn => phaseCap_nonneg α X n hX)
  have hb := (divisorPhase_sq α X T hX).trans
    (mul_le_mul (pow_le_pow_left₀ (Hn_nonneg T) hH 1024)
      (mul_le_mul hc hm (sum_nonneg (fun n hn => phaseCap_nonneg α X n hX)) (by positivity))
      (by positivity) (by positivity))
  have he : (2 * Real.log N) ^ (1024 : ℕ) * (9 * N * (512 * N * Real.log N ^ (1 - 20 * A))) =
      (9 * 512 * 2 ^ (1024 : ℕ)) * (N : ℝ) ^ 2 * Real.log N ^ (1025 - 20 * A) := by
    rw [mul_pow, ← Real.rpow_natCast (Real.log N) 1024]
    rw [show 1025 - 20 * A = (1024 : ℝ) + (1 - 20 * A) by ring, Real.rpow_add hLp]
    ring
  rw [he] at hb
  have hpow : Real.log N ^ (1025 - 20 * A) ≤ Real.log N ^ (1026 - 20 * A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hC : (9 * 512 * 2 ^ (1024 : ℕ) : ℝ) ≤ (2 ^ (520 : ℕ) : ℝ) ^ 2 := by norm_num
  have hfin := hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hC (sq_nonneg (N : ℝ))) hpow
    (Real.rpow_nonneg hLp.le _) (by positivity))
  have ht : ((2 ^ (520 : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2) * Real.log N ^ (1026 - 20 * A) =
      (2 ^ (520 : ℕ) * N * Real.log N ^ (513 - 10 * A)) ^ 2 := by
    have hsq : (Real.log N ^ (513 - 10 * A)) ^ (2 : ℕ) = Real.log N ^ (1026 - 20 * A) := by
      rw [← Real.rpow_mul_natCast hLp.le]
      congr 1
      push_cast
      ring
    rw [← hsq]
    ring
  rw [ht] at hfin
  exact (sq_le_sq₀ (divisorPhase_nonneg α X T hX) (by positivity)).mp hfin

/-- The difference times lcm endpoint stays inside the short reciprocal phase range. -/
private theorem phase_product_endpoint (A : ℝ) (N : ℕ) (x H : ℝ)
    (hA : 10000 ≤ A) (hN : (1 : ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hx : 0 < x) (hxN : x ≤ N) (hH : 0 < H)
    (hHhi : H ≤ 2 ^ (30 : ℕ) * x ^ ((1 : ℝ) / 3)) :
    let K := cutoff3 (10000 * A) N
    let T := ⌊2 * H⌋₊ * (K * K)
    T ≤ N ∧ (T : ℝ) ≤ 4 * N * Real.log N ^ (-20 * A) := by
  let K := cutoff3 (10000 * A) N
  let T := ⌊2 * H⌋₊ * (K * K)
  have hNp : (0 : ℝ) < N := by linarith
  have hLp : 0 < Real.log N := by linarith
  have hHupper : H ≤ 2 ^ (30 : ℕ) * (N : ℝ) ^ ((1 : ℝ) / 3) :=
    hHhi.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num))
      (by positivity))
  have hK : (K : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-(10000 * A)) :=
    Nat.floor_le (by positivity)
  have hKsq : (K : ℝ) ^ 2 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) * Real.log N ^ (-20000 * A) := by
    calc
      _ ≤ ((N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-(10000 * A))) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
      _ = _ := by
        have hn : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) = (N : ℝ) ^ ((2 : ℝ) / 3) := by
          rw [← Real.rpow_mul_natCast hNp.le]
          norm_num
        have hl : (Real.log N ^ (-(10000 * A))) ^ (2 : ℕ) = Real.log N ^ (-20000 * A) := by
          rw [← Real.rpow_mul_natCast hLp.le]
          congr 1
          push_cast
          ring
        rw [mul_pow, hn, hl]
  have hT : (T : ℝ) ≤ 2 ^ (31 : ℕ) * (N : ℝ) * Real.log N ^ (-20000 * A) := by
    have hf : (⌊2 * H⌋₊ : ℝ) ≤ 2 * H := Nat.floor_le (by positivity)
    calc
      (T : ℝ) = (⌊2 * H⌋₊ : ℝ) * (K : ℝ) ^ 2 := by dsimp [T]; push_cast; ring
      _ ≤ (2 * H) * ((N : ℝ) ^ ((2 : ℝ) / 3) * Real.log N ^ (-20000 * A)) :=
        mul_le_mul hf hKsq (sq_nonneg _) (by positivity)
      _ ≤ (2 * (2 ^ (30 : ℕ) * (N : ℝ) ^ ((1 : ℝ) / 3))) *
          ((N : ℝ) ^ ((2 : ℝ) / 3) * Real.log N ^ (-20000 * A)) := by gcongr
      _ = 2 ^ (31 : ℕ) * ((N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((2 : ℝ) / 3)) *
          Real.log N ^ (-20000 * A) := by ring
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hsmall : Real.log N ^ (-19980 * A) ≤ (2 : ℝ) ^ (-(31 : ℝ)) := by
    calc
      _ ≤ Real.log N ^ (-(31 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
  have hbudget : (T : ℝ) ≤ (N : ℝ) * Real.log N ^ (-20 * A) := by
    apply hT.trans
    rw [show -20000 * A = (-20 * A) + (-19980 * A) by ring, Real.rpow_add hLp]
    calc
      _ = (2 ^ (31 : ℕ) * (N : ℝ) * Real.log N ^ (-20 * A)) * Real.log N ^ (-19980 * A) := by ring
      _ ≤ (2 ^ (31 : ℕ) * (N : ℝ) * Real.log N ^ (-20 * A)) * (2 : ℝ) ^ (-(31 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]; ring
  have hone : Real.log N ^ (-20 * A) ≤ (1 : ℝ) :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by nlinarith)
  refine ⟨?_, ?_⟩
  · exact_mod_cast hbudget.trans ((mul_le_mul_of_nonneg_left hone hNp.le).trans_eq (mul_one _))
  · exact hbudget.trans (by have := Real.rpow_nonneg hLp.le (-20 * A); nlinarith)

/-! ## Decomp341c: the off-diagonal mean and the row energy -/

/-- The finite off-diagonal regrouping of Tolev 1999 displays 59 to 61. -/
private theorem finite_offDiagonal_reduction (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) (hH : 0 < H) (hH₁ : H₁ ≤ 2 * H) :
    ODIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] ≤
      2 * (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2) *
        DPH[ α, (2 * M * H), (⌊2 * H⌋₊ * (K * K)) ] := by
  classical
  let S := Ioc ⌊H⌋₊ ⌊H₁⌋₊
  let U := ⌊2 * H⌋₊
  let ks := (Icc 1 K).filter (fun k => Nat.Coprime k l₃)
  let X := 2 * M * H
  let F : ℕ → ℝ := fun r => ∑ h ∈ Icc 1 (K * K), (h.divisors.card : ℝ) ^ 4 * phaseCap α X (h * r)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hF : ∀ r, 0 ≤ F r := fun r => sum_nonneg (fun h hh =>
    mul_nonneg (by positivity) (phaseCap_nonneg α X (h * r) hX))
  have hS : ∀ l ∈ S, l ≤ U := fun l hl =>
    (mem_Ioc.mp hl).2.trans (Nat.floor_le_floor hH₁)
  have he : ODIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] =
      ∑ l ∈ S, ∑ j ∈ S, if l ≠ j then (tau5 l : ℝ) * tau5 j *
        ∑ k₁ ∈ ks, ∑ k₂ ∈ ks,
          ‖CORR[ l₃, N, α, x, M, M₁, (l, k₁), (j, k₂) ]‖ else 0 := by
    simp only [sum_product]
    apply sum_congr rfl
    intro l hl
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    by_cases hn : l ≠ j
    · simp [hn, ks, mul_sum]
    · simp [hn, ks]
  have hpoint (l j : ℕ) (hl : l ∈ S) (hj : j ∈ S) (hne : l ≠ j) :
      (∑ k₁ ∈ ks, ∑ k₂ ∈ ks,
        ‖CORR[ l₃, N, α, x, M, M₁, (l, k₁), (j, k₂) ]‖) ≤
        F (Nat.dist l j) := by
    let r := Nat.dist l j
    have hr : 1 ≤ r := by dsimp [r, Nat.dist]; omega
    have hrU : r ≤ U := by have hlU := hS l hl; have hjU := hS j hj; dsimp [r, Nat.dist]; omega
    have hrH : (r : ℝ) ≤ 2 * H :=
      (show (r : ℝ) ≤ U by exact_mod_cast hrU).trans (Nat.floor_le (by positivity))
    calc
      _ ≤ ∑ k₁ ∈ ks, ∑ k₂ ∈ ks, phaseCap α X (Nat.lcm k₁ k₂ * r) := by
        apply sum_le_sum
        intro k₁ hk₁
        apply sum_le_sum
        intro k₂ hk₂
        have hk₁' := mem_filter.mp hk₁
        have hk₂' := mem_filter.mp hk₂
        have hk₁p := (mem_Icc.mp hk₁'.1).1
        have hk₂p := (mem_Icc.mp hk₂'.1).1
        have hh : 1 ≤ Nat.lcm k₁ k₂ := Nat.lcm_pos (by omega) (by omega)
        calc
          _ ≤ phaseCap (α * ((l : ℝ) - j)) M (Nat.lcm k₁ k₂) :=
            correlation_bound l₃ N α x M M₁ (l, k₁) (j, k₂) hk₁p hk₂p hk₁'.2 hk₂'.2 hM hM₁
          _ = phaseCap (α * r) M (Nat.lcm k₁ k₂) := phaseCap_distance α M l j _
          _ ≤ _ := by
            simpa only [Nat.mul_comm] using phaseCap_product α M H r (Nat.lcm k₁ k₂) hM.le hH.le hr hh hrH
      _ ≤ ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, phaseCap α X (Nat.lcm k₁ k₂ * r) := by
        apply (sum_le_sum (fun k₁ hk₁ =>
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun k₂ hk₂ hnot => phaseCap_nonneg α X _ hX))).trans
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₁ hk₁ hnot =>
          sum_nonneg (fun k₂ hk₂ => phaseCap_nonneg α X _ hX))
      _ ≤ _ := lcm_sum_bound K (fun h => phaseCap α X (h * r)) (fun h => phaseCap_nonneg α X _ hX)
  have hfirst : ODIAG[ l₃, K, N, α, x, M, M₁, H, H₁ ] ≤
      ∑ l ∈ S, ∑ j ∈ S, if l ≠ j then (tau5 l : ℝ) * tau5 j * F (Nat.dist l j) else 0 := by
    rw [he]
    apply sum_le_sum
    intro l hl
    apply sum_le_sum
    intro j hj
    by_cases hn : l ≠ j
    · simp only [ne_eq, hn, ite_true]
      exact mul_le_mul_of_nonneg_left (hpoint l j hl hj hn) (by positivity)
    · simp only [ne_eq, hn, ite_false, le_refl]
  have hsecond := shifted_square_bound S U hS (fun l => (tau5 l : ℝ)) F hF
  have hthird : (∑ r ∈ Icc 1 U, F r) ≤ DPH[ α, X, (U * (K * K)) ] := by
    dsimp [F]
    rw [sum_comm]
    simp only [← mul_sum]
    exact divisor_product_bound U (K * K) (fun n => phaseCap α X n)
      (fun n => phaseCap_nonneg α X n hX)
  exact (hfirst.trans hsecond).trans (mul_le_mul_of_nonneg_left hthird (by positivity))

/-- The off diagonal scalar mean follows from the finite regrouping and phase sum. -/
private theorem offDiagonal_mean :
    ∀ A : ℝ, 10000 ≤ A → ∃ C N₀ : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ l₃ : ℕ,
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M₁ ≤ 2 * M → 0 < H → H₁ ≤ 2 * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ (30 : ℕ) * x ^ ((1 : ℝ) / 3) →
          M * ODIAG[ l₃, (cutoff3 (10000 * A) N), N, α, x, M, M₁, H, H₁ ] ≤
            C * (N : ℝ) ^ 2 * Real.log N ^ (632 - 8 * A) := by
  intro A hA
  obtain ⟨N₁, hparam₁⟩ := eventual_minor_arc_parameters A (by linarith)
  obtain ⟨N₂, hparam₂⟩ := eventual_diagonal_parameters A
  refine ⟨2 ^ (523 : ℕ) * 33 ^ (24 : ℕ), max N₁ (max N₂ 3), by positivity, ?_⟩
  intro N hN l₃ α hα hminor x M M₁ H H₁ hxlo hxN hx hM hM₁ hH hH₁ hMH hHlo hHhi
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  obtain ⟨hL, hτ⟩ := hparam₁ N ((le_max_left _ _).trans hN)
  obtain ⟨_, hlog, _⟩ := hparam₂ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hLp : 0 < Real.log N := by linarith
  have hQ : 0 ≤ Qof A N := Real.rpow_nonneg (by linarith) _
  have hτ1 : 1 ≤ τof A N := by linarith
  obtain ⟨a, q, hq, hqQ, hqt, hcop, _, herr⟩ :=
    minor_arc_reduced_approximation (Qof A N) (τof A N) α hQ hτ hτ1 hα hminor
  let K := cutoff3 (10000 * A) N
  let T := ⌊2 * H⌋₊ * (K * K)
  obtain ⟨hTN, hTS⟩ := phase_product_endpoint A N x H hA hN1 hL (by linarith) hxN hH hHhi
  have hX : 0 ≤ 2 * M * H := by positivity
  have hXN : 2 * M * H ≤ 4 * N := by nlinarith
  have hphase := divisorPhase_bound A N T q a α (2 * M * H) (by linarith) hN1 hL hX hXN
    hTN hTS hq hqQ hqt hcop herr
  obtain ⟨_, _, hHm, _⟩ := diagonal_shell_parameters A N x H (by linarith) hN1
    (by linarith) hlog (by linarith) hxlo hxN hHlo hHhi
  have hmass : (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2) ≤
      2 * H * (33 * Real.log N) ^ (24 : ℕ) :=
    (tau5_square_sum H H₁ hH hH₁).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Hn_nonneg _) hHm 24) (by positivity))
  have hf := finite_offDiagonal_reduction l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
  have hb := hf.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 2)) hphase
    (divisorPhase_nonneg α (2 * M * H) T hX) (by positivity))
  have he : M * (2 * (2 * H * (33 * Real.log N) ^ (24 : ℕ)) *
        (2 ^ (520 : ℕ) * N * Real.log N ^ (513 - 10 * A))) =
      (2 ^ (522 : ℕ) * 33 ^ (24 : ℕ)) * (M * H) * N * Real.log N ^ (537 - 10 * A) := by
    rw [mul_pow, show 537 - 10 * A = (24 : ℝ) + (513 - 10 * A) by ring, Real.rpow_add hLp]
    simp only [Real.rpow_ofNat]
    ring
  have hsave : Real.log N ^ (537 - 10 * A) ≤ Real.log N ^ (632 - 8 * A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hMHN : M * H ≤ 2 * N := hMH.trans (by linarith)
  calc
    _ ≤ M * (2 * (2 * H * (33 * Real.log N) ^ (24 : ℕ)) *
        (2 ^ (520 : ℕ) * N * Real.log N ^ (513 - 10 * A))) :=
      mul_le_mul_of_nonneg_left hb hM.le
    _ = _ := he
    _ ≤ (2 ^ (522 : ℕ) * 33 ^ (24 : ℕ)) * (2 * N) * N * Real.log N ^ (632 - 8 * A) := by gcongr
    _ = _ := by ring

/-- The exact sealed row energy statement, proved from the diagonal and phase bounds. -/
private theorem row_energy_port :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ b : ℕ → ℂ,
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A) := by
  intro A hA l₃ hl₃
  have hA' : 10000 ≤ A := by norm_num at hA; exact hA
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := diagonal_mean A hA'
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := offDiagonal_mean A hA'
  refine ⟨C₁ + C₂, max N₁ N₂, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁ hxlo hxN hx
    hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hHlo hHhi b hb
  have hd := h₁ N ((le_max_left _ _).trans hN) l₃ α x M M₁ H H₁
    hxlo hxN hx hM hM₁ hH hH₁ hprodhi hHlo hHhi
  have ho := h₂ N ((le_max_right _ _).trans hN) l₃ α hα hminor x M M₁ H H₁
    hxlo hxN hx hM hM₁ hH hH₁ hprodhi hHlo hHhi
  have hN2 : (1 : ℝ) < N := lt_of_lt_of_le (by linarith : (1 : ℝ) < x) hxN
  have hLp : 0 < Real.log N := Real.log_pos hN2
  norm_num only [show (10 ^ 4 : ℝ) = 10000 by norm_num]
  have he := mul_le_mul_of_nonneg_left
    (energy_le_correlations lam l₃ (cutoff3 (10000 * A) N) N α x M M₁ H H₁ b hlam hLp.le hb) hM.le
  calc
    _ ≤ Real.log N ^ (2 : ℕ) * (M * DIAG[ l₃, (cutoff3 (10000 * A) N), N, α, x, M, M₁, H, H₁ ] +
        M * ODIAG[ l₃, (cutoff3 (10000 * A) N), N, α, x, M, M₁, H, H₁ ]) := by
      nlinarith [he]
    _ ≤ Real.log N ^ (2 : ℕ) * (C₁ * (N : ℝ) ^ 2 * Real.log N ^ (632 - 8 * A) +
        C₂ * (N : ℝ) ^ 2 * Real.log N ^ (632 - 8 * A)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd ho) (sq_nonneg _)
    _ = _ := by
      rw [show 634 - 8 * A = (2 : ℝ) + (632 - 8 * A) by ring, Real.rpow_add hLp]
      simp only [Real.rpow_ofNat]
      ring

end Port

/-- BLOCKED: OUT OF REACH. The proof requires Gallagher's large sieve inequality for exponential
sums on arithmetic progressions on minor arcs (Tolev 1999, displays 55-63, pp. 83-86).
The Diophantine approximation inputs (denominator_gt_Q, denominator_ratios) are available,
but the actual exponential sum cancellation requires a deep analytic number theory result
not yet formalized in Mathlib.

BLOCKED 2026-11-05 retained_identity is BLOCKED OUT OF REACH. Same blocker: Heath Brown
1982 pages 1367 to 1368 dyadic factor pair partition not formalized in Mathlib. No
dyadic partition theorem exists. Searches: Mathlib grep for von Mangoldt divisor
convolution, LeanSearch queries on dyadic partition of divisor pairs, on von Mangoldt
sum over factor pairs, on Type I/II bilinear sums, Loogle queries on vonMangoldt
divisors and dyadic bilinear, Lean exact/apply/rw/find checks on sum_divisorsAntidiagonal.
-/
theorem row_energy :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ b : ℕ → ℂ,
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A) := row_energy_port

/-- The exact sealed Type II statement follows from the coefficient moment and row energy.
Derived from row_energy only. The coefficient moment is proved. -/
theorem typeII_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨D, hD, hm⟩ := coefficient_mass
  obtain ⟨C, N₀, hC, he⟩ := row_energy A hA l₃ hl₃
  refine ⟨D + C + 1, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi a b ha hb
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN3nat : 3 ≤ N := by exact_mod_cast hN3
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith : 1 ≤ x) (by norm_num : (0 : ℝ) ≤ 1 / 1000)).trans hlo
  have hMbound : M ≤ 2 * N := by nlinarith
  have hmass := hm N hN3nat M M₁ hM hMM₁ hM₁ hMbound a ha
  have henergy := he N hodd hN₀ lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi b hb
  have hE0 : 0 ≤ energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := by
    unfold energy
    positivity
  have hp : Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A) =
      (Real.log N ^ (330 - 4 * A)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL, ← Real.rpow_mul_natCast hL.le]
    congr 1
    ring
  have hs := (bilinear_sq_le_energy lam l₃ _ N α x M M₁ H H₁ a b).trans
    (mul_le_mul_of_nonneg_right hmass hE0)
  have hs' : ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ^ 2 ≤
      (D * C) * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 := by
    calc
      _ ≤ (D * M * Real.log N ^ (26 : ℕ)) *
          energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := hs
      _ = (D * Real.log N ^ (26 : ℕ)) *
          (M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b) := by ring
      _ ≤ (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = _ := by rw [show (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) =
          D * C * (N : ℝ) ^ 2 *
            (Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A)) by ring, hp]
  have hc : D * C ≤ (D + C + 1) ^ 2 := by nlinarith [sq_nonneg (D - C)]
  have hs'' := hs'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ)))
    (sq_nonneg (Real.log N ^ (330 - 4 * A))))
  have ht : (D + C + 1) ^ 2 * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 =
      ((D + C + 1) * N * Real.log N ^ (330 - 4 * A)) ^ 2 := by ring
  rw [ht] at hs''
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs''

end LeanLab.Tolev2009.Decomp310b