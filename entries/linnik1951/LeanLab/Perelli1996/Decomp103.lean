module

public import LeanLab.Perelli1996.Definitions103
public import LeanLab.Perelli1996.Parseval103
public import LeanLab.Perelli1996.Farey103
public import LeanLab.Perelli1996.NairMean103
public import LeanLab.Perelli1996.RamanujanInt400
public import LeanLab.Perelli1996.Tail320
public import LeanLab.Perelli1996.InverseTotient320
public import LeanLab.Perelli1996.PrincipalTail320
public import LeanLab.Perelli1996.B.Sing
public import LeanLab.PNTPort.Vinogradov.MajorArcUncond

/-!
P0083 Perelli 1996, pages 481 through 483.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Decomp103
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88
noncomputable section

/-- The divisor weight from equation 3 plus the logarithm from equation 2. -/
def majorWeight (m : ℕ) (N : ℝ) : ℝ :=
  (m : ℝ) * m.divisors.card / m.totient + Real.log N

/-- `1/(p-1)^2 <= 4/p^2` for `p >= 2`. -/
private theorem inv_sub_one_sq_le {p : ℝ} (hp : 2 ≤ p) : 1 / (p - 1) ^ 2 ≤ 4 / p ^ 2 := by
  have h1 : 0 < p - 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The product of the Sing factors converges at a positive argument. -/
private theorem multipliable_singBody {n : ℕ} (hn : n ≠ 0) :
    Multipliable (fun p : {p : ℕ // p.Prime} =>
      if p.1 ∣ n then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
  have hf : (fun p : {p : ℕ // p.Prime} =>
      if p.1 ∣ n then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2)
      = fun p => 1 + (if p.1 ∣ n then 1 / ((p.1 : ℝ) - 1)
        else -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    funext p; split_ifs <;> ring
  rw [hf]
  apply Real.multipliable_one_add_of_summable
  have hg : Summable (fun p : {p : ℕ // p.Prime} => 4 / ((p.1 : ℝ)) ^ 2) := by
    have : Summable (fun m : ℕ => 4 / ((m : ℝ)) ^ 2) := by
      simpa [div_eq_mul_inv] using
        (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2)).mul_left 4
    exact this.subtype _
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : {p : {p : ℕ // p.Prime} | ¬ (n < p.1)}.Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val) _ Subtype.val_injective.injOn
    apply (Set.finite_Iic n).subset
    rintro _ ⟨p, hp, rfl⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hp
    exact hp
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hp
  have hnd : ¬ p.1 ∣ n := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h) (by omega)
  have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
  rw [if_neg hnd, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_sub_one_sq_le h2

/-- `Sing m` written as the explicit prime product. -/
private theorem sing_as_tprod (m : ℕ) (hm : 0 < m) :
    (Sing m : ℂ) = ∏' p : {p : ℕ // p.Prime},
      ((if p.1 ∣ m then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 : ℝ) : ℂ) := by
  show ((∏' p : {p : ℕ // p.Prime},
      (if p.1 ∣ m then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) : ℝ) : ℂ) = _
  exact (multipliable_singBody hm.ne').map_tprod Complex.ofRealHom Complex.continuous_ofReal

open Finset

/-- **Growth on the window**: for admissible `F` there is `X₀ ≥ 0` with
`F(n) ≥ n^k / 2` for every natural `n ≥ X₀`. -/
private theorem poly_lower (F : ℤ[X]) (hF : Admissible F) :
    ∃ X₀ : ℝ, 0 ≤ X₀ ∧ ∀ n : ℕ, X₀ ≤ n → (n : ℝ) ^ F.natDegree / 2 ≤ (Fv F n : ℝ) := by
  set G := F.map (Int.castRingHom ℝ) with hGdef
  have hinj : Function.Injective (Int.castRingHom ℝ) := (Int.castRingHom ℝ).injective_int
  have hdeg : G.natDegree = F.natDegree := natDegree_map_eq_of_injective hinj F
  have hlc : G.leadingCoeff = (F.leadingCoeff : ℝ) := leadingCoeff_map_of_injective hinj F
  have hlc1 : (1 : ℝ) ≤ F.leadingCoeff := by exact_mod_cast hF.2
  have hE := (isEquivalent_atTop_lead (P := G)).isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hE
  refine ⟨max X 1, by positivity, fun n hn => ?_⟩
  have hnX : X ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  have hb := hX n hnX
  rw [hdeg, hlc] at hb
  have hev : eval (n : ℝ) G = (Fv F n : ℝ) := by
    have := eval_intCast_map (Int.castRingHom ℝ) F (n : ℤ)
    simp [Fv, hGdef]
  simp only [Pi.sub_apply, hev, Real.norm_eq_abs] at hb
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ F.natDegree := one_le_pow₀ hn1
  have hv : 0 < (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := by positivity
  rw [abs_of_pos hv] at hb
  have := (abs_le.1 hb).1
  nlinarith


open Finset

/-- The zero modulus contributes zero. -/
private theorem coefficient_zero (m : ℕ) : (((ArithmeticFunction.moebius (0 : ℕ) : ℂ) ^ 2 / ((0 : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (0 : ℕ) (m)) = 0 := by simp

/-- The modulus one contributes one. -/
private theorem coefficient_one (m : ℕ) : (((ArithmeticFunction.moebius (1 : ℕ) : ℂ) ^ 2 / ((1 : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (1 : ℕ) (m)) = 1 := by
  rw [Ramanujan103.ramanujanSum_dvd 1 m (by norm_num) (one_dvd m)]
  simp

/-- The coefficient is multiplicative in its modulus. -/
private theorem coefficient_mul (m q r : ℕ) (hcop : Nat.Coprime q r) :
    (((ArithmeticFunction.moebius ((q * r) : ℕ) : ℂ) ^ 2 / (((q * r) : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum ((q * r) : ℕ) (m)) = (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)) * (((ArithmeticFunction.moebius (r : ℕ) : ℂ) ^ 2 / ((r : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (r : ℕ) (m)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [coefficient_zero]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [coefficient_zero]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.totient_mul hcop, Ramanujan103.ramanujanSum_mul q r m hq hr hcop]
  push_cast
  ring

/-- The coefficient vanishes at nonsquarefree moduli. -/
private theorem coefficient_nonsquarefree (m q : ℕ) (hq : ¬ Squarefree q) : (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)) = 0 := by
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

/-- The prime factor of the Ramanujan series is the prime factor of Sing. -/
private theorem coefficient_prime (m p : ℕ) (hp : p.Prime) :
    1 + (((ArithmeticFunction.moebius (p : ℕ) : ℂ) ^ 2 / ((p : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (p : ℕ) (m)) = ((if p ∣ m then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1R : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp1 : (p : ℂ) - 1 ≠ 0 := by exact_mod_cast hp1R
  rw [ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp, Ramanujan103.ramanujanSum_prime p m hp]
  rw [Nat.cast_sub hp.one_le]
  simp only [Nat.cast_one, Int.cast_neg, Int.cast_one, neg_one_sq]
  split_ifs <;> push_cast <;> field_simp <;> ring

/-- The norm of every finite coefficient tail obeys the divisor totient majorant. -/
private theorem sum_norm_tail (m : ℕ) (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : ℝ, 0 < P → ∀ s : Finset ℕ,
      (∀ q ∈ s, 0 < q ∧ P < (q : ℝ)) →
      (∑ q ∈ s, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖) ≤
        K / P * ((m : ℝ) * m.divisors.card / m.totient) := by
  obtain ⟨K, hK, htail⟩ := InverseTotient320.inverse_totient_sq_tail
  refine ⟨K, hK, ?_⟩
  intro P hP s hs
  calc
    _ ≤ ∑ q ∈ s, 1 / ((q.totient : ℝ) * (q / Nat.gcd q m).totient) :=
      Finset.sum_le_sum (fun q hq => Ramanujan400.norm_weighted_ramanujanSum_le q m (hs q hq).1)
    _ ≤ _ := Tail320.finite_totient_tail m hm P K hP htail s hs

/-- The Ramanujan coefficient series is absolutely convergent at a positive frequency. -/
private theorem summable_norm_coefficient (m : ℕ) (hm : 0 < m) :
    Summable (fun q : ℕ => ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖) := by
  obtain ⟨K, hK, htail⟩ := sum_norm_tail m hm
  apply summable_of_sum_le (fun q => norm_nonneg _) (c := K / (1 / 2) *
    ((m : ℝ) * m.divisors.card / m.totient))
  intro s
  have hfilter : (∑ q ∈ s, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖) =
      ∑ q ∈ s.filter (fun q => 0 < q), ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnot
    have hq0 : q = 0 := by simp only [Finset.mem_filter, hq, true_and] at hnot; omega
    simp [hq0, coefficient_zero]
  rw [hfilter]
  apply htail (1 / 2) (by norm_num)
  intro q hq
  have hpos := (Finset.mem_filter.mp hq).2
  refine ⟨hpos, ?_⟩
  have h : (1 : ℝ) ≤ q := by exact_mod_cast hpos
  linarith

/-- The full Ramanujan series is the existing prime product Sing. -/
private theorem tsum_coefficient (m : ℕ) (hm : 0 < m) :
    (∑' q : ℕ, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) = (Sing m : ℂ) := by
  have heuler := EulerProduct.eulerProduct_tprod (f := fun q : ℕ => (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) (coefficient_one m)
    (fun {_ _} h => coefficient_mul m _ _ h) (summable_norm_coefficient m hm) (coefficient_zero m)
  have hfactor (p : Nat.Primes) : (∑' e : ℕ, (((ArithmeticFunction.moebius ((p.1 ^ e) : ℕ) : ℂ) ^ 2 / (((p.1 ^ e) : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum ((p.1 ^ e) : ℕ) (m))) =
      ((if p.1 ∣ m then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 : ℝ) : ℂ) := by
    have hzero (e : ℕ) (he : e ∉ ({0, 1} : Finset ℕ)) : (((ArithmeticFunction.moebius ((p.1 ^ e) : ℕ) : ℂ) ^ 2 / (((p.1 ^ e) : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum ((p.1 ^ e) : ℕ) (m)) = 0 := by
      apply coefficient_nonsquarefree
      have he2 : 2 ≤ e := by simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega
      rw [Nat.squarefree_pow_iff p.2.ne_one (by omega)]
      simp only [not_and]
      intro _
      omega
    rw [tsum_eq_sum hzero, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), pow_zero, pow_one,
      coefficient_one]
    simpa only using coefficient_prime m p.1 p.2
  calc
    _ = ∏' p : Nat.Primes, ∑' e : ℕ, (((ArithmeticFunction.moebius ((p.1 ^ e) : ℕ) : ℂ) ^ 2 / (((p.1 ^ e) : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum ((p.1 ^ e) : ℕ) (m)) := heuler.symm
    _ = ∏' p : Nat.Primes, ((if p.1 ∣ m then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 : ℝ) : ℂ) := tprod_congr hfactor
    _ = (Sing m : ℂ) := (sing_as_tprod m hm).symm

/-- The finite singular series approximates Sing with the exact inverse cutoff loss. -/
private theorem partial_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ P : ℝ, 1 ≤ P →
      ‖(Sing m : ℂ) - ∑ q ∈ Icc 1 ⌊P⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ ≤
        K * ((m : ℝ) * m.divisors.card / m.totient) / P := by
  obtain ⟨K, hK, htail⟩ := InverseTotient320.inverse_totient_sq_tail
  refine ⟨K, hK, ?_⟩
  intro m hm P hP
  have hP0 : 0 < P := by linarith
  have hnorm := summable_norm_coefficient m hm
  have hs := hnorm.of_norm
  let s := Icc 1 ⌊P⌋₊
  have hsplit := hs.sum_add_tsum_subtype_compl s
  rw [tsum_coefficient m hm] at hsplit
  have hid : (Sing m : ℂ) - ∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)) =
      ∑' q : {q : ℕ // q ∉ s}, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)) := by
    rw [← hsplit]
    ring
  rw [hid]
  calc
    _ ≤ ∑' q : {q : ℕ // q ∉ s}, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ :=
      norm_tsum_le_tsum_norm (hnorm.subtype _)
    _ ≤ K * ((m : ℝ) * m.divisors.card / m.totient) / P := by
      apply Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
      intro u
      let v : Finset ℕ := (u.image Subtype.val).filter (fun q => 0 < q)
      have hmap : (∑ q ∈ u, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖) = ∑ q ∈ v, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ := by
        calc
          _ = ∑ q ∈ u.image Subtype.val, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ :=
            (Finset.sum_image (f := fun q : ℕ => ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖)
              (fun a _ b _ h => Subtype.ext h)).symm
          _ = ∑ q ∈ v, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro q hq hnot
            have hq0 : q = 0 := by simp only [Finset.mem_filter, hq, true_and] at hnot; omega
            simp [hq0, coefficient_zero]
      rw [hmap]
      have hv : ∀ q ∈ v, 0 < q ∧ P < (q : ℝ) := by
        intro q hq
        obtain ⟨hqmem, hqpos⟩ := Finset.mem_filter.mp hq
        obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hqmem
        have hnot := r.2
        have hqfloor : ⌊P⌋₊ < q := by
          simp only [s, Finset.mem_Icc] at hnot
          rw [hrq] at hnot
          omega
        refine ⟨hqpos, ?_⟩
        exact (Nat.lt_floor_add_one P).trans_le (by exact_mod_cast (show ⌊P⌋₊ + 1 ≤ q by omega))
      calc
        _ ≤ ∑ q ∈ v, 1 / ((q.totient : ℝ) * (q / Nat.gcd q m).totient) :=
          Finset.sum_le_sum (fun q hq => Ramanujan400.norm_weighted_ramanujanSum_le q m (hv q hq).1)
        _ ≤ K / P * ((m : ℝ) * m.divisors.card / m.totient) :=
          Tail320.finite_totient_tail m hm P K hP0 htail v hv
        _ = _ := by ring


open Finset Real MeasureTheory
open LeanLab.Perelli1996.Decomp88

/-- An integer phase is trivial. -/
private theorem e_intCast (k : ℤ) : Kernel.e (k : ℝ) = 1 := by
  unfold Kernel.e
  rw [show Complex.I * ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) = k * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- The additive kernel has modulus one. -/
private theorem norm_e (x : ℝ) : ‖Kernel.e x‖ = 1 := by
  simp [Kernel.e, Complex.norm_exp]

/-- Integer frequencies are periodic with period one. -/
private theorem e_int_mul_add_one (k : ℤ) (x : ℝ) : Kernel.e ((k : ℝ) * (x + 1)) = Kernel.e ((k : ℝ) * x) := by
  rw [mul_add, mul_one, Parseval103.e_add, e_intCast, mul_one]

/-- The coefficient integrand is continuous. -/
private theorem coefficientIntegrand_continuous (M m : ℕ) : Continuous (coefficientIntegrand M m) := by
  unfold coefficientIntegrand primeSum Kernel.e
  fun_prop

/-- The coefficient integrand has period one. -/
private theorem coefficientIntegrand_periodic (M m : ℕ) :
    Function.Periodic (coefficientIntegrand M m) 1 := by
  intro α
  unfold coefficientIntegrand primeSum
  have h1 : ∀ n : ℕ, Kernel.e ((n : ℝ) * (α + 1)) = Kernel.e ((n : ℝ) * α) := fun n => by
    simpa using e_int_mul_add_one (n : ℤ) α
  have h2 : Kernel.e (-(m : ℝ) * (α + 1)) = Kernel.e (-(m : ℝ) * α) := by
    simpa using e_int_mul_add_one (-(m : ℤ)) α
  simp only [h1, h2]

/-- The principal model weight mu q over phi q has modulus at most one. -/
private theorem norm_model_le (q : ℕ) (hq : 0 < q) :
    ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  rw [norm_div]
  have hμ : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hφn : ‖(q.totient : ℂ)‖ = q.totient := by simp
  rw [hφn, div_le_one (by linarith)]
  linarith

/-- The prime sum of page 480 is the lab's Vinogradov sum S, since Lambda 0 is zero. -/
private theorem primeSum_eq_S (M : ℕ) (α : ℝ) : primeSum M α = LeanLab.PNTPort.Vinogradov.S M α := by
  unfold primeSum LeanLab.PNTPort.Vinogradov.S
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_range]
    omega
  · intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_range] at hx hx'
    have : x = 0 := by omega
    subst this
    simp

/-- The kernel T on 0 to M is one plus the lab's Vinogradov kernel V. -/
private theorem T_eq_one_add_V (M : ℕ) (η : ℝ) :
    Kernel.T 0 (M + 1) η = 1 + LeanLab.PNTPort.Vinogradov.V M η := by
  unfold Kernel.T LeanLab.PNTPort.Vinogradov.V
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [Kernel.e]
  · have hI : Finset.Icc 1 M = Finset.Ico (0 + 1) (M + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI, ← Finset.sum_Ico_add' (fun n : ℕ => LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * η)) 0 M 1,
      ← Finset.range_eq_Ico]
    apply Finset.sum_congr rfl
    intro n _
    simp only [zero_add]
    rfl

set_option maxHeartbeats 1600000 in
/-- Page 481 equation 2 via Vaughan 1981 Chapter 3, Lemma 3.1, from the
Siegel Walfisz theorem with partial summation: on the arc at a over q with q at most
L^B, the prime sum equals mu q over phi q times the kernel T up to an error saving any
fixed power of L. The radius L^B over N keeps the partial summation factor 1 plus N
times eta below a power of L. PROVED from LeanLab.PNTPort.Vinogradov.major_arc, which rests on
the lab's unconditional PNTPort.PsiChi.siegelWalfisz. -/
private theorem leaf_arc_pointwise (c : ℝ) (hc : 0 < c) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ B → ∀ a : ℕ, Nat.Coprime a q → ∀ η : ℝ,
      |η| ≤ Real.log N ^ B / N →
      ‖primeSum ⌊c * N⌋₊ ((a : ℝ) / q + η) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          Kernel.T 0 (⌊c * N⌋₊ + 1) η‖ ≤ C * N * Real.log N ^ (-A) := by
  obtain ⟨c', hc', K, hK, hmaj⟩ := LeanLab.PNTPort.Vinogradov.major_arc (B + 1) (by positivity)
  set D := A + 2 * B with hD
  have hF1 := (isLittleO_log_rpow_rpow_atTop (D + 2) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hF1
  have hsq : Filter.Tendsto (fun N : ℝ => Real.sqrt (Real.log N)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hF2 := (isLittleO_rpow_exp_pos_mul_atTop (2 * D) (by positivity : 0 < c' / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hsq.eventually hF2)
  set N₀ := max (max 3 (max N₁ N₂))
    (max ((2 * Real.exp 4 + 2) / c) (Real.exp (2 * |Real.log (c / 2)| + 2 ^ (B + 1) + 1)))
    with hN₀def
  set C := (1 + 2 * π * c) * (7 * Real.sqrt c + K * c + (|Real.log c| + 1) / Real.log 2) + 2
    with hCdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, N₀, by positivity, (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro N hN q hq hqL a hcop η hη
  have hN3 : 3 ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN1' : N₁ ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hN
  have hN2' : N₂ ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hN
  have hNc : (2 * Real.exp 4 + 2) / c ≤ N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNe : Real.exp (2 * |Real.log (c / 2)| + 2 ^ (B + 1) + 1) ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hLdef
  have hLbig : 2 * |Real.log (c / 2)| + 2 ^ (B + 1) + 1 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hNe
    rwa [Real.log_exp] at this
  have h2B : (0 : ℝ) < 2 ^ (B + 1) := by positivity
  have habs : 0 ≤ |Real.log (c / 2)| := abs_nonneg _
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hcN : 2 * Real.exp 4 + 2 ≤ c * N := by
    have := (div_le_iff₀ hc).mp hNc
    linarith
  set M := ⌊c * N⌋₊ with hMdef
  have hMhi : (M : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hMlt : c * N < M + 1 := Nat.lt_floor_add_one _
  have he4 : 0 < Real.exp 4 := Real.exp_pos 4
  have hMlo : c * N / 2 ≤ M := by linarith
  have hM4 : Real.exp 4 ≤ M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  set LM := Real.log M with hLMdef
  have hLMlo : L / 2 ≤ LM := by
    have h1 := Real.log_le_log (by positivity) hMlo
    rw [show c * N / 2 = (c / 2) * N by ring, Real.log_mul (by positivity) hN0.ne'] at h1
    have : -|Real.log (c / 2)| ≤ Real.log (c / 2) := neg_abs_le _
    linarith
  have hLMhi : LM ≤ (|Real.log c| + 1) * L := by
    have h1 := Real.log_le_log hMpos hMhi
    rw [Real.log_mul hc.ne' hN0.ne'] at h1
    have : Real.log c ≤ |Real.log c| := le_abs_self _
    nlinarith [abs_nonneg (Real.log c)]
  -- the modulus condition of the major arc lemma
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hL1 hB.le
  have hq' : (q : ℝ) ≤ LM ^ (B + 1) := by
    have h1 : L ^ B ≤ (L / 2) ^ (B + 1) := by
      rw [Real.div_rpow hL.le (by norm_num), Real.rpow_add_one hL.ne', Real.rpow_add_one
        (by norm_num : (2 : ℝ) ≠ 0)]
      rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)] at h2B hLbig
      have hLB : 0 < L ^ B := by positivity
      have h2 : (0 : ℝ) < 2 ^ B := by positivity
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (show 2 ^ B * 2 ≤ L by linarith) hLB.le]
    have h2 : (L / 2) ^ (B + 1) ≤ LM ^ (B + 1) :=
      Real.rpow_le_rpow (by positivity) hLMlo (by positivity)
    linarith
  have hmaj' := hmaj M hM4 q hq hq' (a : ℤ) (Nat.isCoprime_iff_coprime.mpr hcop) η
  simp only [Int.cast_natCast] at hmaj'
  rw [primeSum_eq_S, T_eq_one_add_V]
  set d : ℂ := (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) with hd
  have hdn : ‖d‖ ≤ 1 := norm_model_le q hq
  have hsplit : LeanLab.PNTPort.Vinogradov.S M (a / q + η) - d * (1 +
      LeanLab.PNTPort.Vinogradov.V M η) =
      (LeanLab.PNTPort.Vinogradov.S M (a / q + η) - d * LeanLab.PNTPort.Vinogradov.V M η) - d := by
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  -- bounds on the pieces of the major arc error
  set E := Real.exp (-c' * (Real.sqrt L / 2)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hY : 1 + 2 * π * |η| * M ≤ (1 + 2 * π * c) * L ^ B := by
    have h1 : |η| * M ≤ c * L ^ B := by
      calc |η| * M ≤ (L ^ B / N) * (c * N) := mul_le_mul hη hMhi (by positivity) (by positivity)
        _ = c * L ^ B := by field_simp
    nlinarith [Real.pi_pos]
  have hsqM : Real.sqrt M ≤ Real.sqrt c * Real.sqrt N := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hMhi
  have hEM : Real.exp (-c' * Real.sqrt (LM / 2)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.sqrt L / 2 ≤ Real.sqrt (LM / 2) := by
      have h4 : Real.sqrt L / 2 = Real.sqrt (L / 4) := by
        rw [Real.sqrt_div' L (by norm_num : (0 : ℝ) ≤ 4),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  have hlogq : Real.log q ≤ L ^ B := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)
    linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hLM0 : 0 ≤ LM := by linarith
  have hbr : 7 * Real.sqrt M + q * K * M * Real.exp (-c' * Real.sqrt (LM / 2)) +
      Real.log q / Real.log 2 * LM ≤
      7 * Real.sqrt c * Real.sqrt N + L ^ B * K * (c * N) * E +
        L ^ B * ((|Real.log c| + 1) * L) / Real.log 2 := by
    have t1 : 7 * Real.sqrt M ≤ 7 * Real.sqrt c * Real.sqrt N := by nlinarith
    have t2 : q * K * M * Real.exp (-c' * Real.sqrt (LM / 2)) ≤ L ^ B * K * (c * N) * E := by
      have := Real.exp_pos (-c' * Real.sqrt (LM / 2))
      gcongr
    have t3 : Real.log q / Real.log 2 * LM ≤ L ^ B * ((|Real.log c| + 1) * L) / Real.log 2 := by
      rw [div_mul_eq_mul_div]
      gcongr
    linarith
  -- the four comparisons with N L^(-A)
  have hLA : L ^ A * L ^ (-A) = 1 := by
    rw [Real.rpow_neg hL.le, mul_inv_cancel₀ (by positivity)]
  have hW0 : 0 < L ^ (-A) := by positivity
  have hF1N := hN₁ N hN1'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul] at hF1N
  have hsqN : Real.sqrt N = N ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow N
  have hsqN1 : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left]
    · nlinarith
    · linarith
  have hsqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hmono : ∀ x : ℝ, x ≤ D + 2 → L ^ x ≤ Real.sqrt N := fun x hx => by
    rw [hsqN]
    exact (Real.rpow_le_rpow_of_exponent_le hL1 hx).trans hF1N
  have w1 : Real.sqrt N * L ^ B ≤ N * L ^ (-A) := by
    have h1 : L ^ B * L ^ A ≤ Real.sqrt N := by
      rw [← Real.rpow_add hL]
      exact hmono _ (by rw [hD]; linarith)
    calc Real.sqrt N * L ^ B = Real.sqrt N * (L ^ B * L ^ A) * L ^ (-A) := by
          linear_combination (-(Real.sqrt N * L ^ B)) * hLA
      _ ≤ Real.sqrt N * Real.sqrt N * L ^ (-A) := by gcongr
      _ = N * L ^ (-A) := by rw [hsqsq]
  have w2 : L ^ B * L ^ B * E * N ≤ N * L ^ (-A) := by
    have hF2N := hN₂ N hN2'
    simp only [Real.norm_eq_abs] at hF2N
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), one_mul] at hF2N
    have hpow : Real.sqrt L ^ (2 * D) = L ^ D := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
      congr 1
      ring
    rw [hpow] at hF2N
    have h1 : L ^ B * L ^ B * L ^ A ≤ Real.exp (c' * (Real.sqrt L / 2)) := by
      rw [← Real.rpow_add hL, ← Real.rpow_add hL]
      calc L ^ (B + B + A) = L ^ D := by rw [hD]; congr 1; ring
        _ ≤ _ := by convert hF2N using 2; ring
    have hEE : Real.exp (c' * (Real.sqrt L / 2)) * E = 1 := by
      rw [hEdef, ← Real.exp_add]
      simp
    calc L ^ B * L ^ B * E * N = (L ^ B * L ^ B * L ^ A) * E * N * L ^ (-A) := by
          linear_combination (-(L ^ B * L ^ B * E * N)) * hLA
      _ ≤ Real.exp (c' * (Real.sqrt L / 2)) * E * N * L ^ (-A) := by gcongr
      _ = N * L ^ (-A) := by rw [hEE]; ring
  have w3 : L ^ B * L ^ B * L ≤ N * L ^ (-A) := by
    have h1 : L ^ B * L ^ B * L * L ^ A ≤ N := by
      have : L ^ B * L ^ B * L * L ^ A = L ^ (B + B + 1 + A) := by
        rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_one]
      rw [this]
      exact (hmono _ (by rw [hD]; linarith)).trans hsqN1
    calc L ^ B * L ^ B * L = (L ^ B * L ^ B * L * L ^ A) * L ^ (-A) := by
          linear_combination (-(L ^ B * L ^ B * L)) * hLA
      _ ≤ N * L ^ (-A) := by gcongr
  have w4 : 1 ≤ N * L ^ (-A) := by
    have h1 : L ^ A ≤ N := (hmono _ (by rw [hD]; linarith)).trans hsqN1
    calc (1 : ℝ) = L ^ A * L ^ (-A) := hLA.symm
      _ ≤ N * L ^ (-A) := by gcongr
  have hY0 : 0 ≤ 1 + 2 * π * |η| * M := by positivity
  have hbr0 : 0 ≤ 7 * Real.sqrt c * Real.sqrt N + L ^ B * K * (c * N) * E +
        L ^ B * ((|Real.log c| + 1) * L) / Real.log 2 := by positivity
  have hX := mul_le_mul hbr hY hY0 hbr0
  have hexpand : (7 * Real.sqrt c * Real.sqrt N + L ^ B * K * (c * N) * E +
        L ^ B * ((|Real.log c| + 1) * L) / Real.log 2) * ((1 + 2 * π * c) * L ^ B) =
      (1 + 2 * π * c) * (7 * Real.sqrt c * (Real.sqrt N * L ^ B) +
        K * c * (L ^ B * L ^ B * E * N) +
        (|Real.log c| + 1) / Real.log 2 * (L ^ B * L ^ B * L)) := by
    field_simp
  rw [hexpand] at hX
  have hk1 : 0 ≤ 1 + 2 * π * c := by positivity
  have hk2 : 0 ≤ 7 * Real.sqrt c := by positivity
  have hk3 : 0 ≤ K * c := by positivity
  have hk4 : 0 ≤ (|Real.log c| + 1) / Real.log 2 := by positivity
  have hsum : 7 * Real.sqrt c * (Real.sqrt N * L ^ B) + K * c * (L ^ B * L ^ B * E * N) +
      (|Real.log c| + 1) / Real.log 2 * (L ^ B * L ^ B * L) ≤
      (7 * Real.sqrt c + K * c + (|Real.log c| + 1) / Real.log 2) * (N * L ^ (-A)) := by
    have := mul_le_mul_of_nonneg_left w1 hk2
    have := mul_le_mul_of_nonneg_left w2 hk3
    have := mul_le_mul_of_nonneg_left w3 hk4
    nlinarith
  have hX2 := hX.trans (mul_le_mul_of_nonneg_left hsum hk1)
  calc _ ≤ (1 + 2 * π * c) * ((7 * Real.sqrt c + K * c + (|Real.log c| + 1) / Real.log 2) *
          (N * L ^ (-A))) + 1 := add_le_add (hmaj'.trans hX2) hdn
    _ ≤ C * N * L ^ (-A) := by
      rw [hCdef]
      nlinarith

/-- Coprimality of an integer numerator with a natural modulus. -/
private theorem coprime_iff_isCoprime (a : ℤ) (q : ℕ) : Nat.Coprime a.natAbs q ↔ IsCoprime a (q : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  rfl

/-- Page 480: the primary major arcs are invariant under translation by one. -/
private theorem mem_majorArcs_add_one (N B α : ℝ) : α + 1 ∈ majorArcs N B ↔ α ∈ majorArcs N B := by
  constructor
  · rintro ⟨q, hq, hqB, a, hcop, hα⟩
    refine ⟨q, hq, hqB, a - q, ?_, ?_⟩
    · rw [coprime_iff_isCoprime] at hcop ⊢
      have := hcop.add_mul_left_left (-1)
      rwa [mul_neg_one, ← sub_eq_add_neg] at this
    · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have : α - ((a - q : ℤ) : ℝ) / q = α + 1 - (a : ℝ) / q := by
        push_cast; field_simp; ring
      rwa [this]
  · rintro ⟨q, hq, hqB, a, hcop, hα⟩
    refine ⟨q, hq, hqB, a + q, ?_, ?_⟩
    · rw [coprime_iff_isCoprime] at hcop ⊢
      have := hcop.add_mul_left_left 1
      rwa [mul_one] at this
    · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have : α + 1 - ((a + q : ℤ) : ℝ) / q = α - (a : ℝ) / q := by
        push_cast; field_simp; ring
      rwa [this]

/-- Page 480: two primary arcs with moduli at most P and radius r, 2 r P^2 below one, meet
only when they are the same arc. -/
private theorem arcs_eq_of_mem (P r : ℝ) (hsmall : 2 * r * (P * P) < 1) (q q' a a' : ℕ)
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqP : (q : ℝ) ≤ P) (hqP' : (q' : ℝ) ≤ P)
    (hc : Nat.Coprime a q) (hc' : Nat.Coprime a' q') (x : ℝ)
    (hx : x ∈ Set.Icc ((a : ℝ) / q - r) ((a : ℝ) / q + r))
    (hx' : x ∈ Set.Icc ((a' : ℝ) / q' - r) ((a' : ℝ) / q' + r)) : q = q' ∧ a = a' := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hdiff : |(a : ℝ) / q - (a' : ℝ) / q'| ≤ 2 * r := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  have hk : ((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ) = ((a : ℝ) / q - (a' : ℝ) / q') * (q * q') := by
    push_cast; field_simp
  have hqq : (q : ℝ) * q' ≤ P * P := mul_le_mul hqP hqP' hq0'.le (hq0.le.trans hqP)
  have hbound : |((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ)| < 1 := by
    rw [hk, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
    have hr0 : 0 ≤ r := by linarith [abs_nonneg ((a : ℝ) / q - (a' : ℝ) / q')]
    calc |(a : ℝ) / q - (a' : ℝ) / q'| * (q * q') ≤ 2 * r * (q * q') := by gcongr
      _ ≤ 2 * r * (P * P) := by gcongr
      _ < 1 := hsmall
  have heq : a * q' = a' * q := by
    rw [abs_lt] at hbound
    have h1 : ((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) < 1 := by
      have := hbound.2; exact_mod_cast this
    have h2 : -1 < ((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) := by
      have := hbound.1; exact_mod_cast this
    omega
  have hd1 : q ∣ q' := by
    have : q ∣ q' * a := ⟨a', by rw [mul_comm q' a, heq, mul_comm]⟩
    exact hc.symm.dvd_of_dvd_mul_right this
  have hd2 : q' ∣ q := by
    have : q' ∣ q * a' := ⟨a, by rw [mul_comm q a', ← heq, mul_comm]⟩
    exact hc'.symm.dvd_of_dvd_mul_right this
  have hqq' : q = q' := Nat.dvd_antisymm hd1 hd2
  refine ⟨hqq', ?_⟩
  subst hqq'
  exact Nat.eq_of_mul_eq_mul_right hq heq

/-- PROVED. Page 480, definition of the primary major arcs: for N large the arcs at a over q
with q at most L^B and radius L^B over N are disjoint, the arcs at 0 and 1 join by
periodicity, and the integral over the major arcs in the unit interval is the sum of the
integrals over the single arcs, indexed by q at most L^B and the reduced residues a. -/
private theorem leaf_arc_integral_split (B : ℝ) (hB : 0 < B) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ f : ℝ → ℂ, Continuous f →
      Function.Periodic f 1 →
      ∫ α in Set.Icc 0 1 ∩ majorArcs N B, f α =
        ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-(Real.log N ^ B / N))..(Real.log N ^ B / N), f ((a : ℝ) / q + η) := by
  have hF := (isLittleO_log_rpow_rpow_atTop (3 * B) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hF
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N hN f hf hper
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  set P := Real.log N ^ B with hP
  set r := P / N with hr
  have hP0 : 0 < P := by positivity
  have hr0 : 0 < r := by positivity
  have hsmall : 2 * r * (P * P) < 1 := by
    have h1 := hN₁ N ((le_max_right _ _).trans hN)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), Real.rpow_one] at h1
    have h3 : Real.log N ^ (3 * B) = P * P * P := by
      rw [hP, ← Real.rpow_add hL, ← Real.rpow_add hL]; congr 1; ring
    rw [h3] at h1
    have : 2 * r * (P * P) = 2 * (P * P * P) / N := by rw [hr]; field_simp
    rw [this, div_lt_one hN0]
    linarith
  have hqr : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → 2 * r * q < 1 := by
    intro q hq hqP
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have : (q : ℝ) ≤ P * P := by nlinarith
    calc 2 * r * q ≤ 2 * r * (P * P) := by gcongr
      _ < 1 := hsmall
  have hinv : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → 2 * r < 1 / q := by
    intro q hq hqP
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    rw [lt_div_iff₀ hq0]
    exact hqr q hq hqP
  have hMA : MeasurableSet (majorArcs N B) := by
    unfold majorArcs; measurability
  have hgper : Function.Periodic ((majorArcs N B).indicator f) 1 := by
    intro α
    simp only [Set.indicator, hper α]
    by_cases h : α ∈ majorArcs N B
    · rw [if_pos ((mem_majorArcs_add_one N B α).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((mem_majorArcs_add_one N B α).mp h')), if_neg h]
  set Q := ⌊P⌋₊ with hQ
  let idx := (Icc 1 Q).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))
  let J : (Σ _ : ℕ, ℕ) → Set ℝ := fun i => Set.Icc ((i.2 : ℝ) / i.1 - r) ((i.2 : ℝ) / i.1 + r)
  have hmemidx : ∀ i ∈ idx, 1 ≤ i.1 ∧ (i.1 : ℝ) ≤ P ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    intro i hi
    simp only [idx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1.1, (Nat.cast_le.mpr hi.1.2).trans (Nat.floor_le hP0.le), hi.2.1, hi.2.2⟩
  have step1 : ∫ α in Set.Icc 0 1 ∩ majorArcs N B, f α =
      ∫ α in (0 : ℝ)..1, (majorArcs N B).indicator f α := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator hMA]
  have step2 : ∫ α in (0 : ℝ)..1, (majorArcs N B).indicator f α =
      ∫ α in Set.Ioc (-r) (-r + 1) ∩ majorArcs N B, f α := by
    have := hgper.intervalIntegral_add_eq 0 (-r)
    rw [zero_add] at this
    rw [this, intervalIntegral.integral_of_le (by linarith), setIntegral_indicator hMA]
  have hae : (Set.Ioc (-r) (-r + 1) ∩ majorArcs N B : Set ℝ) =ᵐ[volume] ⋃ i ∈ idx, J i := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · apply measure_mono_null _ (measure_singleton (-r + 1))
      rintro α ⟨⟨⟨hlo, hhi⟩, q, hq, hqP, a, hcop, hα⟩, hU⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      apply hU
      rw [abs_le] at hα
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
      have h2r := hinv q hq hqP
      rcases lt_or_ge a 0 with ha | ha
      · exfalso
        have ha1 : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
        have : (a : ℝ) / q ≤ -1 / q := div_le_div_of_nonneg_right ha1 hq0.le
        have h1q : -1 / (q : ℝ) = -(1 / q) := by ring
        linarith
      rcases lt_or_ge a q with haq | haq
      · lift a to ℕ using ha
        simp only [Set.mem_iUnion]
        refine ⟨⟨q, a⟩, ?_, ?_⟩
        · simp only [idx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
          refine ⟨⟨hq, Nat.le_floor hqP⟩, by exact_mod_cast haq, ?_⟩
          simpa using hcop
        · simp only [J, Set.mem_Icc]
          push_cast at hα
          constructor <;> linarith
      · exfalso
        have ha1 : (q : ℝ) ≤ a := by exact_mod_cast haq
        have : (1 : ℝ) ≤ (a : ℝ) / q := by rw [le_div_iff₀ hq0]; linarith
        apply hne
        linarith
    · apply measure_mono_null _ (measure_singleton (-r))
      intro α hα
      simp only [Set.mem_diff, Set.mem_iUnion] at hα
      obtain ⟨⟨i, hi, hαi⟩, hn⟩ := hα
      obtain ⟨hq1, hqP, haq, hcop⟩ := hmemidx i hi
      rw [Set.mem_singleton_iff]
      by_contra hne
      apply hn
      have hq0 : (0 : ℝ) < i.1 := by exact_mod_cast hq1
      have h2r := hinv i.1 hq1 hqP
      simp only [J, Set.mem_Icc] at hαi
      have ha0 : (0 : ℝ) ≤ (i.2 : ℝ) / i.1 := by positivity
      have haq' : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast haq
      have hfrac0 : (i.2 : ℝ) / i.1 ≤ ((i.1 : ℝ) - 1) / i.1 :=
        div_le_div_of_nonneg_right (by linarith) hq0.le
      have hfrace : ((i.1 : ℝ) - 1) / i.1 = 1 - 1 / i.1 := by field_simp
      refine ⟨⟨lt_of_le_of_ne (by linarith) (Ne.symm hne), by linarith⟩, i.1, hq1, hqP,
        (i.2 : ℤ), by simpa using hcop, ?_⟩
      rw [abs_le]; push_cast; constructor <;> linarith
  have hdisj : Set.Pairwise (↑idx) (Function.onFun Disjoint J) := by
    intro i hi j hj hij
    show Disjoint (J i) (J j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨hq1, hqP, -, hcop⟩ := hmemidx i hi
    obtain ⟨hq1', hqP', -, hcop'⟩ := hmemidx j hj
    obtain ⟨h1, h2⟩ := arcs_eq_of_mem P r hsmall i.1 j.1 i.2 j.2 hq1 hq1' hqP hqP' hcop hcop'
      x hxi hxj
    exact hij (Sigma.ext h1 (heq_of_eq h2))
  rw [step1, step2, setIntegral_congr_set hae,
    integral_biUnion_finset idx (fun i _ => measurableSet_Icc) hdisj
      (fun i _ => hf.integrableOn_Icc), Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  simp only [J]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_left f ((a : ℝ) / q), sub_eq_add_neg]

/-- Page 481 equation 2: the Ramanujan coefficient as a sum over reduced residues of the
squared principal model weight times the phase at minus m a over q. -/
private theorem coefficient_eq_sum (m q : ℕ) (hq : 0 < q) :
    (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
          Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) := by
  have h := RamanujanInt400.ramanujanSumInt_eq_natAbs q (-(m : ℤ)) hq
  simp only [Int.natAbs_neg, Int.natAbs_natCast] at h
  rw [← h, RamanujanInt400.ramanujanSumInt, Finset.mul_sum, div_pow]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  push_cast
  ring

/-- Page 481 equation 2, PROVED from leaf_arc_pointwise and leaf_arc_integral_split, both proved:
the major arc integral of the coefficient integrand is the finite singular partial sum
times the central kernel integral, up to N L^(-A/2). The error on each arc is the
pointwise error times twice the kernel bound times the arc length, and there are at
most L^(2B) arcs. -/
private theorem arc_model (c : ℝ) (hc : 0 < c) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ m : ℕ,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B, coefficientIntegrand ⌊c * N⌋₊ m α) -
        (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) *
          (∫ α in (-(Real.log N ^ B / N))..(Real.log N ^ B / N),
            Kernel.T 0 (⌊c * N⌋₊ + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α))‖ ≤
        C * N * Real.log N ^ (-A / 2) := by
  obtain ⟨N₁, hN₁, hsplit⟩ := leaf_arc_integral_split B hB
  obtain ⟨C₁, N₂, hC₁, hN₂, hpt⟩ := leaf_arc_pointwise c hc (3 * B + A / 2) B
    (by positivity) hB
  refine ⟨2 * C₁ * (C₁ + 2 * c + 2), max (max N₁ N₂) (Real.exp 1), by positivity,
    hN₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N hN m
  have hN₁' : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN₂' : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNe : Real.exp 1 ≤ N := (le_max_right _ _).trans hN
  have hN3 : 3 ≤ N := hN₁.trans hN₁'
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNe
  have hL : 0 < Real.log N := by linarith
  set M := ⌊c * N⌋₊ with hM
  set L := Real.log N with hLdef
  set r := L ^ B / N with hr
  set Q := ⌊L ^ B⌋₊ with hQ
  have hr0 : 0 ≤ r := by positivity
  set ε := C₁ * N * L ^ (-(3 * B + A / 2)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεN : ε ≤ C₁ * N := by
    have : L ^ (-(3 * B + A / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by
      have : 0 < 3 * B + A / 2 := by positivity
      linarith)
    calc ε = C₁ * N * L ^ (-(3 * B + A / 2)) := rfl
      _ ≤ C₁ * N * 1 := by gcongr
      _ = C₁ * N := by ring
  have hMN : (M : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  set d : ℕ → ℂ := fun q => (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) with hd
  set g : ℝ → ℂ := fun η => Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-(m : ℝ) * η) with hg
  have hgc : Continuous g := by
    simp only [hg, Kernel.T, Kernel.e]
    fun_prop
  have hfc := coefficientIntegrand_continuous M m
  rw [hsplit N hN₁' _ hfc (coefficientIntegrand_periodic M m)]
  -- rewrite the main term as a sum over the arcs
  have hmain : (∑ q ∈ Icc 1 Q, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) * (∫ η in (-r)..r, g η) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ η in (-r)..r, d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [coefficient_eq_sum m q (Finset.mem_Icc.mp hq).1, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [intervalIntegral.integral_const_mul]
  rw [hmain, ← Finset.sum_sub_distrib]
  -- the bound on one arc
  have harc : ∀ q ∈ Icc 1 Q, ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖(∫ η in (-r)..r, coefficientIntegrand M m ((a : ℝ) / q + η)) -
        ∫ η in (-r)..r, d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η‖ ≤
        ε * (ε + 2 * (M + 1)) * (2 * r) := by
    intro q hq a ha
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ L ^ B :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le (by positivity))
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hi1 : IntervalIntegrable (fun η => coefficientIntegrand M m ((a : ℝ) / q + η))
        volume (-r) r := by
      apply Continuous.intervalIntegrable
      exact hfc.comp (continuous_const.add continuous_id)
    have hi2 : IntervalIntegrable
        (fun η => d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η) volume (-r) r := by
      apply Continuous.intervalIntegrable
      exact continuous_const.mul hgc
    rw [← intervalIntegral.integral_sub hi1 hi2]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -r) (b := r) (C := ε * (ε + 2 * (M + 1)))
      (f := fun η => coefficientIntegrand M m ((a : ℝ) / q + η) -
        d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η) ?_
    · have hlen : |r - -r| = 2 * r := by rw [abs_of_nonneg (by linarith)]; ring
      simpa only [hlen] using hbound
    intro η hη
    have hηr : |η| ≤ r := by
      rw [Set.uIoc_of_le (by linarith)] at hη
      exact abs_le.mpr ⟨hη.1.le, hη.2⟩
    have hE := hpt N hN₂' q hq1 hqQ a hcop η hηr
    set S := primeSum M ((a : ℝ) / q + η) with hS
    set T := Kernel.T 0 (M + 1) η with hT
    have hdT : ‖d q * T‖ ≤ M + 1 := by
      rw [norm_mul]
      have h1 := norm_model_le q hq1
      have h2 : ‖T‖ ≤ ((M + 1 : ℕ) : ℝ) := Kernel.norm_T_le 0 (M + 1) η
      push_cast at h2
      calc ‖d q‖ * ‖T‖ ≤ 1 * (M + 1) := by gcongr
        _ = M + 1 := one_mul _
    have hphase : Kernel.e (-(m : ℝ) * ((a : ℝ) / q + η)) =
        Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * Kernel.e (-(m : ℝ) * η) := by
      rw [mul_add, Parseval103.e_add]
    have hexp : coefficientIntegrand M m ((a : ℝ) / q + η) -
        d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η =
        Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * Kernel.e (-(m : ℝ) * η) *
          ((S - d q * T) * ((S - d q * T) + 2 * (d q * T))) := by
      simp only [coefficientIntegrand, hg, hphase]
      rw [← hS, ← hT]
      ring
    rw [hexp, norm_mul, norm_mul, norm_e, norm_e, one_mul, one_mul, norm_mul]
    have hsum : ‖(S - d q * T) + 2 * (d q * T)‖ ≤ ε + 2 * (M + 1) := by
      calc ‖(S - d q * T) + 2 * (d q * T)‖ ≤ ‖S - d q * T‖ + ‖2 * (d q * T)‖ := norm_add_le _ _
        _ = ‖S - d q * T‖ + 2 * ‖d q * T‖ := by rw [norm_mul]; norm_num
        _ ≤ ε + 2 * (M + 1) := by gcongr
    exact mul_le_mul hE hsum (norm_nonneg _) hε0
  -- count the arcs
  have hcount : ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ε * (ε + 2 * (M + 1)) * (2 * r) ≤ (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r)) := by
    have hX : 0 ≤ ε * (ε + 2 * (M + 1)) * (2 * r) := by positivity
    calc ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ε * (ε + 2 * (M + 1)) * (2 * r)
        ≤ ∑ q ∈ Icc 1 Q, (Q : ℝ) * (ε * (ε + 2 * (M + 1)) * (2 * r)) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          have h1 : ((range q).filter (fun a => Nat.Coprime a q)).card ≤ q :=
            (Finset.card_filter_le _ _).trans (by simp)
          exact_mod_cast h1.trans (Finset.mem_Icc.mp hq).2
      _ = (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp only [add_tsub_cancel_right]
          ring
  have hQB : (Q : ℝ) ≤ L ^ B := Nat.floor_le (by positivity)
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hfinal : (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r)) ≤
      2 * C₁ * (C₁ + 2 * c + 2) * N * L ^ (-A / 2) := by
    have hinner : ε + 2 * ((M : ℝ) + 1) ≤ (C₁ + 2 * c + 2) * N := by
      nlinarith
    have hpow : L ^ B * L ^ B * L ^ B * L ^ (-(3 * B + A / 2)) = L ^ (-A / 2) := by
      rw [← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
      congr 1
      ring
    have hQQ : (Q : ℝ) * Q ≤ L ^ B * L ^ B := mul_le_mul hQB hQB hQ0 (by positivity)
    calc (Q : ℝ) * Q * (ε * (ε + 2 * (M + 1)) * (2 * r))
        ≤ L ^ B * L ^ B * (ε * ((C₁ + 2 * c + 2) * N) * (2 * r)) := by
          apply mul_le_mul hQQ _ (by positivity) (by positivity)
          gcongr
      _ = 2 * C₁ * (C₁ + 2 * c + 2) * N * (L ^ B * L ^ B * L ^ B * L ^ (-(3 * B + A / 2))) := by
          rw [hε, hr]
          field_simp
      _ = 2 * C₁ * (C₁ + 2 * c + 2) * N * L ^ (-A / 2) := by rw [hpow]
  calc _ ≤ ∑ q ∈ Icc 1 Q, ‖(∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-r)..r, coefficientIntegrand M m ((a : ℝ) / q + η)) -
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-r)..r, d q ^ 2 * Kernel.e (-(m : ℝ) * ((a : ℝ) / q)) * g η‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ε * (ε + 2 * (M + 1)) * (2 * r) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [← Finset.sum_sub_distrib]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a ha => harc q hq a ha))
    _ ≤ _ := hcount
    _ ≤ _ := hfinal


open Finset Real

/-- The reciprocal Euler product for the positive totient ratio. -/
private theorem ratio_eq_product (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / n.totient = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hEuler : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  have hid : (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp <;> ring
  apply (div_eq_iff hφ.ne').mpr
  rw [hEuler]
  nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) hid]

/-- The totient ratio is at most twice one plus log n, for every positive n. -/
private theorem ratio_le_log (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / n.totient ≤ 2 * (1 + Real.log n) := by
  classical
  let s := n.primeFactors
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hshift : ∀ p ∈ s.image (fun p => p + 1), 3 ≤ p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have := (hs q hq).two_le
    omega
  have hC' := LeanLab.Perelli1996.B.prod_ge_half (s.image (fun p => p + 1)) hshift
  have hC : (1 : ℝ) / 2 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [Finset.prod_image (by intro a ha b hb h; dsimp at h; omega)] at hC'
    simpa using hC'
  have hid : (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2)) = ∏ p ∈ s, (1 + 1 / (p : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp <;> ring
  let D : ℕ := ∏ p ∈ s, p
  have hDsq : Squarefree D := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
    · intro p hp
      exact (hs p hp).squarefree
  have hDprime : D.primeFactors = s := Nat.primeFactors_prod_primeFactors n
  let af : ArithmeticFunction ℝ := ⟨fun d => (d : ℝ)⁻¹, by simp⟩
  have haf : af.IsMultiplicative := by
    refine ⟨by simp [af], fun {a b} _ => ?_⟩
    change ((a * b : ℕ) : ℝ)⁻¹ = (a : ℝ)⁻¹ * (b : ℝ)⁻¹
    simp [mul_comm]
  have hsum : (∏ p ∈ s, (1 + 1 / (p : ℝ))) = ∑ d ∈ D.divisors, (d : ℝ)⁻¹ := by
    have h := haf.prodPrimeFactors_one_add_of_squarefree hDsq
    rw [hDprime] at h
    simpa [af, one_div] using h
  have hsub : D.divisors ⊆ Icc 1 n := by
    intro d hd
    have hdn : d ∣ n := dvd_trans (Nat.dvd_of_mem_divisors hd) (Nat.prod_primeFactors_dvd n)
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn hdn⟩
  have hE : (∏ p ∈ s, (1 + 1 / (p : ℝ))) ≤ 1 + Real.log n := by
    rw [hsum]
    calc
      _ ≤ ∑ d ∈ Icc 1 n, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (harmonic n : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ _ := harmonic_le_one_add_log n
  have hR : 0 ≤ ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hC hR
  rw [ratio_eq_product n hn]
  change (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ≤ _
  nlinarith [hid, hE, hmul]


/-- The norm of the coefficient at modulus one. -/
private theorem coeff_norm_one (m : ℕ) : ‖(((ArithmeticFunction.moebius (1 : ℕ) : ℂ) ^ 2 / ((1 : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (1 : ℕ) (m))‖ = 1 := by
  rw [coefficient_one, norm_one]

/-- The norm of the coefficient vanishes at modulus zero. -/
private theorem coeff_norm_zero (m : ℕ) : ‖(((ArithmeticFunction.moebius (0 : ℕ) : ℂ) ^ 2 / ((0 : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (0 : ℕ) (m))‖ = 0 := by
  rw [coefficient_zero, norm_zero]

/-- The norm of the coefficient is multiplicative in the modulus. -/
private theorem coeff_norm_mul (m q r : ℕ) (h : Nat.Coprime q r) :
    ‖(((ArithmeticFunction.moebius ((q * r) : ℕ) : ℂ) ^ 2 / (((q * r) : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum ((q * r) : ℕ) (m))‖ = ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ * ‖(((ArithmeticFunction.moebius (r : ℕ) : ℂ) ^ 2 / ((r : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (r : ℕ) (m))‖ := by
  rw [coefficient_mul m q r h, norm_mul]

open Finset Real

/-- The positive prime envelope for the absolute Ramanujan coefficients is summable. -/
private theorem summable_prime_envelope :
    Summable (fun p : Nat.Primes => 1 / ((p.1 : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun p : Nat.Primes => 4 / (p.1 : ℝ) ^ 2) := by
    have h : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv] using (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left 4
    exact h.subtype _
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (hf := hs)
  intro p
  exact inv_sub_one_sq_le (by exact_mod_cast p.2.two_le)

/-- The absolute coefficient sum is at most an absolute constant times m over phi m. -/
private theorem sum_norm_le_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (∑' q : ℕ, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖) ≤ C * ((m : ℝ) / m.totient) := by
  classical
  let a : Nat.Primes → ℝ := fun p => 1 / ((p.1 : ℝ) - 1) ^ 2
  let T := ∑' p : Nat.Primes, a p
  let C := Real.exp T
  have hC : 0 < C := Real.exp_pos _
  have ha : ∀ p : Nat.Primes, 0 ≤ a p := fun _ => by dsimp [a]; positivity
  have hsum : Summable a := summable_prime_envelope
  have henvelope (s : Finset Nat.Primes) : (∏ p ∈ s, (1 + a p)) ≤ C := by
    calc
      _ ≤ ∏ p ∈ s, Real.exp (a p) := by
        apply Finset.prod_le_prod₀ (fun p _ => by have := ha p; linarith)
        intro p hp
        have h := Real.add_one_le_exp (a p)
        linarith
      _ = Real.exp (∑ p ∈ s, a p) := by rw [Real.exp_sum]
      _ ≤ C := Real.exp_le_exp.mpr (hsum.sum_le_tsum s (fun p _ => ha p))
  refine ⟨C, hC, ?_⟩
  intro m hm
  let f : ℕ → ℝ := fun q => ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖
  have hf1 : f 1 = 1 := by
    simp only [f]
    exact coeff_norm_one m
  have hf0 : f 0 = 0 := by
    simp only [f]
    exact coeff_norm_zero m
  have hfmul {q r : ℕ} (h : Nat.Coprime q r) : f (q * r) = f q * f r := by
    simp only [f]
    exact coeff_norm_mul m q r h
  have hsf : Summable (fun q => ‖f q‖) := (summable_norm_coefficient m hm).norm
  have heuler := EulerProduct.eulerProduct_hasProd (f := f) hf1 (fun {_ _} h => hfmul h) hsf hf0
  have hfactor (p : Nat.Primes) : (∑' e : ℕ, f (p.1 ^ e)) = 1 + f p.1 := by
    have hzero (e : ℕ) (he : e ∉ ({0, 1} : Finset ℕ)) : f (p.1 ^ e) = 0 := by
      have he2 : 2 ≤ e := by simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega
      have hns : ¬ Squarefree (p.1 ^ e) := by
        rw [Nat.squarefree_pow_iff p.2.ne_one (by omega)]
        simp only [not_and]
        intro _
        omega
      simp only [f]
      rw [coefficient_nonsquarefree m _ hns, norm_zero]
    rw [tsum_eq_sum hzero, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), pow_zero, pow_one, hf1]
  have hprod : HasProd (fun p : Nat.Primes => 1 + f p.1) (∑' q : ℕ, f q) := by
    simpa only [hfactor] using heuler
  have hnormp (p : Nat.Primes) : f p.1 =
      if p.1 ∣ m then 1 / ((p.1 : ℝ) - 1) else 1 / ((p.1 : ℝ) - 1) ^ 2 := by
    have hh := coefficient_prime m p.1 p.2
    have heq : (((ArithmeticFunction.moebius (p.1 : ℕ) : ℂ) ^ 2 / ((p.1 : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (p.1 : ℕ) (m)) =
        ((if p.1 ∣ m then 1 / ((p.1 : ℝ) - 1) else -(1 / ((p.1 : ℝ) - 1) ^ 2) : ℝ) : ℂ) := by
      split_ifs at hh ⊢ <;> push_cast at * <;> linear_combination hh
    dsimp [f]
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    let r : ℕ := p.1
    change |(if r ∣ m then 1 / ((r : ℝ) - 1) else -(1 / ((r : ℝ) - 1) ^ 2))| =
      if r ∣ m then 1 / ((r : ℝ) - 1) else 1 / ((r : ℝ) - 1) ^ 2
    have hp2 : (2 : ℝ) ≤ r := by exact_mod_cast p.2.two_le
    have hpos : 0 ≤ 1 / ((r : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
    have hsquare : 0 ≤ 1 / ((r : ℝ) - 1) ^ 2 := by positivity
    split_ifs <;> simp only [abs_neg, abs_of_nonneg hpos, abs_of_nonneg hsquare]
  have hpoint (p : Nat.Primes) : 1 + f p.1 ≤ (1 + a p) *
      (if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) := by
    rw [hnormp]
    have hp2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
    have hp1 : 0 < (p.1 : ℝ) - 1 := by linarith
    by_cases hd : p.1 ∣ m
    · rw [if_pos hd, if_pos hd]
      have heq : 1 + 1 / ((p.1 : ℝ) - 1) = (p.1 : ℝ) / ((p.1 : ℝ) - 1) := by field_simp <;> ring
      rw [heq]
      have := ha p
      have hnon : 0 ≤ (p.1 : ℝ) / ((p.1 : ℝ) - 1) := by positivity
      nlinarith
    · simp [hd, a]
  have hfinite (s : Finset Nat.Primes) : (∏ p ∈ s, (1 + f p.1)) ≤ C * ((m : ℝ) / m.totient) := by
    let u := s.filter (fun p => p.1 ∣ m)
    let v := u.image (fun p : Nat.Primes => (p : ℕ))
    have hv : v ⊆ m.primeFactors := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact Nat.mem_primeFactors.mpr ⟨q.2, (Finset.mem_filter.mp hq).2, hm.ne'⟩
    have hratio : (∏ p ∈ s, if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) ≤
        (m : ℝ) / m.totient := by
      rw [← Finset.prod_filter]
      change (∏ p ∈ u, (p.1 : ℝ) / ((p.1 : ℝ) - 1)) ≤ _
      have heq : (∏ p ∈ v, (p : ℝ) / ((p : ℝ) - 1)) =
          ∏ p ∈ u, (p.1 : ℝ) / ((p.1 : ℝ) - 1) := by
        dsimp [v]
        exact Finset.prod_image Nat.Primes.coe_nat_injective.injOn
      rw [← heq]
      rw [ratio_eq_product m hm]
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hv
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors (hv hp)).two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp hnot
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
    have hratioProd0 : 0 ≤ ∏ p ∈ s,
        if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 := by
      apply Finset.prod_nonneg
      intro p hp
      split_ifs
      · have hp2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · norm_num
    calc
      _ ≤ ∏ p ∈ s, (1 + a p) *
          (if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) := by
        exact Finset.prod_le_prod₀ (fun p _ => by dsimp [f]; positivity) (fun p _ => hpoint p)
      _ = (∏ p ∈ s, (1 + a p)) *
          (∏ p ∈ s, if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) := by
        rw [Finset.prod_mul_distrib]
      _ ≤ C * ((m : ℝ) / m.totient) :=
        mul_le_mul (henvelope s) hratio hratioProd0 hC.le
  exact le_of_tendsto hprod (Filter.Eventually.of_forall hfinite)

/-- The absolute Ramanujan coefficient sum has an elementary logarithmic bound. -/
private theorem sum_norm_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (∑' q : ℕ, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖) ≤ C * (1 + Real.log m) := by
  obtain ⟨C, hC, hbound⟩ := sum_norm_le_ratio
  refine ⟨2 * C, by positivity, ?_⟩
  intro m hm
  have h := mul_le_mul_of_nonneg_left (ratio_le_log m hm) hC.le
  exact (hbound m hm).trans (by nlinarith)


open Finset Real MeasureTheory

/-- Every finite Ramanujan principal model has a logarithmic central kernel error. -/
private theorem finite_model_error :
    ∃ C : ℝ, 0 < C ∧ ∀ m M : ℕ, 0 < m → m ≤ M → ∀ s : Finset ℕ,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ‖(∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) *
          (∫ α in (-δ)..δ, Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) -
        (m : ℂ) * (∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)))‖ ≤
        C * (1 + Real.log m) * (1 + 1 / (2 * δ)) := by
  obtain ⟨C, hC, hbound⟩ := sum_norm_le_log
  refine ⟨C, hC, ?_⟩
  intro m M hm hmM s δ hδ hhalf
  have hs : ‖∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ ≤ C * (1 + Real.log m) := by
    calc
      _ ≤ ∑ q ∈ s, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ := norm_sum_le _ _
      _ ≤ ∑' q : ℕ, ‖(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))‖ :=
        (summable_norm_coefficient m hm).sum_le_tsum s (fun _ _ => norm_nonneg _)
      _ ≤ _ := hbound m hm
  have hk := PrincipalTail320.central_coefficient_error M m hmM δ hδ hhalf
  have heq : (∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) *
        (∫ α in (-δ)..δ, Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) -
      (m : ℂ) * (∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) =
      (∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) *
        ((∫ α in (-δ)..δ, Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) - (m : ℂ)) := by ring
  rw [heq, norm_mul]
  exact mul_le_mul hs hk (norm_nonneg _) (by positivity)

/-- At primary radius P over N the finite principal model has error C N log N over P.
Page 481 equation 2, with the prime sum comparison excluded. -/
private theorem finite_model_error_scaled (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N P : ℝ, Real.exp 1 ≤ N → 0 < P → P / N ≤ 1 / 2 →
      ∀ m M : ℕ, 0 < m → m ≤ M → (m : ℝ) ≤ c * N → ∀ s : Finset ℕ,
      ‖(∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) *
          (∫ α in (-(P / N))..(P / N), Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) -
        (m : ℂ) * (∑ q ∈ s, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)))‖ ≤
        C * N * Real.log N / P := by
  obtain ⟨C, hC, hbound⟩ := finite_model_error
  refine ⟨C * (2 + |Real.log c|), by positivity, ?_⟩
  intro N P hN hP hhalf m M hm hmM hmN s
  have hN0 : 0 < N := (Real.exp_pos 1).trans_le hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm := Real.log_le_log hmR hmN
  rw [Real.log_mul hc.ne' hN0.ne'] at hlogm
  have hlog : 1 + Real.log m ≤ (2 + |Real.log c|) * Real.log N := by
    have hprod := mul_nonneg (abs_nonneg (Real.log c)) (sub_nonneg.mpr hL1)
    have hlogc := le_abs_self (Real.log c)
    nlinarith
  have hratio : 2 ≤ N / P := by
    apply (le_div_iff₀ hP).mpr
    have h := (div_le_iff₀ hN0).mp hhalf
    linarith
  have hkernel : 1 + 1 / (2 * (P / N)) ≤ N / P := by
    have heq : 1 / (2 * (P / N)) = N / (2 * P) := by field_simp
    rw [heq]
    have hdiv : N / P = 2 * (N / (2 * P)) := by ring
    linarith
  have hb := hbound m M hm hmM s (P / N) (div_pos hP hN0) hhalf
  calc
    _ ≤ C * (1 + Real.log m) * (1 + 1 / (2 * (P / N))) := hb
    _ ≤ C * ((2 + |Real.log c|) * Real.log N) * (N / P) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog hC.le) hkernel (by positivity) (by positivity)
    _ = _ := by ring


/-- The large N geometry needed for equations 16 and 17, from the orders on page 480. -/
theorem arc_parameters (F : ℤ[X]) (hF : Admissible F) (ε B : ℝ)
    (hε : 0 < ε) (hB : 0 < B) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      Real.log N ^ B / N ≤ 1 / 2 ∧ 2 ≤ fareyOrder F N H B := by
  have ht1 := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have ht2 := (isLittleO_log_rpow_rpow_atTop (B / 4) (by norm_num : (0 : ℝ) < 1 / 3)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp ht1
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp ht2
  refine ⟨max 3 (max N₁ N₂), le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hb1 := hN₁ N (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hb2 := hN₂ N (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le B),
    Real.rpow_one, abs_of_pos hN0] at hb1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le (B / 4)),
    abs_of_nonneg (Real.rpow_nonneg hN0.le (1 / 3))] at hb2
  refine ⟨(div_le_iff₀ hN0).mpr (by linarith), ?_⟩
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hF.1)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hpow : N ^ ((1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree) ≤ H ^ F.natDegree := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hH F.natDegree
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hN0.le] at h
  have hbase : (1 : ℝ) / 3 ≤ (1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree := by
    have hid : 1 / (3 * (F.natDegree : ℝ)) * F.natDegree = (1 : ℝ) / 3 := by field_simp
    rw [add_mul, hid]
    have := mul_pos hε hk
    linarith
  have hlow := (Real.rpow_le_rpow_of_exponent_le hN1 hbase).trans hpow
  have harg : 16 ≤ H ^ F.natDegree * Real.log N ^ (-B / 4) := by
    have hL : 0 < Real.log N ^ (B / 4) := Real.rpow_pos_of_pos hlog _
    have hratio : 16 ≤ H ^ F.natDegree / Real.log N ^ (B / 4) := by
      apply (le_div_iff₀ hL).mpr
      linarith
    rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hlog.le, ← div_eq_mul_inv]
    exact hratio
  unfold fareyOrder
  have hs : 4 ≤ Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact harg)
  linarith


/-- Page 480 before equation 1. Polynomial values on the window are eventually positive. -/
private theorem window_pos (F : ℤ[X]) (hF : Admissible F) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → ∀ n ∈ win F N H,
      0 < (Fv F n).toNat := by
  obtain ⟨X₀, hX₀, hX⟩ := poly_lower F hF
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (one_div_pos.mpr hk)).eventually
      (Filter.eventually_ge_atTop (max X₀ 1)))
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N H hN n hn
  have hlo : max X₀ 1 ≤ (n : ℝ) :=
    (hN₁ N ((le_max_right _ _).trans hN)).trans
      ((Nat.le_ceil _).trans (by exact_mod_cast (Finset.mem_Icc.mp hn).1))
  have hp := hX n ((le_max_left _ _).trans hlo)
  have hn1 : (1 : ℝ) ≤ n := (le_max_right _ _).trans hlo
  have hv : (0 : ℝ) < Fv F n := by
    have : (0 : ℝ) < (n : ℝ) ^ F.natDegree := pow_pos (by linarith) _
    linarith
  have hvI : 0 < Fv F n := by exact_mod_cast hv
  omega

/-- Page 481 equation 2, the prime sum comparison on the primary arcs.
On the arc at a over q with q at most L^B, Vaughan 1981 Chapter 3, Lemma 3.1 with the
Siegel Walfisz theorem, replaces the prime sum by mu q over phi q times the kernel T.
Summing the squared model over the reduced residues a gives the Ramanujan coefficient
(((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)) times the central kernel integral over radius L^B over N.
Cited input: Vaughan 1981 Chapter 3; Perelli 1996 page 481 equation 2.
PROVED from arc_model, whose pieces leaf_arc_pointwise, via the lab's
PNTPort Siegel Walfisz major arc lemma, and leaf_arc_integral_split are proved. -/
private theorem prime_model_arc (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (A ε B : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      ∀ n ∈ win F N H,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B,
          coefficientIntegrand ⌊c * N⌋₊ (Fv F n).toNat α) -
        (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) ((Fv F n).toNat))) *
          (∫ α in (-(Real.log N ^ B / N))..(Real.log N ^ B / N),
            Kernel.T 0 (⌊c * N⌋₊ + 1) α ^ 2 * Kernel.e (-((Fv F n).toNat : ℝ) * α))‖ ≤
        C * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) := by
  obtain ⟨C, N₀, hC, hN₀, h⟩ := arc_model c hc A B hA hB
  refine ⟨C, N₀, hC, hN₀, ?_⟩
  intro N H hN _ _ _ n _
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  refine (h N hN _).trans ?_
  have hy : 0 ≤ Real.log N ^ (1 - B) := Real.rpow_nonneg hL _
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hy) (by positivity)

/-- Page 481 equation 2 before completing the singular series.
PROVED from prime_model_arc; the principal model error is PROVED in PrincipalModel320.
Vaughan Chapter 3 supplies the prime approximation.
The primary rectangular arcs are exactly the arcs defined on page 480. -/
private theorem finite_major_arc (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (A ε B : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      ∀ n ∈ win F N H,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B,
          coefficientIntegrand ⌊c * N⌋₊ (Fv F n).toNat α) -
        (Fv F n : ℂ) * (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) ((Fv F n).toNat)))‖ ≤
        C * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) := by
  obtain ⟨CP, NP, hCP, hNP, hprime⟩ := prime_model_arc F hF c hc A ε B hA hε hB
  obtain ⟨CM, hCM, hmodel⟩ := finite_model_error_scaled c hc
  obtain ⟨NA, hNA, harc⟩ := arc_parameters F hF ε B hε hB
  obtain ⟨NW, hNW, hpos⟩ := window_pos F hF
  refine ⟨CP + CM, max (max NP NA) (max NW (Real.exp 1)), by positivity,
    hNP.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu hcut n hn
  have hNP' : NP ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNA' : NA ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNW' : NW ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNe : Real.exp 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := (Real.exp_pos 1).trans_le hNe
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNe
  have hL : 0 < Real.log N := by linarith
  set m := (Fv F n).toNat with hm_def
  have hmpos : 0 < m := hpos N H hNW' n hn
  have hmcast : (m : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hcut n hn).1
  have hmC : (Fv F n : ℂ) = (m : ℂ) := by
    have : ((Fv F n : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by rw [hmcast]
    simpa using this
  have hmN : (m : ℝ) ≤ c * N :=
    (by exact_mod_cast (hcut n hn).2 : (m : ℝ) ≤ (⌊c * N⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))
  have hmM : m ≤ ⌊c * N⌋₊ := (hcut n hn).2
  have hP : 0 < Real.log N ^ B := Real.rpow_pos_of_pos hL B
  have hhalf := (harc N H hNA' hH).1
  have h1 := hprime N H hNP' hH hHu hcut n hn
  have h2 := hmodel N (Real.log N ^ B) hNe hP hhalf m ⌊c * N⌋₊ hmpos hmM hmN
    (Icc 1 ⌊Real.log N ^ B⌋₊)
  have hscale : Real.log N / Real.log N ^ B = Real.log N ^ (1 - B) := by
    rw [Real.rpow_sub hL, Real.rpow_one]
  rw [mul_div_assoc, hscale] at h2
  rw [hmC]
  set I : ℂ := ∫ α in Set.Icc 0 1 ∩ majorArcs N B, coefficientIntegrand ⌊c * N⌋₊ m α
  set S : ℂ := ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))
  set J : ℂ := ∫ α in (-(Real.log N ^ B / N))..(Real.log N ^ B / N),
    Kernel.T 0 (⌊c * N⌋₊ + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)
  have htri : ‖I - (m : ℂ) * S‖ ≤ ‖I - S * J‖ + ‖S * J - (m : ℂ) * S‖ := by
    have : I - (m : ℂ) * S = (I - S * J) + (S * J - (m : ℂ) * S) := by ring
    rw [this]
    exact norm_add_le _ _
  have hA2 : 0 ≤ Real.log N ^ (-A / 2) := by positivity
  have hB1 : 0 ≤ Real.log N ^ (1 - B) := by positivity
  calc ‖I - (m : ℂ) * S‖ ≤ ‖I - S * J‖ + ‖S * J - (m : ℂ) * S‖ := htri
    _ ≤ CP * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) +
        CM * N * Real.log N ^ (1 - B) := add_le_add h1 h2
    _ ≤ (CP + CM) * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) := by
      nlinarith [mul_nonneg (mul_nonneg hCM.le hN0.le) hA2]
/-- Page 481 equation 3 and the singular series expansion used in equation 2.
Only the arithmetic completion of the finite Ramanujan series is estimated here. -/
private theorem singular_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ P : ℝ, 1 ≤ P →
      ‖(Sing m : ℂ) - (∑ q ∈ Icc 1 ⌊P⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)))‖ ≤
        C * ((m : ℝ) * m.divisors.card / m.totient) / P := by
  obtain ⟨C, hC, htail⟩ := partial_tail
  refine ⟨C, hC, ?_⟩
  intro m hm P hP
  exact htail m hm P hP


/-- LEAF. Page 481 equations 2 and 3, squared.
Vaughan 1981 Chapter 3 supplies the major arc approximation.
This states the required variant for the sealed rectangular major arcs. -/
theorem leaf_major_pointwise (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (A ε B : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      ∀ n ∈ win F N H,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B,
          coefficientIntegrand ⌊c * N⌋₊ (Fv F n).toNat α) -
        ((Fv F n : ℝ) * Sing (Fv F n).toNat : ℂ)‖ ^ 2 ≤
        C * N ^ 2 * (Real.log N ^ (-2 * B) * majorWeight (Fv F n).toNat N ^ 2 +
          Real.log N ^ (-A)) := by

  obtain ⟨CF, NF, hCF, hNF, hfinite⟩ := finite_major_arc F hF c hc A ε B hA hε hB
  obtain ⟨CT, hCT, htail⟩ := singular_tail
  obtain ⟨NP, hNP, hpos⟩ := window_pos F hF
  let K := CF + c * CT
  refine ⟨4 * K ^ 2, max (max NF NP) (Real.exp 1), by dsimp [K]; positivity,
    hNF.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu hcut n hn
  have hNF' := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNP' := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN3 : 3 ≤ N := hNF.trans hNF'
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hN)
  have hL : 0 < Real.log N := by linarith
  let m := (Fv F n).toNat
  let w : ℝ := (m : ℝ) * m.divisors.card / m.totient
  have hmpos : 0 < m := hpos N H hNP' n hn
  have hmcast : (m : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hcut n hn).1
  have hmN : (m : ℝ) ≤ c * N :=
    (by exact_mod_cast (hcut n hn).2 : (m : ℝ) ≤ (⌊c * N⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have ht := htail m hmpos (Real.log N ^ B) (Real.one_le_rpow hL1 hB.le)
  have hpart := hfinite N H hNF' hH hHu hcut n hn
  let I : ℂ := ∫ α in Set.Icc 0 1 ∩ majorArcs N B,
    coefficientIntegrand ⌊c * N⌋₊ m α
  have htriangle : ‖I - (Fv F n : ℂ) * (Sing m : ℂ)‖ ≤
      CF * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) +
        c * N * (CT * w / Real.log N ^ B) := by
    calc
      _ ≤ ‖I - (Fv F n : ℂ) * (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)))‖ +
          ‖(Fv F n : ℂ) * ((∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) - (Sing m : ℂ))‖ := by
            have heq : I - (Fv F n : ℂ) * (Sing m : ℂ) =
                (I - (Fv F n : ℂ) * (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m)))) +
                (Fv F n : ℂ) * ((∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 / ((q : ℕ).totient : ℂ) ^ 2) * Ramanujan103.ramanujanSum (q : ℕ) (m))) - (Sing m : ℂ)) := by ring
            rw [heq]
            exact norm_add_le _ _
      _ ≤ CF * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) +
          c * N * (CT * w / Real.log N ^ B) := by
            apply add_le_add hpart
            rw [norm_mul, norm_sub_rev]
            have hnorm : ‖(Fv F n : ℂ)‖ = (m : ℝ) := by
              rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs,
                ← hmcast, abs_of_nonneg (Nat.cast_nonneg _)]
            rw [hnorm]
            exact mul_le_mul hmN ht (norm_nonneg _) (by positivity)
  have hpow1 : Real.log N ^ (1 - B) = Real.log N ^ (-B) * Real.log N := by
    rw [show 1 - B = -B + 1 by ring, Real.rpow_add hL, Real.rpow_one]
  have hpow2 : CT * w / Real.log N ^ B = CT * (Real.log N ^ (-B) * w) := by
    rw [Real.rpow_neg hL.le]
    ring
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : ‖I - (Fv F n : ℂ) * (Sing m : ℂ)‖ ≤
      K * N * (Real.log N ^ (-B) * majorWeight m N + Real.log N ^ (-A / 2)) := by
    refine htriangle.trans ?_
    rw [hpow1, hpow2]
    change CF * N * (Real.log N ^ (-B) * Real.log N + Real.log N ^ (-A / 2)) +
      c * N * (CT * (Real.log N ^ (-B) * w)) ≤
      K * N * (Real.log N ^ (-B) * (w + Real.log N) + Real.log N ^ (-A / 2))
    have hcoeff1 : CF ≤ K := by dsimp [K]; linarith [mul_pos hc hCT]
    have hcoeff2 : c * CT ≤ K := by dsimp [K]; linarith
    have hx : 0 ≤ Real.log N ^ (-B) * Real.log N + Real.log N ^ (-A / 2) := by positivity
    have hy : 0 ≤ Real.log N ^ (-B) * w := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcoeff1 (mul_nonneg hN0.le hx),
      mul_le_mul_of_nonneg_right hcoeff2 (mul_nonneg hN0.le hy)]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hadd := add_sq_le (a := Real.log N ^ (-B) * majorWeight m N)
    (b := Real.log N ^ (-A / 2))
  have he1 : (Real.log N ^ (-B) * majorWeight m N) ^ 2 =
      Real.log N ^ (-2 * B) * majorWeight m N ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 2
    ring
  have he2 : (Real.log N ^ (-A / 2)) ^ 2 = Real.log N ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [he1, he2] at hadd
  have hnon : 0 ≤ Real.log N ^ (-2 * B) * majorWeight m N ^ 2 + Real.log N ^ (-A) := by positivity
  change ‖I - (Fv F n : ℂ) * (Sing m : ℂ)‖ ^ 2 ≤ _
  calc
    _ ≤ (K * N * (Real.log N ^ (-B) * majorWeight m N + Real.log N ^ (-A / 2))) ^ 2 := hsquare
    _ = K ^ 2 * N ^ 2 * (Real.log N ^ (-B) * majorWeight m N + Real.log N ^ (-A / 2)) ^ 2 := by ring
    _ ≤ K ^ 2 * N ^ 2 * (2 * (Real.log N ^ (-2 * B) * majorWeight m N ^ 2 + Real.log N ^ (-A))) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ K ^ 2 * N ^ 2 by positivity) hnon]

/-- LEAF. Page 481 between equations 3 and 4.
Nair 1992 supplies the short interval mean of the divisor weight. -/
theorem leaf_nair_mean (F : ℤ[X]) (hF : Admissible F) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∑ n ∈ win F N H, majorWeight (Fv F n).toNat N ^ 2 ≤
        C * H * Real.log N ^ d := by
  exact Nair103.nair_mean_explicit F hF.1 hF.2

/-- The polynomial window holds at most H plus one integers. -/
theorem card_win_le (F : ℤ[X]) {N H : ℝ} (hN : 0 ≤ N) (hH : 0 ≤ H) :
    ((win F N H).card : ℝ) ≤ H + 1 := by
  unfold win
  rw [Nat.card_Icc]
  have hx : 0 ≤ N ^ (1 / (F.natDegree : ℝ)) := Real.rpow_nonneg hN _
  have hlo := Nat.le_ceil (N ^ (1 / (F.natDegree : ℝ)))
  have hhi := Nat.floor_le (show 0 ≤ N ^ (1 / (F.natDegree : ℝ)) + H by positivity)
  rcases Nat.lt_or_ge (⌊N ^ (1 / (F.natDegree : ℝ)) + H⌋₊ + 1)
      ⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h.le]
    simp only [Nat.cast_zero]
    linarith
  · rw [Nat.cast_sub h]
    push_cast
    linarith

/-- Equation 4, CONDITIONAL ON the pointwise approximation and Nair mean leaves. -/
theorem major (F : ℤ[X]) (hF : Admissible F) (c : ℝ) (hc : 0 < c) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ A ε B : ℝ, 0 < A → 0 < ε → 0 < B →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      majorError F ⌊c * N⌋₊ N H B ≤
        C * H * N ^ 2 * (Real.log N ^ (-2 * B + d) + Real.log N ^ (-A)) := by
  obtain ⟨d, hd, hmean⟩ := leaf_nair_mean F hF
  refine ⟨d, hd, ?_⟩
  intro A ε B hA hε hB
  obtain ⟨CP, NP, hCP, hNP, hpoint⟩ := leaf_major_pointwise F hF c hc A ε B hA hε hB
  obtain ⟨CM, NM, hCM, hNM, hmean⟩ := hmean ε hε
  refine ⟨CP * (CM + 2), max NP NM, by positivity, hNP.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu hcut
  have hNP' := (le_max_left NP NM).trans hN
  have hNM' := (le_max_right NP NM).trans hN
  have hN3 := hNP.trans hNP'
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hexp : 0 ≤ 1 / (3 * (F.natDegree : ℝ)) + ε := by positivity
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith) hexp).trans hH
  have hcard : ((win F N H).card : ℝ) ≤ 2 * H :=
    (card_win_le F hN0.le (by linarith)).trans (by linarith)
  have hsum := Finset.sum_le_sum (hpoint N H hNP' hH hHu hcut)
  have hm := hmean N H hNM' hH hHu
  unfold majorError
  calc
    _ ≤ ∑ n ∈ win F N H, CP * N ^ 2 *
        (Real.log N ^ (-2 * B) * majorWeight (Fv F n).toNat N ^ 2 + Real.log N ^ (-A)) := hsum
    _ = CP * N ^ 2 * (Real.log N ^ (-2 * B) *
        (∑ n ∈ win F N H, majorWeight (Fv F n).toNat N ^ 2) +
        ((win F N H).card : ℝ) * Real.log N ^ (-A)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ CP * N ^ 2 * (Real.log N ^ (-2 * B) * (CM * H * Real.log N ^ d) +
        (2 * H) * Real.log N ^ (-A)) := by gcongr
    _ = CP * CM * H * N ^ 2 * Real.log N ^ (-2 * B + d) +
        2 * CP * H * N ^ 2 * Real.log N ^ (-A) := by
      rw [show Real.log N ^ (-2 * B) * (CM * H * Real.log N ^ d) =
        CM * H * (Real.log N ^ (-2 * B) * Real.log N ^ d) by ring,
        ← Real.rpow_add hL]
      ring
    _ ≤ _ := by
      have h1 : CP * CM ≤ CP * (CM + 2) := by nlinarith
      have h2 : 2 * CP ≤ CP * (CM + 2) := by nlinarith
      rw [mul_add]
      gcongr

/-- The weighted inner integral in page 481 equation 5. -/
def kernelMoment (F : ℤ[X]) (M : ℕ) (N H B ξ : ℝ) : ℝ :=
  ∫ α in minorArcs N B, ‖primeSum M α‖ ^ 2 *
    ‖Section2.polynomialKernel F N H (α - ξ)‖

/-- The largest minor prime mass in an interval of width one over the larger Farey order.
This enlarges every shifted secondary arc in page 483 equation 12. -/
def shortMass (M : ℕ) (N B Q : ℝ) : ℝ :=
  sSup {x | ∃ t : ℝ, x =
    ∫ α in minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2)), ‖primeSum M α‖ ^ 2}

/-- Every local prime second moment is nonnegative, including an unbounded supremum. -/
theorem localMass_nonneg (M : ℕ) (N B Q : ℝ) : 0 ≤ localMass M N B Q := by
  unfold localMass
  apply Real.sSup_nonneg
  rintro x ⟨q, hq, hqQ, a, ha, rfl⟩
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Every short interval prime second moment is nonnegative. -/
theorem shortMass_nonneg (M : ℕ) (N B Q : ℝ) : 0 ≤ shortMass M N B Q := by
  unfold shortMass
  apply Real.sSup_nonneg
  rintro x ⟨t, rfl⟩
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- LEAF. Page 481 equation 5, Parseval followed by the prime second moment bound.
The arbitrary nonnegative U bounds the weighted inner integral uniformly. -/
theorem leaf_parseval (F : ℤ[X]) (c : ℝ) (hc : 0 < c) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H B U : ℝ, N₀ ≤ N →
      0 ≤ U →
      (∀ n ∈ win F N H, 0 ≤ Fv F n) →
      (∀ ξ ∈ minorArcs N B, kernelMoment F ⌊c * N⌋₊ N H B ξ ≤ U) →
      minorError F ⌊c * N⌋₊ N H B ≤ C * N * Real.log N * U := by
  obtain ⟨C, N₀, hC, hN₀, hmoment⟩ := Parseval103.prime_second_moment_scaled c hc
  refine ⟨C, N₀, hC, hN₀, ?_⟩
  intro N H B U hN hU hpos hbound
  let M := ⌊c * N⌋₊
  let s := minorArcs N B
  have hs : s ⊆ Set.Icc (0 : ℝ) 1 := Set.diff_subset
  have hms : MeasurableSet s := by dsimp [s, minorArcs, majorArcs]; measurability
  have hf : Continuous (fun α : ℝ => primeSum M α ^ 2) := by
    unfold primeSum Kernel.e
    fun_prop
  have hfreq (n : ℕ) (hn : n ∈ win F N H) : ((Fv F n).toNat : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hpos n hn)
  have hq := Parseval103.quadratic_le s hs hms (fun α => primeSum M α ^ 2) hf
    (win F N H) (fun n => (Fv F n : ℝ)) U hU
    (by intro ξ hξ; simpa only [norm_pow, kernelMoment, Section2.polynomialKernel, M, s] using hbound ξ hξ)
  have herr : minorError F M N H B =
      ∑ n ∈ win F N H, ‖∫ α in s, primeSum M α ^ 2 *
        Kernel.e (-(Fv F n : ℝ) * α)‖ ^ 2 := by
    unfold minorError
    apply Finset.sum_congr rfl
    intro n hn
    simp only [coefficientIntegrand, hfreq n hn, s]
  rw [← herr] at hq
  have hfull : (∫ ξ in s, ‖primeSum M ξ ^ 2‖) ≤ C * N * Real.log N := by
    calc
      _ = ∫ ξ in s, ‖primeSum M ξ‖ ^ 2 := by simp only [norm_pow]
      _ ≤ ∫ ξ in Set.Icc (0 : ℝ) 1, ‖primeSum M ξ‖ ^ 2 := by
        apply setIntegral_mono_set
        · have hp : Continuous (fun ξ : ℝ => ‖primeSum M ξ‖ ^ 2) := by
            unfold primeSum Kernel.e
            fun_prop
          exact hp.integrableOn_Icc
        · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
        · exact Filter.Eventually.of_forall (fun _ h => hs h)
      _ ≤ _ := hmoment N hN
  exact hq.trans (by nlinarith [mul_le_mul_of_nonneg_right hfull hU])

/-- Equation 9: the Weyl decay exponent once the three denominator bounds hold. -/
private theorem wl_weyl_decay (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (B : ℝ)
    (hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ a : ℤ, ∀ q : ℕ, 0 < q → Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      1 / (q : ℝ) ≤ Real.log N ^ (-B / 4) →
      1 / H ≤ Real.log N ^ (-B / 4) →
      (q : ℝ) / H ^ F.natDegree ≤ Real.log N ^ (-B / 4) →
      ‖Section2.polynomialKernel F N H α‖ ≤ C * H *
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F)) := by
  let D := B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1
  let K := Section2.weylExponent F
  have hK : 0 < K := by dsimp [K, Section2.weylExponent]; positivity
  obtain ⟨C, N₀, hC, hN₀, hw⟩ := hW hF D hD
  refine ⟨C * 4 ^ (1 / K), N₀, by positivity, hN₀, ?_⟩
  intro N H α hN hH hHu a q hq hcop happ h1 h2 h3
  have hN3 := hN₀.trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hw' := hw N H α hN hH hHu a q hq hcop happ
  have hfour : -2 * D + (F.natDegree : ℝ) ^ 2 - 2 = -B / 4 := by dsimp [D]; ring
  rw [hfour] at hw'
  have hbase : 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
      Real.log N ^ (-B / 4) ≤ 4 * Real.log N ^ (-B / 4) := by linarith
  have hnon : 0 ≤ 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
      Real.log N ^ (-B / 4) := by positivity
  have hroot := Real.rpow_le_rpow hnon hbase (show 0 ≤ 1 / K by positivity)
  calc
    _ ≤ C * H * (4 * Real.log N ^ (-B / 4)) ^ (1 / K) *
      Real.log N ^ ((D + 1) / K) := by
      exact hw'.trans (by gcongr)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hL.le _),
        ← Real.rpow_mul hL.le]
      have hexp : (-B / 4) * (1 / K) + (D + 1) / K =
          -(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * K) := by dsimp [D]; ring
      calc
        _ = (C * 4 ^ (1 / K)) * H *
            (Real.log N ^ ((-B / 4) * (1 / K)) * Real.log N ^ ((D + 1) / K)) := by ring
        _ = _ := by rw [← Real.rpow_add hL, hexp]

/-- The reciprocal interval length satisfies the secondary arc threshold. -/
private theorem wl_inv_H (F : ℤ[X]) (hF : Admissible F) (ε B : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      1 / H ≤ Real.log N ^ (-B / 4) := by
  let δ := 1 / (3 * (F.natDegree : ℝ)) + ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb := (isLittleO_log_rpow_rpow_atTop (B / 4) hδ).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hlog := hN₁ N ((le_max_right _ _).trans hN)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] at hlog
  have hlogH : Real.log N ^ (B / 4) ≤ H := hlog.trans hH
  rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hL.le]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _) hlogH

/-- The secondary order is at least two and its square reciprocal exceeds sixteen. -/
private theorem wl_order_bounds (F : ℤ[X]) (hF : Admissible F) (ε B : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      16 ≤ H ^ F.natDegree * Real.log N ^ (-B / 4) ∧ 2 ≤ fareyOrder F N H B := by
  have ht2 := (isLittleO_log_rpow_rpow_atTop (B / 4) (by norm_num : (0 : ℝ) < 1 / 3)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp ht2
  refine ⟨max 3 N₂, le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hb2 := hN₂ N (le_trans (le_max_right _ _) hN)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le (B / 4)),
    abs_of_nonneg (Real.rpow_nonneg hN0.le (1 / 3))] at hb2
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hF.1)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hpow : N ^ ((1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree) ≤ H ^ F.natDegree := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hH F.natDegree
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hN0.le] at h
  have hbase : (1 : ℝ) / 3 ≤ (1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree := by
    have hid : 1 / (3 * (F.natDegree : ℝ)) * F.natDegree = (1 : ℝ) / 3 := by field_simp
    rw [add_mul, hid]
    have := mul_pos hε hk
    linarith
  have hlow := (Real.rpow_le_rpow_of_exponent_le hN1 hbase).trans hpow
  have harg : 16 ≤ H ^ F.natDegree * Real.log N ^ (-B / 4) := by
    have hL : 0 < Real.log N ^ (B / 4) := Real.rpow_pos_of_pos hlog _
    have hratio : 16 ≤ H ^ F.natDegree / Real.log N ^ (B / 4) := by
      apply (le_div_iff₀ hL).mpr
      linarith
    rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hlog.le, ← div_eq_mul_inv]
    exact hratio
  unfold fareyOrder
  have hs : 4 ≤ Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact harg)
  exact ⟨harg, by linarith⟩

/-- The short interval prime mass set is bounded above. -/
private theorem shortMass_bddAbove' (M : ℕ) (N B Q : ℝ) :
    BddAbove {x | ∃ t : ℝ, x =
      ∫ α in minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2)), ‖primeSum M α‖ ^ 2} := by
  refine ⟨(Real.log 4 + 4) * (M : ℝ) * Real.log ((M : ℝ) + 1), ?_⟩
  rintro x ⟨t, rfl⟩
  have hcont : Continuous (fun α : ℝ => ‖primeSum M α‖ ^ 2) := by
    unfold primeSum Kernel.e
    fun_prop
  calc
    _ ≤ ∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum M α‖ ^ 2 := by
      apply setIntegral_mono_set hcont.integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun _ h => Set.diff_subset h.1)
    _ ≤ _ := Parseval103.prime_second_moment M

/-- Every window integral is bounded by the short interval prime mass. -/
private theorem le_shortMass (M : ℕ) (N B Q t : ℝ) :
    (∫ α in minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2)), ‖primeSum M α‖ ^ 2) ≤
      shortMass M N B Q := by
  unfold shortMass
  exact le_csSup (shortMass_bddAbove' M N B Q) ⟨t, rfl⟩

/-- A finite union of sets carries at most the sum of the set integrals. -/
private theorem integral_iUnion_finset_le {ι : Type*} (A : ι → Set ℝ) (t : Set ℝ)
    (g : ℝ → ℝ) (hInt : IntegrableOn g t) (hg : ∀ x, 0 ≤ g x)
    (hmeas : ∀ i, MeasurableSet (t ∩ A i)) (s : Finset ι) :
    (∫ x in t ∩ (⋃ i ∈ s, A i), g x) ≤ ∑ i ∈ s, ∫ x in t ∩ A i, g x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have hU : (⋃ i ∈ insert j s, A i) = A j ∪ ⋃ i ∈ s, A i :=
        Finset.set_biUnion_insert j s A
      rw [hU, Finset.sum_insert hj]
      have hinter : t ∩ ⋃ i ∈ s, A i = ⋃ i ∈ s, (t ∩ A i) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
        tauto
      have hmeasU : MeasurableSet (t ∩ ⋃ i ∈ s, A i) := by
        rw [hinter]
        exact Finset.measurableSet_biUnion s (fun i _ => hmeas i)
      have hcover : t ∩ (A j ∪ ⋃ i ∈ s, A i) ⊆
          (t ∩ A j) ∪ (t ∩ ⋃ i ∈ s, A i) := by
        rintro x ⟨hxt, hx | hx⟩
        · exact Or.inl ⟨hxt, hx⟩
        · exact Or.inr ⟨hxt, hx⟩
      have hintU : IntegrableOn g (t ∩ ⋃ i ∈ s, A i) := hInt.mono_set Set.inter_subset_left
      calc
        _ ≤ (∫ x in t ∩ A j, g x) + ∫ x in t ∩ ⋃ i ∈ s, A i, g x :=
          Farey103.integral_two_cover g hg (t ∩ (A j ∪ ⋃ i ∈ s, A i)) (t ∩ A j)
            (t ∩ ⋃ i ∈ s, A i) (hmeas j) hmeasU
            (hInt.mono_set Set.inter_subset_left) hintU hcover
        _ ≤ (∫ x in t ∩ A j, g x) + ∑ i ∈ s, ∫ x in t ∩ A i, g x := by
          exact add_le_add le_rfl ih

/-- Equation 9 on the complement of the secondary rational arcs. -/
private theorem wl_weyl_secondary (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B)
    (hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B / 4) →
        ∀ a : ℤ, Nat.Coprime a.natAbs q →
          1 / ((q : ℝ) * (H ^ F.natDegree * Real.log N ^ (-B / 4))) <
            |α - (a : ℝ) / q|) →
      ‖Section2.polynomialKernel F N H α‖ ≤ C * H *
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F)) := by
  obtain ⟨C, NW, hC, hNW, hw⟩ := wl_weyl_decay F hF hW B hD
  obtain ⟨NH, hNH, hh⟩ := wl_inv_H F hF ε B hε
  obtain ⟨NG, hNG, hg⟩ := wl_order_bounds F hF ε B hε
  refine ⟨C, NW + NH + NG + 3, hC, by linarith, ?_⟩
  intro N H α hN hH hHu hminor
  have hNW' : NW ≤ N := by linarith
  have hNH' : NH ≤ N := by linarith
  have hNG' : NG ≤ N := by linarith
  have hN3 : 3 ≤ N := hNW.trans hNW'
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  let Q := H ^ F.natDegree * Real.log N ^ (-B / 4)
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have hQ1 : 1 ≤ Q := by
    have h16 := (hg N H hNG' hH).1
    dsimp [Q]
    linarith
  obtain ⟨q, hq, hqQ, a, hcop, happ⟩ := Farey103.dirichlet_real_order α Q hQ1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmall : ¬ (q : ℝ) ≤ Real.log N ^ (B / 4) := by
    intro hbad
    exact (not_lt_of_ge happ.le) (hminor q hq hbad a hcop)
  have hqLarge : Real.log N ^ (B / 4) ≤ q := (lt_of_not_ge hsmall).le
  have happ' : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.le.trans ?_
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq0)
    nlinarith
  apply hw N H α hNW' hH1 hHu a q hq hcop happ'
  · rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hL.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _) hqLarge
  · exact hh N H hNH' hH
  · exact (div_le_iff₀ (pow_pos hH0 _)).mpr (by simpa [Q, mul_comm] using hqQ)

set_option maxHeartbeats 1600000 in
/-- LEAF. Pages 482 and 483 equations 9 through 12.
The Weyl input bounds the complement of the secondary arcs.
At most L to the B over two short intervals cover the secondary arcs. -/
theorem leaf_weyl_localization (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (c : ℝ) (hc : 0 < c)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ ξ ∈ minorArcs N B,
      kernelMoment F ⌊c * N⌋₊ N H B ξ ≤
        C * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        C * H * N * Real.log N ^
          (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
  classical
  obtain ⟨C₁, N₁, hC₁, hN₁, hmom⟩ := Parseval103.prime_second_moment_scaled c hc
  obtain ⟨NO, hNO, hord⟩ := wl_order_bounds F hF ε B hε
  have hexp0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  by_cases hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1
  · obtain ⟨C₂, N₂, hC₂, hN₂, hdecay⟩ := wl_weyl_secondary F hF hW ε B hε hB hD
    refine ⟨max 512 (max (2 * C₁) (C₁ * C₂)), N₁ + (N₂ + (NO + (Real.exp 1 + 3))),
      by positivity, by linarith, ?_⟩
    intro N H hN hH hHu ξ hξ
    have hN1le : N₁ ≤ N := by linarith
    have hN2le : N₂ ≤ N := by linarith
    have hNOle : NO ≤ N := by linarith
    have hNexp : Real.exp 1 ≤ N := by linarith
    have hN3 : 3 ≤ N := hN₁.trans hN1le
    have hN0 : 0 < N := by linarith
    have hNgt1 : 1 ≤ N := by linarith
    have hL : 0 < Real.log N := Real.log_pos (by linarith)
    have hL1 : 1 ≤ Real.log N := by
      have h := Real.log_le_log (Real.exp_pos 1) hNexp
      simpa using h
    have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
    have hH1 : 1 ≤ H := (Real.one_le_rpow hNgt1 (by positivity)).trans hH
    have hξb : |ξ| ≤ 1 := by
      have h := Set.diff_subset hξ
      rw [abs_le]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    set Q : ℝ := fareyOrder F N H B with hQ
    set Qbar : ℝ := H ^ F.natDegree * Real.log N ^ (-B / 4) with hQbar
    obtain ⟨hQbar16, hQ2⟩ := hord N H hNOle hH
    have hQbar0 : 0 < Qbar := by rw [hQbar]; positivity
    have hQ0 : 0 < Q := by linarith
    have hQsq : 4 * Q ^ 2 = Qbar := by
      rw [hQ, hQbar]
      unfold fareyOrder
      have hpos : 0 < H ^ F.natDegree * Real.log N ^ (-B / 4) := by positivity
      rw [div_pow, Real.sq_sqrt hpos.le]
      ring
    have hquarter : 1 / (4 * Q ^ 2) = 1 / Qbar := by rw [hQsq]
    let Qlim : ℕ := ⌈Real.log N ^ (B / 4)⌉₊
    let Arc : ℕ × ℕ → Set ℝ := fun p =>
      Set.Icc (((p.2 : ℝ) - 3 * (Qlim : ℝ)) / (p.1 : ℝ) + ξ - 1 / ((p.1 : ℝ) * Qbar))
        (((p.2 : ℝ) - 3 * (Qlim : ℝ)) / (p.1 : ℝ) + ξ + 1 / ((p.1 : ℝ) * Qbar))
    let T : Finset (ℕ × ℕ) := (Finset.Icc 1 Qlim) ×ˢ Finset.range (6 * Qlim + 1)
    let Sec : Set ℝ := ⋃ p ∈ T, Arc p
    let g : ℝ → ℝ := fun α => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 *
      ‖Section2.polynomialKernel F N H (α - ξ)‖
    have hcontS : Continuous (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) := by
      unfold primeSum Kernel.e
      fun_prop
    have hcontK : Continuous (fun α : ℝ => ‖Section2.polynomialKernel F N H (α - ξ)‖) := by
      unfold Section2.polynomialKernel Kernel.e
      fun_prop
    have hcontg : Continuous g := hcontS.mul hcontK
    have hmajor : MeasurableSet (majorArcs N B) := by unfold majorArcs; measurability
    have hminorMeas : MeasurableSet (minorArcs N B) := measurableSet_Icc.diff hmajor
    have hIntg : IntegrableOn g (minorArcs N B) := hcontg.integrableOn_Icc.mono_set Set.diff_subset
    have hg_nonneg : ∀ α : ℝ, 0 ≤ g α := fun α => mul_nonneg (sq_nonneg _) (norm_nonneg _)
    have hKle : ∀ α : ℝ, ‖Section2.polynomialKernel F N H (α - ξ)‖ ≤ H + 1 := by
      intro α
      have hcard := card_win_le F hN0.le hH0.le
      calc ‖Section2.polynomialKernel F N H (α - ξ)‖
          = ‖∑ n ∈ win F N H, Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := rfl
        _ ≤ ∑ n ∈ win F N H, ‖Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := norm_sum_le _ _
        _ = ((win F N H).card : ℝ) := by simp [Kernel.e, Complex.norm_exp]
        _ ≤ H + 1 := hcard
    have hminorSq : (∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤
        C₁ * N * Real.log N := by
      refine le_trans ?_ (hmom N hN1le)
      apply setIntegral_mono_set hcontS.integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun _ h => Set.diff_subset h)
    have harc_le : ∀ p ∈ T,
        (∫ α in minorArcs N B ∩ Arc p, g α) ≤ 8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by
      rintro ⟨q, j⟩ hp
      obtain ⟨hpq, hpj⟩ := Finset.mem_product.mp hp
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hpq).1
      have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      set x0 : ℝ := ((j : ℝ) - 3 * (Qlim : ℝ)) / (q : ℝ) + ξ with hx0
      have hstep1 : (∫ α in minorArcs N B ∩ Arc (q, j), g α) ≤
          (H + 1) * ∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
        calc (∫ α in minorArcs N B ∩ Arc (q, j), g α)
            ≤ ∫ α in minorArcs N B ∩ Arc (q, j),
                (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
              apply integral_mono
              · exact hIntg.mono_set Set.inter_subset_left
              · exact (continuous_const.mul hcontS).integrableOn_Icc.mono_set
                  (Set.inter_subset_left.trans Set.diff_subset)
              · intro α
                dsimp only [g]
                calc ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * ‖Section2.polynomialKernel F N H (α - ξ)‖
                    ≤ ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * (H + 1) :=
                      mul_le_mul_of_nonneg_left (hKle α) (sq_nonneg _)
                  _ = (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by ring
          _ = (H + 1) * ∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 :=
              integral_const_mul _ _
      have hrle : 1 / ((q : ℝ) * Qbar) ≤ 1 / (4 * Q ^ 2) := by
        rw [hquarter]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [hqR, hQbar16]
      have hsub : Arc (q, j) ⊆ Set.Icc (x0 - 1 / (4 * Q ^ 2)) (x0 + 1 / (4 * Q ^ 2)) := by
        intro α hα
        have hα' : ((j : ℝ) - 3 * (Qlim : ℝ)) / (q : ℝ) + ξ - 1 / ((q : ℝ) * Qbar) ≤ α ∧
            α ≤ ((j : ℝ) - 3 * (Qlim : ℝ)) / (q : ℝ) + ξ + 1 / ((q : ℝ) * Qbar) := hα
        rw [hx0]
        constructor <;> linarith [hα'.1, hα'.2, hrle]
      have hcover : minorArcs N B ∩ Arc (q, j) ⊆
          (minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0) ∪
            (minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2))) := by
        rintro α ⟨hαm, hαA⟩
        have h := hsub hαA
        by_cases hle : α ≤ x0
        · exact Or.inl ⟨hαm, h.1, hle⟩
        · exact Or.inr ⟨hαm, le_of_lt (not_le.mp hle), h.2⟩
      have hmeasu : MeasurableSet (minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0) :=
        hminorMeas.inter measurableSet_Icc
      have hmeasv : MeasurableSet (minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2))) :=
        hminorMeas.inter measurableSet_Icc
      have hintS : IntegrableOn (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) (minorArcs N B) :=
        hcontS.integrableOn_Icc.mono_set Set.diff_subset
      have htwo := Farey103.integral_two_cover (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2)
        (fun _ => sq_nonneg _) (minorArcs N B ∩ Arc (q, j))
        (minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0)
        (minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2))) hmeasu hmeasv
        (hintS.mono_set Set.inter_subset_left) (hintS.mono_set Set.inter_subset_left) hcover
      have hw1 : (∫ α in minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0,
          ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤ shortMass ⌊c * N⌋₊ N B Q := by
        have h := le_shortMass ⌊c * N⌋₊ N B Q (x0 - 1 / (4 * Q ^ 2))
        rwa [show x0 - 1 / (4 * Q ^ 2) + 1 / (4 * Q ^ 2) = x0 by ring] at h
      have hw2 : (∫ α in minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2)),
          ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤ shortMass ⌊c * N⌋₊ N B Q :=
        le_shortMass ⌊c * N⌋₊ N B Q x0
      have hstep2 : (∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤
          2 * shortMass ⌊c * N⌋₊ N B Q := by
        calc _ ≤ (∫ α in minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0,
              ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) +
              ∫ α in minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2)),
                ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := htwo
          _ ≤ shortMass ⌊c * N⌋₊ N B Q + shortMass ⌊c * N⌋₊ N B Q := add_le_add hw1 hw2
          _ = 2 * shortMass ⌊c * N⌋₊ N B Q := by ring
      have hs0 : 0 ≤ shortMass ⌊c * N⌋₊ N B Q := shortMass_nonneg _ _ _ _
      calc (∫ α in minorArcs N B ∩ Arc (q, j), g α)
          ≤ (H + 1) * ∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := hstep1
        _ ≤ (H + 1) * (2 * shortMass ⌊c * N⌋₊ N B Q) :=
            mul_le_mul_of_nonneg_left hstep2 (by linarith : (0 : ℝ) ≤ H + 1)
        _ ≤ 8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by nlinarith [hs0]
    have hSecMeas : ∀ p : ℕ × ℕ, MeasurableSet (minorArcs N B ∩ Arc p) :=
      fun p => hminorMeas.inter measurableSet_Icc
    have hsum_le : (∫ α in minorArcs N B ∩ Sec, g α) ≤
        ∑ p ∈ T, ∫ α in minorArcs N B ∩ Arc p, g α :=
      integral_iUnion_finset_le Arc (minorArcs N B) g hIntg hg_nonneg hSecMeas T
    have hQlimR : (Qlim : ℝ) ≤ 2 * Real.log N ^ (B / 4) := by
      have h2 : (Qlim : ℝ) ≤ Real.log N ^ (B / 4) + 1 := by
        have hp : (0 : ℝ) ≤ Real.log N ^ (B / 4) := (Real.rpow_pos_of_pos hL _).le
        have h := Nat.ceil_lt_add_one hp
        simp only [Qlim]
        exact h.le
      have h1 : (1 : ℝ) ≤ Real.log N ^ (B / 4) := Real.one_le_rpow hL1 (by positivity)
      linarith
    have hQlim1 : 1 ≤ Qlim := by
      have h2 : 0 < Real.log N ^ (B / 4) := Real.rpow_pos_of_pos hL _
      have hpos : 0 < Qlim := by
        simp only [Qlim]
        exact Nat.ceil_pos.mpr h2
      omega
    have hcardT : (T.card : ℝ) ≤ 28 * Real.log N ^ (B / 2) := by
      have hcardN : (Finset.Icc 1 Qlim).card ≤ Qlim := by
        rw [Nat.card_Icc]
        omega
      have hcardj : (Finset.range (6 * Qlim + 1)).card ≤ 7 * Qlim := by
        rw [Finset.card_range]
        omega
      have hcardT' : T.card ≤ Qlim * (7 * Qlim) := by
        have hc : T.card = (Finset.Icc 1 Qlim).card * (Finset.range (6 * Qlim + 1)).card := by
          simp only [T, Finset.card_product]
        rw [hc]
        exact Nat.mul_le_mul hcardN hcardj
      have hsq : Real.log N ^ (B / 2) = Real.log N ^ (B / 4) * Real.log N ^ (B / 4) := by
        rw [← Real.rpow_add hL]
        congr 1
        ring
      have hcast : ((Qlim * (7 * Qlim) : ℕ) : ℝ) = 7 * (Qlim : ℝ) * (Qlim : ℝ) := by
        push_cast
        ring
      have hstep1 : (T.card : ℝ) ≤ 7 * (Qlim : ℝ) * (Qlim : ℝ) := by
        rw [← hcast]
        exact_mod_cast hcardT'
      have hstep2 : 7 * (Qlim : ℝ) * (Qlim : ℝ) ≤ 7 * (2 * Real.log N ^ (B / 4)) *
          (2 * Real.log N ^ (B / 4)) := by
        have h0 : (0 : ℝ) ≤ (Qlim : ℝ) := Nat.cast_nonneg Qlim
        apply mul_le_mul
        · nlinarith
        · exact hQlimR
        · exact h0
        · positivity
      calc (T.card : ℝ) ≤ 7 * (Qlim : ℝ) * (Qlim : ℝ) := hstep1
        _ ≤ 7 * (2 * Real.log N ^ (B / 4)) * (2 * Real.log N ^ (B / 4)) := hstep2
        _ = 28 * Real.log N ^ (B / 2) := by rw [hsq]; ring
    have hTsum : ∑ p ∈ T, (∫ α in minorArcs N B ∩ Arc p, g α) ≤
        512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q := by
      have hs0 : 0 ≤ shortMass ⌊c * N⌋₊ N B Q := shortMass_nonneg _ _ _ _
      have hL2 : 0 < Real.log N ^ (B / 2) := Real.rpow_pos_of_pos hL _
      have hstep : ∑ p ∈ T, (∫ α in minorArcs N B ∩ Arc p, g α) ≤
          ∑ p ∈ T, (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) := Finset.sum_le_sum harc_le
      have hconst : ∑ p ∈ T, (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) =
          (T.card : ℝ) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hconst] at hstep
      have hmono : (T.card : ℝ) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) ≤
          (28 * Real.log N ^ (B / 2)) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) := by
        apply mul_le_mul_of_nonneg_right hcardT
        have hsa := shortMass_nonneg ⌊c * N⌋₊ N B Q
        have hsb : (0 : ℝ) ≤ 8 * (H + 1) := by linarith
        exact mul_nonneg hsb hsa
      have hfin : (28 * Real.log N ^ (B / 2)) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) ≤
          512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q := by
        have hH2 : H + 1 ≤ 2 * H := by linarith
        have e1 : (28 * Real.log N ^ (B / 2)) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) =
            224 * Real.log N ^ (B / 2) * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by ring
        rw [e1]
        have hLH : 0 ≤ Real.log N ^ (B / 2) * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by
          have hsa := shortMass_nonneg ⌊c * N⌋₊ N B Q
          have hsb : (0 : ℝ) ≤ Real.log N ^ (B / 2) * (H + 1) := by positivity
          exact mul_nonneg hsb hsa
        have hLH2 : Real.log N ^ (B / 2) * (H + 1) * shortMass ⌊c * N⌋₊ N B Q ≤
            Real.log N ^ (B / 2) * (2 * H) * shortMass ⌊c * N⌋₊ N B Q := by
          apply mul_le_mul_of_nonneg_right _ hs0
          apply mul_le_mul_of_nonneg_left hH2 hL2.le
        nlinarith [hLH, hLH2]
      exact hstep.trans (hmono.trans hfin)
    have hmeasSec : MeasurableSet Sec := by
      simp only [Sec]
      exact Finset.measurableSet_biUnion T (fun p _ => measurableSet_Icc)
    have hT_le : (∫ α in minorArcs N B \ Sec, g α) ≤
        C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) := by
      have hhyp : ∀ α ∈ minorArcs N B \ Sec, ∀ q : ℕ, 0 < q →
          (q : ℝ) ≤ Real.log N ^ (B / 4) → ∀ a : ℤ, Nat.Coprime a.natAbs q →
          1 / ((q : ℝ) * Qbar) < |(α - ξ) - (a : ℝ) / q| := by
        intro α hα q hq hqq a hcop
        by_contra hcon
        push Not at hcon
        have hαI : α ∈ Set.Icc (0 : ℝ) 1 := Set.diff_subset hα.1
        have hqQlim : q ≤ Qlim := by
          have h1 : (q : ℝ) ≤ (⌈Real.log N ^ (B / 4)⌉₊ : ℝ) := hqq.trans (Nat.le_ceil _)
          have h2 : (q : ℝ) ≤ (Qlim : ℝ) := by
            simp only [Qlim]
            exact h1
          exact_mod_cast h2
        have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
        have hprod : 1 ≤ (q : ℝ) * Qbar := by nlinarith [hqR, hQbar16]
        have hsmall : 1 / ((q : ℝ) * Qbar) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hprod
        have hβ : |α - ξ| ≤ 2 := by
          have h1 : |α| ≤ 1 := by
            rw [abs_le]
            exact ⟨by linarith [hαI.1], by linarith [hαI.2]⟩
          calc |α - ξ| ≤ |α| + |ξ| := abs_sub α ξ
            _ ≤ 2 := by linarith [h1, hξb]
        have hbound : |(a : ℝ) / q| ≤ |α - ξ| + 1 / ((q : ℝ) * Qbar) := by
          have h2 : |(a : ℝ) / q| ≤ |(a : ℝ) / q - (α - ξ)| + |α - ξ| := by
            have h := abs_add_le ((a : ℝ) / q - (α - ξ)) (α - ξ)
            rwa [show ((a : ℝ) / q - (α - ξ)) + (α - ξ) = (a : ℝ) / q by ring] at h
          have h3 : |(a : ℝ) / q - (α - ξ)| = |(α - ξ) - (a : ℝ) / q| := abs_sub_comm _ _
          linarith [h2, h3, hcon]
        have habs : |(a : ℝ)| ≤ 3 * (Qlim : ℝ) := by
          have hmul : |(a : ℝ) / q| * (q : ℝ) = |(a : ℝ)| := by
            rw [abs_div, abs_of_pos hqpos]
            field_simp
          have h1 : |(a : ℝ) / q| * (q : ℝ) ≤ (|α - ξ| + 1 / ((q : ℝ) * Qbar)) * (q : ℝ) :=
            mul_le_mul_of_nonneg_right hbound hqpos.le
          rw [hmul] at h1
          have h2 : |α - ξ| + 1 / ((q : ℝ) * Qbar) ≤ 3 := by linarith
          have h3 : (|α - ξ| + 1 / ((q : ℝ) * Qbar)) * (q : ℝ) ≤ 3 * (q : ℝ) :=
            mul_le_mul_of_nonneg_right h2 hqpos.le
          have h4 : (q : ℝ) ≤ (Qlim : ℝ) := by exact_mod_cast hqQlim
          linarith
        have hlow : -(3 * (Qlim : ℝ)) ≤ (a : ℝ) := (abs_le.mp habs).1
        have hhigh : (a : ℝ) ≤ 3 * (Qlim : ℝ) := (abs_le.mp habs).2
        have hnonneg : (0 : ℤ) ≤ a + 3 * (Qlim : ℤ) := by
          have hh : (-(3 * (Qlim : ℤ))) ≤ a := by exact_mod_cast hlow
          linarith
        have htop : a + 3 * (Qlim : ℤ) ≤ 6 * (Qlim : ℤ) := by
          have hh : a ≤ 3 * (Qlim : ℤ) := by exact_mod_cast hhigh
          linarith
        have hcast : (((a + 3 * (Qlim : ℤ)).toNat : ℤ)) = a + 3 * (Qlim : ℤ) :=
          Int.toNat_of_nonneg hnonneg
        have hlt : (a + 3 * (Qlim : ℤ)).toNat < 6 * Qlim + 1 := by
          have h1 : ((a + 3 * (Qlim : ℤ)).toNat : ℤ) ≤ 6 * (Qlim : ℤ) := by
            rw [hcast]
            exact htop
          have h2 : (a + 3 * (Qlim : ℤ)).toNat ≤ 6 * Qlim := by exact_mod_cast h1
          omega
        have hmem : (q, (a + 3 * (Qlim : ℤ)).toNat) ∈ T := by
          simp only [T, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
          exact ⟨⟨hq, hqQlim⟩, hlt⟩
        have harc_eq : ((a + 3 * (Qlim : ℤ)).toNat : ℝ) - 3 * (Qlim : ℝ) = (a : ℝ) := by
          have h1 : ((((a + 3 * (Qlim : ℤ)).toNat : ℤ)) : ℝ) = ((a + 3 * (Qlim : ℤ) : ℤ) : ℝ) := by
            rw [hcast]
          push_cast at h1
          linarith
        have hmemArc : α ∈ Arc (q, (a + 3 * (Qlim : ℤ)).toNat) := by
          have e : ((a + 3 * (Qlim : ℤ)).toNat : ℝ) - 3 * (Qlim : ℝ) = (a : ℝ) := harc_eq
          simp only [Arc, e, Set.mem_Icc]
          rw [abs_le] at hcon
          constructor <;> linarith [hcon.1, hcon.2]
        have hmemSec : α ∈ Sec := by
          simp only [Sec]
          exact Set.mem_iUnion.mpr ⟨(q, (a + 3 * (Qlim : ℤ)).toNat),
            Set.mem_iUnion.mpr ⟨hmem, hmemArc⟩⟩
        exact hα.2 hmemSec
      have hpoint : ∀ α ∈ minorArcs N B \ Sec,
          ‖Section2.polynomialKernel F N H (α - ξ)‖ ≤
            C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
              (8 * Section2.weylExponent F)) := by
        intro α hα
        refine hdecay N H (α - ξ) hN2le hH hHu ?_
        intro q hq hqq a hcop
        have h := hhyp α hα q hq hqq a hcop
        rwa [← hQbar]
      have hcontW : Continuous (fun α : ℝ =>
          (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
            (8 * Section2.weylExponent F))) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) :=
        continuous_const.mul hcontS
      have hce : (0 : ℝ) ≤ C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F)) := by positivity
      calc (∫ α in minorArcs N B \ Sec, g α)
          ≤ ∫ α in minorArcs N B \ Sec, (C₂ * H * Real.log N ^
              (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F))) *
                ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
            apply integral_mono_ae
            · exact hIntg.mono_set Set.diff_subset
            · exact hcontW.integrableOn_Icc.mono_set (Set.diff_subset.trans Set.diff_subset)
            · filter_upwards [ae_restrict_mem (hminorMeas.diff hmeasSec)] with α hα
              dsimp only [g]
              calc ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * ‖Section2.polynomialKernel F N H (α - ξ)‖
                  ≤ ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * (C₂ * H * Real.log N ^
                      (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
                        (8 * Section2.weylExponent F))) :=
                    mul_le_mul_of_nonneg_left (hpoint α hα) (sq_nonneg _)
                _ = (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
                      (8 * Section2.weylExponent F))) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by ring
        _ = (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
              (8 * Section2.weylExponent F))) * ∫ α in minorArcs N B \ Sec,
                ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := integral_const_mul _ _
        _ ≤ (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
              (8 * Section2.weylExponent F))) * (C₁ * N * Real.log N) := by
            apply mul_le_mul_of_nonneg_left _ hce
            calc (∫ α in minorArcs N B \ Sec, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2)
                ≤ ∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 :=
                  setIntegral_mono_set hcontS.integrableOn_Icc
                    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
                    (Filter.Eventually.of_forall (fun _ h => Set.diff_subset h.1))
              _ ≤ C₁ * N * Real.log N := hmom N hN1le
    have hsplit : (∫ α in minorArcs N B, g α) =
        (∫ α in minorArcs N B ∩ Sec, g α) + ∫ α in minorArcs N B \ Sec, g α := by
      have hunion : (minorArcs N B ∩ Sec) ∪ (minorArcs N B \ Sec) = minorArcs N B := by
        ext α
        constructor
        · rintro (h | h)
          · exact h.1
          · exact h.1
        · intro h
          by_cases hs : α ∈ Sec
          · exact Or.inl ⟨h, hs⟩
          · exact Or.inr ⟨h, hs⟩
      have hdisj : Disjoint (minorArcs N B ∩ Sec) (minorArcs N B \ Sec) := by
        rw [Set.disjoint_left]
        rintro α ⟨-, hs⟩ ⟨-, hns⟩
        exact hns hs
      have h := setIntegral_union hdisj (hminorMeas.diff hmeasSec)
        (hIntg.mono_set Set.inter_subset_left) (hIntg.mono_set Set.diff_subset)
      rwa [hunion] at h
    have hexp : -(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F) + 1 =
        -(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
          (8 * Section2.weylExponent F) - 1 := by
      have hK : Section2.weylExponent F ≠ 0 := by
        unfold Section2.weylExponent
        positivity
      field_simp
      ring
    have hW : Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
        (8 * Section2.weylExponent F)) * Real.log N =
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F) + 1) := by
      have h := Real.rpow_add hL
        (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F)) 1
      simp only [Real.rpow_one] at h
      exact h.symm
    have hshort0 : 0 ≤ shortMass ⌊c * N⌋₊ N B Q := shortMass_nonneg _ _ _ _
    have hLB : 0 ≤ Real.log N ^ (B / 2) := (Real.rpow_pos_of_pos hL _).le
    have hLE : 0 ≤ Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
        16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) :=
      (Real.rpow_pos_of_pos hL _).le
    have hsecond : C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
        (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) =
        C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
          16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
      have e1 : C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) =
          C₁ * C₂ * H * N * (Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
            (8 * Section2.weylExponent F)) * Real.log N) := by ring
      rw [e1, hW, hexp]
    have hterm1 : 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q ≤
        max 512 (max (2 * C₁) (C₁ * C₂)) * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B Q := by
      have h512 : (512 : ℝ) ≤ max 512 (max (2 * C₁) (C₁ * C₂)) := le_max_left _ _
      have h0 : 0 ≤ H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q := by
        have hsa := shortMass_nonneg ⌊c * N⌋₊ N B Q
        have hsb : (0 : ℝ) ≤ H * Real.log N ^ (B / 2) := by positivity
        exact mul_nonneg hsb hsa
      calc 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q =
          512 * (H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q) := by ring
        _ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) *
              (H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q) :=
            mul_le_mul_of_nonneg_right h512 h0
        _ = _ := by ring
    have hterm2 : C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
        16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) ≤
        max 512 (max (2 * C₁) (C₁ * C₂)) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
      have hcc : C₁ * C₂ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have h0 : 0 ≤ H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
          16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by positivity
      calc C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) =
          (C₁ * C₂) * (H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1)) := by ring
        _ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) * (H * N * Real.log N ^
            (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
              (8 * Section2.weylExponent F) - 1)) := mul_le_mul_of_nonneg_right hcc h0
        _ = _ := by ring
    calc kernelMoment F ⌊c * N⌋₊ N H B ξ
        = ∫ α in minorArcs N B, g α := rfl
      _ = (∫ α in minorArcs N B ∩ Sec, g α) + ∫ α in minorArcs N B \ Sec, g α := hsplit
      _ ≤ 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q +
          C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
            (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) :=
          add_le_add (hsum_le.trans hTsum) hT_le
      _ = 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q +
          C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
          rw [hsecond]
      _ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) * H * Real.log N ^ (B / 2) *
            shortMass ⌊c * N⌋₊ N B Q +
          max 512 (max (2 * C₁) (C₁ * C₂)) * H * N *
            Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
              (8 * Section2.weylExponent F) - 1) := add_le_add hterm1 hterm2
  · refine ⟨2 * C₁ + 1, N₁ + (Real.exp 1 + 3), by positivity, by linarith, ?_⟩
    intro N H hN hH hHu ξ hξ
    have hN1le : N₁ ≤ N := by linarith
    have hNexp : Real.exp 1 ≤ N := by linarith
    have hN3 : 3 ≤ N := hN₁.trans hN1le
    have hN0 : 0 < N := by linarith
    have hNgt1 : 1 ≤ N := by linarith
    have hH1 : 1 ≤ H := (Real.one_le_rpow hNgt1 (by positivity)).trans hH
    have hL : 0 < Real.log N := Real.log_pos (by linarith)
    have hL1 : 1 ≤ Real.log N := by
      have h := Real.log_le_log (Real.exp_pos 1) hNexp
      simpa using h
    have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
    have hKpos : 0 < Section2.weylExponent F := by
      unfold Section2.weylExponent
      positivity
    have hBle : B ≤ 4 * (F.natDegree : ℝ) ^ 2 := by
      have hle : B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1 ≤ 0 := not_lt.mp hD
      have hk : (1 : ℝ) ≤ (F.natDegree : ℝ) := by exact_mod_cast hF.1
      nlinarith
    have hpow1 : 1 ≤ -(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
        (8 * Section2.weylExponent F) - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      nlinarith [hBle, hKpos]
    have hKle : ∀ α : ℝ, ‖Section2.polynomialKernel F N H (α - ξ)‖ ≤ H + 1 := by
      intro α
      have hcard := card_win_le F hN0.le hH0.le
      calc ‖Section2.polynomialKernel F N H (α - ξ)‖
          = ‖∑ n ∈ win F N H, Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := rfl
        _ ≤ ∑ n ∈ win F N H, ‖Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := norm_sum_le _ _
        _ = ((win F N H).card : ℝ) := by simp [Kernel.e, Complex.norm_exp]
        _ ≤ H + 1 := hcard
    have hcontS : Continuous (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) := by
      unfold primeSum Kernel.e
      fun_prop
    have hcontK : Continuous (fun α : ℝ => ‖Section2.polynomialKernel F N H (α - ξ)‖) := by
      unfold Section2.polynomialKernel Kernel.e
      fun_prop
    have hminorSq : (∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤
        C₁ * N * Real.log N := by
      refine le_trans ?_ (hmom N hN1le)
      apply setIntegral_mono_set hcontS.integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun _ h => Set.diff_subset h)
    have hstep : (∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 *
        ‖Section2.polynomialKernel F N H (α - ξ)‖) ≤
        (H + 1) * ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
      calc _ ≤ ∫ α in minorArcs N B, (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
            apply integral_mono
            · exact (hcontS.mul hcontK).integrableOn_Icc.mono_set Set.diff_subset
            · exact (continuous_const.mul hcontS).integrableOn_Icc.mono_set Set.diff_subset
            · intro α
              calc ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * ‖Section2.polynomialKernel F N H (α - ξ)‖
                  ≤ ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * (H + 1) :=
                    mul_le_mul_of_nonneg_left (hKle α) (sq_nonneg _)
                _ = (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by ring
        _ = (H + 1) * ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 :=
            integral_const_mul _ _
    have hpow : Real.log N ≤ Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
        16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1 hpow1
      simpa using h
    have hcoef : C₁ * (H + 1) * N ≤ (2 * C₁ + 1) * H * N := by
      have h1 : C₁ * (H + 1) * N = C₁ * H * N + C₁ * N := by ring
      have hcN : 0 ≤ C₁ * N := mul_nonneg hC₁.le hN0.le
      have hCHN : 0 ≤ C₁ * H * N := by positivity
      have h2 : C₁ * N ≤ C₁ * H * N := by
        nlinarith [hcN, hCHN, hH1, hC₁]
      have h4 : 0 ≤ H * N := by positivity
      nlinarith [h1, h2, hCHN, h4, hcN]
    have hfin : (H + 1) * (C₁ * N * Real.log N) ≤
        (2 * C₁ + 1) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
      have h1 : (H + 1) * (C₁ * N * Real.log N) = C₁ * (H + 1) * N * Real.log N := by ring
      rw [h1]
      have h2 : C₁ * (H + 1) * N * Real.log N ≤ C₁ * (H + 1) * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
        have := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ C₁ * (H + 1) * N)
        calc C₁ * (H + 1) * N * Real.log N = (C₁ * (H + 1) * N) * Real.log N := by ring
          _ ≤ (C₁ * (H + 1) * N) * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
              16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := this
          _ = C₁ * (H + 1) * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
              16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by ring
      have h3 : C₁ * (H + 1) * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
          16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) ≤
          (2 * C₁ + 1) * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hcoef
      exact h2.trans h3
    have hterm : (2 * C₁ + 1) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) ≤
        (2 * C₁ + 1) * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        (2 * C₁ + 1) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
      have h1 : 0 ≤ (2 * C₁ + 1) * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B (fareyOrder F N H B) := by
        have hsa := shortMass_nonneg ⌊c * N⌋₊ N B (fareyOrder F N H B)
        have hsb : (0 : ℝ) ≤ (2 * C₁ + 1) * H * Real.log N ^ (B / 2) := by positivity
        exact mul_nonneg hsb hsa
      linarith [h1]
    calc kernelMoment F ⌊c * N⌋₊ N H B ξ
        = ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 *
            ‖Section2.polynomialKernel F N H (α - ξ)‖ := rfl
      _ ≤ (H + 1) * ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := hstep
      _ ≤ (H + 1) * (C₁ * N * Real.log N) :=
          mul_le_mul_of_nonneg_left hminorSq (by linarith)
      _ ≤ (2 * C₁ + 1) * H * N *
            Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
              (8 * Section2.weylExponent F) - 1) := hfin
      _ ≤ _ := hterm


/-- LEAF. Page 483 equations 12 through 14.
A short interval meets at most two Farey cells of order Q.
Each cell lies in its enclosing puncturedArc from task88. -/
theorem leaf_farey_cover (M : ℕ) (N B Q : ℝ) (hQ : 2 ≤ Q) :
    shortMass M N B Q ≤ 2 * localMass M N B Q := by
  unfold shortMass
  apply csSup_le
  · exact ⟨∫ α in minorArcs N B ∩ Set.Icc (0 : ℝ) (0 + 1 / (4 * Q ^ 2)),
      ‖primeSum M α‖ ^ 2, 0, rfl⟩
  · rintro x ⟨t, rfl⟩
    obtain ⟨q, hq, hqQ, a, ha, r, hr, hrQ, b, hb, hcover⟩ := Farey103.rational_two_cover t Q hQ
    let s := minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2))
    let u := puncturedArc N B Q q a
    let v := puncturedArc N B Q r b
    have hsub : s ⊆ u ∪ v := by
      intro α hα
      have hnot : α ∉ majorArcs N B := hα.1.2
      rcases hcover hα.2 with hu | hv
      · exact Or.inl ⟨hu, hnot⟩
      · exact Or.inr ⟨hv, hnot⟩
    have hmeas (k : ℕ) (z : ℤ) : MeasurableSet (puncturedArc N B Q k z) := by
      unfold puncturedArc majorArcs
      measurability
    have hint (k : ℕ) (z : ℤ) : IntegrableOn (fun α => ‖primeSum M α‖ ^ 2)
        (puncturedArc N B Q k z) := by
      have hcont : Continuous (fun α : ℝ => ‖primeSum M α‖ ^ 2) := by
        unfold primeSum Kernel.e
        fun_prop
      exact hcont.integrableOn_Icc.mono_set Set.diff_subset
    have hlocal (k : ℕ) (z : ℤ) (hk : 0 < k) (hkQ : (k : ℝ) ≤ Q)
        (hz : Nat.Coprime z.natAbs k) :
        (∫ α in puncturedArc N B Q k z, ‖primeSum M α‖ ^ 2) ≤ localMass M N B Q := by
      unfold localMass
      exact le_csSup (Farey103.localMass_bddAbove M N B Q hQ) ⟨k, hk, hkQ, z, hz, rfl⟩
    have htwo := Farey103.integral_two_cover (fun α => ‖primeSum M α‖ ^ 2)
      (fun _ => sq_nonneg _) s u v (hmeas q a) (hmeas r b) (hint q a) (hint r b) hsub
    calc
      _ ≤ (∫ α in u, ‖primeSum M α‖ ^ 2) + ∫ α in v, ‖primeSum M α‖ ^ 2 := htwo
      _ ≤ localMass M N B Q + localMass M N B Q := add_le_add
        (hlocal q a hq hqQ ha) (hlocal r b hr hrQ hb)
      _ = _ := by ring

/-- The sealed minor reduction from Parseval, Weyl localization and Farey covering.
CONDITIONAL ON the three smaller leaves. -/
theorem minor (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (c : ℝ) (hc : 0 < c)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B)
    (hparam : ∃ NP : ℝ, 3 ≤ NP ∧ ∀ N H : ℝ, NP ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H → 2 ≤ fareyOrder F N H B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      minorError F ⌊c * N⌋₊ N H B ≤
        C * H * N * Real.log N ^ (B / 2 + 1) *
          localMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        C * H * N ^ 2 * Real.log N ^
          (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F)) := by
  obtain ⟨CP, NP, hCP, hNP, hp⟩ := leaf_parseval F c hc
  obtain ⟨CW, NW, hCW, hNW, hw⟩ := leaf_weyl_localization F hF hW c hc ε B hε hB
  obtain ⟨NG, hNG, hg⟩ := hparam
  refine ⟨2 * CP * CW, max NP (max NW NG), by positivity,
    hNP.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu hcut
  have hNP' := (le_max_left NP (max NW NG)).trans hN
  have hNW' := (le_max_left NW NG).trans ((le_max_right NP (max NW NG)).trans hN)
  have hNG' := (le_max_right NW NG).trans ((le_max_right NP (max NW NG)).trans hN)
  have hN3 := hNP.trans hNP'
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  let Q := fareyOrder F N H B
  let M := ⌊c * N⌋₊
  let E := -(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
    (8 * Section2.weylExponent F)
  let U := 2 * CW * H * Real.log N ^ (B / 2) * localMass M N B Q +
    CW * H * N * Real.log N ^ (E - 1)
  have hm := localMass_nonneg M N B Q
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcover := leaf_farey_cover M N B Q (hg N H hNG' hH)
  have hinner : ∀ ξ ∈ minorArcs N B, kernelMoment F M N H B ξ ≤ U := by
    intro ξ hξ
    calc
      _ ≤ CW * H * Real.log N ^ (B / 2) * shortMass M N B Q +
        CW * H * N * Real.log N ^ (E - 1) := hw N H hNW' hH hHu ξ hξ
      _ ≤ CW * H * Real.log N ^ (B / 2) * (2 * localMass M N B Q) +
        CW * H * N * Real.log N ^ (E - 1) := by gcongr
      _ = U := by dsimp [U]; ring
  have hp' := hp N H B U hNP' hU (fun n hn => (hcut n hn).1) hinner
  calc
    _ ≤ CP * N * Real.log N * U := hp'
    _ = 2 * CP * CW * H * N * Real.log N ^ (B / 2 + 1) * localMass M N B Q +
        CP * CW * H * N ^ 2 * Real.log N ^ E := by
      dsimp [U]
      rw [Real.rpow_add hL, Real.rpow_one,
        show Real.log N ^ E = Real.log N * Real.log N ^ (E - 1) by
          calc
            _ = Real.log N ^ (1 + (E - 1)) := by congr 1; ring
            _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]]
      ring
    _ ≤ _ := by
      have hcoef : CP * CW ≤ 2 * CP * CW := by nlinarith [mul_pos hCP hCW]
      gcongr

end
end LeanLab.Perelli1996.Decomp103
