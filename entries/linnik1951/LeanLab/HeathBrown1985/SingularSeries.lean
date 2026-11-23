module

public import Mathlib
public import LeanLab.HeathBrown1985.Lemma1
public import LeanLab.ChenExplicit.Reductions

/-!
P0096 Heath-Brown 1985, page 57, the singular series: the function
`g_m(q) = μ(q)²/φ(q) Σ_{d ∣ q} d μ(d) E_{d,m}/φ(d)`, its product form
`Π_{p ∣ q} (1 - p E_{p,m}/(p-1))/(p-1)` for squarefree `q`, the bound
`|g_m(q)| ≤ 4 (q, m) d(q) q⁻²` (the paper's `(q,m)/φ(q)² ≪ (q,m) d(q)/q²`), the tail
`Σ_{q > F} (q, m) d(q) q⁻² ≤ (6 + 2 log F) d(m)²/F` (the paper's use of 2.3), and the Euler
product `Σ_q g_m(q) = 𝔖(m)` for `m ≥ 1`.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `E_{d,m} = 1` if `(d, m) = 1`, else `0`. -/
def Ecop (d m : ℕ) : ℝ := if Nat.Coprime m d then 1 else 0

/-- The local factor `v_m(p) = (1 - p E_{p,m}/(p-1))/(p-1)`. -/
def vloc (m p : ℕ) : ℝ := (1 - (p : ℝ) * Ecop p m / ((p : ℝ) - 1)) / ((p : ℝ) - 1)

/-- `g_m(q) = μ(q)²/φ(q) Σ_{d ∣ q} d μ(d) E_{d,m}/φ(d)`, the `q`-term of the main term, page 57. -/
def gm (m q : ℕ) : ℝ :=
  (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) *
    ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Ecop d m / (Nat.totient d : ℝ)

/-- `f(d) = d E_{d,m}/φ(d)` as an arithmetic function. -/
def fE (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => (d : ℝ) * Ecop d m / (Nat.totient d : ℝ), by simp⟩

theorem fE_apply (m d : ℕ) : fE m d = (d : ℝ) * Ecop d m / (Nat.totient d : ℝ) := rfl

theorem fE_mult (m : ℕ) : (fE m).IsMultiplicative := by
  refine ⟨by simp [fE_apply, Ecop], fun {a b} hab => ?_⟩
  simp only [fE_apply, Ecop]
  rw [Nat.totient_mul hab]
  push_cast
  by_cases ha : Nat.Coprime m a <;> by_cases hb : Nat.Coprime m b
  · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨ha, hb⟩), if_pos ha, if_pos hb]; ring
  · rw [if_neg (fun h => hb (Nat.coprime_mul_iff_right.mp h).2), if_neg hb]; ring
  · rw [if_neg (fun h => ha (Nat.coprime_mul_iff_right.mp h).1), if_neg ha]; ring
  · rw [if_neg (fun h => ha (Nat.coprime_mul_iff_right.mp h).1), if_neg ha]; ring

theorem totient_prime_real {p : ℕ} (hp : p.Prime) : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]

/-- The product form of `g_m(q)`. -/
theorem gm_eq (m q : ℕ) :
    gm m q = if Squarefree q then ∏ p ∈ q.primeFactors, vloc m p else 0 := by
  split_ifs with hsq
  · unfold gm
    have hin : ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Ecop d m / (Nat.totient d : ℝ) =
        ∑ d ∈ q.divisors, (μ d : ℝ) * fE m d := by
      apply sum_congr rfl; intro d _; rw [fE_apply]; ring
    rw [hin, ← (fE_mult m).prodPrimeFactors_one_sub_of_squarefree _ hsq,
      totient_eq_prod_of_squarefree q hsq, ArithmeticFunction.moebius_apply_of_squarefree hsq]
    unfold vloc
    rw [prod_div_distrib]
    push_cast
    rw [← pow_mul, show (ArithmeticFunction.cardFactors q * 2) =
      2 * ArithmeticFunction.cardFactors q by ring, pow_mul]
    simp only [neg_one_sq, one_pow]
    rw [div_mul_eq_mul_div, one_mul]
    congr 1
    apply prod_congr rfl; intro p hp
    rw [fE_apply, totient_prime_real (Nat.prime_of_mem_primeFactors hp)]
  · unfold gm
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp

theorem gm_zero (m : ℕ) : gm m 0 = 0 := by
  rw [gm_eq, if_neg (by simp)]

theorem gm_one (m : ℕ) : gm m 1 = 1 := by
  rw [gm_eq, if_pos squarefree_one]; simp

theorem gm_mul (m : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) : gm m (a * b) = gm m a * gm m b := by
  rw [gm_eq, gm_eq, gm_eq]
  by_cases ha : Squarefree a <;> by_cases hb : Squarefree b
  · rw [if_pos (Nat.squarefree_mul_iff.mpr ⟨hab, ha, hb⟩), if_pos ha, if_pos hb,
      Nat.Coprime.primeFactors_mul hab, prod_union hab.disjoint_primeFactors]
  · rw [if_neg (fun h => hb (Nat.squarefree_mul_iff.mp h).2.2), if_neg hb]; ring
  · rw [if_neg (fun h => ha (Nat.squarefree_mul_iff.mp h).2.1), if_neg ha]; ring
  · rw [if_neg (fun h => ha (Nat.squarefree_mul_iff.mp h).2.1), if_neg ha]; ring

theorem vloc_dvd {m p : ℕ} (hp : p.Prime) (h : p ∣ m) : vloc m p = 1 / ((p : ℝ) - 1) := by
  unfold vloc Ecop
  have : ¬ Nat.Coprime m p := fun hc =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc.symm h)
  rw [if_neg this]; simp

theorem vloc_not_dvd {m p : ℕ} (hp : p.Prime) (h : ¬ p ∣ m) :
    vloc m p = -1 / ((p : ℝ) - 1) ^ 2 := by
  unfold vloc Ecop
  have : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm
  rw [if_pos this]
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp; ring

theorem abs_vloc_le_one {m p : ℕ} (hp : p.Prime) : |vloc m p| ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  by_cases h : p ∣ m
  · rw [vloc_dvd hp h, abs_of_pos (by apply div_pos one_pos; linarith), div_le_one (by linarith)]
    linarith
  · have hp1 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
    rw [vloc_not_dvd hp h, abs_div, abs_neg, abs_one, abs_of_pos hp1, div_le_one hp1]
    nlinarith

theorem abs_gm_le_one (m q : ℕ) : |gm m q| ≤ 1 := by
  rw [gm_eq]
  split_ifs
  · rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun p hp => abs_vloc_le_one (Nat.prime_of_mem_primeFactors hp))
  · simp

/-! ### `|g_m(q)| ≤ 4 (q, m) d(q) / q²` -/

theorem two_pow_le_card_divisors (q : ℕ) (hq : 1 ≤ q) :
    (2 : ℝ) ^ q.primeFactors.card ≤ (q.divisors.card : ℝ) := by
  have h := sum_sqfree_divisors_prod q (by omega) (fun _ => 1)
  simp only [prod_const_one, sum_const, nsmul_eq_mul, mul_one] at h
  have e : ∏ p ∈ q.primeFactors, (1 + (1 : ℝ)) = 2 ^ q.primeFactors.card := by
    rw [prod_const]; norm_num
  rw [← e, ← h]
  exact_mod_cast card_le_card (filter_subset _ _)

theorem prod_filter_dvd_le_gcd (q m : ℕ) (hq : 1 ≤ q) :
    (∏ p ∈ q.primeFactors.filter (· ∣ m), (p : ℝ)) ≤ (Nat.gcd q m : ℝ) := by
  have hd : ∏ p ∈ q.primeFactors.filter (· ∣ m), p ∣ Nat.gcd q m := by
    apply Finset.prod_primes_dvd
    · intro p hp; exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).prime
    · intro p hp
      exact Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have hg : 0 < Nat.gcd q m := Nat.gcd_pos_of_pos_left m (by omega)
  have := Nat.le_of_dvd hg hd
  have h' : ((∏ p ∈ q.primeFactors.filter (· ∣ m), p : ℕ) : ℝ) ≤ Nat.gcd q m := by
    exact_mod_cast this
  push_cast at h'; exact h'

/-- `b_p = 2` for `p ≤ 3`, else `1`. -/
def bp (p : ℕ) : ℝ := if p ≤ 3 then 2 else 1

theorem prod_bp_le (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) : ∏ p ∈ s, bp p ≤ 4 := by
  unfold bp
  rw [prod_ite, prod_const_one, mul_one, prod_const]
  have hc : (s.filter (· ≤ 3)).card ≤ 2 := by
    have : s.filter (· ≤ 3) ⊆ Icc 2 3 := by
      intro p hp
      simp only [mem_filter] at hp
      simp only [mem_Icc]; exact ⟨hs p hp.1, hp.2⟩
    have := card_le_card this
    simpa using this
  calc (2 : ℝ) ^ (s.filter (· ≤ 3)).card ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hc
    _ = 4 := by norm_num

theorem abs_vloc_le' {m p : ℕ} (hp : p.Prime) :
    |vloc m p| ≤ (if p ∣ m then (p : ℝ) else 1) * (2 * bp p) / (p : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hb1 : 1 ≤ bp p := by unfold bp; split_ifs <;> norm_num
  have hp0 : (0 : ℝ) < p := by linarith
  by_cases h : p ∣ m
  · rw [vloc_dvd hp h, abs_of_pos (by apply div_pos one_pos; linarith), if_pos h,
      div_le_div_iff₀ (by linarith) (by positivity)]
    have h1 : (p : ℝ) ≤ 2 * bp p * ((p : ℝ) - 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hp0.le]
  · have hp1 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
    rw [vloc_not_dvd hp h, abs_div, abs_neg, abs_one, abs_of_pos hp1, if_neg h,
      div_le_div_iff₀ hp1 (by positivity)]
    unfold bp
    split_ifs with h3
    · nlinarith
    · have h4 : (4 : ℝ) ≤ p := by
        have : 4 ≤ p := by omega
        exact_mod_cast this
      nlinarith

/-- **`|g_m(q)| ≤ 4 (q, m) d(q)/q²`**, the paper's `(q,m)/φ(q)² ≪ (q,m) d(q)/q²`. -/
theorem abs_gm_le (m q : ℕ) (hq : 1 ≤ q) :
    |gm m q| ≤ 4 * (Nat.gcd q m : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 := by
  rw [gm_eq]
  split_ifs with hsq
  · have hP : ∀ p ∈ q.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [abs_prod]
    refine (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun p hp => abs_vloc_le' (m := m) (Nat.prime_of_mem_primeFactors hp))).trans ?_
    rw [prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_pow]
    have hqP : (∏ p ∈ q.primeFactors, (p : ℝ)) = q := by
      have := congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hsq)
      push_cast at this; exact this
    rw [hqP]
    have hA : ∏ p ∈ q.primeFactors, (if p ∣ m then (p : ℝ) else 1) ≤ Nat.gcd q m := by
      rw [prod_ite, prod_const_one, mul_one]; exact prod_filter_dvd_le_gcd q m hq
    have hA0 : 0 ≤ ∏ p ∈ q.primeFactors, (if p ∣ m then (p : ℝ) else 1) :=
      prod_nonneg (fun p hp => by have := hP p hp; split_ifs <;> linarith)
    have h2 : ∏ p ∈ q.primeFactors, (2 : ℝ) ≤ q.divisors.card := by
      rw [prod_const]; exact two_pow_le_card_divisors q hq
    have hb := prod_bp_le q.primeFactors (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have hb0 : 0 ≤ ∏ p ∈ q.primeFactors, bp p :=
      prod_nonneg (fun p _ => by unfold bp; split_ifs <;> norm_num)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq0 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hq0]
    have h20 : 0 ≤ ∏ p ∈ q.primeFactors, (2 : ℝ) := prod_nonneg (fun _ _ => by norm_num)
    have := mul_le_mul hA (mul_le_mul h2 hb hb0 (by positivity)) (by positivity)
      (by positivity : (0 : ℝ) ≤ Nat.gcd q m)
    nlinarith
  · simp only [abs_zero]
    positivity

/-! ### Tail sums -/

theorem sum_Ico_inv_sq_le (V : ℕ) (hV : 1 ≤ V) (k : ℕ) :
    ∑ w ∈ Ico V (V + k), ((w : ℝ) ^ 2)⁻¹ ≤ 2 / (V : ℝ) - 2 / ((V + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, sum_Ico_succ_top (by omega)]
    have hw : (1 : ℝ) ≤ ((V + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ V + k)
    have e : ((V + k + 1 : ℕ) : ℝ) = ((V + k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e]
    set w : ℝ := ((V + k : ℕ) : ℝ)
    have : (w ^ 2)⁻¹ ≤ 2 / w - 2 / (w + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `Σ_{V ≤ w ≤ M} w⁻² ≤ 2/V`. -/
theorem sum_Icc_inv_sq_le (V M : ℕ) (hV : 1 ≤ V) :
    ∑ w ∈ Icc V M, ((w : ℝ) ^ 2)⁻¹ ≤ 2 / (V : ℝ) := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  rcases lt_or_ge M V with h | h
  · rw [Icc_eq_empty (by omega)]; simp; positivity
  · have e : Icc V M = Ico V (V + (M + 1 - V)) := by
      ext w; simp only [mem_Icc, mem_Ico]; omega
    rw [e]
    refine (sum_Ico_inv_sq_le V hV _).trans ?_
    have : (0 : ℝ) ≤ 2 / ((V + (M + 1 - V) : ℕ) : ℝ) := by positivity
    linarith

/-- Multiples of `ℓ` in `(R, M]`: `Σ q⁻² ≤ 2/(ℓ² (⌊R/ℓ⌋ + 1))`. -/
theorem sum_multiples_inv_sq_le (R M ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ q ∈ (Ioc R M).filter (ℓ ∣ ·), ((q : ℝ) ^ 2)⁻¹ ≤
      2 / ((ℓ : ℝ) ^ 2 * ((R / ℓ + 1 : ℕ) : ℝ)) := by
  set V := R / ℓ + 1
  have hsub : (Ioc R M).filter (ℓ ∣ ·) ⊆ (Icc V M).image (ℓ * ·) := by
    intro q hq
    simp only [mem_filter, mem_Ioc] at hq
    obtain ⟨⟨h1, h2⟩, ⟨w, rfl⟩⟩ := hq
    simp only [mem_image, mem_Icc]
    refine ⟨w, ⟨?_, ?_⟩, rfl⟩
    · have : R / ℓ < w := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [mul_comm]; exact h1)
      omega
    · exact le_trans (Nat.le_mul_of_pos_left w (by omega)) h2
  have hinj : Set.InjOn (ℓ * ·) (Icc V M : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  calc _ ≤ ∑ q ∈ (Icc V M).image (ℓ * ·), ((q : ℝ) ^ 2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ w ∈ Icc V M, (((ℓ * w : ℕ) : ℝ) ^ 2)⁻¹ := sum_image hinj
    _ = ((ℓ : ℝ) ^ 2)⁻¹ * ∑ w ∈ Icc V M, ((w : ℝ) ^ 2)⁻¹ := by
        rw [mul_sum]; apply sum_congr rfl; intro w _; push_cast; rw [mul_pow, mul_inv]
    _ ≤ ((ℓ : ℝ) ^ 2)⁻¹ * (2 / (V : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le V M (Nat.le_add_left 1 _)) (by positivity)
    _ = _ := by field_simp

theorem sum_multiples_inv_sq_le_sq (R M ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ q ∈ (Ioc R M).filter (ℓ ∣ ·), ((q : ℝ) ^ 2)⁻¹ ≤ 2 / (ℓ : ℝ) ^ 2 := by
  refine (sum_multiples_inv_sq_le R M ℓ hℓ).trans ?_
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hV : (1 : ℝ) ≤ ((R / ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 (R / ℓ)
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [sq_nonneg (ℓ : ℝ)]

theorem sum_multiples_inv_sq_le_mul (R M ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hR : 1 ≤ R) :
    ∑ q ∈ (Ioc R M).filter (ℓ ∣ ·), ((q : ℝ) ^ 2)⁻¹ ≤ 2 / ((ℓ : ℝ) * R) := by
  refine (sum_multiples_inv_sq_le R M ℓ hℓ).trans ?_
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hn : R ≤ ℓ * (R / ℓ + 1) := by
    have h1 := Nat.div_add_mod R ℓ
    have h2 := Nat.mod_lt R (show ℓ > 0 by omega)
    rw [Nat.mul_succ]; omega
  have hV : (R : ℝ) ≤ ℓ * ((R / ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  calc (ℓ : ℝ) * R ≤ ℓ * (ℓ * ((R / ℓ + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hV hℓR.le
    _ = _ := by ring

/-- `Σ_{u ∈ S} (a, u) w(u) ≤ Σ_{e ∣ a} e Σ_{u ∈ S, e ∣ u} w(u)` for `w ≥ 0`. -/
theorem sum_gcd_mul_le (a : ℕ) (ha : 1 ≤ a) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ u ∈ S, 0 ≤ w u) :
    ∑ u ∈ S, (Nat.gcd a u : ℝ) * w u ≤
      ∑ e ∈ a.divisors, (e : ℝ) * ∑ u ∈ S.filter (e ∣ ·), w u := by
  have hg : ∀ u, (Nat.gcd a u : ℝ) ≤ ∑ e ∈ a.divisors.filter (· ∣ u), (e : ℝ) := by
    intro u
    have hmem : Nat.gcd a u ∈ a.divisors.filter (· ∣ u) := by
      simp only [mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.gcd_dvd_left a u, by omega⟩, Nat.gcd_dvd_right a u⟩
    exact single_le_sum (f := fun e : ℕ => (e : ℝ)) (fun _ _ => by positivity) hmem
  calc ∑ u ∈ S, (Nat.gcd a u : ℝ) * w u
      ≤ ∑ u ∈ S, (∑ e ∈ a.divisors.filter (· ∣ u), (e : ℝ)) * w u :=
        sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (hg u) (hw u hu))
    _ = ∑ u ∈ S, ∑ e ∈ a.divisors.filter (· ∣ u), (e : ℝ) * w u := by
        apply sum_congr rfl; intro u _; rw [sum_mul]
    _ = ∑ e ∈ a.divisors, ∑ u ∈ S.filter (e ∣ ·), (e : ℝ) * w u := by
        rw [Finset.sum_comm' (t' := a.divisors) (s' := fun e => S.filter (e ∣ ·))]
        intro u e; simp only [mem_filter]; tauto
    _ = _ := by apply sum_congr rfl; intro e _; rw [mul_sum]

/-- The weight `w_F(u) = 1/(uF)` for `u ≤ F`, `1/u²` for `u > F`. -/
def wF (F u : ℕ) : ℝ := if u ≤ F then ((u : ℝ) * F)⁻¹ else ((u : ℝ) ^ 2)⁻¹

theorem wF_nonneg (F u : ℕ) : 0 ≤ wF F u := by unfold wF; split_ifs <;> positivity

/-- One pair `(a, u)`: `a Σ_{F < q ≤ M, [a,u] ∣ q} q⁻² ≤ 2 (a, u) w_F(u)`. -/
theorem pair_le (F M a u : ℕ) (hF : 1 ≤ F) (ha : 1 ≤ a) (hu : 1 ≤ u) :
    (a : ℝ) * ∑ q ∈ (Ioc F M).filter (Nat.lcm a u ∣ ·), ((q : ℝ) ^ 2)⁻¹ ≤
      2 * (Nat.gcd a u : ℝ) * wF F u := by
  set ℓ := Nat.lcm a u
  have hℓ : 1 ≤ ℓ := Nat.lcm_pos ha hu
  have hgl : (Nat.gcd a u : ℝ) * ℓ = a * u := by exact_mod_cast Nat.gcd_mul_lcm a u
  have huℓ : (u : ℝ) ≤ ℓ := by exact_mod_cast Nat.le_of_dvd (by omega) (Nat.dvd_lcm_right a u)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hFR : (0 : ℝ) < F := by exact_mod_cast hF
  have hg0 : (0 : ℝ) ≤ Nat.gcd a u := by positivity
  unfold wF
  split_ifs with h
  · have hs := sum_multiples_inv_sq_le_mul F M ℓ hℓ hF
    calc (a : ℝ) * _ ≤ a * (2 / ((ℓ : ℝ) * F)) := mul_le_mul_of_nonneg_left hs haR.le
      _ = 2 * (Nat.gcd a u : ℝ) * ((u : ℝ) * F)⁻¹ := by
          field_simp
          linear_combination (-1 : ℝ) * hgl
  · have hs := sum_multiples_inv_sq_le_sq F M ℓ hℓ
    calc (a : ℝ) * _ ≤ a * (2 / (ℓ : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hs haR.le
      _ ≤ 2 * (Nat.gcd a u : ℝ) * ((u : ℝ) ^ 2)⁻¹ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity), inv_eq_one_div, mul_one_div,
            div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          have : (a : ℝ) * u * u ≤ Nat.gcd a u * ℓ * ℓ := by
            rw [hgl]; exact mul_le_mul_of_nonneg_left huℓ (by positivity)
          nlinarith

/-- `e Σ_{u ≤ M, e ∣ u} w_F(u) ≤ (H_F + 2)/F`. -/
theorem sum_wF_le (F M e : ℕ) (hF : 1 ≤ F) (he : 1 ≤ e) :
    (e : ℝ) * ∑ u ∈ (Icc 1 M).filter (e ∣ ·), wF F u ≤ (Hn F + 2) / F := by
  have hFR : (0 : ℝ) < F := by exact_mod_cast hF
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  rw [← sum_filter_add_sum_filter_not _ (fun u => u ≤ F)]
  have h1 : ∑ u ∈ ((Icc 1 M).filter (e ∣ ·)).filter (fun u => u ≤ F), wF F u ≤ Hn F / e / F := by
    calc _ = ∑ u ∈ ((Icc 1 M).filter (e ∣ ·)).filter (fun u => u ≤ F), (u : ℝ)⁻¹ * (F : ℝ)⁻¹ := by
          apply sum_congr rfl; intro u hu
          unfold wF; rw [if_pos (mem_filter.mp hu).2, mul_inv]
      _ ≤ ∑ u ∈ (Icc 1 F).filter (e ∣ ·), (u : ℝ)⁻¹ * (F : ℝ)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
          intro u hu
          simp only [mem_filter, mem_Icc] at hu ⊢
          exact ⟨⟨hu.1.1.1, hu.2⟩, hu.1.2⟩
      _ = (∑ u ∈ (Icc 1 F).filter (e ∣ ·), (u : ℝ)⁻¹) * (F : ℝ)⁻¹ := by rw [sum_mul]
      _ ≤ Hn F / e * (F : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (sum_inv_multiples_le F e he) (by positivity)
      _ = Hn F / e / F := by rw [div_eq_mul_inv _ (F : ℝ)]
  have h2 : ∑ u ∈ ((Icc 1 M).filter (e ∣ ·)).filter (fun u => ¬ u ≤ F), wF F u ≤ 2 / (e * F) := by
    calc _ = ∑ u ∈ (Ioc F M).filter (e ∣ ·), ((u : ℝ) ^ 2)⁻¹ := by
          apply sum_congr
          · ext u; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
          · intro u hu
            unfold wF; rw [if_neg]
            simp only [mem_filter, mem_Ioc] at hu; omega
      _ ≤ _ := sum_multiples_inv_sq_le_mul F M e he hF
  calc (e : ℝ) * (_ + _) ≤ e * (Hn F / e / F + 2 / (e * F)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) heR.le
    _ = (Hn F + 2) / F := by field_simp

/-- **The tail**: `Σ_{F < q ≤ M} (q, m) d(q)/q² ≤ (6 + 2 log F) d(m)²/F`, the paper's use of 2.3. -/
theorem tail_gcd_le (m F M : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) :
    ∑ q ∈ Ioc F M, (Nat.gcd q m : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 ≤
      (6 + 2 * Real.log F) * (m.divisors.card : ℝ) ^ 2 / F := by
  have hFR : (0 : ℝ) < F := by exact_mod_cast hF
  set W : ℕ → ℝ := fun q => (q.divisors.card : ℝ) / (q : ℝ) ^ 2
  have hA : ∑ q ∈ Ioc F M, (Nat.gcd q m : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 ≤
      ∑ a ∈ m.divisors, (a : ℝ) * ∑ q ∈ (Ioc F M).filter (a ∣ ·), W q := by
    have := sum_gcd_mul_le m hm (Ioc F M) W (fun _ _ => by simp only [W]; positivity)
    refine le_trans (le_of_eq ?_) this
    apply sum_congr rfl; intro q _; simp only [W]; rw [Nat.gcd_comm]; ring
  have hB : ∀ a ∈ m.divisors, (a : ℝ) * ∑ q ∈ (Ioc F M).filter (a ∣ ·), W q ≤
      2 * (Hn F + 2) / F * (a.divisors.card : ℝ) := by
    intro a ha
    have ha1 : 1 ≤ a := Nat.pos_of_mem_divisors ha
    have hd : ∀ q ∈ (Ioc F M).filter (a ∣ ·), W q =
        ∑ u ∈ Icc 1 M, if u ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0 := by
      intro q hq
      simp only [mem_filter, mem_Ioc] at hq
      simp only [W]
      rw [divisors_eq_filter M q (mem_Icc.mpr ⟨by omega, hq.1.2⟩), card_filter]
      push_cast
      rw [div_eq_mul_inv, sum_mul]
      apply sum_congr rfl; intro u _; split_ifs <;> simp
    rw [sum_congr rfl hd, sum_comm]
    have he : ∀ u ∈ Icc 1 M, ∑ q ∈ (Ioc F M).filter (a ∣ ·),
        (if u ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0) =
        ∑ q ∈ (Ioc F M).filter (Nat.lcm a u ∣ ·), ((q : ℝ) ^ 2)⁻¹ := by
      intro u _
      rw [← sum_filter, filter_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext q; simp only [mem_filter, Nat.lcm_dvd_iff]
    rw [sum_congr rfl he, mul_sum]
    calc ∑ u ∈ Icc 1 M, (a : ℝ) * ∑ q ∈ (Ioc F M).filter (Nat.lcm a u ∣ ·), ((q : ℝ) ^ 2)⁻¹
        ≤ ∑ u ∈ Icc 1 M, 2 * ((Nat.gcd a u : ℝ) * wF F u) := by
          apply sum_le_sum; intro u hu
          rw [← mul_assoc]; exact pair_le F M a u hF ha1 (mem_Icc.mp hu).1
      _ = 2 * ∑ u ∈ Icc 1 M, (Nat.gcd a u : ℝ) * wF F u := by rw [mul_sum]
      _ ≤ 2 * ∑ e ∈ a.divisors, (e : ℝ) * ∑ u ∈ (Icc 1 M).filter (e ∣ ·), wF F u :=
          mul_le_mul_of_nonneg_left
            (sum_gcd_mul_le a ha1 (Icc 1 M) (wF F) (fun u _ => wF_nonneg F u)) (by norm_num)
      _ ≤ 2 * ∑ e ∈ a.divisors, (Hn F + 2) / F := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply sum_le_sum; intro e he
          exact sum_wF_le F M e hF (Nat.pos_of_mem_divisors he)
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have hH := Hn_le F
  have hH0 := Hn_nonneg F
  calc _ ≤ _ := hA
    _ ≤ ∑ a ∈ m.divisors, 2 * (Hn F + 2) / F * (a.divisors.card : ℝ) := sum_le_sum hB
    _ = 2 * (Hn F + 2) / F * ∑ a ∈ m.divisors, (a.divisors.card : ℝ) := by rw [mul_sum]
    _ ≤ 2 * (Hn F + 2) / F * (m.divisors.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_card_divisors_divisors_le m hm) (by positivity)
    _ ≤ (6 + 2 * Real.log F) / F * (m.divisors.card : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ hFR.le
        linarith
    _ = _ := by ring

/-! ### Summability and the Euler product -/

/-- `Σ_{F < q ≤ M} |g_m(q)| ≤ 4 (6 + 2 log F) d(m)²/F`. -/
theorem sum_abs_gm_Ioc_le (m F M : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) :
    ∑ q ∈ Ioc F M, |gm m q| ≤ 4 * ((6 + 2 * Real.log F) * (m.divisors.card : ℝ) ^ 2 / F) := by
  calc ∑ q ∈ Ioc F M, |gm m q|
      ≤ ∑ q ∈ Ioc F M, 4 * ((Nat.gcd q m : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2) := by
        apply sum_le_sum; intro q hq
        have := abs_gm_le m q (by have := (mem_Ioc.mp hq).1; omega)
        linarith [show 4 * (Nat.gcd q m : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 =
          4 * ((Nat.gcd q m : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2) by ring]
    _ = 4 * ∑ q ∈ Ioc F M, (Nat.gcd q m : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 := by
        rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tail_gcd_le m F M hm hF) (by norm_num)

theorem summable_abs_gm (m : ℕ) (hm : 1 ≤ m) : Summable (fun q => ‖gm m q‖) := by
  apply summable_of_sum_range_le (c := 2 + 4 * ((6 + 2 * Real.log 1) *
    (m.divisors.card : ℝ) ^ 2 / 1)) (fun _ => norm_nonneg _)
  intro n
  have hsub : range n ⊆ range 2 ∪ Ioc 1 n := by
    intro q hq; simp only [mem_range, mem_union, mem_Ioc] at hq ⊢; omega
  calc ∑ i ∈ range n, ‖gm m i‖ ≤ ∑ i ∈ range 2 ∪ Ioc 1 n, ‖gm m i‖ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ = ∑ i ∈ range 2, ‖gm m i‖ + ∑ i ∈ Ioc 1 n, ‖gm m i‖ := by
        apply sum_union
        rw [disjoint_left]; intro a ha hb; simp only [mem_range, mem_Ioc] at ha hb; omega
    _ ≤ 2 + 4 * ((6 + 2 * Real.log 1) * (m.divisors.card : ℝ) ^ 2 / 1) := by
        apply add_le_add
        · simp only [Real.norm_eq_abs]
          rw [sum_range_succ, sum_range_succ, sum_range_zero]
          have h0 := abs_gm_le_one m 0
          have h1 := abs_gm_le_one m 1
          linarith
        · simp only [Real.norm_eq_abs]
          have := sum_abs_gm_Ioc_le m 1 n hm le_rfl
          simpa using this

theorem gm_prime_pow_tsum (m p : ℕ) (hp : p.Prime) :
    ∑' e, gm m (p ^ e) = 1 + vloc m p := by
  rw [tsum_eq_sum (s := range 2)]
  · rw [sum_range_succ, sum_range_succ, sum_range_zero, pow_zero, pow_one, gm_one, zero_add,
      gm_eq, if_pos hp.prime.squarefree, Nat.Prime.primeFactors hp, prod_singleton]
  · intro e he
    simp only [mem_range, not_lt] at he
    rw [gm_eq, if_neg]
    intro hsq
    have hd : p * p ∣ p ^ e := by
      rw [← pow_two]; exact pow_dvd_pow p he
    exact hp.not_isUnit (hsq p hd)

/-- The Euler factors: `1 + v_m(p) = C(p) D(p) W(p)`. -/
def Cf (n : ℕ) : ℝ := if n.Prime ∧ 2 < n then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1
def Df (m n : ℕ) : ℝ := if n = 2 then (if Even m then 2 else 0) else 1
def Wf (m n : ℕ) : ℝ :=
  if n ∈ m.primeFactors.filter (2 < ·) then ((n : ℝ) - 1) / ((n : ℝ) - 2) else 1

theorem euler_factor_eq (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    Set.mulIndicator {p | Nat.Prime p} (fun p => ∑' e, gm m (p ^ e)) n =
      Cf n * Df m n * Wf m n := by
  by_cases hn : n.Prime
  · rw [Set.mulIndicator_of_mem (show n ∈ {p | Nat.Prime p} from hn), gm_prime_pow_tsum m n hn]
    rcases eq_or_lt_of_le hn.two_le with h2 | h2
    · subst h2
      unfold Cf Df Wf
      simp only [lt_irrefl, and_false, if_false, if_true, mem_filter]
      by_cases he : Even m
      · rw [vloc_dvd Nat.prime_two (even_iff_two_dvd.mp he), if_pos he]; norm_num
      · rw [vloc_not_dvd Nat.prime_two (fun h => he (even_iff_two_dvd.mpr h)), if_neg he]
        norm_num
    · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h2
      unfold Cf Df Wf
      rw [if_pos ⟨hn, h2⟩, if_neg (by omega), mul_one]
      by_cases hd : n ∣ m
      · rw [vloc_dvd hn hd, if_pos (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hn, hd, by omega⟩, h2⟩)]
        have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
        have h2' : (n : ℝ) - 2 ≠ 0 := by linarith
        field_simp; ring
      · rw [vloc_not_dvd hn hd, if_neg (fun h => hd (Nat.dvd_of_mem_primeFactors
          (mem_filter.mp h).1)), mul_one]
        ring
  · rw [Set.mulIndicator_of_notMem (show n ∉ {p | Nat.Prime p} from hn)]
    unfold Cf Df Wf
    rw [if_neg (fun h => hn h.1), if_neg (fun h => hn (by rw [h]; exact Nat.prime_two)),
      if_neg (fun h => hn (Nat.prime_of_mem_primeFactors (mem_filter.mp h).1))]
    ring

theorem hasProd_Cf : HasProd Cf ChenExplicit.twinC := by
  have h : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1 - 1 / ((p : ℝ) - 1) ^ 2)
      ChenExplicit.twinC := ChenExplicit.twinC_multipliable.hasProd
  have e : (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1 - 1 / ((p : ℝ) - 1) ^ 2) =
      Cf ∘ Subtype.val := by
    funext p; simp only [Function.comp, Cf]; rw [if_pos p.2]
  rw [e] at h
  rw [Subtype.val_injective.hasProd_iff] at h
  · exact h
  · intro n hn
    unfold Cf
    rw [if_neg]
    intro h'
    exact hn ⟨⟨n, h'⟩, rfl⟩

/-- **The singular series as a sum**: `Σ_q g_m(q) = 𝔖(m)` for `m ≥ 1`, by the Euler product. -/
theorem hasSum_gm (m : ℕ) (hm : 1 ≤ m) : HasSum (gm m) (singular m) := by
  have hs := summable_abs_gm m hm
  have hE := EulerProduct.eulerProduct_hasProd_mulIndicator (f := gm m) (gm_one m)
    (fun hab => gm_mul m hab) hs (gm_zero m)
  have e : Set.mulIndicator {p | Nat.Prime p} (fun p => ∑' e, gm m (p ^ e)) =
      fun n => Cf n * Df m n * Wf m n := by
    funext n; exact euler_factor_eq m hm n
  rw [e] at hE
  have hD : HasProd (Df m) (if Even m then 2 else 0) := by
    have := hasProd_ite_eq 2 (if Even m then (2 : ℝ) else 0)
    convert this using 1
    funext b; simp only [Df]
  have hW : HasProd (Wf m) (∏ p ∈ m.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))) := by
    have := hasProd_prod_of_ne_finset_one (f := Wf m) (s := m.primeFactors.filter (2 < ·))
      (L := SummationFilter.unconditional ℕ)
      (fun b hb => by unfold Wf; rw [if_neg hb])
    convert this using 1
    apply prod_congr rfl; intro p hp; unfold Wf; rw [if_pos hp]
  have hP := (hasProd_Cf.mul hD).mul hW
  have hu := hE.unique hP
  have hval : ChenExplicit.twinC * (if Even m then 2 else 0) *
      ∏ p ∈ m.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) = singular m := by
    unfold singular
    split_ifs <;> ring
  rw [← hval, ← hu]
  exact hs.of_norm.hasSum

/-- **The tail of the singular series**:
`|𝔖(m) - Σ_{q ≤ F} g_m(q)| ≤ 4 (6 + 2 log F) d(m)²/F`. -/
theorem abs_singular_sub_le (m F : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) :
    |singular m - ∑ q ∈ Icc 1 F, gm m q| ≤
      4 * ((6 + 2 * Real.log F) * (m.divisors.card : ℝ) ^ 2 / F) := by
  have hs := summable_abs_gm m hm
  have hsum := (hasSum_gm m hm).tsum_eq
  have hsplit := hs.of_norm.sum_add_tsum_nat_add (F + 1)
  have hfin : ∑ q ∈ range (F + 1), gm m q = ∑ q ∈ Icc 1 F, gm m q := by
    symm
    apply sum_subset
    · intro q hq; simp only [mem_Icc, mem_range] at hq ⊢; omega
    · intro q hq1 hq
      simp only [mem_range] at hq1
      simp only [mem_Icc, not_and, not_le] at hq
      have : q = 0 := by
        by_contra h
        have := hq (by omega)
        omega
      rw [this, gm_zero]
  rw [← hsum, ← hsplit, hfin, add_sub_cancel_left]
  have hs' : Summable (fun i => ‖gm m (i + (F + 1))‖) :=
    (summable_nat_add_iff (f := fun i => ‖gm m i‖) (F + 1)).mpr hs
  refine (norm_tsum_le_tsum_norm hs').trans ?_
  apply Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
  intro n
  have e : ∑ i ∈ range n, ‖gm m (i + (F + 1))‖ = ∑ q ∈ Ioc F (F + n), |gm m q| := by
    have h1 : Ioc F (F + n) = Ico (F + 1) (F + 1 + n) := by ext q; simp only [mem_Ioc, mem_Ico]; omega
    rw [h1, sum_Ico_eq_sum_range, show F + 1 + n - (F + 1) = n by omega]
    apply sum_congr rfl; intro i _; rw [Real.norm_eq_abs, add_comm]
  rw [e]
  exact sum_abs_gm_Ioc_le m F (F + n) hm hF

end LeanLab.HeathBrown1985
