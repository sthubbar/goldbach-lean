module

public import LeanLab.HardyLittlewood1923.U1463ThmA

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T0403Z-7595, unit U-1468, paper P0004.

# Hardy-Littlewood 1923, the Euler product of the singular series `S_r`, every `r ≥ 3`

Printed, eq. (3.114) and the product of Theorem B, eq. (3.32) p. 29: for `r ≥ 3`,
`S_r(n) = Σ_q (μ(q)/φ(q))^r c_q(n) = 2 C_r ∏_{p ∣ n, p > 2} ((p-1)^r + (-1)^r (p-1))/((p-1)^r - (-1)^r)`
when `n ≡ r mod 2`, and `S_r(n) = 0` otherwise.

Route, by multiplicativity as `U1438Sing` does for `r = 3`: `q ↦ (μ(q)/φ(q))^r c_q(n)` is the
pointwise product of the multiplicative `(μ/φ)^r` and `c_·(n) = (d ↦ d 1_{d ∣ n}) * μ`; its value at a
prime is `(-1)^r/(p-1)^r · c_p(n)`, at most `1/(p-1)²` for `r ≥ 3`, so the series converges absolutely
and Mathlib's `IsMultiplicative.eulerProduct` gives the product over primes. Each local factor is
`frR r p` times the local factor of `Br r n`, and the factor at `2` is `1 ± (-1)^r ∈ {0, 2}`.

* `singR_eq_E2`: for `r ≥ 3`, `n ≥ 1`, `S_r(n) = E₂ C_r Br r n`, `E₂ = 2` for like parity, else `0`.
* `singRProductPos`: U-1463's target `SingRProduct` for every `r ≥ 3` and every `n ≥ 1`.
* `not_singRProduct`: U-1463's `SingRProduct` as stated is FALSE, at `r = 4`, `n = 0`:
  `S_4(0) ≥ 9/4 > 2 ≥ 2 C_4 Br 4 0`; `c_q(0) = φ(q)`, so `n = 0` is outside the printed product.
* `printedA_form_all_U1468`: printed Theorem A (3.113), every `r ≥ 3`, CONDITIONAL ON
  `ExplicitFormulaLog` only.

Every proof is complete, no axiom. Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1468

open Real Finset Filter Topology
open ArithmeticFunction (pmul_apply ppow_apply intCoe_apply isMultiplicative_moebius
  moebius_apply_prime moebius_eq_zero_of_not_squarefree IsMultiplicative)
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1444 (singR)
open LeanLab.HardyLittlewood1923.U1463
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight)
open LeanLab.PNTPort.Vinogradov (cR cR_mult cR_apply ramanujan_prime dvd_primorial_of_sqf)

/-! ### The term of `S_r` as a multiplicative function -/

/-- `q ↦ 1/φ(q)`, `0` at `0`. -/
noncomputable def invPhi : ArithmeticFunction ℝ := ⟨fun q => ((q.totient : ℕ) : ℝ)⁻¹, by simp⟩

lemma invPhi_apply (q : ℕ) : invPhi q = ((q.totient : ℕ) : ℝ)⁻¹ := rfl

lemma invPhi_mult : invPhi.IsMultiplicative := by
  refine ⟨by simp [invPhi_apply], fun {a b} hab => ?_⟩
  rw [invPhi_apply, invPhi_apply, invPhi_apply, Nat.totient_mul hab]
  push_cast
  rw [mul_inv]

/-- `q ↦ μ(q)/φ(q)`. -/
noncomputable def muPhi : ArithmeticFunction ℝ := (μ : ArithmeticFunction ℝ).pmul invPhi

lemma muPhi_mult : muPhi.IsMultiplicative := isMultiplicative_moebius.intCast.pmul invPhi_mult

lemma muPhi_apply (q : ℕ) : muPhi q = (μ q : ℝ) / (q.totient : ℝ) := by
  rw [muPhi, pmul_apply, intCoe_apply, invPhi_apply, div_eq_mul_inv]

/-- The term `(μ(q)/φ(q))^r c_q(n)` of `S_r(n)`, multiplicative in `q`. -/
noncomputable def fR (r n : ℕ) : ArithmeticFunction ℝ := (muPhi.ppow r).pmul (cR n)

lemma fR_mult (r n : ℕ) : (fR r n).IsMultiplicative := muPhi_mult.ppow.pmul (cR_mult n)

lemma fR_apply {r : ℕ} (hr : 1 ≤ r) (n q : ℕ) :
    fR r n q = ((μ q : ℝ) / (q.totient : ℝ)) ^ r * LeanLab.HeathBrown1985.ramanujan q n := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [ArithmeticFunction.map_zero, ArithmeticFunction.map_zero, Int.cast_zero, zero_div,
      zero_pow (by omega : r ≠ 0), zero_mul]
  · rw [fR, pmul_apply, ppow_apply (by omega), muPhi_apply, cR_apply hq]

lemma singR_eq_tsum {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : singR r n = ∑' q, fR r n q := by
  unfold singR
  exact tsum_congr fun q => (fR_apply hr n q).symm

lemma fR_zero_of_not_sqf {r : ℕ} (hr : 1 ≤ r) (n : ℕ) {q : ℕ} (h : ¬ Squarefree q) :
    fR r n q = 0 := by
  rw [fR_apply hr, moebius_eq_zero_of_not_squarefree h, Int.cast_zero, zero_div,
    zero_pow (by omega : r ≠ 0), zero_mul]

lemma fR_prime {r : ℕ} (hr : 1 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    fR r n p = (-1 : ℝ) ^ r / ((p : ℝ) - 1) ^ r * (if p ∣ n then (p : ℝ) - 1 else -1) := by
  rw [fR_apply hr, ramanujan_prime hp, moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, div_pow]
  push_cast
  ring

lemma abs_fR_prime_le {r : ℕ} (hr : 3 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    |fR r n p| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  rw [fR_prime (by omega) n hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set x : ℝ := (p : ℝ) - 1 with hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hc : |(if p ∣ n then x else -1)| ≤ x := by
    split_ifs
    · rw [abs_of_pos hx0]
    · rw [abs_neg, abs_one]; exact hx1
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (pow_pos hx0 _)]
  have hxs : x ^ 2 * x ≤ x ^ r := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [pow_succ x s]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx1 (by omega : 2 ≤ s)) hx0.le
  have hxr : 0 < x ^ r := pow_pos hx0 r
  calc 1 / x ^ r * |(if p ∣ n then x else -1)| ≤ 1 / x ^ r * x :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ 1 / x ^ 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hxr (by positivity)]
        nlinarith

/-! ### Absolute convergence -/

lemma sum_range_abs_fR_le {r : ℕ} (hr : 3 ≤ r) (n Q : ℕ) :
    ∑ q ∈ range Q, |fR r n q| ≤ Real.exp 8 := by
  calc ∑ q ∈ range Q, |fR r n q| = ∑ q ∈ (range Q).filter Squarefree, |fR r n q| := by
        rw [sum_filter]
        refine sum_congr rfl fun q _ => ?_
        split_ifs with h
        · rfl
        · rw [fR_zero_of_not_sqf (by omega) n h, abs_zero]
    _ ≤ ∑ q ∈ (range Q).filter Squarefree, absSqrt (fR r n) q := by
        refine sum_le_sum fun q hq => ?_
        rw [mem_filter] at hq
        rw [absSqrt_apply]
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero hq.2.ne_zero
        have hs : 1 ≤ Real.sqrt q := by rw [Real.one_le_sqrt]; exact hq1
        have := abs_nonneg (fR r n q)
        nlinarith
    _ ≤ ∑ d ∈ (primorial Q).divisors, absSqrt (fR r n) d := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_filter, mem_range] at hd
          exact Nat.mem_divisors.2 ⟨dvd_primorial_of_sqf hd.2 hd.1.le, (primorial_pos Q).ne'⟩
        · intro d _ _; rw [absSqrt_apply]; positivity
    _ ≤ Real.exp (8 * 1) :=
        sum_divisors_absSqrt_le _ (fR_mult r n) 1 (by norm_num)
          (fun p hp => abs_fR_prime_le hr n hp) Q
    _ = Real.exp 8 := by norm_num

/-- **Absolute convergence** of `S_r(n)`, `r ≥ 3`, every `n`. -/
theorem summable_norm_fR {r : ℕ} (hr : 3 ≤ r) (n : ℕ) : Summable (fun q => ‖fR r n q‖) := by
  simp only [Real.norm_eq_abs]
  exact summable_of_sum_range_le (fun q => abs_nonneg _) (sum_range_abs_fR_le hr n)

/-! ### The Euler product -/

lemma tsum_fR_prime_pow {r : ℕ} (hr : 1 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑' e, fR r n (p ^ e) = 1 + fR r n p := by
  have h0 : ∀ e ∉ range 2, fR r n (p ^ e) = 0 := by
    intro e he
    rw [mem_range, not_lt] at he
    apply fR_zero_of_not_sqf hr
    intro h
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)] at h
    omega
  rw [tsum_eq_sum h0, sum_range_succ, sum_range_one, pow_zero, pow_one, (fR_mult r n).map_one]

/-- The partial Euler products `∏_{p ≤ M} (1 + f(p))` tend to `S_r(n)`. -/
theorem tendsto_prod_fR {r : ℕ} (hr : 3 ≤ r) (n : ℕ) :
    Tendsto (fun M : ℕ => ∏ p ∈ Nat.primesLE M, (1 + fR r n p)) atTop (𝓝 (singR r n)) := by
  rw [singR_eq_tsum (by omega)]
  have hT := (fR_mult r n).eulerProduct (summable_norm_fR hr n)
  have := hT.comp (tendsto_add_atTop_nat 1)
  refine this.congr fun M => ?_
  simp only [Function.comp_apply]
  exact prod_congr rfl fun p hp => tsum_fR_prime_pow (by omega) n (Nat.prime_of_mem_primesBelow hp)

/-- The factor at `2`: `2` for `n ≡ r mod 2`, else `0`. -/
noncomputable def E2 (r n : ℕ) : ℝ := if n % 2 = r % 2 then 2 else 0

/-- **The local identity**: `1 + f(p) = [p = 2] E₂ · frR r p · rrR (r-1) n p`. -/
theorem local_fR {r : ℕ} (hr : 3 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    1 + fR r n p = (if p = 2 then E2 r n else 1) * frR r p * rrR (r - 1) n p := by
  have hr1 : r - 1 + 1 = r := by omega
  rw [fR_prime (by omega) n hp]
  by_cases h2 : p = 2
  · subst h2
    have hf : frR r 2 = 1 := by simp [frR]
    have hrr : rrR (r - 1) n 2 = 1 := by simp [rrR]
    have h1 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    rw [hf, hrr, h1, one_pow, div_one, if_pos rfl, mul_one, mul_one, E2]
    rcases Nat.even_or_odd r with ho | ho
    · rw [ho.neg_one_pow]
      have := Nat.even_iff.1 ho
      split_ifs <;> first | omega | norm_num
    · rw [ho.neg_one_pow]
      have := Nat.odd_iff.1 ho
      split_ifs <;> first | omega | norm_num
  · rw [if_neg h2, one_mul]
    have hq := two_le_q hp h2
    by_cases hn : p ∣ n
    · rw [if_pos hn, rrR, if_pos ⟨h2, hn⟩, hr1]
      simp only [frR, if_neg h2, bfacR]
      set x : ℝ := (p : ℝ) - 1 with hx
      have hx0 : 0 < x := by linarith
      have hxr : 1 < x ^ r := one_lt_pow₀ (by linarith) (by omega)
      have hs := neg_one_pow_bounds r
      have hden : x ^ r - (-1) ^ r ≠ 0 := by
        apply ne_of_gt; linarith [hs.2]
      have hxr0 : x ^ r ≠ 0 := by positivity
      field_simp
    · rw [if_neg hn, rrR, if_neg (fun h => hn h.2), mul_one]
      simp only [frR, if_neg h2]
      ring

/-- The partial Euler product, `M ≥ n ≥ 1`, `M ≥ 2`. -/
theorem prod_fR_eq {r : ℕ} (hr : 3 ≤ r) {n M : ℕ} (hn : 0 < n) (hM : n ≤ M) (hM2 : 2 ≤ M) :
    ∏ p ∈ Nat.primesLE M, (1 + fR r n p) =
      E2 r n * (∏ p ∈ Nat.primesLE M, frR r p) * Br r n := by
  have hB : Br r n = ∏ p ∈ Nat.primesLE M, rrR (r - 1) n p := by
    have := Br_eq_prod (r - 1) n M hn hM
    rwa [show r - 1 + 1 = r by omega] at this
  have h2 : 2 ∈ Nat.primesLE M := Nat.mem_primesLE.2 ⟨hM2, Nat.prime_two⟩
  rw [hB, prod_congr rfl fun p hp => local_fR hr n (Nat.mem_primesLE.1 hp).2, prod_mul_distrib,
    prod_mul_distrib, prod_ite_eq', if_pos h2]

/-- **The Euler product of `S_r`**: for `r ≥ 3` and `n ≥ 1`, `S_r(n) = E₂ C_r Br r n`. -/
theorem singR_eq_E2 {r : ℕ} (hr : 3 ≤ r) {n : ℕ} (hn : 0 < n) :
    singR r n = E2 r n * Cr r * Br r n := by
  have hR : Tendsto (fun M : ℕ => E2 r n * (∏ p ∈ Nat.primesLE M, frR r p) * Br r n) atTop
      (𝓝 (E2 r n * Cr r * Br r n)) :=
    ((tendsto_frR r hr).const_mul (E2 r n)).mul_const (Br r n)
  have hev : (fun M : ℕ => ∏ p ∈ Nat.primesLE M, (1 + fR r n p)) =ᶠ[atTop]
      fun M => E2 r n * (∏ p ∈ Nat.primesLE M, frR r p) * Br r n :=
    eventually_atTop.2 ⟨max n 2, fun M hM =>
      prod_fR_eq hr hn (le_of_max_le_left hM) (le_of_max_le_right hM)⟩
  exact tendsto_nhds_unique ((tendsto_prod_fR hr n).congr' hev) hR

/-- U-1463's `SingRProduct` restricted to `n ≥ 1`. -/
def SingRProductPos : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n : ℕ, 0 < n →
    (n % 2 = r % 2 → singR r n = 2 * Cr r * Br r n) ∧ (n % 2 ≠ r % 2 → singR r n = 0)

/-- **The printed product of `S_r`, every `r ≥ 3`, every `n ≥ 1`**, unconditional. -/
theorem singRProductPos : SingRProductPos := by
  intro r hr n hn
  rw [singR_eq_E2 hr hn, E2]
  constructor
  · intro h; rw [if_pos h]
  · intro h; rw [if_neg h]; ring

/-! ### `n = 0`: U-1463's `SingRProduct` is false as stated -/

lemma Br_zero (r : ℕ) : Br r 0 = 1 := by
  simp [Br]

lemma Cr_four_le_one : Cr 4 ≤ 1 := by
  refine le_of_tendsto' (tendsto_frR 4 (by norm_num)) fun M => ?_
  apply prod_le_one₀
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.1 hp).2.two_le
    unfold frR
    split_ifs
    · norm_num
    · have h1 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 4 := one_le_pow₀ (by linarith)
      have : (-1 : ℝ) ^ 4 / ((p : ℝ) - 1) ^ 4 ≤ 1 := by
        rw [div_le_one (by linarith)]; norm_num; linarith
      linarith
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.1 hp).2.two_le
    unfold frR
    split_ifs
    · norm_num
    · have : 0 ≤ (-1 : ℝ) ^ 4 / ((p : ℝ) - 1) ^ 4 := by
        apply div_nonneg (by norm_num); apply pow_nonneg; linarith
      linarith

lemma one_add_fR_zero {p : ℕ} (hp : p.Prime) :
    1 + fR 4 0 p = 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  rw [fR_prime (by norm_num) 0 hp, if_pos (dvd_zero p)]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- `S_4(0) ≥ 9/4`. -/
lemma singR_four_zero_ge : (9 : ℝ) / 4 ≤ singR 4 0 := by
  refine ge_of_tendsto (tendsto_prod_fR (by norm_num) 0) (eventually_atTop.2 ⟨3, fun M hM => ?_⟩)
  have hsub : ({2, 3} : Finset ℕ) ⊆ Nat.primesLE M := by
    intro p hp
    rw [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.mem_primesLE.2 ⟨by omega, Nat.prime_two⟩
    · exact Nat.mem_primesLE.2 ⟨hM, Nat.prime_three⟩
  have hge : ∀ p ∈ Nat.primesLE M, 1 ≤ 1 + fR 4 0 p := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    rw [one_add_fR_zero hpp]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
      apply div_nonneg (by norm_num); apply pow_nonneg; linarith
    linarith
  calc (9 : ℝ) / 4 = ∏ p ∈ ({2, 3} : Finset ℕ), (1 + fR 4 0 p) := by
        rw [prod_pair (by norm_num), one_add_fR_zero Nat.prime_two,
          one_add_fR_zero Nat.prime_three]
        norm_num
    _ = ∏ p ∈ Nat.primesLE M, (if p ∈ ({2, 3} : Finset ℕ) then 1 + fR 4 0 p else 1) := by
        rw [prod_ite_mem, inter_eq_right.2 hsub]
    _ ≤ ∏ p ∈ Nat.primesLE M, (1 + fR 4 0 p) := by
        apply Finset.prod_le_prod₀
        · intro p hp; split_ifs
          · exact le_trans zero_le_one (hge p hp)
          · norm_num
        · intro p hp; split_ifs
          · exact le_rfl
          · exact hge p hp

/-- **U-1463's open target `SingRProduct` is false as stated**: at `r = 4`, `n = 0`, like parity,
`S_4(0) ≥ 9/4` while `2 C_4 Br 4 0 ≤ 2`. Only `n ≥ 1` matters for Theorem A. -/
theorem not_singRProduct : ¬ U1463.SingRProduct := by
  intro h
  have h1 := (h 4 (by norm_num) 0).1 (by norm_num)
  rw [Br_zero, mul_one] at h1
  have h2 := singR_four_zero_ge
  have h3 := Cr_four_le_one
  linarith

/-! ### Printed Theorem A, every `r ≥ 3`, on `ExplicitFormulaLog` only -/

/-- Like parity, `n ≥ 1`: `Mr r n` is the printed main term `n^{r-1}/(r-1)! S_r(n)`. -/
theorem Mr_eq_printed_pos {r n : ℕ} (hr : 3 ≤ r) (hn : 0 < n) (h : n % 2 = r % 2) :
    Mr r n = (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n := by
  rw [(singRProductPos r hr n hn).1 h, Mr]; ring

/-- Vacuity: `singR_eq_E2` applies, `r = 4`, `n = 2`, like parity, and gives `S_4(2) > 0`. -/
theorem singR_four_two_pos : 0 < singR 4 2 := by
  rw [singR_eq_E2 (by norm_num) (by norm_num), E2, if_pos (by norm_num)]
  have hC := Cr_pos 4 (by norm_num)
  obtain ⟨c, K, hc, hb⟩ := Br_bounds 4 (by norm_num)
  have := (hb 2).1
  have : 0 < Br 4 2 := lt_of_lt_of_le hc this
  positivity

end LeanLab.HardyLittlewood1923.U1468
