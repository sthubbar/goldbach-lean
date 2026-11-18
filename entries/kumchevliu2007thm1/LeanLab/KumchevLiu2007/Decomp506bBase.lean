module

public import LeanLab.KumchevLiu2007.Decomp129s
public import LeanLab.PNTSieve.MertensLower
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Shared numerical definitions and elementary sieve estimates from pages 16 and 17.
These declarations are moved unchanged from Decomp506b to avoid an import cycle.
No analytic leaf is declared in this file.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task506b

open Real Complex MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 2, the fixed Y window used in displays 57 and 58. -/
noncomputable def Y (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)

/-- Page 8 display 34 and page 16, the lower prime factor cutoff. -/
noncomputable def z0 (X B ε : ℝ) : ℝ := Y X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)

/-- Page 16, the primes in I3. -/
noncomputable def primeWindow (X B ε : ℝ) : Finset ℕ :=
  (Finset.range (⌊Y X ε ^ (1 / 4 : ℝ)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ z0 X B ε ≤ (p : ℝ) ∧ (p : ℝ) < Y X ε ^ (1 / 4 : ℝ))

/-- Page 16, the lower endpoint of J of p. -/
noncomputable def jlo (X ε : ℝ) (p : ℕ) : ℝ :=
  max (p : ℝ) (Real.sqrt (Y X ε) / (2 * p))

/-- Page 16, the upper endpoint of J of p, clamped for an empty interval. -/
noncomputable def jhi (X ε : ℝ) (p : ℕ) : ℝ :=
  max (jlo X ε p) (Real.sqrt (Y X ε) / p)

/-- Page 16 display 57, the integral main term N. -/
noncomputable def primeMass (X B ε : ℝ) : ℝ :=
  ∑ p ∈ primeWindow X B ε, ∫ u in jlo X ε p..jhi X ε p, 1 / Real.log u

/-- Page 16, the semiprime products in I2, with the smaller prime in I3. -/
noncomputable def semiprimes (X B ε : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.sqrt (Y X ε)⌋₊ + 1)).filter
    (fun q => Real.sqrt (Y X ε) / 2 ≤ (q : ℝ) ∧ (q : ℝ) < Real.sqrt (Y X ε) ∧
      ∃ p ∈ primeWindow X B ε, ∃ r : ℕ, r.Prime ∧ p ≤ r ∧ q = p * r)

/-- Page 17, the progression count for A at modulus d. -/
noncomputable def progressionCount (X B ε : ℝ) (n d : ℕ) : ℝ :=
  ((semiprimes X B ε).filter (fun q => d ∣ n - q ^ 2)).card

/-- Page 17, the multiplicative sieve density g. -/
noncomputable def density (n d : ℕ) : ℝ :=
  if Nat.Coprime n d then
    (((Finset.range d).filter (fun x => x ^ 2 % d = n % d)).card : ℝ) / Nat.totient d
  else 0

/-- Page 17, the absolute squarefree remainder sum at D equal to Y to the one ninth. -/
noncomputable def remainder (X B ε : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
    (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      |progressionCount X B ε n d - density n d * primeMass X B ε|

/-- Page 17 display 58, the sifted pair count in the sealed leaf. -/
noncomputable def siftedCount (X B δ ε : ℝ) (n : ℕ) : ℝ :=
  (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => (∀ p : ℕ, p.Prime → p ∣ v.1 → (Real.exp (Real.log X ^ (1 - δ / 2))) ≤ (p : ℝ)) ∧
      ¬ v.2.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ)

/-- Page 17 display 58, the product of one minus g at primes up to z. -/
noncomputable def sieveProduct (X δ : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊(Real.exp (Real.log X ^ (1 - δ / 2)))⌋₊ + 1)).filter Nat.Prime,
      (1 - if p ∣ n then 0 else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / (Nat.totient p : ℝ))

/-- Page 16 display 57, the numerical size of N. -/
noncomputable def massScale (X ε : ℝ) : ℝ :=
  Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-2 : ℝ) * Real.log (Real.log X)

/-- Page 17 display 58, the arbitrary logarithmic error size. -/
noncomputable def errorScale (X ε A : ℝ) : ℝ :=
  Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-A)

/-- Page 17, every local sieve factor is nonnegative. -/
theorem sieve_factor_nonneg (n p : ℕ) (hp : p.Prime) :
    0 ≤ (1 : ℝ) - if p ∣ n then 0 else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / Nat.totient p := by
  by_cases hpn : p ∣ n
  · simp [hpn]
  haveI : Fact p.Prime := ⟨hp⟩
  have hc := Finset.card_filter_le (Finset.univ.erase (0 : ZMod p))
    (fun x => x ^ 2 = (n : ZMod p))
  rw [← Task129s.root_count_range_eq p n hpn] at hc
  have hcard : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by simp
  rw [hcard, ← Nat.totient_prime hp] at hc
  have ht : (0 : ℝ) < Nat.totient p := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  simp only [hpn, ↓reduceIte]
  exact sub_nonneg.mpr ((div_le_one ht).mpr (by exact_mod_cast hc))

/-- Page 17 display 58, the sieve product is nonnegative for every n. -/
theorem sieveProduct_nonneg (X δ : ℝ) (n : ℕ) : 0 ≤ sieveProduct X δ n := by
  unfold sieveProduct
  exact Finset.prod_nonneg fun p hp => sieve_factor_nonneg n p (Finset.mem_filter.mp hp).2

/-- Page 17, the distribution remainder is nonnegative. -/
theorem remainder_nonneg (X B ε : ℝ) (n : ℕ) : 0 ≤ remainder X B ε n := by
  unfold remainder
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)

/-- Page 17, Cauchy's inequality for nonnegative prime distribution errors. -/
theorem cauchy_discrepancies {ι : Type*} (s : Finset ι) (w E : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hE : ∀ i ∈ s, 0 ≤ E i) :
    (∑ i ∈ s, w i * E i) ^ 2 ≤
      (∑ i ∈ s, w i ^ 2 * E i) * ∑ i ∈ s, E i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => mul_nonneg (sq_nonneg _) (hE i hi)) hE
  intro i hi
  nlinarith [sq_nonneg (w i * E i)]

/-- Page 17, the Cauchy step with a pointwise error bound and a divisor moment bound. -/
theorem cauchy_with_moments {ι : Type*} (s : Finset ι) (w E : ι → ℝ)
    (M T V : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hE : ∀ i ∈ s, 0 ≤ E i)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hpoint : ∀ i ∈ s, E i ≤ M) (hmoment : ∑ i ∈ s, w i ^ 2 ≤ T)
    (hBV : ∑ i ∈ s, E i ≤ V) :
    (∑ i ∈ s, w i * E i) ^ 2 ≤ M * T * V := by
  have hweighted : (∑ i ∈ s, w i ^ 2 * E i) ≤ M * T := by
    calc _ ≤ ∑ i ∈ s, w i ^ 2 * M := by
           exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hpoint i hi) (sq_nonneg _)
         _ = M * ∑ i ∈ s, w i ^ 2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
         _ ≤ M * T := mul_le_mul_of_nonneg_left hmoment hM
  exact (cauchy_discrepancies s w E hw hE).trans
    (mul_le_mul hweighted hBV (Finset.sum_nonneg hE) (mul_nonneg hM hT))

/-- Page 16 display 57, each logarithmic integral is bounded by interval length over log p. -/
theorem j_integral_bound (X ε : ℝ) (p : ℕ) (hp : p.Prime) :
    (∫ u in jlo X ε p..jhi X ε p, 1 / Real.log u) ≤
      (1 / Real.log p) * (Real.sqrt (Y X ε) / p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hab : jlo X ε p ≤ jhi X ε p := le_max_left _ _
  have hlo : 0 ≤ jlo X ε p := hp0.le.trans (le_max_left _ _)
  have hlen : |jhi X ε p - jlo X ε p| ≤ Real.sqrt (Y X ε) / p := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    unfold jhi
    rw [sub_le_iff_le_add]
    have hroot : 0 ≤ Real.sqrt (Y X ε) / p := by positivity
    exact max_le (by linarith) (by linarith)
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := jlo X ε p) (b := jhi X ε p) (C := 1 / Real.log p) (f := fun u => 1 / Real.log u) ?_
  · exact (le_norm_self _).trans (hn.trans (mul_le_mul_of_nonneg_left hlen (by positivity)))
  intro u hu
  rw [Set.uIoc_of_le hab] at hu
  have hpu : (p : ℝ) ≤ u := (le_max_left _ _).trans hu.1.le
  have hlu : Real.log p ≤ Real.log u := Real.log_le_log hp0 hpu
  have hlu0 : 0 < Real.log u := hlp.trans_le hlu
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.log u)]
  exact one_div_le_one_div_of_le hlp hlu

/-- Page 16 display 57, reduce N to a reciprocal prime sum once log p is large. -/
theorem primeMass_bound_of_logs (X B ε L : ℝ) (hL : 0 < L)
    (hlogs : ∀ p ∈ primeWindow X B ε, L / 32 ≤ Real.log p) :
    primeMass X B ε ≤ (32 * Real.sqrt (Y X ε) / L) *
      ∑ p ∈ primeWindow X B ε, (1 : ℝ) / p := by
  unfold primeMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlp : 0 < Real.log p := lt_of_lt_of_le (by positivity) (hlogs p hp)
  have hinv : 1 / Real.log p ≤ 32 / L := by
    rw [div_le_div_iff₀ hlp hL]
    linarith [hlogs p hp]
  calc _ ≤ (1 / Real.log p) * (Real.sqrt (Y X ε) / p) := j_integral_bound X ε p hpp
       _ ≤ (32 / L) * (Real.sqrt (Y X ε) / p) :=
         mul_le_mul_of_nonneg_right hinv (by positivity)
       _ = (32 * Real.sqrt (Y X ε) / L) * (1 / p) := by ring

/-- Page 16 display 57, elementary logarithmic bounds for the short prime factor window. -/
theorem prime_window_parameters (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      0 < Real.log X ∧ 1 ≤ Real.log (Real.log X) ∧
      2 ≤ ⌊z0 X B ε / 2⌋₊ ∧
      ⌊z0 X B ε / 2⌋₊ ≤ ⌊Y X ε ^ (1 / 4 : ℝ)⌋₊ ∧
      Real.log X / 32 ≤ Real.log (⌊z0 X B ε / 2⌋₊ : ℝ) ∧
      Real.log (⌊Y X ε ^ (1 / 4 : ℝ)⌋₊ : ℝ) -
          Real.log (⌊z0 X B ε / 2⌋₊ : ℝ) + 14 ≤
        (2 * B + 18) * Real.log (Real.log X) ∧
      ∀ p ∈ primeWindow X B ε,
        p ∈ (Finset.Ioc ⌊z0 X B ε / 2⌋₊ ⌊Y X ε ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime := by
  have hc : 0 < 1 / (128 * (B + 1)) := by positivity
  have hs := Real.tendsto_log_atTop.eventually (Real.isLittleO_log_id_atTop.bound hc)
  have hlarge : ∀ᶠ X : ℝ in Filter.atTop, 128 ≤ Real.log X ∧ Real.exp 1 ≤ Real.log X := by
    exact (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 128)).and
      (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (Real.exp 1)))
  filter_upwards [hs, hlarge, Filter.eventually_gt_atTop (1 : ℝ)] with X hs hx hx1
  let L := Real.log X
  have hL : 0 < L := by dsimp [L]; linarith [hx.1]
  have hlogL : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hx.2
    simpa only [Real.log_exp] using hh
  have hs' : Real.log L ≤ L / (128 * (B + 1)) := by
    change ‖Real.log L‖ ≤ (1 / (128 * (B + 1))) * ‖L‖ at hs
    simpa only [Real.norm_eq_abs, abs_of_pos hL,
      abs_of_nonneg (by linarith : 0 ≤ Real.log L), one_div, div_eq_mul_inv, one_mul, mul_comm] using hs
  have hs'' : 128 * (B + 1) * Real.log L ≤ L := by
    have hh := (le_div_iff₀ (show 0 < 128 * (B + 1) by positivity)).mp hs'
    nlinarith
  have hsmall : 2 * B * Real.log L ≤ L / 32 := by
    nlinarith [mul_nonneg hB.le (show 0 ≤ Real.log L by linarith)]
  have hX : 0 < X := by linarith
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hX _
  have hU : 0 < Y X ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hY _
  have hz : 0 < z0 X B ε := by unfold z0; positivity
  have hlogU : Real.log (Y X ε ^ (1 / 4 : ℝ)) = (7 / 12 + ε / 2) / 4 * L := by
    rw [Real.log_rpow hY, Y, Real.log_rpow hX]
    dsimp [L]; ring
  have hlogz : Real.log (z0 X B ε) = (7 / 12 + ε / 2) / 4 * L - 2 * B * Real.log L := by
    unfold z0
    rw [Real.log_mul hU.ne' (by positivity), Real.log_zpow,
      Real.log_rpow hL, hlogU]
    norm_num
    ring
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlogzlarge : L / 32 + Real.log 4 ≤ Real.log (z0 X B ε) := by
    rw [hlogz]
    have he : 0 ≤ ε * L := mul_nonneg hε.le hL.le
    dsimp [L] at *
    nlinarith [hx.1]
  have hz4 : 4 ≤ z0 X B ε :=
    (Real.log_le_log_iff (by norm_num) hz).mp (by linarith)
  let y : ℕ := ⌊z0 X B ε / 2⌋₊
  let w : ℕ := ⌊Y X ε ^ (1 / 4 : ℝ)⌋₊
  have hy2 : 2 ≤ y := (Nat.le_floor (by linarith : (2 : ℝ) ≤ z0 X B ε / 2))
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hyquarter : z0 X B ε / 4 ≤ (y : ℝ) := by
    have hh := Nat.lt_floor_add_one (z0 X B ε / 2)
    change z0 X B ε / 2 < (y : ℝ) + 1 at hh
    linarith
  have hlogy : Real.log (z0 X B ε) - Real.log 4 ≤ Real.log (y : ℝ) := by
    have hh := Real.log_le_log (show 0 < z0 X B ε / 4 by positivity) hyquarter
    rwa [Real.log_div hz.ne' (by norm_num)] at hh
  have hzy : z0 X B ε ≤ Y X ε ^ (1 / 4 : ℝ) := by
    apply (Real.log_le_log_iff hz hU).mp
    rw [hlogz, hlogU]
    nlinarith [mul_nonneg hB.le (show 0 ≤ Real.log L by linarith)]
  have hyw : y ≤ w := Nat.floor_mono (show z0 X B ε / 2 ≤ Y X ε ^ (1 / 4 : ℝ) by linarith)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hlogw : Real.log (w : ℝ) ≤ Real.log (Y X ε ^ (1 / 4 : ℝ)) :=
    Real.log_le_log hw0 (Nat.floor_le hU.le)
  refine ⟨hL, hlogL, hy2, hyw, by linarith, ?_, ?_⟩
  · rw [hlogU] at hlogw
    rw [hlogz] at hlogy
    nlinarith
  · intro p hp
    obtain ⟨hpR, hpp, hpz, hpU⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hpp⟩
    · have hylt : (y : ℝ) < p := (Nat.floor_le (by positivity : 0 ≤ z0 X B ε / 2)).trans_lt
          (show z0 X B ε / 2 < p by linarith)
      exact_mod_cast hylt
    · exact Nat.le_floor hpU.le

/-- Page 16 display 57, the short reciprocal prime sum has size log log X over log X. -/
theorem prime_reciprocal_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      0 < Real.log X ∧
      (∀ p ∈ primeWindow X B ε, Real.log X / 32 ≤ Real.log p) ∧
      (∑ p ∈ primeWindow X B ε, (1 : ℝ) / p) ≤
        32 * (2 * B + 18) * Real.log (Real.log X) / Real.log X := by
  filter_upwards [prime_window_parameters B ε hB hε] with X hx
  obtain ⟨hL, hll, hy, hyw, hlogy, hdiff, hsub⟩ := hx
  let y : ℕ := ⌊z0 X B ε / 2⌋₊
  let w : ℕ := ⌊Y X ε ^ (1 / 4 : ℝ)⌋₊
  have hly : 0 < Real.log (y : ℝ) := lt_of_lt_of_le (by positivity) hlogy
  refine ⟨hL, ?_, ?_⟩
  · intro p hp
    have hpy := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hsub p hp)).1).1
    exact hlogy.trans (Real.log_le_log (by exact_mod_cast (show 0 < y by omega))
      (by exact_mod_cast hpy.le))
  · calc _ ≤ ∑ p ∈ (Finset.Ioc y w).filter Nat.Prime, (1 : ℝ) / p :=
           Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
         _ ≤ (Real.log w - Real.log y + 14) / Real.log y :=
           LeanLab.PNTSieve.Mertens.sum_inv_primes_block y w hy hyw
         _ ≤ ((2 * B + 18) * Real.log (Real.log X)) / Real.log y :=
           div_le_div_of_nonneg_right hdiff hly.le
         _ ≤ 32 * (2 * B + 18) * Real.log (Real.log X) / Real.log X := by
           rw [div_le_div_iff₀ hly hL]
           have hh : 0 ≤ (2 * B + 18) * Real.log (Real.log X) := by positivity
           nlinarith [mul_nonneg hh (show 0 ≤ 32 * Real.log (y : ℝ) - Real.log X by linarith)]

/-- Page 16 display 57, N is at most a constant times the stated main term scale. -/
theorem prime_mass_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → primeMass X B ε ≤ C * massScale X ε := by
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp (prime_reciprocal_bound B ε hB hε)
  refine ⟨1024 * (2 * B + 18), X0, by positivity, ?_⟩
  intro X hX
  obtain ⟨hL, hlogs, hsum⟩ := hX0 X hX
  have hbound := (primeMass_bound_of_logs X B ε (Real.log X) hL hlogs).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 32 * Real.sqrt (Y X ε) / Real.log X))
  convert hbound using 1
  unfold massScale
  rw [Real.sqrt_eq_rpow, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg hL.le, Real.rpow_two]
  ring

/-- Page 16 before display 56, a rough composite below the cube of its roughness cutoff
has exactly two prime factors. This is a derived elementary support step. -/
theorem rough_composite_two_primes (q : ℕ) (z : ℝ) (hz : 1 < z) (hq : 1 < q)
    (hnp : ¬ q.Prime) (hrough : ∀ p : ℕ, p.Prime → p ∣ q → z ≤ (p : ℝ))
    (hsmall : (q : ℝ) < z ^ 3) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≤ r ∧ q = p * r ∧ z ≤ (p : ℝ) ∧ p ^ 2 ≤ q := by
  let p := q.minFac
  let r := q / p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ q := Nat.minFac_dvd q
  have hpr : p ≤ r := Nat.minFac_le_div (by omega) hnp
  have hr1 : 1 < r := lt_of_lt_of_le hp.one_lt hpr
  have hqr : q = p * r := by
    dsimp [r]
    exact (Nat.mul_div_cancel' hpd).symm
  have hzp : z ≤ (p : ℝ) := hrough p hp hpd
  have hr : r.Prime := by
    by_contra hnr
    let s := r.minFac
    have hs : s.Prime := Nat.minFac_prime (by omega)
    have hsd : s ∣ q := (Nat.minFac_dvd r).trans (Nat.div_dvd_of_dvd hpd)
    have hzs : z ≤ (s : ℝ) := hrough s hs hsd
    have hsq : s ^ 2 ≤ r := Nat.minFac_sq_le_self (by omega) hnr
    have hsqR : (s : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hsq
    have hz2 : z ^ 2 ≤ (r : ℝ) := by nlinarith
    have hqR : (q : ℝ) = (p : ℝ) * (r : ℝ) := by exact_mod_cast hqr
    have hcube : z ^ 3 ≤ (q : ℝ) := by
      rw [hqR, pow_succ]
      simpa only [mul_comm] using mul_le_mul hz2 hzp (by linarith : 0 ≤ z) (by positivity : (0 : ℝ) ≤ r)
    linarith
  exact ⟨p, r, hp, hr, hpr, hqr, hzp, Nat.minFac_sq_le_self (by omega) hnp⟩

end LeanLab.KumchevLiu2007.Task506b
