module

public import LeanLab.PNTPort.BVMax.RenyiMain
public import LeanLab.PNTPort.BVMax.TauGoldbachMain

/-!
# The parameter choice closing Brun's pure sieve on `{N - p}`

Unit U-5502, CLOUD 20261019T1218Z-cloud24, IDEAS I-5051. AI wrote the Lean code. Known mathematics:
Brun's pure sieve with Bombieri-Vinogradov level, the shape of Rényi 1948 with a slowly growing
number of prime factors.

`renyi_loglog`: there is `N₀` such that every even `N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and
`Ω(m) ≤ 360 log log N + 7218`. Unconditional and ineffective, through `renyi_main` and the lab's
Siegel-Walfisz. Rényi's fixed `K` needs a sieve stronger than the pure sieve, the fundamental lemma.

Parameters, `ℓ = log N`: `r = 2⌈30(log ℓ + 20)⌉ + 1`, odd; `z = ⌊e^{ℓ/(3r)}⌋`; `P` the primes
`3 ≤ p ≤ z` not dividing `N`. Then every `∏T`, `|T| ≤ r`, is at most `z^r ≤ N^{1/3}`, the factorial
term of `renyi_main` is at most `e^{-(r+1)} ≤ e^{-37}/log z`, so the sifted count is at least
`c (N - 2)/ℓ² - K N/ℓ³` with `c = e^{-36} - e^{-37}`, more than `z + 1`. A survivor `N - p` with
`p > z` is odd, has no prime factor `≤ z`, so `z^{Ω(N - p)} ≤ N` and `Ω ≤ ℓ/log z ≤ 6r`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset Real

/-- The deterministic core: at an even `N` where three explicit inequalities hold, `N = p + m` with
`Ω(m) ≤ 360 log log N + 7218`. `B, K` are the constants of `renyi_main` at `A = 3`. -/
theorem renyi_core {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ z : ℕ, 3 ≤ z → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p ∧ p ≤ z) →
      ∀ r : ℕ, Odd r →
      (∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
        ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      liD ((N - 1 : ℕ) : ℝ) * (Real.exp (-36) / Real.log z -
        (Real.log (Real.log z) + 20) ^ (r + 1) / (r + 1).factorial) -
        K * N / Real.log N ^ (3 : ℝ) ≤ (LeanLab.PNTSieve.Bonferroni.sifted (goldbachSeq N) P : ℝ))
    (N : ℕ) (hE : Even N) (h4 : 4 ≤ N)
    (hE1 : 5 * (60 * Real.log (Real.log N) + 1203) ≤ Real.log N)
    (hE2 : Real.exp (Real.log N / 3) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : K * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧
      (ArithmeticFunction.cardFactors m : ℝ) ≤ 360 * Real.log (Real.log N) + 7218 := by
  classical
  set ℓ := Real.log N with hℓ
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast h4
  have hℓpos : 0 < ℓ := Real.log_pos (by linarith)
  -- log ℓ ≥ 0
  have hℓ1 : 1 ≤ ℓ := by
    have he : Real.exp 1 ≤ N := by have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this
  have hlℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  -- r
  set k := ⌈30 * (Real.log ℓ + 20)⌉₊ with hk
  set r := 2 * k + 1 with hr
  have hrodd : Odd r := ⟨k, rfl⟩
  have hk1 : 30 * (Real.log ℓ + 20) ≤ (k : ℝ) := Nat.le_ceil _
  have hk2 : (k : ℝ) < 30 * (Real.log ℓ + 20) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrr : (r : ℝ) = 2 * k + 1 := by rw [hr]; push_cast; ring
  have hr_lo : 60 * (Real.log ℓ + 20) ≤ (r : ℝ) + 1 := by rw [hrr]; linarith
  have hr_hi : (r : ℝ) ≤ 60 * Real.log ℓ + 1203 := by rw [hrr]; linarith
  have hrpos : (0 : ℝ) < r := by rw [hrr]; positivity
  have hℓr : 5 * (r : ℝ) ≤ ℓ := by linarith
  -- z
  set w := Real.exp (ℓ / (3 * r)) with hw
  set z := ⌊w⌋₊ with hz
  have hw53 : 5 / 3 ≤ ℓ / (3 * r) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hw3 : (4 : ℝ) ≤ w := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 / 3 by norm_num)
    have := Real.exp_le_exp.mpr hw53
    rw [hw]; nlinarith
  have hz3 : 3 ≤ z := Nat.le_floor (by push_cast; linarith)
  have hzw : (z : ℝ) ≤ w := Nat.floor_le (by linarith)
  have hzw2 : w / 2 ≤ (z : ℝ) := by
    have := Nat.lt_floor_add_one w
    rw [← hz] at this
    linarith
  have hz3r : (3 : ℝ) ≤ z := by exact_mod_cast hz3
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogz_hi : Real.log z ≤ ℓ / (3 * r) := by
    calc Real.log z ≤ Real.log w := Real.log_le_log (by linarith) hzw
      _ = ℓ / (3 * r) := Real.log_exp _
  have hlogz_lo : ℓ / (6 * r) ≤ Real.log z := by
    have h2 : Real.log (w / 2) ≤ Real.log z := Real.log_le_log (by linarith) hzw2
    rw [Real.log_div (by linarith) (by norm_num), hw, Real.log_exp] at h2
    have hl2 := Real.log_two_lt_d9
    have : ℓ / (6 * r) + 0.7 ≤ ℓ / (3 * r) := by
      rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hr1 : (1 : ℝ) ≤ r := by rw [hrr]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hlogz_ℓ : Real.log z ≤ ℓ :=
    hlogz_hi.trans (div_le_self hℓpos.le (by linarith))
  -- the sieve set
  set P := (Icc 3 z).filter (fun p => p.Prime ∧ ¬ p ∣ N) with hP
  have hPmem : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p ∧ p ≤ z := by
    intro p hp
    rw [hP, mem_filter, mem_Icc] at hp
    exact ⟨hp.2.1, hp.2.2, hp.1.1, hp.1.2⟩
  have hzr : ((z : ℝ)) ^ r ≤ Real.exp (ℓ / 3) := by
    calc ((z : ℝ)) ^ r ≤ w ^ r := pow_le_pow_left₀ (by positivity) hzw r
      _ = Real.exp (ℓ / 3) := by
        have hrℓ : (r : ℝ) * (ℓ / (3 * r)) = ℓ / 3 := by
          rw [mul_div_assoc', mul_comm (3 : ℝ) r, mul_div_mul_left _ _ hrpos.ne']
        rw [hw, ← Real.exp_nat_mul, hrℓ]
  have hT : ∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    intro T hT
    rw [mem_filter, mem_powerset] at hT
    apply Nat.le_floor
    have h1 : ∏ p ∈ T, p ≤ z ^ T.card :=
      Finset.prod_le_pow_card T _ z (fun p hp => (hPmem p (hT.1 hp)).2.2.2)
    have h2 : z ^ T.card ≤ z ^ r := Nat.pow_le_pow_right (by omega) hT.2
    have h3 : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (z : ℝ) ^ r := by exact_mod_cast h1.trans h2
    linarith
  have hS := hK N (by omega) z hz3 P hPmem r hrodd hT
  -- the factorial term
  have hlogz1 : 5 / 6 ≤ Real.log z := by
    refine le_trans ?_ hlogz_lo
    rw [le_div_iff₀ (by positivity)]; linarith
  have hloglog_lo : -1 ≤ Real.log (Real.log z) := by
    have := Real.one_sub_inv_le_log_of_pos hlogz_pos
    have : (Real.log z)⁻¹ ≤ 6 / 5 := by
      rw [inv_le_comm₀ hlogz_pos (by norm_num)]; linarith
    linarith
  have hloglog_hi : Real.log (Real.log z) ≤ Real.log ℓ := Real.log_le_log hlogz_pos hlogz_ℓ
  set u := Real.log (Real.log z) + 20 with hu
  have hu0 : 0 ≤ u := by linarith
  have he3 : Real.exp 3 * u ≤ ((r + 1 : ℕ) : ℝ) := by
    have h3 : Real.exp 3 < 21 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have h1 : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ h0 this.le 3
      norm_num at h1
      linarith
    push_cast
    have hu20 : u ≤ Real.log ℓ + 20 := by rw [hu]; linarith
    have : Real.exp 3 * u ≤ 21 * (Real.log ℓ + 20) := by
      calc Real.exp 3 * u ≤ 21 * u := mul_le_mul_of_nonneg_right h3.le hu0
        _ ≤ 21 * (Real.log ℓ + 20) := by linarith
    linarith
  have hfac := pow_div_factorial_le_exp_neg u hu0 (r + 1) he3
  have hfac2 : Real.exp (-(((r + 1 : ℕ) : ℝ))) ≤ Real.exp (-37) / Real.log z := by
    rw [le_div_iff₀ hlogz_pos]
    have hx : Real.exp (-(((r + 1 : ℕ) : ℝ))) * Real.log z ≤
        Real.exp (-(((r + 1 : ℕ) : ℝ))) * ℓ :=
      mul_le_mul_of_nonneg_left hlogz_ℓ (Real.exp_pos _).le
    have hy : Real.exp (-(((r + 1 : ℕ) : ℝ))) * ℓ ≤ Real.exp (-37) := by
      calc Real.exp (-(((r + 1 : ℕ) : ℝ))) * ℓ
          = Real.exp (-(((r + 1 : ℕ) : ℝ))) * Real.exp (Real.log ℓ) := by rw [Real.exp_log hℓpos]
        _ = Real.exp (-(((r + 1 : ℕ) : ℝ)) + Real.log ℓ) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-37) := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
    linarith
  set c := Real.exp (-36) - Real.exp (-37) with hc
  have hcpos : 0 < c := by
    rw [hc, sub_pos]; exact Real.exp_lt_exp.mpr (by norm_num)
  have hbr : c / ℓ ≤ Real.exp (-36) / Real.log z - u ^ (r + 1) / (r + 1).factorial := by
    have : Real.exp (-36) / Real.log z - Real.exp (-37) / Real.log z = c / Real.log z := by
      rw [hc]; ring
    have h2 : c / ℓ ≤ c / Real.log z := div_le_div_of_nonneg_left hcpos.le hlogz_pos hlogz_ℓ
    have h3 := hfac.trans hfac2
    linarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hmain : ((N : ℝ) - 2) / ℓ * (c / ℓ) ≤
      liD ((N - 1 : ℕ) : ℝ) * (Real.exp (-36) / Real.log z - u ^ (r + 1) / (r + 1).factorial) :=
    mul_le_mul hliD hbr (div_nonneg hcpos.le hℓpos.le) (hliD0.trans hliD)
  have hmain2 : ((N : ℝ) - 2) / ℓ * (c / ℓ) = c * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp
  have hzle : (z : ℝ) ≤ Real.exp (ℓ / 3) := by
    have : (z : ℝ) ≤ (z : ℝ) ^ r := by
      have hr1 : 1 ≤ r := by omega
      calc (z : ℝ) = (z : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (z : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr1
    linarith
  have hSbig : (z : ℝ) + 2 ≤ (LeanLab.PNTSieve.Bonferroni.sifted (goldbachSeq N) P : ℝ) := by
    rw [hu] at hmain
    linarith
  -- a survivor N - p with p > z
  set Surv := (goldbachSeq N).filter (fun a => ∀ p ∈ P, ¬ p ∣ a) with hSurv
  have hcardS : (z : ℝ) + 2 ≤ (Surv.card : ℝ) := by
    have : (LeanLab.PNTSieve.Bonferroni.sifted (goldbachSeq N) P : ℝ) = (Surv.card : ℝ) := by
      simp [LeanLab.PNTSieve.Bonferroni.sifted, hSurv]
    linarith
  have hsmall : ((range (z + 1)).image (fun p => N - p)).card ≤ z + 1 :=
    card_image_le.trans (by simp)
  obtain ⟨m, hmS, hmn⟩ : ∃ m ∈ Surv, m ∉ (range (z + 1)).image (fun p => N - p) := by
    by_contra h
    push Not at h
    have hsub : Surv ⊆ (range (z + 1)).image (fun p => N - p) := fun m hm => h m hm
    have := card_le_card hsub
    have : (Surv.card : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast this.trans hsmall
    linarith
  rw [hSurv, mem_filter] at hmS
  obtain ⟨hmG, hmP⟩ := hmS
  unfold goldbachSeq at hmG
  rw [mem_image] at hmG
  obtain ⟨p, hp, rfl⟩ := hmG
  rw [mem_filter, mem_range] at hp
  obtain ⟨hpN, hpp⟩ := hp
  have hpz : z < p := by
    by_contra h
    push Not at h
    exact hmn (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
  have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
  have hmodd : Odd (N - p) := by
    rcases hE with ⟨a, ha⟩
    rcases hpodd with ⟨b, hb⟩
    exact ⟨a - b - 1, by omega⟩
  have hm0 : N - p ≠ 0 := by omega
  -- every prime factor of N - p exceeds z
  have hfac_big : ∀ q ∈ (N - p).primeFactorsList, z ≤ q := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactorsList hq
    have hqd := Nat.dvd_of_mem_primeFactorsList hq
    by_contra hlt
    push Not at hlt
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hqd)
    have hq3 : 3 ≤ q := by have := hqp.two_le; omega
    by_cases hqN : q ∣ N
    · have : q ∣ p := by
        have h1 := Nat.dvd_sub hqN hqd
        rwa [Nat.sub_sub_self hpN.le] at h1
      have := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp this
      omega
    · exact hmP q (by rw [hP, mem_filter, mem_Icc]; exact ⟨⟨hq3, hlt.le⟩, hqp, hqN⟩) hqd
  have hpow := pow_bigOmega_le (N - p) z hm0 hfac_big
  -- Ω(N - p) log z ≤ ℓ
  set Ω := ArithmeticFunction.cardFactors (N - p) with hΩ
  have hpowr : (z : ℝ) ^ Ω ≤ N := by
    have : z ^ Ω ≤ N := hpow.trans (Nat.sub_le N p)
    exact_mod_cast this
  have hlogpow : (Ω : ℝ) * Real.log z ≤ ℓ := by
    have := Real.log_le_log (by positivity) hpowr
    rwa [Real.log_pow] at this
  have hΩ6r : (Ω : ℝ) ≤ 6 * r := by
    have h1 : (Ω : ℝ) * (ℓ / (6 * r)) ≤ ℓ :=
      (mul_le_mul_of_nonneg_left hlogz_lo (Nat.cast_nonneg _)).trans hlogpow
    have h2 : (Ω : ℝ) * (ℓ / (6 * r)) = (Ω : ℝ) * ℓ / (6 * r) := by ring
    rw [h2, div_le_iff₀ (by positivity)] at h1
    exact le_of_mul_le_mul_right (h1.trans_eq (mul_comm _ _)) hℓpos
  refine ⟨p, N - p, hpp, by omega, by omega, ?_⟩
  linarith

open Filter in
/-- The three inequalities of `renyi_core` hold for every large real `x`. -/
theorem renyi_large (B K : ℝ) : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    4 ≤ x ∧ 5 * (60 * Real.log (Real.log x) + 1203) ≤ Real.log x ∧
    Real.exp (Real.log x / 3) ≤ Real.sqrt x / Real.log x ^ B ∧
    K * x / Real.log x ^ (3 : ℝ) + Real.exp (Real.log x / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * (x - 2) / Real.log x ^ 2 := by
  set c := Real.exp (-36) - Real.exp (-37) with hc
  have hcpos : 0 < c := by
    rw [hc, sub_pos]; exact Real.exp_lt_exp.mpr (by norm_num)
  have e1 : ∀ᶠ x in atTop, 5 * (60 * Real.log (Real.log x) + 1203) ≤ Real.log x := by
    have h1 : ∀ᶠ ℓ in atTop, 300 * Real.log ℓ + 6015 ≤ ℓ := by
      have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 600 by norm_num)
      filter_upwards [hb, eventually_ge_atTop (12030 : ℝ)] with ℓ h hℓ
      simp only [Real.norm_eq_abs, id] at h
      rw [abs_of_nonneg (show (0 : ℝ) ≤ ℓ by linarith)] at h
      have := le_abs_self (Real.log ℓ)
      nlinarith
    filter_upwards [Real.tendsto_log_atTop.eventually h1] with x hx
    linarith
  have hexp3 : ∀ x : ℝ, 0 < x → Real.exp (Real.log x / 3) = x ^ (1 / 3 : ℝ) := by
    intro x hx
    rw [Real.rpow_def_of_pos hx]; ring_nf
  have e2 : ∀ᶠ x in atTop, Real.exp (Real.log x / 3) ≤ Real.sqrt x / Real.log x ^ B := by
    have hb := (isLittleO_log_rpow_rpow_atTop B (show (0 : ℝ) < 1 / 6 by norm_num)).bound one_pos
    filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x h hx
    have hl : 0 < Real.log x := Real.log_pos hx
    have hlB : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hl B
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlB,
      abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul] at h
    rw [le_div_iff₀ hlB, hexp3 x (by linarith), Real.sqrt_eq_rpow]
    calc x ^ (1 / 3 : ℝ) * Real.log x ^ B ≤ x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add (by linarith)]; norm_num
  have e3 : ∀ᶠ x in atTop, K * x / Real.log x ^ (3 : ℝ) + Real.exp (Real.log x / 3) + 2 ≤
      c * (x - 2) / Real.log x ^ 2 := by
    have hb := (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 2 / 3 by norm_num)).bound
      (show (0 : ℝ) < c / 8 by positivity)
    filter_upwards [hb, eventually_ge_atTop (8 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (8 * |K| / c + 1))] with x h hx8 hlK
    have hl : 0 < Real.log x := by
      have : 0 ≤ 8 * |K| / c := by positivity
      linarith
    set ℓ := Real.log x with hℓ
    have hx0 : 0 < x := by linarith
    have h2r : ℓ ^ (2 : ℝ) = ℓ ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h2r, abs_of_pos (by positivity),
      abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at h
    rw [h3r, hexp3 x hx0]
    have hx13 : 1 ≤ x ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hsplit : x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    -- K x / ℓ³ ≤ (c/8) x / ℓ²
    have hK1 : K ≤ c / 8 * ℓ := by
      have : 8 * |K| / c ≤ ℓ := by linarith
      rw [div_le_iff₀ hcpos] at this
      have := le_abs_self K
      nlinarith
    have hA : K * x / ℓ ^ 3 ≤ c / 8 * x / ℓ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : K * x * ℓ ^ 2 ≤ c / 8 * ℓ * x * ℓ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hx0.le) (by positivity)
      nlinarith
    -- 3 x^{1/3} ≤ (3c/8) x / ℓ²
    have hB : 3 * x ^ (1 / 3 : ℝ) ≤ 3 * c / 8 * x / ℓ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 3 * x ^ (1 / 3 : ℝ) by positivity)
      nlinarith
    have hC : c / 8 * x / ℓ ^ 2 + 3 * c / 8 * x / ℓ ^ 2 ≤ c * (x - 2) / ℓ ^ 2 := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    linarith
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((e1.and e2).and (e3.and (eventually_ge_atTop (4 : ℝ))))
  exact ⟨X, fun x hx => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hX x hx
    exact ⟨h4, h1, h2, h3⟩⟩

/-- **Brun's pure sieve on `{N - p}`, assembled, PROVED unconditional.** There is `N₀` such that every
even `N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 360 log log N + 7218`. Ineffective. -/
theorem renyi_loglog : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧
      (ArithmeticFunction.cardFactors m : ℝ) ≤ 360 * Real.log (Real.log N) + 7218 := by
  obtain ⟨B, -, K, hK⟩ := renyi_main 3 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B K
  refine ⟨⌈X⌉₊, fun N hN hE => ?_⟩
  have hx : X ≤ (N : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hN)
  obtain ⟨h4, h1, h2, h3⟩ := hX N hx
  exact renyi_core hK N hE (by exact_mod_cast h4) h1 h2 h3

end LeanLab.PNTPort.BVMax

