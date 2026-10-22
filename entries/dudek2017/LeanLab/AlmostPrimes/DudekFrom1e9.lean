module

public import LeanLab.AlmostPrimes.DudekGroups
public import LeanLab.AlmostPrimes.DudekCount

/-!
# Dudek's prime plus square-free theorem from `10⁹`, I-5067

Unit U-5662, CLOUD 20261019T1515Z-cloud27. AI wrote the Lean code. KNOWN mathematics, Dudek 2017.

`bad_sum_le9`: for `N ≥ 10⁹`, with `Q = 80⌈log N⌉`, the Brun-Titchmarsh classes of the odd primes
`r ≤ Q` plus the tail `Σ_{Q < n ≤ N} ⌊N/n²⌋` total at most `0.906 N / log N`. The primes are split
into nine groups, `3`, `5`, `7`, `{11, 13}`, `{17, ..., 31}`, `(31, 127]`, `(127, 511]`,
`(511, 2047]` and `(2047, Q]`, each with its own level `θ` in `brun_titchmarsh_ap_pow`, its own
lower bound `log N - 2 log b` for `log((N + 1)/r²)` and its own prime weight `Σ 1/(r(r - 1))`.
`dudek_even_from_1e9`: every even `N ≥ 10⁹` is a prime plus a square-free number, no cited input,
against Chebyshev's `π(N) ≥ (0.9212 N - 5 log N)/log N`. The range below `10⁹` is the kernel
check of `Verifications/U1437Fast/`.
-/

@[expose] public section


open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.DudekFrom1e9

open LeanLab.AlmostPrimes.DudekLarge LeanLab.AlmostPrimes.DudekFrom4e18
open LeanLab.AlmostPrimes.DudekGroups LeanLab.AlmostPrimes.DudekCount

/-- `e^{-x} ≤ 1/(e₁^n (1 + d + d²/2))`, `d = y₀ - n`, for `n ≤ y₀ ≤ x`, `e₁ = 2.7182818283`. -/
lemma exp_neg_le2 (n : ℕ) {x y₀ : ℝ} (hn : (n : ℝ) ≤ y₀) (hy : y₀ ≤ x) :
    exp (-x) ≤ 1 / ((2.7182818283 : ℝ) ^ n * (1 + (y₀ - n) + (y₀ - n) ^ 2 / 2)) := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := y₀ - n) (by linarith)
  have h1 : (2.7182818283 : ℝ) ^ n * (1 + (y₀ - n) + (y₀ - n) ^ 2 / 2) ≤ exp x := by
    have he : exp y₀ = exp n * exp (y₀ - n) := by rw [← Real.exp_add]; ring_nf
    calc _ ≤ exp n * exp (y₀ - n) :=
          mul_le_mul (exp_nat_ge n) hq (by positivity) (exp_pos _).le
      _ = exp y₀ := he.symm
      _ ≤ exp x := Real.exp_le_exp.mpr hy
  have h0 : 0 < (2.7182818283 : ℝ) ^ n * (1 + (y₀ - n) + (y₀ - n) ^ 2 / 2) := by
    apply mul_pos (by positivity); nlinarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le h0 h1

/-- `n L² ≤ c e^{a L}` for `L ≥ 20.7`, from three numeric conditions at `L = 20.7`. -/
lemma cnt_le (n m : ℕ) {a c L : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hL : 20.7 ≤ L)
    (hm : (m : ℝ) ≤ a * 20.7)
    (h0 : (n : ℝ) * 20.7 ^ 2 ≤ c * (2.7182818283 : ℝ) ^ m)
    (h1 : 2 * (n : ℝ) * 20.7 ≤ c * (2.7182818283 : ℝ) ^ m * a)
    (h2 : (n : ℝ) ≤ c * (2.7182818283 : ℝ) ^ m * a ^ 2 / 2) :
    (n : ℝ) * L ^ 2 ≤ c * exp (a * L) := by
  set s := L - 20.7 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  set E := (2.7182818283 : ℝ) ^ m with hE
  have hq := Real.quadratic_le_exp_of_nonneg (x := a * L - m) (by nlinarith)
  have hexp : E * (1 + a * s + (a * s) ^ 2 / 2) ≤ exp (a * L) := by
    have he : exp (a * L) = exp m * exp (a * L - m) := by rw [← Real.exp_add]; ring_nf
    rw [he]
    have hd : a * s ≤ a * L - m := by rw [hs]; nlinarith
    have hq' : 1 + a * s + (a * s) ^ 2 / 2 ≤ 1 + (a * L - m) + (a * L - m) ^ 2 / 2 := by
      have : 0 ≤ a * s := by positivity
      nlinarith
    exact mul_le_mul (exp_nat_ge m) (hq'.trans hq) (by positivity) (exp_pos _).le
  have hLs : L = 20.7 + s := by rw [hs]; ring
  have hcE : 0 ≤ c * E := by positivity
  calc (n : ℝ) * L ^ 2 = n * 20.7 ^ 2 + 2 * n * 20.7 * s + n * s ^ 2 := by rw [hLs]; ring
    _ ≤ c * E + c * E * a * s + c * E * a ^ 2 / 2 * s ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1 hs0
        have := mul_le_mul_of_nonneg_right h2 (sq_nonneg s)
        linarith
    _ = c * (E * (1 + a * s + (a * s) ^ 2 / 2)) := by ring
    _ ≤ c * exp (a * L) := mul_le_mul_of_nonneg_left hexp hc

/-- **One group.** A set `T` of primes `r ≤ b` with `2r² ≤ N + 1`, a level `θ`, `log b ≤ lb`, a
factor bound `F` valid for `λ ≥ 20.7 - 2 lb`, `20.7 ≤ k (20.7 - 2 lb)` and weight `w`. -/
lemma group_le {N : ℕ} (hN1 : 1 ≤ N) (hL : 20.7 ≤ Real.log N) (T : Finset ℕ) {b lb θ F k w : ℝ}
    (hT : ∀ r ∈ T, r.Prime ∧ 2 * r ^ 2 ≤ N + 1 ∧ (r : ℝ) ≤ b)
    (hlb : Real.log b ≤ lb) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hlam0 : 0 < 20.7 - 2 * lb)
    (hF : ∀ lam : ℝ, 20.7 - 2 * lb ≤ lam →
      1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam)) ≤ F)
    (hk : 20.7 ≤ k * (20.7 - 2 * lb)) (hk1 : 1 ≤ k)
    (hw : ∑ r ∈ T, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ w) :
    ∑ r ∈ T, ((cls N r).card : ℝ) ≤
      T.card * (N : ℝ) ^ θ + 1 / θ * ((N : ℝ) + 1) * F * w * k / Real.log N := by
  set L := Real.log N with hLdef
  set lam := L - 2 * lb with hlam
  have hlamge : 20.7 - 2 * lb ≤ lam := by rw [hlam]; linarith
  have hlampos : 0 < lam := by linarith
  have hFl := hF lam hlamge
  have hF0 : 0 ≤ F := le_trans (by positivity) hFl
  have hLpos : 0 < L := by linarith
  have hper : ∀ r ∈ T, ((cls N r).card : ℝ) ≤ (N : ℝ) ^ θ +
      1 / θ * ((N : ℝ) + 1) * F / lam * ((1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1))) := by
    intro r hr
    obtain ⟨hp, h2, hrb⟩ := hT r hr
    have hr1 : 1 ≤ r := hp.one_lt.le
    have hlog := log_cls_ge (N := N) hN1 hr1 hrb
    have hc := cls_card_pow_gen hp h2 hN1 hθ0 hθ1 hlampos (by rw [hlam]; linarith)
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hp.two_le
    have hrr : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    calc ((cls N r).card : ℝ) ≤ _ := hc
      _ ≤ (N : ℝ) ^ θ + 1 / θ * ((N : ℝ) + 1) * F / (lam * ((r : ℝ) * ((r : ℝ) - 1))) := by
          gcongr
      _ = _ := by field_simp
  calc ∑ r ∈ T, ((cls N r).card : ℝ)
      ≤ ∑ r ∈ T, ((N : ℝ) ^ θ + 1 / θ * ((N : ℝ) + 1) * F / lam *
          ((1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)))) := sum_le_sum hper
    _ = T.card * (N : ℝ) ^ θ + 1 / θ * ((N : ℝ) + 1) * F / lam *
          ∑ r ∈ T, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
    _ ≤ T.card * (N : ℝ) ^ θ + 1 / θ * ((N : ℝ) + 1) * F / lam * w := by
        gcongr
    _ ≤ T.card * (N : ℝ) ^ θ + 1 / θ * ((N : ℝ) + 1) * F * w * k / L := by
        have hkl : L ≤ k * lam := by rw [hlam]; nlinarith
        have : 1 / lam ≤ k / L := by
          rw [div_le_div_iff₀ hlampos hLpos]; linarith
        have hA : 0 ≤ 1 / θ * ((N : ℝ) + 1) * F * w := by
          have : 0 ≤ w := le_trans (sum_nonneg (fun r hr => by
            obtain ⟨hp, -, -⟩ := hT r hr
            have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hp.two_le
            have : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
            positivity)) hw
          positivity
        calc T.card * (N : ℝ) ^ θ + 1 / θ * ((N : ℝ) + 1) * F / lam * w
            = T.card * (N : ℝ) ^ θ + (1 / θ * ((N : ℝ) + 1) * F * w) * (1 / lam) := by ring
          _ ≤ T.card * (N : ℝ) ^ θ + (1 / θ * ((N : ℝ) + 1) * F * w) * (k / L) := by gcongr
          _ = _ := by ring


/-- `e₁^n (1 + d + d²/2) ≤ e^y`, `d = y - n`, for `n ≤ y`. -/
lemma exp_ge_q (n : ℕ) {y : ℝ} (hn : (n : ℝ) ≤ y) :
    (2.7182818283 : ℝ) ^ n * (1 + (y - n) + (y - n) ^ 2 / 2) ≤ exp y := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := y - n) (by linarith)
  have he : exp y = exp n * exp (y - n) := by rw [← Real.exp_add]; ring_nf
  rw [he]
  exact mul_le_mul (exp_nat_ge n) hq (by positivity) (exp_pos _).le

/-- `n L² ≤ c e^{a L}` for `L ≥ 20.7`, from a base `E₀ ≤ e^{20.7 a}`. -/
lemma cnt_le' (n : ℕ) {a c L E₀ : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hL : 20.7 ≤ L)
    (hE : E₀ ≤ exp (a * 20.7)) (hE0 : 0 ≤ E₀)
    (h0 : (n : ℝ) * 20.7 ^ 2 ≤ c * E₀) (h1 : 2 * (n : ℝ) * 20.7 ≤ c * E₀ * a)
    (h2 : (n : ℝ) ≤ c * E₀ * a ^ 2 / 2) :
    (n : ℝ) * L ^ 2 ≤ c * exp (a * L) := by
  set s := L - 20.7 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hq := Real.quadratic_le_exp_of_nonneg (x := a * s) (by positivity)
  have hexp : E₀ * (1 + a * s + (a * s) ^ 2 / 2) ≤ exp (a * L) := by
    have he : exp (a * L) = exp (a * 20.7) * exp (a * s) := by rw [← Real.exp_add, hs]; ring_nf
    rw [he]
    exact mul_le_mul hE hq (by positivity) (exp_pos _).le
  have hLs : L = 20.7 + s := by rw [hs]; ring
  have hcE : 0 ≤ c * E₀ := by positivity
  calc (n : ℝ) * L ^ 2 = n * 20.7 ^ 2 + 2 * n * 20.7 * s + n * s ^ 2 := by rw [hLs]; ring
    _ ≤ c * E₀ + c * E₀ * a * s + c * E₀ * a ^ 2 / 2 * s ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1 hs0
        have := mul_le_mul_of_nonneg_right h2 (sq_nonneg s)
        linarith
    _ = c * (E₀ * (1 + a * s + (a * s) ^ 2 / 2)) := by ring
    _ ≤ c * exp (a * L) := mul_le_mul_of_nonneg_left hexp hc

/-- `log b ≤ (c/a) · 0.6931471808` from `b^a ≤ 2^c`. -/
lemma log_le_pow2 (b : ℝ) (hb : 0 < b) (a c : ℕ) (ha : 0 < a) (h : b ^ a ≤ 2 ^ c) :
    Real.log b ≤ (c : ℝ) / a * 0.6931471808 := by
  have h' := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  have h2 := Real.log_two_lt_d9
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [div_mul_eq_mul_div, le_div_iff₀ ha']
  nlinarith

/-- A count term: `#T ≤ n` and `n L² ≤ c e^{(1 - θ) L}` give `#T · N^θ · L ≤ (c/20.7) N`. -/
lemma count_term {N : ℕ} (hNpos : (0 : ℝ) < N) {L θ c : ℝ} (hLdef : L = Real.log N)
    (hL : 20.7 ≤ L) (T : Finset ℕ) (n : ℕ) (hT : T.card ≤ n)
    (hc : (n : ℝ) * L ^ 2 ≤ c * exp ((1 - θ) * L)) :
    (T.card : ℝ) * (N : ℝ) ^ θ * L ≤ c / 20.7 * N := by
  have hNθ : (N : ℝ) ^ θ = exp (θ * L) := by rw [Real.rpow_def_of_pos hNpos, hLdef]; ring_nf
  have hN : (N : ℝ) = exp (θ * L) * exp ((1 - θ) * L) := by
    rw [← Real.exp_add, hLdef]; ring_nf; rw [Real.exp_log hNpos]
  have hT' : (T.card : ℝ) ≤ n := by exact_mod_cast hT
  have hLpos : 0 < L := by linarith
  have hE := exp_pos (θ * L)
  have h1 : (T.card : ℝ) * exp (θ * L) * L ^ 2 ≤ c * N := by
    rw [hN]
    have := mul_le_mul_of_nonneg_right hc hE.le
    have h2 : (T.card : ℝ) * L ^ 2 ≤ n * L ^ 2 := mul_le_mul_of_nonneg_right hT' (sq_nonneg L)
    nlinarith
  rw [hNθ, div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
  have h0 : 0 ≤ (T.card : ℝ) * exp (θ * L) * L :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (exp_pos _).le) hLpos.le
  have h3 := mul_le_mul_of_nonneg_left hL h0
  nlinarith [h1, h3]

set_option maxHeartbeats 16000000 in
/-- **The bad-prime budget from `10⁹`.** For `N ≥ 10⁹`, with `Q = 80⌈log N⌉`, the classes of the
odd primes `r ≤ Q` and the tail total at most `0.906 N / log N`. -/
theorem bad_sum_le9 (N : ℕ) (hN : (10 ^ 9 : ℝ) ≤ N) :
    (∑ r ∈ (Icc 3 (80 * ⌈Real.log N⌉₊)).filter Nat.Prime, ((cls N r).card : ℝ)) +
      ∑ n ∈ Ioc (80 * ⌈Real.log N⌉₊) N, ((N / n ^ 2 : ℕ) : ℝ) ≤ 0.906 * N / Real.log N := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  set L := Real.log N with hLdef
  have hL : 20.7 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hNpos]
    refine le_trans ?_ hN
    have h207 : exp 20.7 ^ 10 = exp 207 := by rw [← Real.exp_nat_mul]; norm_num
    have h207' : exp 207 ≤ (2.7182818286 : ℝ) ^ 207 := by
      have := Real.exp_nat_mul 1 207
      rw [mul_one] at this
      rw [show (207 : ℝ) = ((207 : ℕ) : ℝ) by norm_num, this]
      exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 207
    by_contra hc
    push Not at hc
    have : ((10 : ℝ) ^ 9) ^ 10 ≤ exp 20.7 ^ 10 := pow_le_pow_left₀ (by positivity) hc.le 10
    rw [h207] at this
    have := this.trans h207'
    norm_num at this
  have hLpos : 0 < L := by linarith
  have hexpL : exp L = N := Real.exp_log hNpos
  -- `12800 (L + 1)² ≤ N`
  have hNbig : 12800 * (L + 1) ^ 2 ≤ (N : ℝ) := by
    have hq := Real.quadratic_le_exp_of_nonneg (x := L - 20) (by linarith)
    have he : exp L = exp ((20 : ℕ) : ℝ) * exp (L - 20) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have h20 : (4.8e8 : ℝ) ≤ exp ((20 : ℕ) : ℝ) := le_trans (by norm_num) (exp_nat_ge 20)
    rw [← hexpL, he]
    have := mul_le_mul h20 hq (by nlinarith) (exp_pos _).le
    calc 12800 * (L + 1) ^ 2 = 12800 * ((L - 20) ^ 2 + 42 * (L - 20) + 441) := by ring
      _ ≤ 4.8e8 * (1 + (L - 20) + (L - 20) ^ 2 / 2) := by nlinarith [sq_nonneg (L - 20)]
      _ ≤ _ := this
  set Q : ℕ := 80 * ⌈L⌉₊ with hQdef
  have hQr : (Q : ℝ) = 80 * (⌈L⌉₊ : ℝ) := by rw [hQdef]; push_cast; ring
  have hceil1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hceil2 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
  have hQlo : 80 * L ≤ (Q : ℝ) := by rw [hQr]; linarith
  have hQhi : (Q : ℝ) ≤ 80 * (L + 1) := by rw [hQr]; linarith
  have hQ31 : 31 ≤ Q := by
    have : (31 : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  have hQ1 : 1 ≤ Q := by omega
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hsq : ∀ r : ℕ, r ≤ Q → 2 * r ^ 2 ≤ N + 1 := by
    intro r hr
    have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
    have : (2 : ℝ) * (r : ℝ) ^ 2 ≤ N := by
      have h0 : (0 : ℝ) ≤ r := by positivity
      have : (r : ℝ) ^ 2 ≤ (80 * (L + 1)) ^ 2 := pow_le_pow_left₀ h0 (hr'.trans hQhi) 2
      nlinarith
    have : 2 * r ^ 2 ≤ N := by exact_mod_cast this
    omega
  -- the split
  set S := (Icc 3 Q).filter Nat.Prime with hS
  have hmemS : ∀ r ∈ S, r.Prime ∧ r ≤ Q := by
    intro r hr; rw [hS, mem_filter, mem_Icc] at hr; exact ⟨hr.2, hr.1.2⟩
  have hsplit0 := (sum_filter_add_sum_filter_not S (· ≤ 31) (fun r => ((cls N r).card : ℝ))).symm
  rw [small_primes hQ31] at hsplit0
  rw [show (insert 3 {5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) =
      insert 3 (insert 5 (insert 7 ({11, 13} ∪ {17, 19, 23, 29, 31}))) by decide,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_union (by decide)] at hsplit0
  set R := S.filter (fun r => ¬ r ≤ 31) with hR
  set R1 := R.filter (· ≤ 127) with hR1
  set R' := R.filter (fun r => ¬ r ≤ 127) with hR'
  set R2 := R'.filter (· ≤ 511) with hR2
  set R'' := R'.filter (fun r => ¬ r ≤ 511) with hR''
  set R3 := R''.filter (· ≤ 2047) with hR3
  set RQ := R''.filter (fun r => ¬ r ≤ 2047) with hRQ
  have hsR := (sum_filter_add_sum_filter_not R (· ≤ 127) (fun r => ((cls N r).card : ℝ))).symm
  have hsR' := (sum_filter_add_sum_filter_not R' (· ≤ 511) (fun r => ((cls N r).card : ℝ))).symm
  have hsR'' := (sum_filter_add_sum_filter_not R'' (· ≤ 2047)
    (fun r => ((cls N r).card : ℝ))).symm
  have mR : ∀ r ∈ R, r.Prime ∧ r ≤ Q ∧ 31 < r := by
    intro r hr; rw [hR, mem_filter] at hr
    exact ⟨(hmemS r hr.1).1, (hmemS r hr.1).2, by omega⟩
  have mR1 : ∀ r ∈ R1, r.Prime ∧ r ≤ Q ∧ 31 < r ∧ r ≤ 127 := by
    intro r hr; rw [hR1, mem_filter] at hr; exact ⟨(mR r hr.1).1, (mR r hr.1).2.1, (mR r hr.1).2.2, hr.2⟩
  have mR' : ∀ r ∈ R', r.Prime ∧ r ≤ Q ∧ 127 < r := by
    intro r hr; rw [hR', mem_filter] at hr; exact ⟨(mR r hr.1).1, (mR r hr.1).2.1, by omega⟩
  have mR2 : ∀ r ∈ R2, r.Prime ∧ r ≤ Q ∧ 127 < r ∧ r ≤ 511 := by
    intro r hr; rw [hR2, mem_filter] at hr; exact ⟨(mR' r hr.1).1, (mR' r hr.1).2.1, (mR' r hr.1).2.2, hr.2⟩
  have mR'' : ∀ r ∈ R'', r.Prime ∧ r ≤ Q ∧ 511 < r := by
    intro r hr; rw [hR'', mem_filter] at hr; exact ⟨(mR' r hr.1).1, (mR' r hr.1).2.1, by omega⟩
  have mR3 : ∀ r ∈ R3, r.Prime ∧ r ≤ Q ∧ 511 < r ∧ r ≤ 2047 := by
    intro r hr; rw [hR3, mem_filter] at hr; exact ⟨(mR'' r hr.1).1, (mR'' r hr.1).2.1, (mR'' r hr.1).2.2, hr.2⟩
  have mRQ : ∀ r ∈ RQ, r.Prime ∧ r ≤ Q ∧ 2047 < r := by
    intro r hr; rw [hRQ, mem_filter] at hr; exact ⟨(mR'' r hr.1).1, (mR'' r hr.1).2.1, by omega⟩
  -- weights of the large groups
  have wpos : ∀ r : ℕ, 2 ≤ r → (0 : ℝ) ≤ 1 / ((r : ℝ) * ((r : ℝ) - 1)) := by
    intro r hr
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity
  have hw1 : ∑ r ∈ R1, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.004976 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := (Ioc 31 127).filter Nat.Prime) ?_ ?_)
      wsum_31_127
    · intro r hr; have := mR1 r hr; rw [mem_filter, mem_Ioc]; exact ⟨⟨this.2.2.1, this.2.2.2⟩, this.1⟩
    · intro r hr _; rw [mem_filter] at hr; exact wpos r hr.2.two_le
  have hw2 : ∑ r ∈ R2, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.0010544 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := (Ioc 127 511).filter Nat.Prime) ?_ ?_)
      wsum_127_511
    · intro r hr; have := mR2 r hr; rw [mem_filter, mem_Ioc]; exact ⟨⟨this.2.2.1, this.2.2.2⟩, this.1⟩
    · intro r hr _; rw [mem_filter] at hr; exact wpos r hr.2.two_le
  have hw3 : ∑ r ∈ R3, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.00020883 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := (Ioc 511 2047).filter Nat.Prime) ?_ ?_)
      wsum_511_2047
    · intro r hr; have := mR3 r hr; rw [mem_filter, mem_Ioc]; exact ⟨⟨this.2.2.1, this.2.2.2⟩, this.1⟩
    · intro r hr _; rw [mem_filter] at hr; exact wpos r hr.2.two_le
  have hwQ : ∑ r ∈ RQ, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 1 / 2047 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := Ioc 2047 Q) ?_ ?_) ?_
    · intro r hr; have := mRQ r hr; rw [mem_Ioc]; exact ⟨this.2.2, this.2.1⟩
    · intro r hr _; rw [mem_Ioc] at hr; exact wpos r (by omega)
    · have := sum_Ioc_inv_mul_pred_le (a := 2047) (by norm_num) Q
      push_cast at this; exact this
  -- cards
  have hc1 : R1.card ≤ 96 := by
    calc R1.card ≤ (Ioc 31 127).card := card_le_card (fun r hr => by
          have := mR1 r hr; rw [mem_Ioc]; exact ⟨this.2.2.1, this.2.2.2⟩)
      _ = 96 := by simp
  have hc2 : R2.card ≤ 384 := by
    calc R2.card ≤ (Ioc 127 511).card := card_le_card (fun r hr => by
          have := mR2 r hr; rw [mem_Ioc]; exact ⟨this.2.2.1, this.2.2.2⟩)
      _ = 384 := by simp
  have hc3 : R3.card ≤ 1536 := by
    calc R3.card ≤ (Ioc 511 2047).card := card_le_card (fun r hr => by
          have := mR3 r hr; rw [mem_Ioc]; exact ⟨this.2.2.1, this.2.2.2⟩)
      _ = 1536 := by simp
  have hcQ : RQ.card ≤ Q := by
    calc RQ.card ≤ (Ioc 0 Q).card := card_le_card (fun r hr => by
          have := mRQ r hr; rw [mem_Ioc]; exact ⟨by omega, this.2.1⟩)
      _ = Q := by simp
  have hl2 := Real.log_two_lt_d9
  -- group 3
  have lb3 : Real.log 3 ≤ 1.0989 := by
    have := log_le_pow2 3 (by norm_num) 41 65 (by norm_num) (by norm_num)
    linarith [show (65 : ℝ) / 41 * 0.6931471808 ≤ 1.0989 by norm_num]
  have G3 := group_le hN1 hL ({3} : Finset ℕ) (b := 3) (lb := 1.0989) (θ := 2/5) (F := 1.0512)
    (k := 1.1188) (w := 1/6) (by intro r hr; simp only [mem_singleton] at hr; subst hr; exact ⟨by norm_num, hsq _ (by omega), by norm_num⟩)
    (by push_cast; exact lb3) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 18 (x := lam) (y₀ := (20.7 - 2 * 1.0989)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (2/5 : ℝ)) * lam)
        (y₀ := (1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.0989)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 18 * (1 + ((20.7 - 2 * 1.0989) - (18 : ℕ)) +
          ((20.7 - 2 * 1.0989) - (18 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.0989) - (3 : ℕ)) +
          ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.0989) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0512 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_insert, Finset.sum_singleton])
  have C3 := count_term hNpos hLdef hL ({3} : Finset ℕ) 1 (by decide)
    (cnt_le' 1 (a := 1 - 2/5) (c := 0.001780531) (E₀ := 245466) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 2/5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 5
  have lb5 : Real.log 5 ≤ 1.612 := by
    have := log_le_pow2 5 (by norm_num) 43 100 (by norm_num) (by norm_num)
    linarith [show (100 : ℝ) / 43 * 0.6931471808 ≤ 1.612 by norm_num]
  have G5 := group_le hN1 hL ({5} : Finset ℕ) (b := 5) (lb := 1.612) (θ := 2/5) (F := 1.0616)
    (k := 1.1845) (w := 1/20) (by intro r hr; simp only [mem_singleton] at hr; subst hr; exact ⟨by norm_num, hsq _ (by omega), by norm_num⟩)
    (by push_cast; exact lb5) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 17 (x := lam) (y₀ := (20.7 - 2 * 1.612)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (2/5 : ℝ)) * lam)
        (y₀ := (1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.612)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 17 * (1 + ((20.7 - 2 * 1.612) - (17 : ℕ)) +
          ((20.7 - 2 * 1.612) - (17 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.612) - (3 : ℕ)) +
          ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.612) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0616 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_insert, Finset.sum_singleton])
  have C5 := count_term hNpos hLdef hL ({5} : Finset ℕ) 1 (by decide)
    (cnt_le' 1 (a := 1 - 2/5) (c := 0.001780531) (E₀ := 245466) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 2/5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 7
  have lb7 : Real.log 7 ≤ 1.964 := by
    have := log_le_pow2 7 (by norm_num) 12 34 (by norm_num) (by norm_num)
    linarith [show (34 : ℝ) / 12 * 0.6931471808 ≤ 1.964 by norm_num]
  have G7 := group_le hN1 hL ({7} : Finset ℕ) (b := 7) (lb := 1.964) (θ := 2/5) (F := 1.0703)
    (k := 1.2342) (w := 1/42) (by intro r hr; simp only [mem_singleton] at hr; subst hr; exact ⟨by norm_num, hsq _ (by omega), by norm_num⟩)
    (by push_cast; exact lb7) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 16 (x := lam) (y₀ := (20.7 - 2 * 1.964)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (2/5 : ℝ)) * lam)
        (y₀ := (1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.964)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 16 * (1 + ((20.7 - 2 * 1.964) - (16 : ℕ)) +
          ((20.7 - 2 * 1.964) - (16 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.964) - (3 : ℕ)) +
          ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 1.964) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0703 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_insert, Finset.sum_singleton])
  have C7 := count_term hNpos hLdef hL ({7} : Finset ℕ) 1 (by decide)
    (cnt_le' 1 (a := 1 - 2/5) (c := 0.001780531) (E₀ := 245466) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 2/5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 13
  have lb13 : Real.log 13 ≤ 2.6 := by
    have := log_le_pow2 13 (by norm_num) 4 15 (by norm_num) (by norm_num)
    linarith [show (15 : ℝ) / 4 * 0.6931471808 ≤ 2.6 by norm_num]
  have G13 := group_le hN1 hL ({11, 13} : Finset ℕ) (b := 13) (lb := 2.6) (θ := 2/5) (F := 1.0902)
    (k := 1.3355) (w := 0.015502) (by intro r hr; simp only [mem_insert, mem_singleton] at hr; rcases hr with h | h <;> subst h <;> exact ⟨by norm_num, hsq _ (by omega), by norm_num⟩)
    (by push_cast; exact lb13) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 15 (x := lam) (y₀ := (20.7 - 2 * 2.6)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (2/5 : ℝ)) * lam)
        (y₀ := (1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 2.6)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 15 * (1 + ((20.7 - 2 * 2.6) - (15 : ℕ)) +
          ((20.7 - 2 * 2.6) - (15 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 2.6) - (3 : ℕ)) +
          ((1 - 2 * (2/5 : ℝ)) * (20.7 - 2 * 2.6) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0902 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by rw [Finset.sum_pair (by norm_num)]; norm_num)
  have C13 := count_term hNpos hLdef hL ({11, 13} : Finset ℕ) 2 (by decide)
    (cnt_le' 2 (a := 1 - 2/5) (c := 0.003561062) (E₀ := 245466) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 2/5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 31
  have lb31 : Real.log 32 ≤ 3.4658 := by
    have := log_le_pow2 32 (by norm_num) 1 5 (by norm_num) (by norm_num)
    linarith [show (5 : ℝ) / 1 * 0.6931471808 ≤ 3.4658 by norm_num]
  have G31 := group_le hN1 hL ({17, 19, 23, 29, 31} : Finset ℕ) (b := 32) (lb := 3.4658) (θ := 19/50) (F := 1.0738)
    (k := 1.5035) (w := 0.010884) (by intro r hr; simp only [mem_insert, mem_singleton] at hr; rcases hr with h | h | h | h | h <;> subst h <;> exact ⟨by norm_num, hsq _ (by omega), by norm_num⟩)
    (by push_cast; exact lb31) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 13 (x := lam) (y₀ := (20.7 - 2 * 3.4658)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (19/50 : ℝ)) * lam)
        (y₀ := (1 - 2 * (19/50 : ℝ)) * (20.7 - 2 * 3.4658)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 13 * (1 + ((20.7 - 2 * 3.4658) - (13 : ℕ)) +
          ((20.7 - 2 * 3.4658) - (13 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (19/50 : ℝ)) * (20.7 - 2 * 3.4658) - (3 : ℕ)) +
          ((1 - 2 * (19/50 : ℝ)) * (20.7 - 2 * 3.4658) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0738 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_insert, Finset.sum_singleton])
  have C31 := count_term hNpos hLdef hL ({17, 19, 23, 29, 31} : Finset ℕ) 5 (by decide)
    (cnt_le' 5 (a := 1 - 19/50) (c := 0.006154143) (E₀ := 355094) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 19/50) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 127
  have lb127 : Real.log 128 ≤ 4.8521 := by
    have := log_le_pow2 128 (by norm_num) 1 7 (by norm_num) (by norm_num)
    linarith [show (7 : ℝ) / 1 * 0.6931471808 ≤ 4.8521 by norm_num]
  have G127 := group_le hN1 hL R1 (b := 128) (lb := 4.8521) (θ := 17/50) (F := 1.0603)
    (k := 1.8826) (w := 0.004976) (fun r hr => ⟨(mR1 r hr).1, hsq r (mR1 r hr).2.1, by have := (mR1 r hr).2.2.2; exact_mod_cast (by omega : r ≤ 128)⟩)
    (by push_cast; exact lb127) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 10 (x := lam) (y₀ := (20.7 - 2 * 4.8521)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (17/50 : ℝ)) * lam)
        (y₀ := (1 - 2 * (17/50 : ℝ)) * (20.7 - 2 * 4.8521)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 10 * (1 + ((20.7 - 2 * 4.8521) - (10 : ℕ)) +
          ((20.7 - 2 * 4.8521) - (10 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (17/50 : ℝ)) * (20.7 - 2 * 4.8521) - (3 : ℕ)) +
          ((1 - 2 * (17/50 : ℝ)) * (20.7 - 2 * 4.8521) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0603 := by norm_num
      linarith)
    (by norm_num) (by norm_num) hw1
  have C127 := count_term hNpos hLdef hL R1 96 hc1
    (cnt_le' 96 (a := 1 - 17/50) (c := 0.050415859) (E₀ := 832233) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 13 (y := (1 - 17/50) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 511
  have lb511 : Real.log 512 ≤ 6.2384 := by
    have := log_le_pow2 512 (by norm_num) 1 9 (by norm_num) (by norm_num)
    linarith [show (9 : ℝ) / 1 * 0.6931471808 ≤ 6.2384 by norm_num]
  have G511 := group_le hN1 hL R2 (b := 512) (lb := 6.2384) (θ := 13/50) (F := 1.0422)
    (k := 2.5173) (w := 0.0010544) (fun r hr => ⟨(mR2 r hr).1, hsq r (mR2 r hr).2.1, by have := (mR2 r hr).2.2.2; exact_mod_cast (by omega : r ≤ 512)⟩)
    (by push_cast; exact lb511) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 8 (x := lam) (y₀ := (20.7 - 2 * 6.2384)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (13/50 : ℝ)) * lam)
        (y₀ := (1 - 2 * (13/50 : ℝ)) * (20.7 - 2 * 6.2384)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 8 * (1 + ((20.7 - 2 * 6.2384) - (8 : ℕ)) +
          ((20.7 - 2 * 6.2384) - (8 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (13/50 : ℝ)) * (20.7 - 2 * 6.2384) - (3 : ℕ)) +
          ((1 - 2 * (13/50 : ℝ)) * (20.7 - 2 * 6.2384) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0422 := by norm_num
      linarith)
    (by norm_num) (by norm_num) hw2
  have C511 := count_term hNpos hLdef hL R2 384 hc2
    (cnt_le' 384 (a := 1 - 13/50) (c := 0.03751375) (E₀ := 4473852) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 15 (y := (1 - 13/50) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 2047
  have lb2047 : Real.log 2048 ≤ 7.6247 := by
    have := log_le_pow2 2048 (by norm_num) 1 11 (by norm_num) (by norm_num)
    linarith [show (11 : ℝ) / 1 * 0.6931471808 ≤ 7.6247 by norm_num]
  have G2047 := group_le hN1 hL R3 (b := 2048) (lb := 7.6247) (θ := 1/5) (F := 1.0849)
    (k := 3.7978) (w := 0.00020883) (fun r hr => ⟨(mR3 r hr).1, hsq r (mR3 r hr).2.1, by have := (mR3 r hr).2.2.2; exact_mod_cast (by omega : r ≤ 2048)⟩)
    (by push_cast; exact lb2047) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 5 (x := lam) (y₀ := (20.7 - 2 * 7.6247)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (1/5 : ℝ)) * lam)
        (y₀ := (1 - 2 * (1/5 : ℝ)) * (20.7 - 2 * 7.6247)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 5 * (1 + ((20.7 - 2 * 7.6247) - (5 : ℕ)) +
          ((20.7 - 2 * 7.6247) - (5 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (1/5 : ℝ)) * (20.7 - 2 * 7.6247) - (3 : ℕ)) +
          ((1 - 2 * (1/5 : ℝ)) * (20.7 - 2 * 7.6247) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0849 := by norm_num
      linarith)
    (by norm_num) (by norm_num) hw3
  have C2047 := count_term hNpos hLdef hL R3 1536 hc3
    (cnt_le' 1536 (a := 1 - 1/5) (c := 0.044004864) (E₀ := 15255674) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 16 (y := (1 - 1/5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group Q
  have hlogQ : Real.log Q ≤ 5 / 128 * (L + 1) + 6.62465 := by
    have h1 := Real.log_le_sub_one_of_pos (x := (Q : ℝ) / 2048) (by positivity)
    rw [Real.log_div hQ0.ne' (by norm_num)] at h1
    have h2048 : Real.log 2048 = 11 * Real.log 2 := by
      rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; push_cast; ring
    have : (Q : ℝ) / 2048 ≤ 80 * (L + 1) / 2048 := by linarith
    linarith
  set lbQ : ℝ := 5 / 128 * (L + 1) + 6.62465 with hlbQ
  set lamQ : ℝ := L - 2 * lbQ with hlamQ
  have hlamQ0 : 20.7 - 5 / 64 * 21.7 - 13.2493 ≤ lamQ := by rw [hlamQ, hlbQ]; linarith
  have hpQ : 0 < lamQ := lt_of_lt_of_le (by norm_num) hlamQ0
  have hRQb : ∀ r ∈ RQ, r.Prime ∧ 2 * r ^ 2 ≤ N + 1 ∧ (r : ℝ) ≤ Q :=
    fun r hr => ⟨(mRQ r hr).1, hsq r (mRQ r hr).2.1, by exact_mod_cast (mRQ r hr).2.1⟩
  have hperQ : ∀ r ∈ RQ, ((cls N r).card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 5) +
      1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ * ((1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1))) := by
    intro r hr
    obtain ⟨hp, h2, hrb⟩ := hRQb r hr
    have hlog := log_cls_ge (N := N) hN1 hp.one_lt.le hrb
    have hc := cls_card_pow_gen hp h2 hN1 (θ := 1 / 5) (by norm_num) (by norm_num) hpQ
      (by rw [hlamQ]; linarith)
    have hF : 1 + 2 * exp (-lamQ) + 2 * exp (-((1 - 2 * (1 / 5 : ℝ)) * lamQ)) ≤ 1.0706 := by
      have e1 := exp_neg_le2 5 (x := lamQ) (y₀ := 20.7 - 5 / 64 * 21.7 - 13.2493) (by norm_num) hlamQ0
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (1 / 5 : ℝ)) * lamQ)
        (y₀ := (1 - 2 * (1 / 5 : ℝ)) * (20.7 - 5 / 64 * 21.7 - 13.2493)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 5 * (1 + ((20.7 - 5 / 64 * 21.7 - 13.2493) - (5 : ℕ)) +
          ((20.7 - 5 / 64 * 21.7 - 13.2493) - (5 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (1 / 5 : ℝ)) * (20.7 - 5 / 64 * 21.7 - 13.2493) - (3 : ℕ)) +
          ((1 - 2 * (1 / 5 : ℝ)) * (20.7 - 5 / 64 * 21.7 - 13.2493) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0706 := by norm_num
      linarith
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hp.two_le
    have hrr : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    calc ((cls N r).card : ℝ) ≤ _ := hc
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 /
            (lamQ * ((r : ℝ) * ((r : ℝ) - 1))) := by gcongr
      _ = _ := by field_simp
  have GQ : ∑ r ∈ RQ, ((cls N r).card : ℝ) ≤ RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) +
      1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047) * 3.5967 / L := by
    calc ∑ r ∈ RQ, ((cls N r).card : ℝ) ≤ ∑ r ∈ RQ, ((N : ℝ) ^ ((1 : ℝ) / 5) +
          1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ * ((1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)))) :=
          sum_le_sum hperQ
      _ = RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ *
            ∑ r ∈ RQ, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
      _ ≤ RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ *
            (1 / 2047) := by gcongr
      _ ≤ _ := by
          have hkl : L ≤ 3.5967 * lamQ := by rw [hlamQ, hlbQ]; linarith
          have : 1 / lamQ ≤ 3.5967 / L := by rw [div_le_div_iff₀ hpQ hLpos]; linarith
          have hA : 0 ≤ 1 / (1 / 5 : ℝ) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047) := by positivity
          calc RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ * (1 / 2047)
              = RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) +
                  (1 / (1 / 5 : ℝ) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047)) * (1 / lamQ) := by ring
            _ ≤ RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) +
                  (1 / (1 / 5 : ℝ) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047)) * (3.5967 / L) := by gcongr
            _ = _ := by ring
  have CQ : (RQ.card : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 5) * L ≤ 0.002406516 * N := by
    have hcard : (RQ.card : ℝ) * L ≤ 84 * L ^ 2 := by
      have h1 : (RQ.card : ℝ) ≤ Q := by exact_mod_cast hcQ
      have h2 : (RQ.card : ℝ) ≤ 84 * L := by linarith
      nlinarith
    have hc := cnt_le' 84 (a := 1 - 1 / 5) (c := 0.002406516) (E₀ := 15255674) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 16 (y := (1 - 1 / 5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    push_cast at hc
    have hNθ : (N : ℝ) ^ ((1 : ℝ) / 5) = exp (L * (1 / 5)) := by
      rw [Real.rpow_def_of_pos hNpos]
    have hE := exp_pos (L * (1 / 5))
    rw [hNθ]
    calc (RQ.card : ℝ) * exp (L * (1 / 5)) * L = ((RQ.card : ℝ) * L) * exp (L * (1 / 5)) := by ring
      _ ≤ (84 * L ^ 2) * exp (L * (1 / 5)) := mul_le_mul_of_nonneg_right hcard hE.le
      _ ≤ 0.002406516 * exp ((1 - 1 / 5) * L) * exp (L * (1 / 5)) :=
          mul_le_mul_of_nonneg_right hc hE.le
      _ = 0.002406516 * N := by
          rw [mul_assoc, ← Real.exp_add, show (1 - 1 / 5) * L + L * (1 / 5) = L by ring, hexpL]
  -- assemble
  have htail := tail_le (N := N) hQ1
  have hNQ : (N : ℝ) / Q * L ≤ N / 80 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hQ0 (by norm_num)]
    have := mul_le_mul_of_nonneg_left hQlo hNpos.le
    linarith
  have htailL := mul_le_mul_of_nonneg_right htail hLpos.le
  rw [sum_singleton, card_singleton] at G3
  rw [card_singleton] at C3
  have G3' := mul_le_mul_of_nonneg_right G3 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G3'
  rw [sum_singleton, card_singleton] at G5
  rw [card_singleton] at C5
  have G5' := mul_le_mul_of_nonneg_right G5 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G5'
  rw [sum_singleton, card_singleton] at G7
  rw [card_singleton] at C7
  have G7' := mul_le_mul_of_nonneg_right G7 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G7'
  have G13' := mul_le_mul_of_nonneg_right G13 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G13'
  have G31' := mul_le_mul_of_nonneg_right G31 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G31'
  have G127' := mul_le_mul_of_nonneg_right G127 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G127'
  have G511' := mul_le_mul_of_nonneg_right G511 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G511'
  have G2047' := mul_le_mul_of_nonneg_right G2047 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G2047'
  have GQ' := mul_le_mul_of_nonneg_right GQ hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at GQ'
  rw [le_div_iff₀ hLpos, hsplit0, hsR, hsR', hsR'']
  simp only [add_mul]
  push_cast at C3 C5 C7 C13 C31 C127 C511 C2047
  linarith

/-- **Dudek's theorem for even `N ≥ 10⁹`, PROVED, no cited input.** -/
theorem dudek_even_from_1e9 (N : ℕ) (hE : Even N) (hN : (10 ^ 9 : ℝ) ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  by_contra hno
  have hb := bad_sum_le9 N hN
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hLle : L ≤ N / 1000000 + 14 := by
    have h1 := Real.log_le_sub_one_of_pos (x := (N : ℝ) / 1000000) (by positivity)
    rw [Real.log_div hNpos.ne' (by norm_num)] at h1
    have : Real.log 1000000 ≤ 20 * Real.log 2 := by
      have h := Real.log_le_log (x := 1000000) (y := (2 : ℝ) ^ 20) (by norm_num) (by norm_num)
      rw [Real.log_pow] at h; push_cast at h; exact h
    linarith [Real.log_two_lt_d9]
  have h30 : 30 ≤ N := by
    have : (30 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hcount := card_le_of_no_rep (80 * ⌈L⌉₊) hE (by omega) hno
  have hpi := LeanLab.ChebyshevExplicit.pi_ge_chebyshev30 N h30
  rw [div_le_iff₀ hLpos, ← hLdef] at hpi
  have h1 := hcount.trans hb
  rw [le_div_iff₀ hLpos] at h1
  nlinarith

end LeanLab.AlmostPrimes.DudekFrom1e9

