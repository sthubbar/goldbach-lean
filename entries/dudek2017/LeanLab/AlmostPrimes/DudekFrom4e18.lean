module

public import LeanLab.AlmostPrimes.DudekLarge
public import LeanLab.PNTPort.LargeSieve.MontgomeryAPCor
public import LeanLab.ChebyshevExplicit.Psi30

/-!
# Dudek's prime plus square-free theorem from `e^42`, below the `4·10¹⁸` Goldbach check

Unit U-5651, CLOUD 20261019T1515Z-cloud27, idea I-5065. AI wrote the Lean code. Known mathematics,
Dudek 2017, BJS Theorem 53.

`dudek_even_from_exp42`: every even `N ≥ e^42 ≈ 1.74·10¹⁸` is `p + m`, `p` prime, `m ≥ 1`
square-free. No cited input.

Same counting as the lab's `DudekLarge.dudek_even_large`, which needed `N ≥ e^12000`, with two
inputs changed:
* the class `N mod r²` is bounded by `brun_titchmarsh_ap_pow` at `θ = 9/20`, which has no
  logarithmic error factor, in place of `brunTitchmarsh_ap`;
* `π(N)` is bounded below by Chebyshev's `0.9212 N / log N`, `ChebyshevExplicit.pi_ge_chebyshev30`,
  in place of Mathlib's `log 2 · N / log N`.
The primes `r ≤ Q = 40⌈log N⌉` are split into `r = 3`, `5 ≤ r ≤ 31` and `31 < r ≤ Q`, each with its
own lower bound for `log((N + 1)/r²)`. With `L = log N ≥ 42` the bad primes number at most
`0.858 N/L`, below `π(N) - 1 ≥ 0.9212 N/L - 6`.
-/

@[expose] public section


open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.DudekFrom4e18

open LeanLab.AlmostPrimes.DudekLarge

/-- The class set in the form `brun_titchmarsh_ap_pow` counts. -/
lemma cls_eq (N r : ℕ) :
    cls N r = (Ioc 0 (0 + (N + 1))).filter (fun p => p.Prime ∧ p % r ^ 2 = N % r ^ 2) := by
  ext p
  simp only [cls, mem_filter, mem_Icc, mem_Ioc, zero_add]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩

/-- **One class, power level.** For a prime `r ≥ 3` with `2r² ≤ N + 1` and any `0 < λ` below
`log((N + 1)/r²)`, the primes `p ≤ N + 1` with `p ≡ N mod r²` number at most
`N^{9/20} + (20/9)(N + 1)(1 + 2e^{-λ} + 2e^{-λ/10}) / (λ r(r - 1))`. -/
theorem cls_card_pow {N r : ℕ} (hr : r.Prime) (h2 : 2 * r ^ 2 ≤ N + 1) (hN : 1 ≤ N)
    {lam : ℝ} (hlam : 0 < lam) (hlt : lam ≤ Real.log (((N + 1 : ℕ) : ℝ) / ((r ^ 2 : ℕ) : ℝ))) :
    ((cls N r).card : ℝ) ≤ (N : ℝ) ^ ((9 : ℝ) / 20) +
      20 / 9 * ((N : ℝ) + 1) * (1 + 2 * exp (-lam) + 2 * exp (-lam / 10)) /
        (lam * ((r : ℝ) * ((r : ℝ) - 1))) := by
  have hr2 : 2 ≤ r := hr.two_le
  have hk : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hbt := LeanLab.PNTPort.LargeSieve.brun_titchmarsh_ap_pow 0 (N + 1) (r ^ 2) N hk h2
    (θ := 9 / 20) (by norm_num)
  rw [← cls_eq] at hbt
  set t : ℝ := (((N + 1 : ℕ) : ℝ)) / ((r ^ 2 : ℕ) : ℝ) with ht
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hk0 : (0 : ℝ) < ((r ^ 2 : ℕ) : ℝ) := by positivity
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hk0]; exact_mod_cast h2
  have ht0 : 0 < t := by linarith
  have hlogt : lam ≤ Real.log t := hlt
  have hlogt0 : 0 < Real.log t := lt_of_lt_of_le hlam hlogt
  -- `t ≤ N`, so `t^θ ≤ N^θ`
  have htN : t ≤ N := by
    rw [ht, div_le_iff₀ hk0]
    have : 4 ≤ r ^ 2 := by nlinarith
    have : (4 : ℝ) ≤ ((r ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Nat.cast_add, Nat.cast_one]; nlinarith
  have hpow1 : t ^ ((9 : ℝ) / 20) ≤ (N : ℝ) ^ ((9 : ℝ) / 20) :=
    Real.rpow_le_rpow ht0.le htN (by norm_num)
  -- `t^{9/10} = t · t^{-1/10}` and `t^{-1/10} ≤ e^{-λ/10}`, `1/t ≤ e^{-λ}`
  have hsplit : t ^ (2 * ((9 : ℝ) / 20)) = t * t ^ (-(1 : ℝ) / 10) := by
    rw [show 2 * ((9 : ℝ) / 20) = 1 + (-(1 : ℝ) / 10) by norm_num, Real.rpow_add ht0,
      Real.rpow_one]
  have hneg : t ^ (-(1 : ℝ) / 10) ≤ exp (-lam / 10) := by
    rw [Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr; nlinarith
  have hinv : 1 / t ≤ exp (-lam) := by
    have : exp lam ≤ t := by
      calc exp lam ≤ exp (Real.log t) := Real.exp_le_exp.mpr hlogt
        _ = t := Real.exp_log ht0
    rw [Real.exp_neg, div_le_iff₀ ht0, inv_mul_eq_div, le_div_iff₀ (exp_pos _)]; linarith
  -- totient
  have htot : (((r ^ 2).totient : ℕ) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hr two_pos]
    rw [Nat.cast_mul, Nat.cast_sub hr.one_lt.le]; simp
  rw [htot] at hbt
  have hkr : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by push_cast; ring
  have hrr : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
  -- `k (t + 2 + 2 t^{9/10}) = (N + 1)(1 + 2/t + 2 t^{-1/10})`
  have hkt : ((r ^ 2 : ℕ) : ℝ) * t = (N : ℝ) + 1 := by
    rw [ht, mul_div_cancel₀ _ hk0.ne']; push_cast; ring
  have hmain : ((r ^ 2 : ℕ) : ℝ) * (t + 2 + 2 * t ^ (2 * ((9 : ℝ) / 20))) =
      ((N : ℝ) + 1) * (1 + 2 * (1 / t) + 2 * t ^ (-(1 : ℝ) / 10)) := by
    rw [hsplit, ← hkt]; field_simp
  have hfac : 1 + 2 * (1 / t) + 2 * t ^ (-(1 : ℝ) / 10) ≤
      1 + 2 * exp (-lam) + 2 * exp (-lam / 10) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc ((cls N r).card : ℝ) ≤ t ^ ((9 : ℝ) / 20) + ((r ^ 2 : ℕ) : ℝ) *
        (t + 2 + 2 * t ^ (2 * ((9 : ℝ) / 20))) /
          ((9 / 20) * ((r : ℝ) * ((r : ℝ) - 1) * Real.log t)) := by
        convert hbt using 2
    _ = t ^ ((9 : ℝ) / 20) + 20 / 9 * ((N : ℝ) + 1) * (1 + 2 * (1 / t) +
          2 * t ^ (-(1 : ℝ) / 10)) / (Real.log t * ((r : ℝ) * ((r : ℝ) - 1))) := by
        rw [hmain]; field_simp
    _ ≤ (N : ℝ) ^ ((9 : ℝ) / 20) + 20 / 9 * ((N : ℝ) + 1) *
          (1 + 2 * exp (-lam) + 2 * exp (-lam / 10)) / (lam * ((r : ℝ) * ((r : ℝ) - 1))) := by
        gcongr

/-- `e^n ≥ 2.7182818283^n`. -/
lemma exp_nat_ge (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ exp n := by
  have h := Real.exp_nat_mul 1 n
  rw [mul_one] at h
  rw [h]; exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n

/-- `e^{-x} ≤ 1/(2.7182818283^n (1 + (x - n)))` for `x ≥ n`. -/
lemma exp_neg_le (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    exp (-x) ≤ 1 / ((2.7182818283 : ℝ) ^ n * (1 + (x - n))) := by
  have h1 : (2.7182818283 : ℝ) ^ n * (1 + (x - n)) ≤ exp x := by
    have he : exp x = exp n * exp (x - n) := by rw [← Real.exp_add]; ring_nf
    rw [he]
    apply mul_le_mul (exp_nat_ge n) _ (by linarith) (exp_pos _).le
    linarith [Real.add_one_le_exp (x - n)]
  have h0 : 0 < (2.7182818283 : ℝ) ^ n * (1 + (x - n)) := by
    apply mul_pos (by positivity); linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le h0 h1

/-- The factor `1 + 2e^{-λ} + 2e^{-λ/10}` for `λ/10 ≥ a ≥ n` and `λ ≥ 20`. -/
lemma F_le {lam a : ℝ} (n : ℕ) (hn : (n : ℝ) ≤ a) (ha : a ≤ lam / 10) (h20 : 20 ≤ lam) :
    1 + 2 * exp (-lam) + 2 * exp (-lam / 10) ≤
      1 + 2 / (2.7182818283 : ℝ) ^ 20 + 2 / ((2.7182818283 : ℝ) ^ n * (1 + (a - n))) := by
  have h1 := exp_neg_le 20 (x := lam) (by push_cast; linarith)
  have h2 := exp_neg_le n (x := lam / 10) (by linarith)
  have hp20 : (0 : ℝ) < (2.7182818283 : ℝ) ^ 20 := by positivity
  have hpn : (0 : ℝ) < (2.7182818283 : ℝ) ^ n := by positivity
  have h1' : 1 / ((2.7182818283 : ℝ) ^ 20 * (1 + (lam - ((20 : ℕ) : ℝ)))) ≤
      1 / (2.7182818283 : ℝ) ^ 20 := by
    apply one_div_le_one_div_of_le hp20
    push_cast
    nlinarith
  have h2' : 1 / ((2.7182818283 : ℝ) ^ n * (1 + (lam / 10 - n))) ≤
      1 / ((2.7182818283 : ℝ) ^ n * (1 + (a - n))) := by
    apply one_div_le_one_div_of_le (mul_pos hpn (by linarith))
    apply mul_le_mul_of_nonneg_left _ hpn.le; linarith
  have e : -lam / 10 = -(lam / 10) := by ring
  rw [e]
  have := h1.trans h1'
  have := h2.trans h2'
  rw [div_eq_mul_one_div 2 ((2.7182818283 : ℝ) ^ 20),
    div_eq_mul_one_div 2 ((2.7182818283 : ℝ) ^ n * (1 + (a - n)))]
  linarith

/-- `5000 L (L + 1) ≤ e^{0.55 L}` for `L ≥ 42`. -/
lemma poly_le_exp42 {L : ℝ} (hL : 42 ≤ L) : 5000 * L * (L + 1) ≤ exp (0.55 * L) := by
  set s := 0.55 * L - 23 with hs
  have hs0 : 0.1 ≤ s := by rw [hs]; linarith
  have he : exp (0.55 * L) = exp ((23 : ℕ) : ℝ) * exp s := by
    rw [← Real.exp_add]; congr 1; rw [hs]; push_cast; ring
  have h23 : (9e9 : ℝ) ≤ exp ((23 : ℕ) : ℝ) := le_trans (by norm_num) (exp_nat_ge 23)
  have hq := Real.quadratic_le_exp_of_nonneg (x := s) (by linarith)
  have hLs : L = (s + 23) / 0.55 := by rw [hs]; ring
  rw [he]
  have : 9e9 * (1 + s + s ^ 2 / 2) ≤ exp ((23 : ℕ) : ℝ) * exp s :=
    mul_le_mul h23 hq (by positivity) (exp_pos _).le
  rw [hLs]
  nlinarith

/-- `log 3 ≤ 1.109036`, from `3⁵ ≤ 2⁸`. -/
lemma log3_le : Real.log 3 ≤ 1.109036 := by
  have h : Real.log ((3 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 8) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  have := Real.log_two_lt_d9
  push_cast at h
  linarith

/-- `log((N + 1)/r²) ≥ log N - 2 log R` for `1 ≤ r ≤ R`. -/
lemma log_cls_ge {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) {R : ℝ} (hrR : (r : ℝ) ≤ R) :
    Real.log N - 2 * Real.log R ≤ Real.log (((N + 1 : ℕ) : ℝ) / ((r ^ 2 : ℕ) : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Real.log_div (by positivity) (by positivity)]
  have h1 : Real.log N ≤ Real.log (((N + 1 : ℕ) : ℝ)) :=
    Real.log_le_log hN0 (by push_cast; linarith)
  have h2 : Real.log (((r ^ 2 : ℕ) : ℝ)) = 2 * Real.log r := by
    push_cast; rw [Real.log_pow]; push_cast; ring
  have h3 : Real.log r ≤ Real.log R := Real.log_le_log hr0 hrR
  linarith

/-- `Σ_{5 ≤ r ≤ 31, r prime} 1/(r(r - 1)) ≤ 0.1002`. -/
lemma sumB_le : ∑ r ∈ ({5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ),
    (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.1002 := by
  simp; norm_num

/-- The ten primes `3 ≤ r ≤ 31`, once `Q ≥ 31`. -/
lemma small_primes {Q : ℕ} (hQ : 31 ≤ Q) :
    ((Icc 3 Q).filter Nat.Prime).filter (· ≤ 31) = insert 3 {5, 7, 11, 13, 17, 19, 23, 29, 31} := by
  have : ((Icc 3 Q).filter Nat.Prime).filter (· ≤ 31) = (Icc 3 31).filter Nat.Prime := by
    ext r; simp only [mem_filter, mem_Icc]; constructor
    · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨⟨h1, by omega⟩, h2⟩, h3⟩
  rw [this]; decide

/-- The class bound summed over a set `T` of primes `r ≥ 3` sharing one `λ`. -/
lemma sum_cls_le {N : ℕ} (hN : 1 ≤ N) (T : Finset ℕ) (hT : ∀ r ∈ T, r.Prime ∧ 2 * r ^ 2 ≤ N + 1)
    {lam F : ℝ} (hlam : 0 < lam)
    (hlt : ∀ r ∈ T, lam ≤ Real.log (((N + 1 : ℕ) : ℝ) / ((r ^ 2 : ℕ) : ℝ)))
    (hF : 1 + 2 * exp (-lam) + 2 * exp (-lam / 10) ≤ F) :
    ∑ r ∈ T, ((cls N r).card : ℝ) ≤ T.card * (N : ℝ) ^ ((9 : ℝ) / 20) +
      20 / 9 * ((N : ℝ) + 1) * F / lam * ∑ r ∈ T, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
  rw [mul_sum, ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
  apply sum_le_sum
  intro r hr
  obtain ⟨hp, h2⟩ := hT r hr
  have hc := cls_card_pow hp h2 hN hlam (hlt r hr)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hp.two_le
  have hrr : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hFF : 1 + 2 * exp (-lam) + 2 * exp (-lam / 10) ≤ F := hF
  calc ((cls N r).card : ℝ) ≤ _ := hc
    _ ≤ (N : ℝ) ^ ((9 : ℝ) / 20) + 20 / 9 * ((N : ℝ) + 1) * F /
          (lam * ((r : ℝ) * ((r : ℝ) - 1))) := by gcongr
    _ = _ := by field_simp

set_option maxHeartbeats 1000000 in
/-- **The bad-prime budget.** For `N ≥ e^42`, with `Q = 40⌈log N⌉`, the Brun-Titchmarsh classes
of the odd primes `r ≤ Q` and the tail `Σ_{Q < n ≤ N} ⌊N/n²⌋` total at most `0.87 N / log N`. -/
theorem bad_sum_le (N : ℕ) (hN : exp 42 ≤ N) :
    (∑ r ∈ (Icc 3 (40 * ⌈Real.log N⌉₊)).filter Nat.Prime, ((cls N r).card : ℝ)) +
      ∑ n ∈ Ioc (40 * ⌈Real.log N⌉₊) N, ((N / n ^ 2 : ℕ) : ℝ) ≤ 0.87 * N / Real.log N := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : 42 ≤ L := by
    have := Real.log_le_log (exp_pos 42) hN
    rwa [Real.log_exp] at this
  have hexpL : exp L = N := Real.exp_log hNpos
  have hpoly := poly_le_exp42 hL
  have hexp55 : exp (0.55 * L) ≤ N := by
    rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith)
  have hNbig : 5000 * L * (L + 1) ≤ (N : ℝ) := hpoly.trans hexp55
  have h30 : 30 ≤ N := by
    have : (30 : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have h4 : 4 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  -- parameters
  set Q : ℕ := 40 * ⌈L⌉₊ with hQdef
  have hQr : (Q : ℝ) = 40 * (⌈L⌉₊ : ℝ) := by rw [hQdef]; push_cast; ring
  have hceil1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hceil2 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hQlo : 40 * L ≤ (Q : ℝ) := by rw [hQr]; linarith
  have hQhi : (Q : ℝ) ≤ 40 * (L + 1) := by rw [hQr]; linarith
  have hQ31 : 31 ≤ Q := by
    have : (31 : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  have hQ1 : 1 ≤ Q := by omega
  have hQ0 : (0 : ℝ) < Q := by linarith
  -- every `r ≤ Q` has `2r² ≤ N + 1`
  have hsq : ∀ r : ℕ, r ≤ Q → 2 * r ^ 2 ≤ N + 1 := by
    intro r hr
    have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
    have : (2 : ℝ) * (r : ℝ) ^ 2 ≤ N := by
      have h0 : (0 : ℝ) ≤ r := by positivity
      have : (r : ℝ) ^ 2 ≤ (40 * (L + 1)) ^ 2 := by
        apply pow_le_pow_left₀ h0 (hr'.trans hQhi)
      nlinarith
    have : 2 * r ^ 2 ≤ N := by exact_mod_cast this
    omega
  -- the three λ
  have hl2 := Real.log_two_lt_d9
  have hl3 := log3_le
  set lA : ℝ := L - 2.21808 with hlA
  set lB : ℝ := L - 6.93148 with hlB
  set lC : ℝ := L - 5 / 108 * (L + 1) - 12.972 with hlC
  have hlog32 : Real.log 32 ≤ 3.465736 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; push_cast; linarith
  have hlogQ : Real.log Q ≤ 40 * (L + 1) / 1728 + 6.486 := by
    have h1 := Real.log_le_sub_one_of_pos (x := (Q : ℝ) / 1728) (by positivity)
    rw [Real.log_div hQ0.ne' (by norm_num)] at h1
    have h1728 : Real.log 1728 = 6 * Real.log 2 + 3 * Real.log 3 := by
      rw [show (1728 : ℝ) = 2 ^ 6 * 3 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]; push_cast; ring
    have : (Q : ℝ) / 1728 ≤ 40 * (L + 1) / 1728 := by linarith
    linarith
  -- the two groups of classes
  set S := (Icc 3 Q).filter Nat.Prime with hS
  have htail := tail_le (N := N) hQ1
  have hsplit := (sum_filter_add_sum_filter_not S (· ≤ 31)
    (fun r => ((cls N r).card : ℝ))).symm
  rw [small_primes hQ31, sum_insert (by decide)] at hsplit
  have hmem : ∀ r ∈ S, r.Prime ∧ 2 * r ^ 2 ≤ N + 1 := by
    intro r hr
    rw [hS, mem_filter, mem_Icc] at hr
    exact ⟨hr.2, hsq r hr.1.2⟩
  -- r = 3
  have hA := cls_card_pow (r := 3) Nat.prime_three (hsq 3 (by omega)) hN1 (lam := lA)
    (by rw [hlA]; linarith)
    (by
      have := log_cls_ge (N := N) (r := 3) hN1 (by norm_num) (R := 3) (by norm_num)
      rw [hlA]; linarith)
  have hFA : 1 + 2 * exp (-lA) + 2 * exp (-lA / 10) ≤ 1.06 := by
    have := F_le (lam := lA) (a := 3.978) 3 (by norm_num) (by rw [hlA]; linarith)
      (by rw [hlA]; linarith)
    refine this.trans ?_
    norm_num
  -- 5 ≤ r ≤ 31
  have hBmem : ∀ r ∈ ({5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ),
      r.Prime ∧ 2 * r ^ 2 ≤ N + 1 := by
    intro r hr
    have hr' : r.Prime ∧ r ≤ 31 := by
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with h | h | h | h | h | h | h | h | h <;> subst h <;> norm_num
    exact ⟨hr'.1, hsq r (by omega)⟩
  have hB := sum_cls_le hN1 _ hBmem (lam := lB) (F := 1.07) (by rw [hlB]; linarith)
    (by
      intro r hr
      have hr31 : r ≤ 31 ∧ 1 ≤ r := by
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with h | h | h | h | h | h | h | h | h <;> subst h <;> norm_num
      have hrR : (r : ℝ) ≤ 32 := by
        have : (r : ℝ) ≤ 31 := by exact_mod_cast hr31.1
        linarith
      have := log_cls_ge (N := N) hN1 hr31.2 hrR
      rw [hlB]; linarith)
    (by
      have := F_le (lam := lB) (a := 3.506) 3 (by norm_num) (by rw [hlB]; linarith)
        (by rw [hlB]; linarith)
      refine this.trans ?_
      norm_num)
  -- 31 < r ≤ Q
  have hCmem : ∀ r ∈ S.filter (fun r => ¬ r ≤ 31), r.Prime ∧ 2 * r ^ 2 ≤ N + 1 :=
    fun r hr => hmem r (mem_filter.mp hr).1
  have hC := sum_cls_le hN1 _ hCmem (lam := lC) (F := 1.17) (by rw [hlC]; linarith)
    (by
      intro r hr
      rw [mem_filter, hS, mem_filter, mem_Icc] at hr
      have hrR : (r : ℝ) ≤ Q := by exact_mod_cast hr.1.1.2
      have := log_cls_ge (N := N) hN1 (by omega) hrR
      rw [hlC]; linarith)
    (by
      have := F_le (lam := lC) (a := 2.703) 2 (by norm_num) (by rw [hlC]; linarith)
        (by rw [hlC]; linarith)
      refine this.trans ?_
      norm_num)
  have hCsum : ∑ r ∈ S.filter (fun r => ¬ r ≤ 31), (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤
      1 / 31 := by
    have hsub : S.filter (fun r => ¬ r ≤ 31) ⊆ Ioc 31 Q := by
      intro r hr
      rw [mem_filter, hS, mem_filter, mem_Icc] at hr
      rw [mem_Ioc]; omega
    refine le_trans (sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro r hr _
      rw [mem_Ioc] at hr
      have : (31 : ℝ) < r := by exact_mod_cast hr.1
      have : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
      positivity
    · have := sum_Ioc_inv_mul_pred_le (a := 31) (by norm_num) Q
      push_cast at this; exact this
  have hCcard : ((S.filter (fun r => ¬ r ≤ 31)).card : ℝ) ≤ Q := by
    have : (S.filter (fun r => ¬ r ≤ 31)).card ≤ Q :=
      (card_filter_le _ _).trans ((card_filter_le _ _).trans (by simp))
    exact_mod_cast this
  have hBcard : (({5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ).card : ℝ) = 9 := by
    rw [show ({5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ).card = 9 by decide]; norm_num
  have hBsum := sumB_le
  have hLpos : 0 < L := by linarith
  -- `N^{9/20} = e^{0.45 L}` and `Q N^{9/20} ≤ N/(100 L)`
  have hNθ : (N : ℝ) ^ ((9 : ℝ) / 20) = exp (0.45 * L) := by
    rw [Real.rpow_def_of_pos hNpos, ← hLdef]; ring_nf
  have hsplitexp : exp (0.55 * L) * exp (0.45 * L) = N := by
    rw [← Real.exp_add, ← hexpL]; ring_nf
  set E := exp (0.45 * L) with hEdef
  have hE0 : 0 < E := exp_pos _
  have hQE : ((Q : ℝ) + 10) * E * (100 * L) ≤ N := by
    rw [← hsplitexp]
    have h1 : ((Q : ℝ) + 10) * (100 * L) ≤ 5000 * L * (L + 1) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right (h1.trans hpoly) hE0.le
    calc ((Q : ℝ) + 10) * E * (100 * L) = ((Q : ℝ) + 10) * (100 * L) * E := by ring
      _ ≤ _ := h2
  -- the main terms, each `≤ c (N + 1)/L`
  have hiA : L * (1 / lA) ≤ 1 / 0.947 := by
    rw [hlA, mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hiB : L * (1 / lB) ≤ 1 / 0.83 := by
    rw [hlB, mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hiC : L * (1 / lC) ≤ 1 / 0.64 := by
    rw [hlC, mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  rw [hNθ] at hA hB hC
  -- assemble
  have hbad : (∑ r ∈ S, ((cls N r).card : ℝ)) + ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) ≤
      ((Q : ℝ) + 10) * E + 20 / 9 * ((N : ℝ) + 1) *
        (1.06 / lA * (1 / 6) + 1.07 / lB * 0.1002 + 1.17 / lC * (1 / 31)) + N / Q := by
    have h3 : (1 : ℝ) / ((3 : ℕ) * (((3 : ℕ) : ℝ) - 1)) = 1 / 6 := by norm_num
    have hA' : ((cls N 3).card : ℝ) ≤ E + 20 / 9 * ((N : ℝ) + 1) * 1.06 / lA * (1 / 6) := by
      have hlA0 : 0 < lA := by rw [hlA]; linarith
      calc ((cls N 3).card : ℝ) ≤ _ := hA
        _ ≤ E + 20 / 9 * ((N : ℝ) + 1) * 1.06 / (lA * (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1))) := by
          gcongr
        _ = _ := by push_cast; field_simp; ring
    have hlB0 : 0 < lB := by rw [hlB]; linarith
    have hlC0 : 0 < lC := by rw [hlC]; linarith
    have hN10 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have kB : 0 ≤ 20 / 9 * ((N : ℝ) + 1) * 1.07 / lB := by positivity
    have kC : 0 ≤ 20 / 9 * ((N : ℝ) + 1) * 1.17 / lC := by positivity
    have hB2 := mul_le_mul_of_nonneg_left hBsum kB
    have hC2 := mul_le_mul_of_nonneg_left hCsum kC
    have hCE := mul_le_mul_of_nonneg_right hCcard hE0.le
    rw [hBcard] at hB
    have e1 : 20 / 9 * ((N : ℝ) + 1) *
        (1.06 / lA * (1 / 6) + 1.07 / lB * 0.1002 + 1.17 / lC * (1 / 31)) =
        20 / 9 * ((N : ℝ) + 1) * 1.06 / lA * (1 / 6) + 20 / 9 * ((N : ℝ) + 1) * 1.07 / lB * 0.1002
          + 20 / 9 * ((N : ℝ) + 1) * 1.17 / lC * (1 / 31) := by ring
    rw [e1]
    linarith
  -- final contradiction
  have hLA := mul_le_mul_of_nonneg_left hiA (by positivity : (0 : ℝ) ≤ 20 / 9 * ((N : ℝ) + 1))
  have hLB := mul_le_mul_of_nonneg_left hiB (by positivity : (0 : ℝ) ≤ 20 / 9 * ((N : ℝ) + 1))
  have hLC := mul_le_mul_of_nonneg_left hiC (by positivity : (0 : ℝ) ≤ 20 / 9 * ((N : ℝ) + 1))
  have hNQ : (N : ℝ) / Q * L ≤ N / 40 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hQ0 (by norm_num)]
    have := mul_le_mul_of_nonneg_left hQlo hNpos.le
    linarith
  have hmulL := mul_le_mul_of_nonneg_right hbad hLpos.le
  have e2 : (((Q : ℝ) + 10) * E + 20 / 9 * ((N : ℝ) + 1) *
        (1.06 / lA * (1 / 6) + 1.07 / lB * 0.1002 + 1.17 / lC * (1 / 31)) + N / Q) * L =
      ((Q : ℝ) + 10) * E * L + (20 / 9 * ((N : ℝ) + 1) * (L * (1 / lA))) * (1.06 / 6) +
        (20 / 9 * ((N : ℝ) + 1) * (L * (1 / lB))) * (1.07 * 0.1002) +
        (20 / 9 * ((N : ℝ) + 1) * (L * (1 / lC))) * (1.17 / 31) + N / Q * L := by
    ring
  rw [e2] at hmulL
  have hQEL : ((Q : ℝ) + 10) * E * L ≤ N / 100 := by linarith
  have hNL : 200000 * L ≤ (N : ℝ) := by nlinarith
  rw [le_div_iff₀ hLpos]
  linarith

/-- **Dudek's theorem for even `N ≥ e^42`, PROVED, no cited input.** Every even `N ≥ e^42` is
`p + m` with `p` prime and `m ≥ 1` square-free. `e^42 < 1.74·10¹⁸`. -/
theorem dudek_even_from_exp42 (N : ℕ) (hE : Even N) (hN : exp 42 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  by_contra hno
  have hb := bad_sum_le N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : 42 ≤ L := by
    have := Real.log_le_log (exp_pos 42) hN
    rwa [Real.log_exp] at this
  have hexpL : exp L = N := Real.exp_log hNpos
  have hexp55 : exp (0.55 * L) ≤ N := by
    rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith)
  have hNbig : 5000 * L * (L + 1) ≤ (N : ℝ) := (poly_le_exp42 hL).trans hexp55
  have hNL : 200000 * L ≤ (N : ℝ) := by nlinarith
  have h30 : 30 ≤ N := by
    have : (30 : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hcount := card_le_of_no_rep (40 * ⌈L⌉₊) hE (by omega) hno
  have hpi := LeanLab.ChebyshevExplicit.pi_ge_chebyshev30 N h30
  have hLpos : 0 < L := by linarith
  rw [div_le_iff₀ hLpos, ← hLdef] at hpi
  have h1 := hcount.trans hb
  rw [le_div_iff₀ hLpos] at h1
  nlinarith

/-- `e^42 ≤ 4·10¹⁸`; in fact `e^42 < 1.74·10¹⁸`. -/
lemma exp42_le : exp 42 ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) := by
  have h := Real.exp_nat_mul 1 42
  rw [mul_one] at h
  have h' : exp 42 = exp 1 ^ 42 := by rw [← h]; norm_num
  rw [h']
  calc exp 1 ^ 42 ≤ (2.7182818286 : ℝ) ^ 42 :=
        pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 42
    _ ≤ _ := by norm_num

/-- Vacuity test: the hypothesis of `dudek_even_from_exp42` holds for `N = 4·10¹⁸`, an even
number. -/
example : Even (4 * 10 ^ 18) ∧ exp 42 ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) :=
  ⟨⟨2 * 10 ^ 18, by norm_num⟩, exp42_le⟩

end LeanLab.AlmostPrimes.DudekFrom4e18

