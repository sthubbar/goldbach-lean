module

public import LeanLab.ChebyshevExplicit.Psi30
public import LeanLab.ChebyshevExplicit.Psi30Quadratic
public import LeanLab.BS2022GRH.Cert1575W00
public import LeanLab.BS2022GRH.Cert1575W01
public import LeanLab.BS2022GRH.Cert1575W02
public import LeanLab.BS2022GRH.Cert1575W03
public import LeanLab.BS2022GRH.Cert1575W04
public import LeanLab.BS2022GRH.Cert1575W05
public import LeanLab.BS2022GRH.Cert1575W06
public import LeanLab.BS2022GRH.Cert1575W07
public import LeanLab.BS2022GRH.Cert1575W08
public import LeanLab.BS2022GRH.Cert1575W09
public import LeanLab.BS2022GRH.Cert1575W10

/-!
BS2022GRH, P0021, idea I-0088, unit U-1575, PC run 20261027T0807Z-9485, T1 PALOMAR: a proof of
the numeric leaf `ChenThresholdGRH.Eps1500`, ε(1500) < 1/8349, display (6) p. 1221.

* Head, kernel checked: Σ over primes 1501 ≤ p < H = 9003001 of 1/p² ≤ 7963599791126110·10⁻²⁰.
  The windows `Cert1575W00` to `Cert1575W10` run `decide +kernel`, no native_decide, over the
  numbers n ≡ 1, 5 mod 6 and add ⌊10²⁰/n²⌋ + 1 whenever gcd(n, m!) = 1, m = 1499 or 3000 below
  every prime of the window. No primality certificate is needed for an upper bound.
* Tail, proved: Σ over primes p ≥ H of 1/p² ≤ (C·H − θ₀)/(16 H²) + C/(16 H), C = 89/80,
  θ₀ = 8191444, by discrete summation by parts against θ(n) − θ(H − 1), with
  θ(x) ≤ 1.10556 x + 5 log² x/(4 log 6) + 5 log x/4 from `ChebyshevExplicit.Psi30Quadratic`,
  ψ(n) ≥ 0.9212 n − 5 log n from `ChebyshevExplicit.Psi30` and Mathlib's ψ − θ ≤ 2√x log x.
* `eps1500_proved : Eps1500copy`, the verbatim copy of `Eps1500`, PROVED, margin about 8.8·10⁻¹⁰ in 1 + 1/8349 − e^x.

AI-written Lean code, Claude, unit U-1575. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Cert1575
open Real Finset Chebyshev LeanLab.BS2022GRH.Cert1575Defs

/-- Verbatim copy of `ChenThresholdGRH.epsJ`, display (6) p. 1221; `Cert1575Closed` checks that
`Eps1500copy` is `ChenThresholdGRH.Eps1500` by definitional unfolding. The copy lets this module
build without the BS2022GRH chain. -/
noncomputable def epsJcopy (u : ℝ) : ℝ :=
  exp (1.131e-7 + (u / (u - 2) + 0.501) *
    ∑' p : {p : ℕ // p.Prime ∧ u ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2) - 1

/-- Verbatim copy of `ChenThresholdGRH.Eps1500`: ε(1500) < 1/8349. -/
def Eps1500copy : Prop := epsJcopy 1500 < 1 / 8349

/-! ### The kernel functions -/

lemma fac_eq (m : ℕ) : fac m = m.factorial := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Nat.factorial_succ, ← ih]; rfl

lemma inner_eq (F M : ℕ) : ∀ f n s, Cert1575Defs.inner F M f n s = s + T F M f n := by
  intro f
  induction f with
  | zero => intro n s; simp [Cert1575Defs.inner, T]
  | succ f ih =>
    intro n s
    show Cert1575Defs.inner F M f (n + 6) (s + term F M n + term F M (n + 4)) =
      s + (term F M n + term F M (n + 4) + T F M f (n + 6))
    rw [ih]; ring

lemma T_add (F M : ℕ) : ∀ a b n, T F M (a + b) n = T F M a n + T F M b (n + 6 * a) := by
  intro a
  induction a with
  | zero => intro b n; simp [T]
  | succ a ih =>
    intro b n
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show term F M n + term F M (n + 4) + T F M (a + b) (n + 6) =
      (term F M n + term F M (n + 4) + T F M a (n + 6)) + T F M b (n + 6 * (a + 1))
    rw [ih, show n + 6 + 6 * a = n + 6 * (a + 1) by ring]
    ring

lemma outer_sound (F M S B : ℕ) : ∀ K n s, outer F M S B K n s = true →
    s + T F M (B * K) n ≤ S := by
  intro K
  induction K with
  | zero => intro n s h; simpa [outer, T] using h
  | succ K ih =>
    intro n s h
    simp only [outer, Bool.and_eq_true] at h
    have h2 := ih _ _ h.2
    rw [inner_eq] at h2
    rw [show B * (K + 1) = B + B * K by ring, T_add]
    omega

/-! ### From the window checks to the real prime sum -/

/-- `a n = 1/n²` on primes, `0` elsewhere. -/
noncomputable def a (n : ℕ) : ℝ := if n.Prime then 1 / (n : ℝ) ^ 2 else 0

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by unfold a; split_ifs <;> positivity

lemma not_prime_of_dvd {p n : ℕ} (hp : 2 ≤ p) (h : p ∣ n) (hn : p < n) : ¬ n.Prime :=
  fun h' => by have := h'.eq_one_or_self_of_dvd p h; omega

lemma a_eq_zero {n : ℕ} (h : ¬ n.Prime) : a n = 0 := by simp [a, h]

lemma a_le_term {F M n : ℕ} (hM : 0 < M) (hc : n.Prime → Nat.Coprime F n) :
    a n ≤ (term F M n : ℝ) / M := by
  unfold a
  split_ifs with hp
  · have hg : Nat.gcd F n = 1 := hc hp
    have hterm : term F M n = M / (n * n) + 1 := by simp [term, hg]
    rw [hterm]
    have hn : 0 < n * n := Nat.mul_pos hp.pos hp.pos
    have key : M < (M / (n * n) + 1) * (n * n) := by
      have := Nat.lt_div_mul_add (a := M) hn; nlinarith
    have keyR : (M : ℝ) < ((M / (n * n) + 1 : ℕ) : ℝ) * ((n : ℝ) ^ 2) := by
      have : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
      rw [← this]; exact_mod_cast key
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hp.pos) 2
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    rw [div_le_div_iff₀ hn2 hMR]; linarith
  · positivity

lemma block6 (lo : ℕ) (h6 : lo % 6 = 1) (h7 : 7 ≤ lo) :
    ∑ n ∈ Ico lo (lo + 6), a n = a lo + a (lo + 4) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have e1 : a (lo + 1) = 0 := a_eq_zero (not_prime_of_dvd (p := 2) le_rfl
    (Nat.dvd_of_mod_eq_zero (by omega)) (by omega))
  have e2 : a (lo + 2) = 0 := a_eq_zero (not_prime_of_dvd (p := 3) (by norm_num)
    (Nat.dvd_of_mod_eq_zero (by omega)) (by omega))
  have e3 : a (lo + 3) = 0 := a_eq_zero (not_prime_of_dvd (p := 2) le_rfl
    (Nat.dvd_of_mod_eq_zero (by omega)) (by omega))
  have e5 : a (lo + 5) = 0 := a_eq_zero (not_prime_of_dvd (p := 2) le_rfl
    (Nat.dvd_of_mod_eq_zero (by omega)) (by omega))
  simp only [show lo + 6 - lo = 6 by omega, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, add_zero, e1, e2, e3, e5]

lemma window (F M : ℕ) (hM : 0 < M) : ∀ f lo, lo % 6 = 1 → 7 ≤ lo →
    (∀ p, p.Prime → lo ≤ p → Nat.Coprime F p) →
    ∑ n ∈ Ico lo (lo + 6 * f), a n ≤ (T F M f lo : ℝ) / M := by
  intro f
  induction f with
  | zero => intro lo _ _ _; simp [T]
  | succ f ih =>
    intro lo h6 h7 hc
    rw [← Finset.sum_Ico_consecutive a (show lo ≤ lo + 6 by omega)
      (show lo + 6 ≤ lo + 6 * (f + 1) by omega), block6 lo h6 h7]
    have h1 := a_le_term (F := F) (M := M) (n := lo) hM (fun hp => hc lo hp le_rfl)
    have h2 := a_le_term (F := F) (M := M) (n := lo + 4) hM (fun hp => hc _ hp (by omega))
    have h3 := ih (lo + 6) (by omega) (by omega) (fun p hp hle => hc p hp (by omega))
    rw [show lo + 6 + 6 * f = lo + 6 * (f + 1) by ring] at h3
    simp only [T]
    push_cast
    rw [add_div, add_div]
    linarith

lemma cop_fac {m p : ℕ} (hp : p.Prime) (h : m < p) : Nat.Coprime (fac m) p := by
  rw [fac_eq]
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
    (fun hd => by have := (Nat.Prime.dvd_factorial hp).1 hd; omega))

lemma win_bound {m S B K lo hi : ℕ} (h : outer (fac m) (10 ^ 20) S B K lo 0 = true)
    (h6 : lo % 6 = 1) (h7 : 7 ≤ lo) (hm : m < lo) (hhi : lo + 6 * (B * K) = hi) :
    ∑ n ∈ Ico lo hi, a n ≤ (S : ℝ) / 10 ^ 20 := by
  have hs := outer_sound _ _ _ _ _ _ _ h
  have hw := window (fac m) (10 ^ 20) (by positivity) (B * K) lo h6 h7
    (fun p hp hle => cop_fac hp (by omega))
  rw [hhi] at hw
  have hs' : T (fac m) (10 ^ 20) (B * K) lo ≤ S := by omega
  have : (T (fac m) (10 ^ 20) (B * K) lo : ℝ) ≤ S := by exact_mod_cast hs'
  have hM : ((10 ^ 20 : ℕ) : ℝ) = (10 : ℝ) ^ 20 := by norm_num
  rw [hM] at hw
  exact hw.trans (by gcongr)

lemma chain {x y : ℝ} {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r)
    (h1 : ∑ n ∈ Ico p q, a n ≤ x) (h2 : ∑ n ∈ Ico q r, a n ≤ y) :
    ∑ n ∈ Ico p r, a n ≤ x + y := by
  rw [← Finset.sum_Ico_consecutive a hpq hqr]; linarith

/-- **Head**, kernel checked: Σ over primes 1501 ≤ p < 9003001 of 1/p² ≤ 7963599791126110·10⁻²⁰. -/
theorem head_le : ∑ n ∈ Ico 1501 9003001, a n ≤ 7963599791126110 / 10 ^ 20 := by
  have h0 := win_bound win00 (by norm_num) (by norm_num) (by norm_num) (hi := 3001) (by norm_num)
  have h1 := win_bound win01 (by norm_num) (by norm_num) (by norm_num) (hi := 903001) (by norm_num)
  have h2 := win_bound win02 (by norm_num) (by norm_num) (by norm_num) (hi := 1803001) (by norm_num)
  have h3 := win_bound win03 (by norm_num) (by norm_num) (by norm_num) (hi := 2703001) (by norm_num)
  have h4 := win_bound win04 (by norm_num) (by norm_num) (by norm_num) (hi := 3603001) (by norm_num)
  have h5 := win_bound win05 (by norm_num) (by norm_num) (by norm_num) (hi := 4503001) (by norm_num)
  have h6 := win_bound win06 (by norm_num) (by norm_num) (by norm_num) (hi := 5403001) (by norm_num)
  have h7 := win_bound win07 (by norm_num) (by norm_num) (by norm_num) (hi := 6303001) (by norm_num)
  have h8 := win_bound win08 (by norm_num) (by norm_num) (by norm_num) (hi := 7203001) (by norm_num)
  have h9 := win_bound win09 (by norm_num) (by norm_num) (by norm_num) (hi := 8103001) (by norm_num)
  have h10 := win_bound win10 (by norm_num) (by norm_num) (by norm_num) (hi := 9003001) (by norm_num)
  have := chain (by norm_num) (by norm_num) h0 <| chain (by norm_num) (by norm_num) h1 <|
    chain (by norm_num) (by norm_num) h2 <| chain (by norm_num) (by norm_num) h3 <|
    chain (by norm_num) (by norm_num) h4 <| chain (by norm_num) (by norm_num) h5 <|
    chain (by norm_num) (by norm_num) h6 <| chain (by norm_num) (by norm_num) h7 <|
    chain (by norm_num) (by norm_num) h8 <| chain (by norm_num) (by norm_num) h9 h10
  norm_num at this
  linarith

/-! ### Tail by summation by parts -/

/-- `g n = 1/(n² log n)`. -/
noncomputable def g (n : ℕ) : ℝ := 1 / ((n : ℝ) ^ 2 * log n)

lemma theta_succ (n : ℕ) :
    θ ((n + 1 : ℕ) : ℝ) = θ (n : ℝ) + (if (n + 1).Prime then log ((n + 1 : ℕ) : ℝ) else 0) := by
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log, Nat.primesLE_succ]
  split_ifs with hp
  · rw [Finset.sum_insert]
    · ring
    · exact Nat.notMem_primesBelow (n + 1)
  · simp

lemma a_eq_dtheta (n : ℕ) (hn : 1 ≤ n) :
    a (n + 1) = (θ ((n + 1 : ℕ) : ℝ) - θ (n : ℝ)) * g (n + 1) := by
  rw [theta_succ, a, g]
  split_ifs with hp
  · have h1 : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 1)
    have hl : 0 < log ((n + 1 : ℕ) : ℝ) := Real.log_pos h1
    have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
    rw [add_sub_cancel_left]
    field_simp
  · simp

lemma exp16_le : exp 16 ≤ 9003001 := by
  have h := Real.exp_one_lt_d9
  have : exp 16 = exp 1 ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h' := h.le
  calc exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 := by gcongr
    _ ≤ 9003001 := by norm_num

lemma log_ge16 {x : ℝ} (hx : 9003001 ≤ x) : 16 ≤ log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]; linarith [exp16_le]

lemma log_le17 {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 9003001) : log x ≤ 17 := by
  rw [Real.log_le_iff_le_exp hx0]
  have h := Real.exp_one_gt_d9
  have : exp 17 = exp 1 ^ 17 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h' := h.le
  calc x ≤ 9003001 := hx
    _ ≤ (2.7182818283 : ℝ) ^ 17 := by norm_num
    _ ≤ exp 1 ^ 17 := by gcongr

lemma log6_ge : (1.386 : ℝ) ≤ log 6 := by
  have h2 := Real.log_two_gt_d9
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have : log 4 < log 6 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- θ(x) ≤ (89/80) x for x ≥ 9·10⁶, from the lab's Chebyshev bound. -/
lemma theta_le_C {x : ℝ} (hx : 9000000 ≤ x) : θ x ≤ 89 / 80 * x := by
  have h := LeanLab.ChebyshevExplicit.theta_le_110556_quadratic_real (x := x) (by linarith)
  have hx0 : 0 ≤ x := by linarith
  set s := √x with hs
  set t := √s with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hss : s ^ 2 = x := Real.sq_sqrt hx0
  have htt : t ^ 2 = s := Real.sq_sqrt hs0
  have hs3000 : 3000 ≤ s := by
    rw [hs, show (3000 : ℝ) = √(3000 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have ht1' : 1 ≤ t := by nlinarith
  have hts : t ≤ s := by nlinarith
  have hlog : log x = 4 * log t := by
    rw [← hss, ← htt, Real.log_pow, Real.log_pow]; push_cast; ring
  have ht1 : log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by nlinarith)
  have hlx0 : 0 ≤ log x := Real.log_nonneg (by linarith)
  have hl1 : log x ≤ 4 * t := by linarith
  have hl2 : log x ^ 2 ≤ 16 * s := by nlinarith
  have hl6 := log6_ge
  have hc : 5 / (4 * log 6) ≤ 5 / (4 * 1.386) := by gcongr
  have hc0 : 0 ≤ 5 / (4 * log 6) := by positivity
  have hA : 5 / (4 * log 6) * log x ^ 2 ≤ 5 / (4 * 1.386) * (16 * s) :=
    mul_le_mul hc hl2 (sq_nonneg _) (by norm_num)
  have hB : 5 / 4 * log x ≤ 5 * s := by nlinarith
  have hss3 := mul_le_mul_of_nonneg_right hs3000 hs0
  nlinarith

/-- θ(9003000) ≥ 8191444. -/
lemma theta_H_ge : (8191444 : ℝ) ≤ θ ((9003000 : ℕ) : ℝ) := by
  have hψ := LeanLab.ChebyshevExplicit.psi_ge_09212 9003000 (by norm_num)
  have hd := Chebyshev.psi_sub_theta_le (x := ((9003000 : ℕ) : ℝ)) (by norm_num)
  have hl := log_le17 (x := ((9003000 : ℕ) : ℝ)) (by norm_num) (by norm_num)
  have hl0 : 0 ≤ log ((9003000 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
  have hsq : √((9003000 : ℕ) : ℝ) ≤ 3001 := by
    rw [show (3001 : ℝ) = √(3001 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsq0 : 0 ≤ √((9003000 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hp : √((9003000 : ℕ) : ℝ) * log ((9003000 : ℕ) : ℝ) ≤ 3001 * 17 :=
    mul_le_mul hsq hl hl0 (by norm_num)
  push_cast at hψ hd hp hl ⊢
  nlinarith

lemma g_pos {n : ℕ} (hn : 2 ≤ n) : 0 < g n := by
  unfold g
  have : (1 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_pos this
  positivity

lemma g_anti {n : ℕ} (hn : 2 ≤ n) : g (n + 1) ≤ g n := by
  unfold g
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.log_pos h1
  have hle : log (n : ℝ) ≤ log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  apply one_div_le_one_div_of_le (by positivity)
  have : (n : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by gcongr; push_cast; linarith
  exact mul_le_mul this hle hl.le (by positivity)

lemma g_le {n : ℕ} (hn : 9003001 ≤ n) : g (n + 1) ≤ 1 / 16 * (1 / (n : ℝ) - 1 / (n + 1)) := by
  unfold g
  have hn' : (9003001 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := log_ge16 (x := ((n + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  push_cast at hl
  have hpos : (0 : ℝ) < n := by linarith
  have e : 1 / (n : ℝ) - 1 / (n + 1) = 1 / ((n : ℝ) * (n + 1)) := by field_simp; ring
  rw [e]
  push_cast
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  have : 16 * ((n : ℝ) * (n + 1)) ≤ 16 * ((n + 1 : ℝ) ^ 2) := by nlinarith
  have := mul_le_mul_of_nonneg_left hl (sq_nonneg ((n : ℝ) + 1))
  nlinarith

/-- The summation by parts invariant, with `θH` standing for θ(9003000). -/
lemma tail_inv (C θ₀ θH : ℝ) (hC : 0 ≤ C) (hθH : θ ((9003000 : ℕ) : ℝ) = θH)
    (hU : ∀ n : ℕ, 9003001 ≤ n → θ (n : ℝ) - θH ≤ C * n - θ₀) :
    ∀ k : ℕ, ∑ n ∈ Ico 9003001 (9003001 + k + 1), a n +
      ((C * ((9003001 + k : ℕ) : ℝ) - θ₀) - (θ ((9003001 + k : ℕ) : ℝ) - θH))
        * g (9003001 + k)
      ≤ (C * 9003001 - θ₀) * g 9003001 + C / 16 * (1 / 9003001 - 1 / ((9003001 + k : ℕ) : ℝ)) := by
  intro k
  induction k with
  | zero =>
    have ha : a 9003001 = (θ ((9003001 : ℕ) : ℝ) - θH) * g 9003001 := by
      rw [← hθH]; exact a_eq_dtheta 9003000 (by norm_num)
    rw [show 9003001 + 0 + 1 = 9003001 + 1 from rfl, Finset.sum_Ico_succ_top (le_refl _),
      Finset.Ico_self, Finset.sum_empty, zero_add, show 9003001 + 0 = 9003001 from rfl, ha]
    exact le_of_eq (by push_cast; ring)
  | succ k ih =>
    set N := 9003001 + k with hN
    have hN2 : 2 ≤ N := by omega
    rw [show 9003001 + (k + 1) + 1 = (N + 1) + 1 by omega, Finset.sum_Ico_succ_top (by omega),
      show 9003001 + (k + 1) = N + 1 by omega]
    rw [a_eq_dtheta N (by omega)]
    have hgN := g_anti hN2
    have hgle := g_le (n := N) (by omega)
    have hUN := hU N (by omega)
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have key : 0 ≤ ((C * (N : ℝ) - θ₀) - (θ (N : ℝ) - θH)) * (g N - g (N + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    have hCg : C * g (N + 1) ≤ C / 16 * (1 / (N : ℝ) - 1 / (N + 1)) := by
      have := mul_le_mul_of_nonneg_left hgle hC
      calc C * g (N + 1) ≤ C * (1 / 16 * (1 / (N : ℝ) - 1 / ((N : ℝ) + 1))) := this
        _ = C / 16 * (1 / (N : ℝ) - 1 / (N + 1)) := by ring
    have h := add_le_add (sub_le_sub ih key) hCg
    calc _ = (∑ n ∈ Ico 9003001 (N + 1), a n + ((C * (N : ℝ) - θ₀) - (θ (N : ℝ) - θH)) * g N)
          - ((C * (N : ℝ) - θ₀) - (θ (N : ℝ) - θH)) * (g N - g (N + 1)) + C * g (N + 1) := by
          ring
      _ ≤ (C * 9003001 - θ₀) * g 9003001 + C / 16 * (1 / 9003001 - 1 / (N : ℝ)) - 0
          + C / 16 * (1 / (N : ℝ) - 1 / (N + 1)) := h
      _ = _ := by ring

/-- **Tail**: for every k, Σ over primes 9003001 ≤ p ≤ 9003001 + k of 1/p² is at most
(C·9003001 − 8191444)/(16·9003001²) + C/(16·9003001) with C = 89/80. -/
theorem tail_le (k : ℕ) : ∑ n ∈ Ico 9003001 (9003001 + k + 1), a n ≤
    (89 / 80 * 9003001 - 8191444) / (16 * 9003001 ^ 2) + 89 / 80 / (16 * 9003001) := by
  have hθ0 := theta_H_ge
  obtain ⟨θH, hθH⟩ : ∃ t, θ ((9003000 : ℕ) : ℝ) = t := ⟨_, rfl⟩
  rw [hθH] at hθ0
  have hU : ∀ n : ℕ, 9003001 ≤ n → θ (n : ℝ) - θH ≤ 89 / 80 * n - 8191444 := by
    intro n hn
    have : (9000000 : ℝ) ≤ n := by exact_mod_cast (by omega : 9000000 ≤ n)
    exact sub_le_sub (theta_le_C this) hθ0
  have h := tail_inv (89 / 80) 8191444 θH (by norm_num) hθH hU k
  set N := 9003001 + k with hN
  have hDN : 0 ≤ (89 / 80 * (N : ℝ) - 8191444) - (θ (N : ℝ) - θH) :=
    sub_nonneg.2 (hU N (by omega))
  have hgN := (g_pos (n := N) (by omega)).le
  have hdrop := mul_nonneg hDN hgN
  have hinv : 0 ≤ 1 / (N : ℝ) := by positivity
  have hgH : g 9003001 ≤ 1 / (16 * 9003001 ^ 2) := by
    unfold g
    have hl := log_ge16 (x := ((9003001 : ℕ) : ℝ)) (by norm_num)
    apply one_div_le_one_div_of_le (by positivity)
    push_cast at hl ⊢
    nlinarith
  have hUH : 0 ≤ (89 / 80 * 9003001 - 8191444 : ℝ) := by norm_num
  have h1 := mul_le_mul_of_nonneg_left hgH hUH
  have h2 : (89 / 80 : ℝ) / 16 * (1 / 9003001 - 1 / (N : ℝ)) ≤ 89 / 80 / 16 * (1 / 9003001) := by
    gcongr; exact sub_le_self _ hinv
  calc _ ≤ (89 / 80 * 9003001 - 8191444) * g 9003001 + 89 / 80 / 16 * (1 / 9003001 - 1 / (N : ℝ)) :=
        (le_add_of_nonneg_right hdrop).trans h
    _ ≤ (89 / 80 * 9003001 - 8191444) * (1 / (16 * 9003001 ^ 2)) + 89 / 80 / 16 * (1 / 9003001) :=
        add_le_add h1 h2
    _ = _ := by ring

/-! ### The prime sum and ε(1500) -/

/-- Σ over primes p ≥ 1500 of 1/p², bounded through every finite subset. -/
theorem primeSum_le :
    ∑' p : {p : ℕ // p.Prime ∧ (1500 : ℝ) ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2 ≤
      7963599791126110 / 10 ^ 20 +
      ((89 / 80 * 9003001 - 8191444) / (16 * 9003001 ^ 2) + 89 / 80 / (16 * 9003001)) := by
  apply Real.tsum_le_of_sum_le (fun _ => by simp only [Pi.zero_apply]; positivity)
  intro u
  set X := 9003001 + u.sup (fun x => x.1) with hX
  have himg : ∑ x ∈ u, 1 / ((x : ℕ) : ℝ) ^ 2 = ∑ n ∈ u.image (fun x => x.1), a n := by
    rw [Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
    apply Finset.sum_congr rfl
    intro x _
    simp [a, x.2.1]
  rw [himg]
  have hsub : u.image (fun x => x.1) ⊆ Ico 1501 (9003001 + (X - 9003001) + 1) := by
    intro n hn
    simp only [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    have h1 : (1500 : ℝ) ≤ (x.1 : ℝ) := x.2.2
    have h1' : 1500 ≤ x.1 := by exact_mod_cast h1
    have h1500 : x.1 ≠ 1500 := by
      intro h; have := x.2.1; rw [h] at this
      exact not_prime_of_dvd (p := 2) le_rfl ⟨750, rfl⟩ (by norm_num) this
    have hle : x.1 ≤ u.sup (fun x => x.1) := Finset.le_sup (f := fun x : {p : ℕ // p.Prime ∧ (1500 : ℝ) ≤ (p : ℝ)} => x.1) hx
    simp only [Finset.mem_Ico]; omega
  calc _ ≤ ∑ n ∈ Ico 1501 (9003001 + (X - 9003001) + 1), a n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => a_nonneg n)
    _ = ∑ n ∈ Ico 1501 9003001, a n + ∑ n ∈ Ico 9003001 (9003001 + (X - 9003001) + 1), a n :=
        (Finset.sum_Ico_consecutive a (by norm_num) (by omega)).symm
    _ ≤ _ := add_le_add head_le (tail_le _)

/-- **`Eps1500`, PROVED**: ε(1500) = exp(1.131·10⁻⁷ + (1500/1498 + 0.501) Σ_{p ≥ 1500} 1/p²) − 1
is below 1/8349. -/
theorem eps1500_proved : Eps1500copy := by
  unfold Eps1500copy epsJcopy
  set S := ∑' p : {p : ℕ // p.Prime ∧ (1500 : ℝ) ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2 with hS
  have hSle := primeSum_le
  rw [← hS] at hSle
  have hS0 : 0 ≤ S := tsum_nonneg (fun _ => by positivity)
  set xb : ℝ := 1.131e-7 + ((1500 : ℝ) / (1500 - 2) + 0.501) * (7963599791126110 / 10 ^ 20 +
      ((89 / 80 * 9003001 - 8191444) / (16 * 9003001 ^ 2) + 89 / 80 / (16 * 9003001))) with hxb
  have hc : (0 : ℝ) ≤ (1500 : ℝ) / (1500 - 2) + 0.501 := by norm_num
  have hx : 1.131e-7 + ((1500 : ℝ) / (1500 - 2) + 0.501) * S ≤ xb := by
    have := mul_le_mul_of_nonneg_left hSle hc; rw [hxb]; linarith
  have hxb0 : 0 ≤ xb := by rw [hxb]; norm_num
  have hxb1 : xb ≤ 1 := by rw [hxb]; norm_num
  have he := Real.exp_bound' hxb0 hxb1 (n := 3) (by norm_num)
  have hmono := Real.exp_le_exp.2 hx
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at he
  norm_num at he
  have hpoly : 1 + xb + xb ^ 2 / 2 + xb ^ 3 * 4 / 18 < 1 + 1 / 8349 := by rw [hxb]; norm_num
  nlinarith

end LeanLab.BS2022GRH.Cert1575

