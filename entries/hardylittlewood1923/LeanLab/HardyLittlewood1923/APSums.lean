module

public import Mathlib
public import LeanLab.PNTPort.PsiChi.SiegelWalfisz

/-! AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5707, paper P0004.
Hardy-Littlewood 1923 input: for a fixed modulus `d` and `(a, d) = 1`,
`Σ_{p ≤ n, p ≡ a (d)} (n - p)^2 = n^3 / (3 φ(d) log n) + o(n^3 / log n)`, uniformly in `a`.
Route: Siegel-Walfisz `LeanLab.PNTPort.PsiChi.siegelWalfisz` at `A = 1` gives
`ψ(j; d, a) = j/φ(d) + o(j)`; discrete summation by parts turns the von Mangoldt weighted sum
into `Σ_{j<n} ψ(j; d, a) (2(n - j) - 1)`; Mathlib's `Chebyshev.psi_sub_theta_le` removes prime
powers; the `log p` weight is removed by splitting at `p = n^(1-η)`.
No cited input beyond what `siegelWalfisz` itself proves. Binary Goldbach is OPEN. -/

@[expose] public section

open Real Finset

namespace LeanLab.HardyLittlewood1923

lemma sum_mul_sub (g : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ range (n + 1), g m * ((n : ℝ) - m) = ∑ j ∈ range n, ∑ m ∈ range (j + 1), g m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ _ (n + 1), sum_range_succ (fun j => ∑ m ∈ range (j + 1), g m) n, ← ih]
    push_cast
    rw [sub_self, mul_zero, add_zero, ← sum_add_distrib]
    apply sum_congr rfl; intro m _; ring

lemma sum_mul_sub_sq (g : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ range (n + 1), g m * ((n : ℝ) - m) ^ 2 =
      ∑ j ∈ range n, (∑ m ∈ range (j + 1), g m) * (2 * ((n : ℝ) - j) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ m ∈ range (n + 1 + 1), g m * (((n + 1 : ℕ) : ℝ) - m) ^ 2 =
        ∑ m ∈ range (n + 1), g m * ((n : ℝ) - m) ^ 2
          + 2 * ∑ m ∈ range (n + 1), g m * ((n : ℝ) - m) + ∑ m ∈ range (n + 1), g m := by
      rw [sum_range_succ _ (n + 1), mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      rw [show (((n + 1 : ℕ) : ℝ) - (n + 1 : ℕ)) = 0 by ring, zero_pow two_ne_zero, mul_zero,
        add_zero]
      apply sum_congr rfl; intro m _; push_cast; ring
    rw [h1, ih, sum_mul_sub]
    symm
    rw [sum_range_succ (fun j => (∑ m ∈ range (j + 1), g m) * (2 * (((n + 1 : ℕ) : ℝ) - j) - 1)) n]
    have hs : ∑ j ∈ range n, (∑ m ∈ range (j + 1), g m) * (2 * (((n + 1 : ℕ) : ℝ) - j) - 1) =
        ∑ j ∈ range n, (∑ m ∈ range (j + 1), g m) * (2 * ((n : ℝ) - j) - 1)
          + 2 * ∑ j ∈ range n, ∑ m ∈ range (j + 1), g m := by
      rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
    rw [hs]; push_cast; ring

lemma sum_w (n : ℕ) : ∑ j ∈ range n, (2 * ((n : ℝ) - j) - 1) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have : ∑ j ∈ range n, (2 * (((n + 1 : ℕ) : ℝ) - j) - 1) =
        ∑ j ∈ range n, (2 * ((n : ℝ) - j) - 1) + ∑ j ∈ range n, (2 : ℝ) := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
    rw [this, ih, sum_const, card_range]; push_cast; ring

lemma sum_id (n : ℕ) : ∑ j ∈ range n, (j : ℝ) = (n : ℝ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_jw (n : ℕ) :
    ∑ j ∈ range n, (j : ℝ) * (2 * ((n : ℝ) - j) - 1) = (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have : ∑ j ∈ range n, (j : ℝ) * (2 * (((n + 1 : ℕ) : ℝ) - j) - 1) =
        ∑ j ∈ range n, (j : ℝ) * (2 * ((n : ℝ) - j) - 1) + 2 * ∑ j ∈ range n, (j : ℝ) := by
      rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
    rw [this, ih, sum_id]; push_cast; ring

/-- Error propagation through the weights. -/
lemma abs_sum_err_le (e : ℕ → ℝ) (B δ : ℝ)
    (he : ∀ j, |e j| ≤ B + δ * j) (n : ℕ) :
    |∑ j ∈ range n, e j * (2 * ((n : ℝ) - j) - 1)| ≤
      B * (n : ℝ) ^ 2 + δ * ((n : ℝ) * (n - 1) * (2 * n - 1) / 6) := by
  rw [← sum_w, ← sum_jw, mul_sum, mul_sum, ← sum_add_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast (mem_range.1 hj)
  have hw : 0 ≤ 2 * ((n : ℝ) - j) - 1 := by linarith
  rw [abs_mul, abs_of_nonneg hw]
  have := mul_le_mul_of_nonneg_right (he j) hw
  nlinarith

open scoped ArithmeticFunction.vonMangoldt
open Filter

/-- The von Mangoldt weight restricted to the residue class of `a` mod `d`. -/
noncomputable def gfun (d a : ℕ) (m : ℕ) : ℝ := if m % d = a % d then Λ m else 0

lemma sum_Icc_one_eq_range (f : ℕ → ℝ) (h0 : f 0 = 0) (n : ℕ) :
    ∑ m ∈ Icc 1 n, f m = ∑ m ∈ range (n + 1), f m := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ _ (n + 1)]

lemma sum_Ioc_zero_eq_range (f : ℕ → ℝ) (h0 : f 0 = 0) (n : ℕ) :
    ∑ m ∈ Ioc 0 n, f m = ∑ m ∈ range (n + 1), f m := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [sum_Ioc_succ_top (by omega), ih, sum_range_succ _ (n + 1)]

lemma psi_eq_sum_gfun (d a j : ℕ) :
    HeathBrown1985.psi (j : ℝ) d a = ∑ m ∈ range (j + 1), gfun d a m := by
  unfold HeathBrown1985.psi
  rw [Nat.floor_natCast, sum_filter]
  exact sum_Icc_one_eq_range (gfun d a) (by simp [gfun]) j

/-- The prime sum `T = Σ_{p ≤ n, p ≡ a} log p (n - p)^2`. -/
lemma T_le_W (d a n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d), Real.log p * ((n : ℝ) - p) ^ 2
      ≤ ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ 2 := by
  rw [sum_filter]
  refine sum_le_sum fun m _ => ?_
  split_ifs with h
  · simp [gfun, h.2, ArithmeticFunction.vonMangoldt_apply_prime h.1]
  · unfold gfun; split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)
    · simp

lemma W_sub_T_le (d a n : ℕ) :
    ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ 2
      - ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
          Real.log p * ((n : ℝ) - p) ^ 2
      ≤ (n : ℝ) ^ 2 * (Chebyshev.psi n - Chebyshev.theta n) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter,
    sum_filter, sum_Ioc_zero_eq_range _ (by simp), mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun m hm => ?_
  have hm' : (m : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hm)
  have hsq : ((n : ℝ) - m) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  by_cases hp : m.Prime
  · by_cases hc : m % d = a % d
    · simp [gfun, hp, hc, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [gfun, hp, hc]
  · simp only [hp, false_and, ite_false, sub_zero, not_false_eq_true, ite_true]
    unfold gfun; split_ifs
    · rw [mul_comm ((n : ℝ) ^ 2)]; exact mul_le_mul_of_nonneg_left hsq hΛ
    · rw [zero_mul]; exact mul_nonneg (sq_nonneg _) hΛ

lemma T_nonneg (d a n : ℕ) :
    0 ≤ ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
      Real.log p * ((n : ℝ) - p) ^ 2 := by
  refine sum_nonneg fun p hp => mul_nonneg (Real.log_natCast_nonneg p) (sq_nonneg _)

lemma T_le_LS (d a n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
      Real.log p * ((n : ℝ) - p) ^ 2 ≤
    Real.log n * ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
      ((n : ℝ) - p) ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  rw [mem_filter, mem_range] at hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
  have hpn : (p : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 hp.1
  exact mul_le_mul_of_nonneg_right (Real.log_le_log hp0 hpn) (sq_nonneg _)

lemma LS_le_T (d a n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη1 : η < 1) :
    (1 - η) * (Real.log n * ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
      ((n : ℝ) - p) ^ 2 - Real.log n * (n : ℝ) ^ 2 * ((n : ℝ) ^ (1 - η) + 1)) ≤
    ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
      Real.log p * ((n : ℝ) - p) ^ 2 := by
  set P := (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d) with hP
  set t : ℝ := (n : ℝ) ^ (1 - η) with ht
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN _
  have hlogt : Real.log t = (1 - η) * Real.log n := Real.log_rpow hN _
  rw [← sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) < t)]
  set Ps := P.filter (fun p : ℕ => (p : ℝ) < t)
  set Pb := P.filter (fun p : ℕ => ¬ (p : ℝ) < t)
  have hsmall : ∑ p ∈ Ps, ((n : ℝ) - p) ^ 2 ≤ (n : ℝ) ^ 2 * (t + 1) := by
    have h1 : ∑ p ∈ Ps, ((n : ℝ) - p) ^ 2 ≤ Ps.card • ((n : ℝ) ^ 2) := by
      refine sum_le_card_nsmul _ _ _ fun p hp => ?_
      have hp' := (mem_filter.1 (mem_filter.1 hp).1).1
      have hpn : (p : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hp')
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      nlinarith
    have h2 : Ps.card ≤ ⌈t⌉₊ := by
      calc Ps.card ≤ (range ⌈t⌉₊).card := by
            refine card_le_card fun p hp => ?_
            exact mem_range.2 (Nat.lt_ceil.2 (mem_filter.1 hp).2)
        _ = ⌈t⌉₊ := card_range _
    have h3 : (Ps.card : ℝ) ≤ t + 1 :=
      le_trans (by exact_mod_cast h2) (Nat.ceil_lt_add_one ht0.le).le
    rw [nsmul_eq_mul] at h1
    nlinarith [sq_nonneg (n : ℝ)]
  have hbig : (1 - η) * Real.log n * ∑ p ∈ Pb, ((n : ℝ) - p) ^ 2 ≤
      ∑ p ∈ P, Real.log p * ((n : ℝ) - p) ^ 2 := by
    rw [mul_sum]
    refine le_trans (sum_le_sum fun p hp => ?_) (sum_le_sum_of_subset_of_nonneg
      (filter_subset _ P) fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (sq_nonneg _))
    have htp : t ≤ p := not_lt.1 (mem_filter.1 hp).2
    have : (1 - η) * Real.log n ≤ Real.log p := hlogt ▸ Real.log_le_log ht0 htp
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h1η : 0 < 1 - η := by linarith
  have := mul_le_mul_of_nonneg_left hsmall hL
  have := mul_le_mul_of_nonneg_left this h1η.le
  nlinarith

lemma eventually_log_le (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * (n : ℝ) ^ r := by
  have h := ((isLittleO_log_rpow_atTop hr).def hc).and (eventually_ge_atTop (1 : ℝ))
  refine (tendsto_natCast_atTop_atTop.eventually h).mono fun n hn => ?_
  obtain ⟨h1, h2⟩ := hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at h1
  exact (le_abs_self _).trans h1

lemma psi_ap_eventually (d a : ℕ) (hd : 1 ≤ d) (ha : Nat.Coprime a d) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ j : ℕ in atTop,
      |HeathBrown1985.psi (j : ℝ) d a - (j : ℝ) / (Nat.totient d : ℝ)| ≤ δ * j := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.PsiChi.siegelWalfisz 1 one_pos
  have hlim : Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x))) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
      (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
    have h2 := tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    refine h2.congr fun x => ?_
    simp [neg_mul]
  have hpos : 0 < δ / (|K| + 1) := by positivity
  have h := ((hlim.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop (2 : ℝ))).and
    (tendsto_log_atTop.eventually_ge_atTop (d : ℝ))
  refine (tendsto_natCast_atTop_atTop.eventually h).mono fun j hj => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hj
  have := hK j h2 d a hd ha (by rwa [Real.rpow_one])
  refine this.trans ?_
  set E := Real.exp (-c * Real.sqrt (Real.log j))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h4 : (|K| + 1) * E ≤ δ := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |K| + 1)).1 h1
    linarith
  have h5 : K * E ≤ (|K| + 1) * E := mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hE
  have : K * E ≤ δ := h5.trans h4
  calc K * (j : ℝ) * E = (K * E) * j := by ring
    _ ≤ δ * j := mul_le_mul_of_nonneg_right this hj0

lemma exists_B (e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ᶠ j : ℕ in atTop, |e j| ≤ δ * j) :
    ∃ B, 0 ≤ B ∧ ∀ j, |e j| ≤ B + δ * j := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 h
  refine ⟨∑ j ∈ range J, |e j|, sum_nonneg fun _ _ => abs_nonneg _, fun j => ?_⟩
  have hδj : 0 ≤ δ * j := mul_nonneg hδ (Nat.cast_nonneg j)
  have hB : 0 ≤ ∑ j ∈ range J, |e j| := sum_nonneg fun _ _ => abs_nonneg _
  by_cases hj : j < J
  · have := single_le_sum (f := fun j => |e j|) (fun _ _ => abs_nonneg _) (mem_range.2 hj)
    linarith
  · have := hJ j (not_lt.1 hj); linarith

/-- The weighted sum `W` against the main term. -/
lemma W_approx (d a : ℕ) (B δ : ℝ)
    (hB : ∀ j : ℕ, |HeathBrown1985.psi (j : ℝ) d a - (j : ℝ) / (Nat.totient d : ℝ)| ≤ B + δ * j)
    (n : ℕ) :
    |∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ 2
      - ((n : ℝ) * (n - 1) * (2 * n - 1) / 6) / (Nat.totient d : ℝ)| ≤
      B * (n : ℝ) ^ 2 + δ * ((n : ℝ) * (n - 1) * (2 * n - 1) / 6) := by
  rw [sum_mul_sub_sq, ← sum_jw, sum_div, ← sum_sub_distrib]
  have := abs_sum_err_le (fun j => HeathBrown1985.psi (j : ℝ) d a - (j : ℝ) / (Nat.totient d : ℝ))
    B δ hB n
  convert this using 3 with j _
  all_goals first | exact sum_jw n | (rw [psi_eq_sum_gfun]; ring)

lemma ap_sum_sq_eventually (d : ℕ) (hd : 1 ≤ d) (a : ℕ) (ha : Nat.Coprime a d) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
    |∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d), ((n : ℝ) - p) ^ 2
      - (n : ℝ) ^ 3 / (3 * (Nat.totient d : ℝ) * Real.log n)| ≤ ε * (n : ℝ) ^ 3 / Real.log n := by
  set δ := ε / 10 with hδdef
  have hδ : 0 < δ := by positivity
  set η := min (1 / 2 : ℝ) (ε / 4) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη12 : η ≤ 1 / 2 := min_le_left _ _
  have hηε : η ≤ ε / 4 := min_le_right _ _
  obtain ⟨B, hB0, hB⟩ := exists_B _ δ hδ.le (psi_ap_eventually d a hd ha δ hδ)
  have hφ : (1 : ℝ) ≤ Nat.totient d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.2 (by omega)).ne'
  filter_upwards [eventually_log_le (δ / 2) (1 / 2) (by positivity) (by norm_num),
    eventually_log_le (δ / 2) η (by positivity) hη0,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (B / δ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / (2 * δ)),
    eventually_ge_atTop 2] with n h1 h2 h3 h4 h5
  -- the ingredients
  have hWM := W_approx d a B δ hB n
  have hTW := T_le_W d a n
  have hT0 := T_nonneg d a n
  have hWT := W_sub_T_le d a n
  have hTLS := T_le_LS d a n
  have hLST := LS_le_T d a n (by omega) η (by linarith)
  set N : ℝ := (n : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast h5
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  set φ : ℝ := (Nat.totient d : ℝ) with hφdef
  set S := ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
    ((n : ℝ) - p) ^ 2 with hSdef
  set T := ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
    Real.log p * ((n : ℝ) - p) ^ 2 with hTdef
  set W := ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ 2 with hWdef
  set M := N * (N - 1) * (2 * N - 1) / 6 with hMdef
  set F := N ^ 3 / (3 * φ) with hFdef
  set t := N ^ (1 - η) with htdef
  have hps : Chebyshev.psi N - Chebyshev.theta N ≤ δ * N := by
    refine (Chebyshev.psi_sub_theta_le (by linarith)).trans ?_
    rw [← Real.sqrt_eq_rpow] at h1
    have hs := Real.mul_self_sqrt hN0.le
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt N)
    nlinarith
  have hWT' : W - T ≤ δ * N ^ 3 := by
    have := mul_le_mul_of_nonneg_left hps (sq_nonneg N)
    nlinarith
  have hLt : L * N ^ 2 * (t + 1) ≤ δ * N ^ 3 := by
    have e1 : N ^ η * t = N := by
      rw [htdef, ← Real.rpow_add hN0]; simp
    have e2 : N ^ η ≤ N := by
      calc N ^ η ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = N := Real.rpow_one N
    have ht0 : 0 ≤ t := Real.rpow_nonneg hN0.le _
    have : L * (t + 1) ≤ δ * N := by
      have := mul_le_mul_of_nonneg_right h2 ht0
      have := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ δ / 2)
      have e1' : δ / 2 * N ^ η * t = δ / 2 * N := by rw [mul_assoc, e1]
      linarith
    calc L * N ^ 2 * (t + 1) = L * (t + 1) * N ^ 2 := by ring
      _ ≤ δ * N * N ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg N)
      _ = δ * N ^ 3 := by ring
  have hBN : B * N ^ 2 ≤ δ * N ^ 3 := by
    have : B ≤ δ * N := by rwa [div_le_iff₀ hδ, mul_comm] at h3
    have := mul_le_mul_of_nonneg_right this (sq_nonneg N)
    linarith
  have hhalf : N ^ 2 / 2 ≤ δ * N ^ 3 := by
    have : 1 ≤ 2 * δ * N := by rwa [div_le_iff₀ (by positivity), mul_comm] at h4
    have := mul_le_mul_of_nonneg_right this (sq_nonneg N)
    linarith
  have hMeq : M = N ^ 3 / 3 - N ^ 2 / 2 + N / 6 := by simp only [hMdef]; ring
  have hNN : N * 2 ≤ N * N := mul_le_mul_of_nonneg_left hN2 hN0.le
  have hNN2 : N ^ 2 * 2 ≤ N ^ 2 * N := mul_le_mul_of_nonneg_left hN2 (sq_nonneg N)
  have hMu : M ≤ N ^ 3 / 3 := by
    rw [hMeq]; have : N ^ 2 = N * N := by ring
    have : N ^ 3 = N ^ 2 * N := by ring
    linarith
  have hMl : N ^ 3 / 3 - N ^ 2 / 2 ≤ M := by
    rw [hMeq]; linarith
  have hM0 : 0 ≤ M := by
    have : N ^ 3 = N ^ 2 * N := by ring
    have : 0 ≤ N ^ 2 := sq_nonneg N
    linarith
  have hMφu : M / φ ≤ F := by
    rw [hFdef, show N ^ 3 / (3 * φ) = (N ^ 3 / 3) / φ by ring]
    exact div_le_div_of_nonneg_right hMu (by linarith)
  have hMφl : F - N ^ 2 / 2 ≤ M / φ := by
    have a1 : (N ^ 3 / 3 - N ^ 2 / 2) / φ ≤ M / φ := div_le_div_of_nonneg_right hMl (by linarith)
    have a2 : (N ^ 2 / 2) / φ ≤ N ^ 2 / 2 := div_le_self (by positivity) hφ
    have a3 : (N ^ 3 / 3 - N ^ 2 / 2) / φ = F - (N ^ 2 / 2) / φ := by
      rw [hFdef, sub_div, div_div]
    linarith
  have hF : F ≤ N ^ 3 / 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hF0 : 0 ≤ F := by positivity
  have hδM : δ * M ≤ δ * (N ^ 3 / 3) := mul_le_mul_of_nonneg_left hMu hδ.le
  have hWa := (abs_le.1 hWM)
  -- lower bound
  have hlow : F - ε * N ^ 3 ≤ L * S := by
    have hδN : δ * N ^ 3 = ε / 10 * N ^ 3 := by rw [hδdef]
    linarith [hWa.1]
  -- upper bound
  have hW0 : 0 ≤ W := hT0.trans hTW
  set X := L * S - L * N ^ 2 * (t + 1) with hXdef
  have hX : X ≤ (1 + 2 * η) * W := by
    have hXW : (1 - η) * X ≤ W := hLST.trans hTW
    by_cases hXs : X ≤ 0
    · have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 * η) hW0
      linarith
    · push Not at hXs
      have h12 : 0 ≤ 1 - 2 * η := by linarith
      have := mul_nonneg (mul_nonneg hη0.le h12) hXs.le
      have := mul_le_mul_of_nonneg_left hXW (by linarith : (0 : ℝ) ≤ 1 + 2 * η)
      linarith
  have hWu : W ≤ F + (4 / 3) * δ * N ^ 3 := by linarith
  have hup : L * S ≤ F + ε * N ^ 3 := by
    have a1 := mul_le_mul_of_nonneg_left hWu (by linarith : (0 : ℝ) ≤ 1 + 2 * η)
    have a2 : η * F ≤ η * (N ^ 3 / 3) := mul_le_mul_of_nonneg_left hF hη0.le
    have a3 : η * (δ * N ^ 3) ≤ (1 / 2) * (δ * N ^ 3) :=
      mul_le_mul_of_nonneg_right hη12 (by positivity)
    have a4 : η * N ^ 3 ≤ (ε / 4) * N ^ 3 := mul_le_mul_of_nonneg_right hηε (by positivity)
    have hδN : δ * N ^ 3 = ε / 10 * N ^ 3 := by rw [hδdef]
    linarith
  have hkey : |L * S - F| ≤ ε * N ^ 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have : S - N ^ 3 / (3 * φ * L) = (L * S - F) / L := by
    rw [hFdef]; field_simp
  rw [this, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right hkey hL.le

theorem ap_sum_sq : ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a : ℕ,
    Nat.Coprime a d →
    |∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d), ((n : ℝ) - p) ^ 2
      - (n : ℝ) ^ 3 / (3 * (Nat.totient d : ℝ) * Real.log n)| ≤ ε * (n : ℝ) ^ 3 / Real.log n := by
  intro d hd ε hε
  have h : ∀ᶠ n : ℕ in atTop, ∀ r ∈ range d, Nat.Coprime r d →
      |∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = r % d), ((n : ℝ) - p) ^ 2
        - (n : ℝ) ^ 3 / (3 * (Nat.totient d : ℝ) * Real.log n)| ≤ ε * (n : ℝ) ^ 3 / Real.log n := by
    rw [eventually_all_finset]
    intro r _
    by_cases hr : Nat.Coprime r d
    · exact (ap_sum_sq_eventually d hd r hr ε hε).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n hn => absurd hn hr
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  refine ⟨n₀, fun n hn a ha => ?_⟩
  have hra : Nat.Coprime (a % d) d := by
    unfold Nat.Coprime; rw [← Nat.gcd_rec]; exact Nat.Coprime.symm ha
  have := hn₀ n hn (a % d) (mem_range.2 (Nat.mod_lt _ (by omega))) hra
  simpa only [Nat.mod_mod] using this

end LeanLab.HardyLittlewood1923

