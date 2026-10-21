module

public import LeanLab.HardyLittlewood1923.TheoremBRec
public import LeanLab.GoldbachAverage.OddSumPNT

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5903, paper P0004.

# Hardy-Littlewood 1923, the mean of `N_2(n) log² n`

`sum_N2_log_sq`: `Σ_{n ≤ N} N_2(n) log² n = N²/2 + o(N²)`, where `N_2(n)` is the number of
ordered pairs of primes with sum `n`, the `Nr 2` of TheoremC.lean.

Route: write `θ'(a) = log a` on primes and `0` otherwise. The convolution
`P(N) = Σ_{n ≤ N} Σ_{a ≤ n} θ'(a) θ'(n - a)` equals `Σ_{a ≤ N} θ'(a) θ(N - a)`, and by Abel
summation `Σ_{a ≤ N} θ'(a) (N - a) = Σ_{m < N} θ(m)`. The prime number theorem in the uniform
form `LeanLab.GoldbachAverage.psiN_uniform`, with Mathlib's `ψ - θ ≤ 2 √x log x`, gives
`θ(m) = m + o(N)` uniformly for `m ≤ N`, hence `P(N) = N²/2 + o(N²)`.
Each pair `p + q = n` has `log p log q ≤ log² n`, so the sum is at least `P(N)`. For the upper
bound, pairs with both primes at least `X = ⌈N^{1-δ}⌉` have
`(1 - δ)² log² n ≤ log p log q`, and the other pairs number at most `2 X` for each `n`, which
contributes `o(N²)` after the weight `log² N`.

Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

namespace FCount

/-- `log a` on primes, `0` otherwise. -/
noncomputable def th (a : ℕ) : ℝ := if a.Prime then Real.log a else 0

/-- `θ(m)` as a sum from `0`. -/
noncomputable def Th (m : ℕ) : ℝ := ∑ b ∈ range (m + 1), th b

/-- The prime pair convolution `Σ_{n ≤ N} Σ_{a ≤ n} θ'(a) θ'(n - a)`. -/
noncomputable def P (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), ∑ a ∈ range (n + 1), th a * th (n - a)

lemma th_nonneg (a : ℕ) : 0 ≤ th a := by
  unfold th; split_ifs
  · exact Real.log_natCast_nonneg a
  · rfl

lemma Th_eq (m : ℕ) : Th m = Chebyshev.theta m := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Th, Nat.range_succ_eq_Icc_zero, sum_filter]
  rfl

lemma log_nat_mono {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

lemma log_four_lt_two : Real.log 4 < 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_lt_d9
  linarith

lemma Th_le (N : ℕ) : Th N ≤ 2 * N := by
  rw [Th_eq]
  have := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) N)
  have := log_four_lt_two
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Swapping the order of a convolution sum. -/
lemma sum_conv (g : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range (N + 1), ∑ a ∈ range (n + 1), g a (n - a) =
      ∑ a ∈ range (N + 1), ∑ b ∈ range (N - a + 1), g a b := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : ∀ a ∈ range (N + 1), ∑ b ∈ range (N + 1 - a + 1), g a b
        = ∑ b ∈ range (N - a + 1), g a b + g a (N + 1 - a) := by
      intro a ha
      rw [mem_range] at ha
      rw [show N + 1 - a = N - a + 1 by omega, sum_range_succ]
    rw [sum_range_succ, ih, sum_range_succ (fun a => ∑ b ∈ range (N + 1 - a + 1), g a b),
      sum_congr rfl hstep, sum_add_distrib, sum_range_succ (fun a => g a (N + 1 - a))]
    simp only [Nat.sub_self, zero_add, sum_range_one]
    ring

/-- Abel summation: `Σ_{a ≤ N} f(a) (N - a) = Σ_{m < N} Σ_{b ≤ m} f(b)`. -/
lemma sum_mul_sub (f : ℕ → ℝ) (N : ℕ) :
    ∑ a ∈ range (N + 1), f a * ((N : ℝ) - a) = ∑ m ∈ range N, ∑ b ∈ range (m + 1), f b := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun m => ∑ b ∈ range (m + 1), f b), ← ih,
      sum_range_succ (fun a => f a * (((N + 1 : ℕ) : ℝ) - a))]
    push_cast
    rw [show ((N : ℝ) + 1 - (N + 1)) = 0 by ring, mul_zero, add_zero, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    ring

lemma sum_range_cast (N : ℕ) : ∑ m ∈ range N, (m : ℝ) = (N : ℝ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `θ(m) = m + o(N)` uniformly for `m ≤ N`. -/
lemma theta_uniform {η : ℝ} (hη : 0 < η) : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m ≤ N →
    |Th m - m| ≤ η * N := by
  obtain ⟨C, hC0, hC⟩ := LeanLab.GoldbachAverage.psiN_uniform
  have h1 : ∀ᶠ x : ℝ in atTop, 2 * C / η ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ η / 4 * x ^ (1 / 2 : ℝ) := by
    have := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show 0 < η / 4 by positivity)
    filter_upwards [this, eventually_ge_atTop 1] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by positivity)] at hx
    exact hx
  have h3 := tendsto_natCast_atTop_atTop.eventually (h1.and h2)
  filter_upwards [h3, eventually_ge_atTop 2] with N hN hN2 m hm
  obtain ⟨hN1, hNs⟩ := hN
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp [Th, th, Nat.not_prime_zero]; positivity
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hpsi := hC N hN2 m hm
  rw [LeanLab.GoldbachAverage.psiN_eq] at hpsi
  have hle := Chebyshev.theta_le_psi (m : ℝ)
  have hsub := Chebyshev.psi_sub_theta_le hm1'
  have hsq : √(m : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt hmN
  have hlm : Real.log m ≤ Real.log N := log_nat_mono hm
  have hlm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hB1 : 2 * √(m : ℝ) * Real.log m ≤ η / 2 * N := by
    have hs : √(N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hss : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hNpos.le
    have : 2 * √(m : ℝ) * Real.log m ≤ 2 * √(N : ℝ) * Real.log N := by
      have := mul_le_mul hsq hlm hlm0 (Real.sqrt_nonneg _)
      linarith
    rw [← hs] at hNs
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hB2 : C * N / Real.log N ≤ η / 2 * N := by
    rw [div_le_iff₀ hlN]
    have : 2 * C ≤ η * Real.log N := by
      rw [div_le_iff₀ hη] at hN1; linarith
    nlinarith
  rw [Th_eq]
  rw [abs_le] at hpsi ⊢
  constructor <;> linarith [hpsi.1, hpsi.2]

lemma P_eq (N : ℕ) : P N = ∑ a ∈ range (N + 1), th a * Th (N - a) := by
  have := sum_conv (fun a b => th a * th b) N
  rw [P, this]
  simp_rw [Th, mul_sum]

/-- `P(N) = N²/2 + o(N²)`. -/
lemma P_asymp {η : ℝ} (hη : 0 < η) : ∀ᶠ N : ℕ in atTop, |P N - (N : ℝ) ^ 2 / 2| ≤ η * N ^ 2 := by
  have hη' : 0 < η / 4 := by positivity
  filter_upwards [theta_uniform hη', tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / η)]
    with N hU hNl
  set e := η / 4 with he
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hE1 : |∑ a ∈ range (N + 1), th a * Th (N - a) -
      ∑ a ∈ range (N + 1), th a * ((N : ℝ) - a)| ≤ Th N * (e * N) := by
    rw [← sum_sub_distrib, Th, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a ha => ?_)
    rw [mem_range] at ha
    rw [← mul_sub, abs_mul, abs_of_nonneg (th_nonneg a)]
    apply mul_le_mul_of_nonneg_left _ (th_nonneg a)
    have := hU (N - a) (Nat.sub_le N a)
    rwa [Nat.cast_sub (by omega : a ≤ N)] at this
  have hE2 : |∑ m ∈ range N, Th m - ∑ m ∈ range N, (m : ℝ)| ≤ N * (e * N) := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ range N, |Th m - m| ≤ ∑ _m ∈ range N, e * N :=
          sum_le_sum fun m hm => hU m (by rw [mem_range] at hm; omega)
      _ = N * (e * N) := by simp
  have hAbel : ∑ a ∈ range (N + 1), th a * ((N : ℝ) - a) = ∑ m ∈ range N, Th m :=
    sum_mul_sub th N
  rw [hAbel] at hE1
  rw [sum_range_cast] at hE2
  rw [P_eq]
  have hThN := Th_le N
  have hTh0 : 0 ≤ Th N := by rw [Th]; exact sum_nonneg fun b _ => th_nonneg b
  have hNl' : 2 ≤ η * N := by rwa [div_le_iff₀ hη, mul_comm] at hNl
  have h1 : Th N * (e * N) ≤ 2 * e * N ^ 2 := by
    have := mul_le_mul_of_nonneg_right hThN (by positivity : 0 ≤ e * N)
    nlinarith
  have h2 : (N : ℝ) / 2 ≤ e * N ^ 2 := by
    rw [he]; nlinarith
  rw [abs_le] at hE1 hE2 ⊢
  constructor <;> nlinarith [hE1.1, hE1.2, hE2.1, hE2.2]

/-- Pairs `(p, n - p)` of primes. -/
lemma sum_S2 (n : ℕ) (h : ℕ → ℕ → ℝ) :
    ∑ t ∈ Sr 2 n, h (t 0) (t 1) =
      ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime), h p (n - p) := by
  refine Finset.sum_nbij' (fun t => t 0) (fun p => ![p, n - p]) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_Sr, Fin.sum_univ_two] at ht
    obtain ⟨h1, h2, h3⟩ := ht
    simp only [mem_filter, mem_range]
    refine ⟨h1 0, h2 0, ?_⟩
    rw [show n - t 0 = t 1 by omega]; exact h2 1
  · intro p hp
    simp only [mem_filter, mem_range] at hp
    rw [mem_Sr]
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · fin_cases i
      · simpa using hp.1
      · simp
    · fin_cases i
      · simpa using hp.2.1
      · simpa using hp.2.2
    · simp [Fin.sum_univ_two]; omega
  · intro t ht
    simp only [mem_Sr, Fin.sum_univ_two] at ht
    ext i; fin_cases i
    · simp
    · simp; omega
  · intro p _; simp
  · intro t ht
    simp only [mem_Sr, Fin.sum_univ_two] at ht
    rw [show n - t 0 = t 1 by omega]

lemma Nr2_eq (n : ℕ) : (Nr 2 n : ℝ) * Real.log n ^ 2 =
    ∑ p ∈ range (n + 1), if p.Prime ∧ (n - p).Prime then Real.log n ^ 2 else 0 := by
  rw [← sum_filter, Nr_eq, Finset.cast_card, sum_mul, one_mul]
  exact sum_S2 n (fun _ _ => Real.log n ^ 2)

/-- Lower bound, row by row. -/
lemma row_lower (n : ℕ) :
    ∑ p ∈ range (n + 1), th p * th (n - p) ≤ (Nr 2 n : ℝ) * Real.log n ^ 2 := by
  rw [Nr2_eq]
  apply sum_le_sum
  intro p hp
  rw [mem_range] at hp
  by_cases hpr : p.Prime ∧ (n - p).Prime
  · rw [if_pos hpr, th, th, if_pos hpr.1, if_pos hpr.2, sq]
    exact mul_le_mul (log_nat_mono (by omega)) (log_nat_mono (by omega))
      (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · rw [if_neg hpr]
    unfold th
    rcases not_and_or.1 hpr with h | h <;> simp [h]

/-- Upper bound, pair by pair. -/
lemma pt_upper {N n p X : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hn : n ≤ N)
    (hlX : (1 - δ) * Real.log N ≤ Real.log X) :
    (1 - δ) ^ 2 * (if p.Prime ∧ (n - p).Prime then Real.log n ^ 2 else 0) ≤
      th p * th (n - p) + Real.log N ^ 2 *
        ((if p < X then 1 else 0) + (if n - p < X then 1 else 0)) := by
  have hln : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlnN : Real.log n ≤ Real.log N := log_nat_mono hn
  have hthp := th_nonneg p
  have hthq := th_nonneg (n - p)
  have hI1 : (0 : ℝ) ≤ if p < X then 1 else 0 := by split_ifs <;> norm_num
  have hI2 : (0 : ℝ) ≤ if n - p < X then 1 else 0 := by split_ifs <;> norm_num
  have hLN : 0 ≤ Real.log N ^ 2 := sq_nonneg _
  have hd : (1 - δ) ^ 2 ≤ 1 := by nlinarith
  have hsq : Real.log n ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ hln hlnN 2
  by_cases hpr : p.Prime ∧ (n - p).Prime
  · rw [if_pos hpr]
    have hb : (1 - δ) ^ 2 * Real.log n ^ 2 ≤ Real.log N ^ 2 := by nlinarith
    by_cases hpX : p < X
    · rw [if_pos hpX]; nlinarith
    by_cases hqX : n - p < X
    · rw [if_pos hqX]; nlinarith
    rw [if_neg hpX, if_neg hqX, th, th, if_pos hpr.1, if_pos hpr.2]
    have hXp : Real.log X ≤ Real.log p := log_nat_mono (by omega)
    have hXq : Real.log X ≤ Real.log (n - p : ℕ) := log_nat_mono (by omega)
    have ha : 0 ≤ (1 - δ) * Real.log n := mul_nonneg (by linarith) hln
    have hb1 : (1 - δ) * Real.log n ≤ (1 - δ) * Real.log N :=
      mul_le_mul_of_nonneg_left hlnN (by linarith)
    have hm := mul_le_mul (hb1.trans (hlX.trans hXp)) (hb1.trans (hlX.trans hXq)) ha
      (Real.log_natCast_nonneg _)
    nlinarith
  · rw [if_neg hpr, mul_zero]
    positivity

lemma card_lt_le (n X : ℕ) :
    ∑ p ∈ range (n + 1), (if p < X then (1 : ℝ) else 0) ≤ X := by
  rw [sum_boole]
  have : #((range (n + 1)).filter (fun p => p < X)) ≤ #(range X) := by
    apply card_le_card
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact hp.2
  rw [card_range] at this
  exact_mod_cast this

lemma card_sub_lt_le (n X : ℕ) :
    ∑ p ∈ range (n + 1), (if n - p < X then (1 : ℝ) else 0) ≤ X := by
  rw [sum_boole]
  have : #((range (n + 1)).filter (fun p => n - p < X)) ≤ #(range X) := by
    apply card_le_card_of_injOn (fun p => n - p)
    · intro p hp
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_coe] at hp ⊢
      exact hp.2
    · intro a ha b hb hab
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
      simp only at hab
      omega
  rw [card_range] at this
  exact_mod_cast this

lemma row_upper {N n X : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hn : n ≤ N)
    (hlX : (1 - δ) * Real.log N ≤ Real.log X) :
    (1 - δ) ^ 2 * ((Nr 2 n : ℝ) * Real.log n ^ 2) ≤
      ∑ p ∈ range (n + 1), th p * th (n - p) + Real.log N ^ 2 * (2 * X) := by
  rw [Nr2_eq, mul_sum]
  calc _ ≤ ∑ p ∈ range (n + 1), (th p * th (n - p) + Real.log N ^ 2 *
          ((if p < X then 1 else 0) + (if n - p < X then 1 else 0))) :=
        sum_le_sum fun p _ => pt_upper hδ0 hδ1 hn hlX
    _ = ∑ p ∈ range (n + 1), th p * th (n - p) + Real.log N ^ 2 *
          (∑ p ∈ range (n + 1), (if p < X then (1 : ℝ) else 0) +
            ∑ p ∈ range (n + 1), (if n - p < X then (1 : ℝ) else 0)) := by
        rw [sum_add_distrib, ← mul_sum, sum_add_distrib]
    _ ≤ _ := by
        have := card_lt_le n X
        have := card_sub_lt_le n X
        have hLN : 0 ≤ Real.log N ^ 2 := sq_nonneg _
        nlinarith

/-- The threshold `X = ⌈N^{1-δ}⌉`. -/
lemma exists_X {η δ : ℝ} (hη : 0 < η) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ N : ℕ in atTop, ∃ X : ℕ, 1 ≤ X ∧ (X : ℝ) * Real.log N ^ 2 ≤ η * N ∧
      (1 - δ) * Real.log N ≤ Real.log X := by
  set c := min 1 (η / 2) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hc2 : c ≤ η / 2 := min_le_right _ _
  have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x ^ (δ / 2) := by
    have := (isLittleO_log_rpow_atTop (show 0 < δ / 2 by positivity)).bound hc0
    filter_upwards [this, eventually_ge_atTop 1] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by positivity)] at hx
    exact hx
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h2, eventually_ge_atTop 1]
    with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  set Y := (N : ℝ) ^ (1 - δ) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1' (by linarith)
  have hYc : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  have hYc2 : (⌈Y⌉₊ : ℝ) < Y + 1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨⌈Y⌉₊, ?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ ⌈Y⌉₊ := hY1.trans hYc
    exact_mod_cast this
  · have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN1'
    have hsq : Real.log N ^ 2 ≤ c ^ 2 * (N : ℝ) ^ δ := by
      have := pow_le_pow_left₀ hl0 hN 2
      have hpow : ((N : ℝ) ^ (δ / 2)) ^ 2 = (N : ℝ) ^ δ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
      rwa [mul_pow, hpow] at this
    have hYN : Y * (N : ℝ) ^ δ = N := by
      rw [hY, ← Real.rpow_add hNpos]; simp
    have hpos : 0 ≤ (N : ℝ) ^ δ := by positivity
    have hcc : 2 * c ^ 2 ≤ η := by nlinarith
    calc (⌈Y⌉₊ : ℝ) * Real.log N ^ 2 ≤ (2 * Y) * (c ^ 2 * (N : ℝ) ^ δ) :=
          mul_le_mul (by linarith) hsq (sq_nonneg _) (by linarith)
      _ = 2 * c ^ 2 * (Y * (N : ℝ) ^ δ) := by ring
      _ ≤ η * N := by rw [hYN]; exact mul_le_mul_of_nonneg_right hcc hNpos.le
  · calc (1 - δ) * Real.log N = Real.log Y := by rw [hY, Real.log_rpow hNpos]
      _ ≤ Real.log ⌈Y⌉₊ := Real.log_le_log (by linarith) hYc

end FCount

open FCount in
/-- `Σ_{n ≤ N} N_2(n) log² n = N²/2 + o(N²)`. -/
theorem sum_N2_log_sq : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |∑ n ∈ Finset.range (N + 1), (Nr 2 n : ℝ) * Real.log n ^ 2 - (N : ℝ) ^ 2 / 2| ≤
      ε * (N : ℝ) ^ 2 := by
  intro ε hε
  set η := ε / 20 with hη
  set δ := ε / (8 * (1 + ε)) with hδ
  have hηpos : 0 < η := by positivity
  have hδpos : 0 < δ := by positivity
  have hδ8 : δ * (8 * (1 + ε)) = ε := by rw [hδ]; field_simp
  have hδ1 : δ < 1 := by nlinarith
  have hδε : 2 * δ * (1 / 2 + ε) ≤ ε / 4 := by nlinarith
  have hev := (P_asymp hηpos).and ((exists_X hηpos hδpos hδ1).and (eventually_ge_atTop 1))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hP, ⟨X, -, hXl, hlX⟩, hN1⟩ := hN₀ N hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set S := ∑ n ∈ Finset.range (N + 1), (Nr 2 n : ℝ) * Real.log n ^ 2 with hS
  have hlow : P N ≤ S := sum_le_sum fun n _ => row_lower n
  have hup : (1 - δ) ^ 2 * S ≤ P N + (N + 1) * (Real.log N ^ 2 * (2 * X)) := by
    rw [hS, mul_sum]
    calc _ ≤ ∑ n ∈ range (N + 1), (∑ p ∈ range (n + 1), th p * th (n - p) +
            Real.log N ^ 2 * (2 * X)) :=
          sum_le_sum fun n hn => row_upper hδpos.le hδ1.le
            (by rw [mem_range] at hn; omega) hlX
      _ = _ := by rw [sum_add_distrib, P]; simp
  have hP0 : 0 ≤ P N :=
    sum_nonneg fun n _ => sum_nonneg fun a _ => mul_nonneg (th_nonneg a) (th_nonneg _)
  have hS0 : 0 ≤ S := hP0.trans hlow
  have hErr : (N + 1 : ℝ) * (Real.log N ^ 2 * (2 * X)) ≤ 4 * η * N ^ 2 := by
    have : (N + 1 : ℝ) ≤ 2 * N := by linarith
    have h0 : 0 ≤ (X : ℝ) * Real.log N ^ 2 := by positivity
    nlinarith
  rw [abs_le] at hP ⊢
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · have h1 : (1 - 2 * δ) * S ≤ (1 - δ) ^ 2 * S := by nlinarith [sq_nonneg δ]
    by_contra hcon
    rw [not_le] at hcon
    have h12 : 0 < 1 - 2 * δ := by nlinarith
    have := mul_lt_mul_of_pos_left hcon h12
    nlinarith
end LeanLab.HardyLittlewood1923

