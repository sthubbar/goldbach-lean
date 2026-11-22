module

public import LeanLab.Song2020.Characteristic139

/-!
AI wrote the Lean code, 2026-11-15, toward the step s1_lambda_reduction.
Source: Yanbo Song, arXiv 2012.06322 v1, printed page 5, from "For S1, we first observe" to
"We have shown so far".
This file holds the two generic steps of that passage, for an arbitrary complex weight:
the passage from the primes of the window to the von Mangoldt function, with the count of
the proper prime powers, and the discrete partial summation over the window against a
sequence whose sums over initial segments of the window are bounded. The window is written
out inline as the filter of Finset.range, exactly as in the target statement, since the
lab rules for this step allowed no new definition.
Binary Goldbach is open; nothing here changes that.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteS1Abel

open LeanLab.Song2020 LeanLab.Song2020.State1562

/-- Song 2020, page 5, the passage from primes to the von Mangoldt function: the quotient
Lambda(x) / log x lies between 0 and 1 at every natural number. It is 1 at a prime, 1/k at a
k-th prime power, and 0 elsewhere, also at x = 0 and x = 1 where Lean divides by zero to
zero. -/
theorem vonMangoldt_div_log_bounds (x : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) ∧
      ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) ≤ 1 := by
  constructor
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg x)
  · rcases Nat.lt_or_ge x 2 with h | h
    · have h0 : Real.log (x : ℝ) = 0 := by
        interval_cases x <;> simp
      rw [h0, div_zero]
      exact zero_le_one
    · have hpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast h)
      rw [div_le_one hpos]
      exact ArithmeticFunction.vonMangoldt_le_log

/-- Song 2020, page 5, the passage from primes to the von Mangoldt function over any finite
set of integers: the sum over its primes is the sum with the factor Lambda(x) / log x minus
the sum over its proper prime powers. -/
private theorem sum_filter_prime_eq (s : Finset ℕ) (F : ℕ → ℂ) :
    ∑ x ∈ s.filter (fun x : ℕ => x.Prime), F x =
      ∑ x ∈ s, ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * F x -
        ∑ x ∈ s.filter (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime),
          ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * F x := by
  have key : ∀ x : ℕ,
      ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * F x =
        (if x.Prime then F x else 0) + (if IsPrimePow x ∧ ¬ x.Prime then
          ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * F x else 0) := by
    intro x
    by_cases hp : x.Prime
    · have hlog : Real.log (x : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      have h1 : ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) = 1 := by
        rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hlog]
      rw [h1, if_pos hp, if_neg (fun h => h.2 hp)]
      simp
    · by_cases hq : IsPrimePow x
      · rw [if_neg hp, if_pos ⟨hq, hp⟩, zero_add]
      · have h0 : ArithmeticFunction.vonMangoldt x = 0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hq
        rw [if_neg hp, if_neg (fun h => hq h.1), h0]
        simp
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_congr rfl (fun x _ => key x),
    Finset.sum_add_distrib, add_sub_cancel_right]

/-- Song 2020, page 5, the passage from primes to the von Mangoldt function, as an identity:
a sum over the primes of the window is the sum over the whole window with the factor
Lambda(x) / log x, minus the same sum over the proper prime powers of the window. -/
theorem sum_windowPrimes_eq (n : ℕ) (y : ℝ) (F : ℕ → ℂ) :
    ∑ p ∈ windowPrimes n y, F p =
      ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
          ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * F x -
        ∑ x ∈ ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter
            (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime),
          ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * F x := by
  have hL : ∑ p ∈ windowPrimes n y, F p =
      ∑ x ∈ ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter (fun x : ℕ => x.Prime), F x := by
    rw [Finset.filter_filter]
    unfold windowPrimes
    exact Finset.sum_congr (Finset.filter_congr (fun x _ => and_comm)) (fun _ _ => rfl)
  rw [hL]
  exact sum_filter_prime_eq _ F

/-- Song 2020, page 5, the prime power error the paper absorbs in O(n^(3/2-gamma)): there are
at most 2 sqrt N proper prime powers up to N. A proper prime power p^k is m^2 with
m = p^(k/2) for even k, and minFac(m) m^2 with m = p^((k-1)/2) for odd k at least 3, and in
both cases m is at most sqrt N. -/
theorem card_properPrimePow_le (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime)).card ≤
      2 * Nat.sqrt N := by
  have hsub : ((Finset.range (N + 1)).filter (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime)) ⊆
      (Finset.Icc 1 (Nat.sqrt N)).image (fun m : ℕ => m ^ 2) ∪
        (Finset.Icc 1 (Nat.sqrt N)).image (fun m : ℕ => m.minFac * m ^ 2) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxN, hpp, hnp⟩ := hx
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff x).1 hpp
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hnp (by simpa using hp)
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · left
      subst hj
      have he : (p ^ j) ^ 2 = p ^ (2 * j) := by rw [← pow_mul, mul_comm]
      refine ⟨p ^ j, Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero), ?_⟩, he⟩
      rw [Nat.le_sqrt', he]
      omega
    · right
      subst hj
      have hj0 : j ≠ 0 := by omega
      have he : (p ^ j).minFac * (p ^ j) ^ 2 = p ^ (2 * j + 1) := by
        rw [hp.pow_minFac hj0, ← pow_mul, mul_comm j 2, pow_succ, mul_comm]
      refine ⟨p ^ j, Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero), ?_⟩, he⟩
      rw [Nat.le_sqrt']
      have h1 : (p ^ j) ^ 2 ≤ (p ^ j).minFac * (p ^ j) ^ 2 :=
        Nat.le_mul_of_pos_left _ (Nat.minFac_pos _)
      rw [he] at h1
      omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 := Finset.card_image_le (s := Finset.Icc 1 (Nat.sqrt N)) (f := fun m : ℕ => m ^ 2)
  have h2 := Finset.card_image_le (s := Finset.Icc 1 (Nat.sqrt N))
    (f := fun m : ℕ => m.minFac * m ^ 2)
  rw [Nat.card_Icc] at h1 h2
  omega

/-- Song 2020, page 5, the window |x - n/3| < y with y at most n/3 holds only integers
between 1 and n. -/
theorem window_mem_bounds (n : ℕ) (y : ℝ) (hy : y ≤ (n : ℝ) / 3) (x : ℕ)
    (hx : x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)) :
    1 ≤ x ∧ x ≤ n := by
  rw [Finset.mem_filter] at hx
  obtain ⟨_, hx⟩ := hx
  rw [abs_lt] at hx
  obtain ⟨h1, h2⟩ := hx
  constructor
  · have h3 : (0 : ℝ) < (x : ℝ) := by linarith
    exact Nat.succ_le_of_lt (by exact_mod_cast h3)
  · have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 : (x : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast h3

/-- Song 2020, page 5, the window |x - n/3| < y is a block of consecutive integers. -/
theorem window_eq_Ico (n : ℕ) (y : ℝ) :
    ∃ a b : ℕ, (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y) = Finset.Ico a b := by
  by_cases h0 : 0 ≤ (n : ℝ) / 3 - y
  · refine ⟨Nat.floor ((n : ℝ) / 3 - y) + 1, Nat.ceil ((n : ℝ) / 3 + y), ?_⟩
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, abs_lt]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨Nat.succ_le_of_lt ((Nat.floor_lt h0).2 (by linarith)), Nat.lt_ceil.2 (by linarith)⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.floor_lt h0).1 (Nat.lt_of_succ_le h1)
      have h4 := Nat.lt_ceil.1 h2
      exact ⟨by omega, by linarith, by linarith⟩
  · refine ⟨0, Nat.ceil ((n : ℝ) / 3 + y), ?_⟩
    rw [not_le] at h0
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, abs_lt]
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨Nat.zero_le _, Nat.lt_ceil.2 (by linarith)⟩
    · rintro ⟨_, h2⟩
      have h4 := Nat.lt_ceil.1 h2
      exact ⟨by omega, by linarith, by linarith⟩

/-- Song 2020, page 5, the error of the passage from primes to the von Mangoldt function:
with a factor F of modulus at most P, the proper prime powers of the window contribute at
most 2 P n^(1/2). -/
theorem norm_sum_properPrimePow_le (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : y ≤ (n : ℝ) / 3)
    (F : ℕ → ℂ) (P : ℝ) (hF : ∀ x : ℕ, ‖F x‖ ≤ P) :
    ‖∑ x ∈ ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter
            (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime),
          ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * F x‖ ≤
      2 * P * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hF 0)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ P ?_).trans ?_
  · intro x _
    obtain ⟨h0, h1⟩ := vonMangoldt_div_log_bounds x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    calc ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) * ‖F x‖
        ≤ 1 * P := mul_le_mul h1 (hF x) (norm_nonneg _) zero_le_one
      _ = P := one_mul P
  rw [nsmul_eq_mul]
  have hcard : (((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime)).card ≤ 2 * Nat.sqrt n := by
    refine (Finset.card_le_card ?_).trans (card_properPrimePow_le n)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (window_mem_bounds n y hy x hx.1).2), hx.2⟩
  have hsq : ((Nat.sqrt n : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.nat_sqrt_le_real_sqrt
  have hc : (((((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime)).card : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : (((((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime)).card : ℕ) : ℝ) ≤
        ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at h1
    linarith
  calc (((((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter (fun x : ℕ => IsPrimePow x ∧ ¬ x.Prime)).card : ℕ) : ℝ) * P
      ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 2)) * P := mul_le_mul_of_nonneg_right hc hP0
    _ = 2 * P * (n : ℝ) ^ ((1 : ℝ) / 2) := by ring

/-- Song 2020, page 5, "by partial summation", the summation by parts identity over a block
of consecutive integers from a to b inclusive. -/
private theorem sum_Ico_by_parts (w c : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a (b + 1), w x * c x =
      w b * ∑ x ∈ Finset.Ico a (b + 1), c x -
        ∑ x ∈ Finset.Ico a b, (w (x + 1) - w x) * ∑ z ∈ Finset.Ico a (x + 1), c z := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top (by omega : a ≤ b + 1) (fun x => w x * c x), ih,
      Finset.sum_Ico_succ_top (by omega : a ≤ b + 1) c,
      Finset.sum_Ico_succ_top hab
        (fun x => (w (x + 1) - w x) * ∑ z ∈ Finset.Ico a (x + 1), c z)]
    ring

/-- Song 2020, page 5, "by partial summation", over a block of consecutive integers: if the
sums of c over the initial segments Ico a m, m at most b, are at most B in modulus, then the
sum of w c over Ico a b is at most the modulus of the last weight plus the total variation of
w over the block, times B. -/
theorem norm_sum_Ico_mul_le (w c : ℕ → ℂ) (a b : ℕ) (B : ℝ)
    (hB : ∀ m : ℕ, m ≤ b → ‖∑ x ∈ Finset.Ico a m, c x‖ ≤ B) :
    ‖∑ x ∈ Finset.Ico a b, w x * c x‖ ≤
      (‖w (b - 1)‖ + ∑ x ∈ Finset.Ico a (b - 1), ‖w (x + 1) - w x‖) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  rcases Nat.lt_or_ge a b with hab | hab
  · obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
    have had : a ≤ d := by omega
    rw [sum_Ico_by_parts w c a d had, Nat.add_sub_cancel, add_mul, Finset.sum_mul]
    refine (norm_sub_le _ _).trans
      (add_le_add ?_ ((norm_sum_le _ _).trans (Finset.sum_le_sum ?_)))
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _ le_rfl) (norm_nonneg _)
    · intro x hx
      rw [norm_mul]
      have hx2 := (Finset.mem_Ico.1 hx).2
      exact mul_le_mul_of_nonneg_left (hB _ (by omega)) (norm_nonneg _)
  · rw [Finset.Ico_eq_empty_of_le hab, Finset.sum_empty, norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))) hB0

/-- Song 2020, page 5, "by partial summation", in the window form: if the sums of c over the
initial segments of the window, cut at any real t, are at most B in modulus and the weight w
is at most S in modulus, then the window sum of w c is at most S plus the total variation of
w over the window, times B. -/
theorem norm_window_sum_mul_le (n : ℕ) (y : ℝ) (w c : ℕ → ℂ) (B S : ℝ)
    (hB : ∀ t : ℝ, ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t), c x‖ ≤ B)
    (hS : ∀ x : ℕ, ‖w x‖ ≤ S) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), w x * c x‖ ≤
      (S + ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), ‖w (x + 1) - w x‖) * B := by
  obtain ⟨a, b, hab⟩ := window_eq_Ico n y
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hseg : ∀ m : ℕ, m ≤ b → ‖∑ x ∈ Finset.Ico a m, c x‖ ≤ B := by
    intro m hm
    have hff : (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ (m : ℝ) - 1) =
        ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter (fun x : ℕ => (x : ℝ) ≤ (m : ℝ) - 1) := by
      rw [Finset.filter_filter]
    have hset : Finset.Ico a m = (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ (m : ℝ) - 1) := by
      rw [hff, hab]
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, by omega⟩, ?_⟩
        have h3 : ((x + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
        push_cast at h3
        linarith
      · rintro ⟨⟨h1, _⟩, h2⟩
        refine ⟨h1, ?_⟩
        have h3 : ((x + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
          push_cast
          linarith
        exact_mod_cast h3
    rw [hset]
    exact hB _
  rw [hab]
  refine (norm_sum_Ico_mul_le w c a b B hseg).trans
    (mul_le_mul_of_nonneg_right (add_le_add (hS _) ?_) hB0)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico_right (Nat.sub_le _ _)) (fun _ _ _ => norm_nonneg _)

/-- Song 2020, page 5, the total variation of a weight whose steps are of size 1/x: the sum
of 1/x over the window is at most 1 + log n, since the window lies between 1 and n. This is
the logarithmic loss that the factor n^epsilon of the reduction absorbs. -/
theorem sum_window_inv_le (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : y ≤ (n : ℝ) / 3) :
    ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), (1 : ℝ) / (x : ℝ) ≤
      1 + Real.log (n : ℝ) := by
  have hsub : ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)) ⊆ Finset.Icc 1 n :=
    fun x hx => Finset.mem_Icc.2 (window_mem_bounds n y hy x hx)
  have hh : ∀ N : ℕ, ∑ x ∈ Finset.Icc 1 N, (1 : ℝ) / (x : ℝ) = ((harmonic N : ℚ) : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      ring
  calc ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), (1 : ℝ) / (x : ℝ)
      ≤ ∑ x ∈ Finset.Icc 1 n, (1 : ℝ) / (x : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ((harmonic n : ℚ) : ℝ) := hh n
    _ ≤ 1 + Real.log (n : ℝ) := harmonic_le_one_add_log n

/-- Song 2020, page 5, from "For S1, we first observe" to the partial summation display, for
one frequency and a generic weight G and unimodular factor E: the sum of G E over the primes
of the window is at most the size S of G / log plus its total variation V (1 + log n), times
the bound B for the von Mangoldt sums of E over initial segments of the window, plus the
proper prime power error 2 P n^(1/2). -/
theorem norm_sum_windowPrimes_le (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : y ≤ (n : ℝ) / 3)
    (G E : ℕ → ℂ) (B S V P : ℝ)
    (hE : ∀ x : ℕ, ‖E x‖ ≤ 1)
    (hB : ∀ t : ℝ, ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * E x‖ ≤ B)
    (hV0 : 0 ≤ V)
    (hS : ∀ x : ℕ, ‖G x / ((Real.log (x : ℝ) : ℝ) : ℂ)‖ ≤ S)
    (hV : ∀ x : ℕ, 1 ≤ x →
      ‖G (x + 1) / ((Real.log ((x + 1 : ℕ) : ℝ) : ℝ) : ℂ) -
        G x / ((Real.log (x : ℝ) : ℝ) : ℂ)‖ ≤ V / (x : ℝ))
    (hP : ∀ x : ℕ, ‖G x‖ ≤ P) :
    ‖∑ p ∈ windowPrimes n y, G p * E p‖ ≤
      (S + V * (1 + Real.log (n : ℝ))) * B + 2 * P * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [sum_windowPrimes_eq n y (fun x => G x * E x)]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have hcongr : ∀ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        ((ArithmeticFunction.vonMangoldt x / Real.log (x : ℝ) : ℝ) : ℂ) * (G x * E x) =
          (G x / ((Real.log (x : ℝ) : ℝ) : ℂ)) *
            ((ArithmeticFunction.vonMangoldt x : ℂ) * E x) := by
      intro x _
      push_cast
      ring
    rw [Finset.sum_congr rfl hcongr]
    refine (norm_window_sum_mul_le n y (fun x => G x / ((Real.log (x : ℝ) : ℝ) : ℂ))
      (fun x => (ArithmeticFunction.vonMangoldt x : ℂ) * E x) B S hB hS).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hB0
    refine add_le_add le_rfl ?_
    calc ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
          ‖G (x + 1) / ((Real.log ((x + 1 : ℕ) : ℝ) : ℝ) : ℂ) -
            G x / ((Real.log (x : ℝ) : ℝ) : ℂ)‖
        ≤ ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), V * ((1 : ℝ) / (x : ℝ)) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          have h1 := hV x (window_mem_bounds n y hy x hx).1
          rw [mul_one_div]
          exact h1
      _ = V * ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), (1 : ℝ) / (x : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ V * (1 + Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_window_inv_le n hn y hy) hV0
  · refine norm_sum_properPrimePow_le n hn y hy (fun x => G x * E x) P (fun x => ?_)
    rw [norm_mul]
    calc ‖G x‖ * ‖E x‖ ≤ ‖G x‖ * 1 := mul_le_mul_of_nonneg_left (hE x) (norm_nonneg _)
      _ ≤ P := by rw [mul_one]; exact hP x

/-- Song 2020, page 5, the sum over 1 at most |h| at most H split into the frequencies k and
-k for k from 1 to H. -/
theorem sum_nonzero_Icc_eq (H : ℕ) (f : ℤ → ℝ) :
    ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), f h =
      ∑ k ∈ Finset.Icc 1 H, (f (k : ℤ) + f (-(k : ℤ))) := by
  have hset : (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0) =
      (Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ)) ∪
        (Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ)) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h0⟩
      rcases lt_or_gt_of_ne h0 with hneg | hpos
      · right
        exact ⟨h.natAbs, by omega, by omega⟩
      · left
        exact ⟨h.natAbs, by omega, by omega⟩
    · rintro (⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩)
      · exact ⟨⟨by omega, by omega⟩, by omega⟩
      · exact ⟨⟨by omega, by omega⟩, by omega⟩
  have hdisj : Disjoint ((Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ)))
      ((Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ))) := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    rw [Finset.mem_image] at h1 h2
    obtain ⟨k, hk, rfl⟩ := h1
    obtain ⟨j, hj, hjk⟩ := h2
    rw [Finset.mem_Icc] at hk hj
    omega
  have hi1 : ∑ h ∈ (Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ)), f h =
      ∑ k ∈ Finset.Icc 1 H, f (k : ℤ) :=
    Finset.sum_image (fun a _ b _ hab => by omega)
  have hi2 : ∑ h ∈ (Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ)), f h =
      ∑ k ∈ Finset.Icc 1 H, f (-(k : ℤ)) :=
    Finset.sum_image (fun a _ b _ hab => by omega)
  rw [hset, Finset.sum_union hdisj, hi1, hi2, ← Finset.sum_add_distrib]

end LeanLab.Song2020.RouteS1Abel
