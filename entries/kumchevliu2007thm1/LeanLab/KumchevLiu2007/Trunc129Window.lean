module

public import LeanLab.KumchevLiu2007.Decomp506b

/-!
Kumchev and Liu, arXiv 0801.0130, paper P0088. Truncated window route for the
transition regime of Proposition 2, pages 16 and 17, displays 56 to 59, and the
window of page 2 displays 4 to 6.

This file holds the two elementary window inputs of the truncated route:
the residual R0(n) is at most the sifted pair count of display 56, for every n,
and the weighted integer count r2(n) of display 6 is at least half the length of
the truncated m2 window times L to the -2.

This file declares nothing new: only theorems. The window pair set, the rough
count and the prime count are written out exactly as in Leaves129.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Trunc129

open Real LeanLab.KumchevLiu2007 Task506b
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 16 display 56 and page 8 display 35, truncated window version in an
abstract form. For any finite set W of pairs whose second entry is at least the
cutoff c and whose first entry is at least the level z, the count of pairs with
m1 prime and m2 rough minus the count with both prime is at most the sifted
count: m1 without prime factors below z, m2 rough and not prime. No condition
on n enters, so the bound holds on truncated windows too. Elementary. -/
theorem residual_le_sifted_gen (W : Finset (ℕ × ℕ)) (c z : ℝ)
    (h2c : ∀ v ∈ W, c ≤ (v.2 : ℝ)) (h1z : ∀ v ∈ W, z ≤ (v.1 : ℝ)) :
    |(((W.filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → c ≤ (p : ℝ))).card : ℝ) -
      ((W.filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))| ≤
      ((W.filter (fun v => (∀ p : ℕ, p.Prime → p ∣ v.1 → z ≤ (p : ℝ)) ∧
        ¬ v.2.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → c ≤ (p : ℝ))).card : ℝ) := by
  classical
  set F := W.filter (fun v => v.1.Prime ∧
    ∀ p : ℕ, p.Prime → p ∣ v.2 → c ≤ (p : ℝ)) with hF
  have h1 := Finset.card_filter_add_card_filter_not (s := F) (fun v => v.2.Prime)
  have h2 : F.filter (fun v => v.2.Prime) = W.filter (fun v => v.1.Prime ∧ v.2.Prime) := by
    ext v
    simp only [Finset.mem_filter, hF]
    constructor
    · rintro ⟨⟨hv, hp, _⟩, hq⟩
      exact ⟨hv, hp, hq⟩
    · rintro ⟨hv, hp, hq⟩
      refine ⟨⟨hv, hp, ?_⟩, hq⟩
      intro p hp' hd
      rw [(Nat.prime_dvd_prime_iff_eq hp' hq).mp hd]
      exact h2c v hv
  have h1' : (F.card : ℝ) = ((F.filter (fun v => v.2.Prime)).card : ℝ) +
      ((F.filter (fun v => ¬ v.2.Prime)).card : ℝ) := by exact_mod_cast h1.symm
  have hres : (F.card : ℝ) - ((W.filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ) =
      ((F.filter (fun v => ¬ v.2.Prime)).card : ℝ) := by
    rw [← h2, h1']
    ring
  rw [hres, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Finset.card_le_card (by
    intro v hv
    simp only [Finset.mem_filter, hF] at hv ⊢
    obtain ⟨⟨hvW, hp, hrough⟩, hnp⟩ := hv
    refine ⟨hvW, ?_, hnp, hrough⟩
    intro p hp' hd
    rw [(Nat.prime_dvd_prime_iff_eq hp' hp).mp hd]
    exact h1z v hvW)

/-- Page 2 before display 4 and page 16, used for the truncated window version
of display 56. For Y at least 16 and P at least 1 the cutoff
z0 = Y to the 1/4 times P to the -2 lies below the lower end sqrt Y / 2 of the
window I2. -/
theorem cutoff_below_window_aux {Y P : ℝ} (hY16 : 16 ≤ Y) (hP : 1 ≤ P) :
    Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ Real.sqrt Y / 2 := by
  have hY0 : 0 ≤ Y := by linarith
  have h4 : (2 : ℝ) ≤ Y ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hY16 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have e : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    linarith
  have hsq : Real.sqrt Y = Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
    norm_num
  have hPz : P ^ (-2 : ℤ) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ hP (by norm_num))
  have hq0 : 0 ≤ Y ^ (1 / 4 : ℝ) := Real.rpow_nonneg hY0 _
  rw [hsq]
  calc Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ Y ^ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left hPz hq0
    _ ≤ Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) / 2 := by nlinarith

/-- Page 2 before display 4, used for the truncated window version of displays
56 to 59. For X at least 512 and epsilon at most 11/18, twice
Y = X to the 7/12 + epsilon/2 is at most X. -/
theorem two_window_le {X ε : ℝ} (hε1 : ε ≤ 11 / 18) (hX : 512 ≤ X) :
    2 * X ^ (7 / 12 + ε / 2) ≤ X := by
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have h1 : X ^ (7 / 12 + ε / 2) ≤ X ^ (8 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have h2 : (2 : ℝ) ≤ X ^ (1 / 9 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hX (show (0 : ℝ) ≤ 1 / 9 by norm_num)
    have e : (512 : ℝ) ^ (1 / 9 : ℝ) = 2 := by
      rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, show (1 / 9 : ℝ) = ((9 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    linarith
  have h3 : X ^ (8 / 9 : ℝ) * X ^ (1 / 9 : ℝ) = X := by
    rw [← Real.rpow_add hXpos]; norm_num
  have h0 : 0 ≤ X ^ (8 / 9 : ℝ) := Real.rpow_nonneg hXpos.le _
  nlinarith

/-- Page 2 and page 17 before display 58, used for the truncated window version
of display 56. For X large in terms of delta, with epsilon at most 11/18, the
sieve level z = exp of L to the 1 - delta/2 is below X - Y, the lower end of
the window I1. -/
theorem sieveLevel_below_window_aux {X δ ε : ℝ} (hδ : 0 < δ) (hε1 : ε ≤ 11 / 18)
    (hX : 512 ≤ X) (hL : max 2 ((2 : ℝ) ^ (2 / δ)) ≤ Real.log X) :
    Real.exp (Real.log X ^ (1 - δ / 2)) ≤ X - X ^ (7 / 12 + ε / 2) := by
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hL2 : 2 ≤ Real.log X := le_trans (le_max_left _ _) hL
  have hLpos : 0 < Real.log X := by linarith
  have hYle : 2 * X ^ (7 / 12 + ε / 2) ≤ X := two_window_le hε1 hX
  have hLd : (2 : ℝ) ≤ Real.log X ^ (δ / 2) := by
    have h := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hL)
      (show 0 ≤ δ / 2 by linarith)
    rwa [← Real.rpow_mul (by norm_num), show 2 / δ * (δ / 2) = 1 by field_simp,
      Real.rpow_one] at h
  have hsplit : Real.log X ^ (1 - δ / 2) * Real.log X ^ (δ / 2) = Real.log X := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hlz0 : 0 ≤ Real.log X ^ (1 - δ / 2) := Real.rpow_nonneg hLpos.le _
  have hhalf : Real.log X ^ (1 - δ / 2) ≤ Real.log X / 2 := by nlinarith
  have hlog2 : Real.log 2 ≤ Real.log X / 2 := by
    have := Real.log_two_lt_d9; linarith
  have hz : Real.exp (Real.log X ^ (1 - δ / 2)) ≤ X / 2 := by
    rw [← Real.exp_log (show 0 < X / 2 by positivity)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hXpos.ne' (by norm_num)]
    linarith
  linarith

/-- Page 16 display 56 and page 8 display 35, truncated window version: for
every n, with no restriction on n - X, the residual R0(n), the count of window
pairs with m1 prime and m2 rough minus the count with both prime, is at most
the sifted pair count of page 17 display 58 in absolute value, once X is large
in terms of delta. The cutoff z0 is below the window I2 and the sieve level z
is below the window I1. Elementary. -/
theorem trunc_residual_le_sifted (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ,
      |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))| ≤
        Task506b.siftedCount X B δ ε n := by
  refine ⟨max 512 (Real.exp (max 2 ((2 : ℝ) ^ (2 / δ)))), ?_⟩
  intro X hX n
  have h512 : 512 ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hL : max 2 ((2 : ℝ) ^ (2 / δ)) ≤ Real.log X := by
    have hE := le_trans (le_max_right _ _) hX
    have := Real.log_le_log (Real.exp_pos _) hE
    rwa [Real.log_exp] at this
  have hL1 : 1 ≤ Real.log X := by linarith [le_max_left 2 ((2 : ℝ) ^ (2 / δ))]
  have hP : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hY16 : 16 ≤ X ^ (7 / 12 + ε / 2) := by
    have h1 : X ^ (1 / 2 : ℝ) ≤ X ^ (7 / 12 + ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h2 : (16 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by linarith)
    linarith
  have hcut : (X ^ (7 / 12 + ε / 2)) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
      Real.sqrt (X ^ (7 / 12 + ε / 2)) / 2 := cutoff_below_window_aux hY16 hP
  have hz : Real.exp (Real.log X ^ (1 - δ / 2)) ≤ X - X ^ (7 / 12 + ε / 2) :=
    sieveLevel_below_window_aux hδ hε1 h512 hL
  unfold Task506b.siftedCount
  exact residual_le_sifted_gen _ _ _
    (fun v hv => hcut.trans (Finset.mem_filter.mp hv).2.2.2.1)
    (fun v hv => hz.trans (Finset.mem_filter.mp hv).2.1)

/-- Page 2 display 6, the size of r2 used on page 16 with display 57, truncated
window version in counting form: every m2 in a set K of integers in the window
I2 with m2 squared above n minus X gives the admissible pair n minus m2
squared, m2, of weight at least L to the minus 2. The window pair set is
written out. Elementary. -/
theorem r2_ge_card_aux (X Y : ℝ) (n : ℕ) (K : Finset ℕ) (hYX : 2 * Y ≤ X)
    (hs4 : 4 ≤ Real.sqrt Y) (hXn : X < (n : ℝ))
    (hK : ∀ k ∈ K, Real.sqrt Y / 2 ≤ (k : ℝ) ∧ (k : ℝ) < Real.sqrt Y ∧
      (n : ℝ) - X < (k : ℝ) ^ 2) :
    (K.card : ℝ) * (1 / (Real.log X * Real.log X)) ≤
      ∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
        (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) := by
  have hYpos : 0 < Y := by
    by_contra h; push Not at h; rw [Real.sqrt_eq_zero'.mpr h] at hs4; linarith
  have hss : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hYpos.le
  have hsY : Real.sqrt Y ≤ Y := by nlinarith
  set L := Real.log X with hL
  set Wn := ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
        (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n) with hWn
  let f : ℕ → ℕ × ℕ := fun k => (n - k ^ 2, k)
  have hfacts : ∀ k ∈ K, f k ∈ Wn ∧
      1 / (L * L) ≤ 1 / (Real.log ((f k).1 : ℝ) * Real.log ((f k).2 : ℝ)) := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := hK k hk
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hkY : (k : ℝ) ^ 2 < Y := by nlinarith
    have hkn : k ^ 2 ≤ n := by
      have : ((k ^ 2 : ℕ) : ℝ) ≤ n := by push_cast; linarith
      exact_mod_cast this
    have hm1 : ((n - k ^ 2 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) ^ 2 := by
      rw [Nat.cast_sub hkn]; push_cast; ring
    have hm1lo : X - Y < ((n - k ^ 2 : ℕ) : ℝ) := by rw [hm1]; linarith
    have hm1hi : ((n - k ^ 2 : ℕ) : ℝ) < X := by rw [hm1]; linarith
    refine ⟨?_, ?_⟩
    · rw [hWn, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hm1hi.le)),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hk2.le))⟩,
        hm1lo.le, hm1hi, hk1, hk2, Nat.sub_add_cancel hkn⟩
    · simp only [f]
      have hl1 : 0 < Real.log ((n - k ^ 2 : ℕ) : ℝ) := Real.log_pos (by linarith)
      have hl1' : Real.log ((n - k ^ 2 : ℕ) : ℝ) ≤ L := Real.log_le_log (by linarith) hm1hi.le
      have hl2 : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
      have hl2' : Real.log (k : ℝ) ≤ L := Real.log_le_log (by linarith) (by linarith)
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul hl1' hl2' hl2.le (by linarith)
  have hinj : Set.InjOn f K := fun a _ b _ h => congrArg Prod.snd h
  have hnonneg : ∀ v ∈ Wn, v ∉ K.image f →
      0 ≤ 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) := by
    intro v _ _
    have := Real.log_natCast_nonneg v.1
    have := Real.log_natCast_nonneg v.2
    positivity
  have hsub : K.image f ⊆ Wn := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact (hfacts k hk).1
  calc (K.card : ℝ) * (1 / (L * L)) = ∑ k ∈ K, 1 / (L * L) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ K, 1 / (Real.log ((f k).1 : ℝ) * Real.log ((f k).2 : ℝ)) :=
        Finset.sum_le_sum (fun k hk => (hfacts k hk).2)
    _ = ∑ v ∈ K.image f, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) :=
        by rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg

/-- Page 2 displays 4 to 6 and page 16, the comparison size of r2(n) used with
display 57, truncated window version: for X < n < X + Y, when the truncated m2
window from max of sqrt Y / 2 and sqrt of n - X up to sqrt Y has length W at
least 4, the weighted integer count r2(n) of display 6 is at least
W / 2 times L to the -2. Every integer m2 strictly inside the truncated window
gives the admissible pair n - m2^2, m2, there are at least W - 1 of them, and
each weight is at least L to the -2. Elementary. -/
theorem trunc_integerMain_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) < X + Task506b.Y X ε →
      4 ≤ Real.sqrt (Task506b.Y X ε) - max (Real.sqrt (Task506b.Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) →
      (Real.sqrt (Task506b.Y X ε) - max (Real.sqrt (Task506b.Y X ε) / 2) (Real.sqrt ((n : ℝ) - X))) / 2 *
          Real.log X ^ (-2 : ℝ) ≤
        ∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) := by
  refine ⟨512, ?_⟩
  intro X hX n hXn _hnY hW
  have hYdef : Task506b.Y X ε = X ^ (7 / 12 + ε / 2) := rfl
  rw [hYdef] at hW ⊢
  have hYX : 2 * X ^ (7 / 12 + ε / 2) ≤ X := two_window_le hε1 hX
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hs0 : 0 ≤ Real.sqrt (X ^ (7 / 12 + ε / 2)) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (X ^ (7 / 12 + ε / 2)) / 2 ≤
      max (Real.sqrt (X ^ (7 / 12 + ε / 2)) / 2) (Real.sqrt ((n : ℝ) - X)) := le_max_left _ _
  have hb2 : Real.sqrt ((n : ℝ) - X) ≤
      max (Real.sqrt (X ^ (7 / 12 + ε / 2)) / 2) (Real.sqrt ((n : ℝ) - X)) := le_max_right _ _
  generalize max (Real.sqrt (X ^ (7 / 12 + ε / 2)) / 2) (Real.sqrt ((n : ℝ) - X)) = b
    at hW hb1 hb2 ⊢
  have hb0 : 0 ≤ b := by linarith
  have hs4 : 4 ≤ Real.sqrt (X ^ (7 / 12 + ε / 2)) := by linarith
  have hKcard : (Real.sqrt (X ^ (7 / 12 + ε / 2)) - b) / 2 ≤
      ((Finset.Ioo ⌊b⌋₊ ⌈Real.sqrt (X ^ (7 / 12 + ε / 2))⌉₊).card : ℝ) := by
    have h1 := Nat.le_ceil (Real.sqrt (X ^ (7 / 12 + ε / 2)))
    have h2 := Nat.floor_le hb0
    have hlt : ⌊b⌋₊ + 1 ≤ ⌈Real.sqrt (X ^ (7 / 12 + ε / 2))⌉₊ := by
      have : ((⌊b⌋₊ + 1 : ℕ) : ℝ) ≤ (⌈Real.sqrt (X ^ (7 / 12 + ε / 2))⌉₊ : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    rw [Nat.card_Ioo, Nat.sub_sub, Nat.cast_sub hlt]
    push_cast
    linarith
  have hmem : ∀ k ∈ Finset.Ioo ⌊b⌋₊ ⌈Real.sqrt (X ^ (7 / 12 + ε / 2))⌉₊,
      Real.sqrt (X ^ (7 / 12 + ε / 2)) / 2 ≤ (k : ℝ) ∧
      (k : ℝ) < Real.sqrt (X ^ (7 / 12 + ε / 2)) ∧ (n : ℝ) - X < (k : ℝ) ^ 2 := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have hbk : b < (k : ℝ) := (Nat.floor_lt hb0).mp hk.1
    have hks : (k : ℝ) < Real.sqrt (X ^ (7 / 12 + ε / 2)) := Nat.lt_ceil.mp hk.2
    refine ⟨by linarith, hks, ?_⟩
    have hk0 : (0 : ℝ) < k := by linarith
    exact (Real.sqrt_lt' hk0).mp (lt_of_le_of_lt hb2 hbk)
  have hmain := r2_ge_card_aux X (X ^ (7 / 12 + ε / 2)) n
    (Finset.Ioo ⌊b⌋₊ ⌈Real.sqrt (X ^ (7 / 12 + ε / 2))⌉₊) hYX hs4 hXn hmem
  have hrw : Real.log X ^ (-2 : ℝ) = 1 / (Real.log X * Real.log X) := by
    rw [Real.rpow_neg hLpos.le, Real.rpow_two, sq, one_div]
  rw [hrw]
  exact (mul_le_mul_of_nonneg_right hKcard (by positivity)).trans hmain

end LeanLab.KumchevLiu2007.Trunc129

