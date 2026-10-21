module

public import LeanLab.BrunGap.Sieve
public import LeanLab.Brun1919.Final

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Brun's upper bound and Brun's theorem for prime pairs (p, p + h), every even gap h ≥ 2.
-/

@[expose] public section

open Finset
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
namespace LeanLab.BrunGap

/-- **Brun's upper bound for gap `h`**: `π_h(N) ≤ C 𝔖(h) N / log² N`, with `C` independent
of `h`. Here `singProd h = ∏_{p ∣ h} (1 + 1/p)`. -/
theorem gapUpper (h : ℕ) (hh : Even h) (hh0 : h ≠ 0) :
    ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → (gapCount h N : ℝ) ≤ C * singProd h * N / Real.log N ^ 2 := by
  refine ⟨128 + 5 * 17 ^ 8, fun N hN => ?_⟩
  have hN1 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsp := one_le_singProd h
  set S := singProd h
  set z := √(N : ℝ) with hz
  have hz1 : 1 < z := by
    rw [hz, Real.lt_sqrt (by norm_num)]; linarith
  have hb := gapCount_le h N hh hh0 hz1
  have hlogz : Real.log z = Real.log N / 2 := Real.log_sqrt (by positivity)
  have hlogz0 : 0 ≤ Real.log z := Real.log_nonneg hz1.le
  have hmain : 32 * (N : ℝ) * S / Real.log z ^ 2 = 128 * S * N / Real.log N ^ 2 := by
    rw [hlogz]; field_simp; ring
  have hlz : Real.log z ≤ Real.log N := by rw [hlogz]; linarith
  have hpow1 : 1 ≤ (1 + Real.log z) ^ 6 := one_le_pow₀ (by linarith)
  have herr1 : z * (1 + Real.log z) ^ 6 + (z + 1) ≤ 5 * (z * (1 + Real.log N) ^ 6) := by
    have : (1 + Real.log z) ^ 6 ≤ (1 + Real.log N) ^ 6 := by gcongr
    nlinarith
  have hpb := polylog_bound N (by linarith)
  have herr2 : z * (1 + Real.log N) ^ 6 ≤ 17 ^ 8 * N / Real.log N ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have herr3 : (17 : ℝ) ^ 8 * N / Real.log N ^ 2 ≤ 17 ^ 8 * S * N / Real.log N ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (0 : ℝ) ≤ 17 ^ 8 * N := by positivity
    nlinarith
  have : (128 + 5 * 17 ^ 8 : ℝ) * S * N / Real.log N ^ 2 =
      128 * S * N / Real.log N ^ 2 + 5 * (17 ^ 8 * S * N / Real.log N ^ 2) := by ring
  rw [this]
  linarith

/-- Dyadic block bound from an upper bound `π_h(N) ≤ C N / log² N`. -/
lemma block_le {h : ℕ} {C : ℝ}
    (hC : ∀ N : ℕ, 3 ≤ N → (gapCount h N : ℝ) ≤ C * N / Real.log N ^ 2)
    (hC0 : 0 ≤ C) (k : ℕ) :
    ∑ p ∈ Ico (2 ^ k) (2 ^ (k + 1)), (if p.Prime ∧ (p + h).Prime then (1 : ℝ) / p else 0) ≤
      2 * C / Real.log 2 ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  have hterm : ∀ p ∈ Ico (2 ^ k) (2 ^ (k + 1)),
      (if p.Prime ∧ (p + h).Prime then (1 : ℝ) / p else 0) ≤
        (1 / 2 ^ k) * (if p.Prime ∧ (p + h).Prime then (1 : ℝ) else 0) := by
    intro p hp
    simp only [mem_Ico] at hp
    have hp1 : (2 : ℝ) ^ k ≤ p := by exact_mod_cast hp.1
    split_ifs
    · rw [mul_one]; exact one_div_le_one_div_of_le hpk hp1
    · simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_boole] at hsum
  have hcount : (#{p ∈ Ico (2 ^ k) (2 ^ (k + 1)) | p.Prime ∧ (p + h).Prime} : ℝ) ≤
      gapCount h (2 ^ (k + 1)) := by
    unfold gapCount
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
      (fun x hx => by simp only [mem_Ico, mem_range] at hx ⊢; omega))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : ∑ p ∈ Ico (2 ^ 0) (2 ^ (0 + 1)),
        (if p.Prime ∧ (p + h).Prime then (1 : ℝ) / p else 0) = 0 := by
      simp [Nat.not_prime_one]
    rw [this]; positivity
  · have h3 : 3 ≤ 2 ^ (k + 1) := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hU := hC _ h3
    push_cast at hU
    rw [Real.log_pow] at hU
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have : (1 / 2 ^ k) * (C * 2 ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * Real.log 2) ^ 2) =
        2 * C / Real.log 2 ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
      push_cast; field_simp; ring
    calc _ ≤ (1 / 2 ^ k) * (#{p ∈ Ico (2 ^ k) (2 ^ (k + 1)) | p.Prime ∧ (p + h).Prime} : ℝ) :=
          hsum
      _ ≤ (1 / 2 ^ k) * (C * 2 ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * Real.log 2) ^ 2) := by
        gcongr; exact hcount.trans hU
      _ = _ := this

/-- **Brun's theorem for gap `h`.** For every even `h ≥ 2`, the sum of `1/p` over primes `p`
with `p + h` prime converges. -/
theorem brun_gap (h : ℕ) (hh : Even h) (hh0 : h ≠ 0) :
    Summable (fun p : ℕ => if p.Prime ∧ (p + h).Prime then (1 : ℝ) / p else 0) := by
  obtain ⟨C₀, hC₀⟩ := gapUpper h hh hh0
  set C := C₀ * singProd h with hCdef
  have hC : ∀ N : ℕ, 3 ≤ N → (gapCount h N : ℝ) ≤ C * N / Real.log N ^ 2 := hC₀
  set f : ℕ → ℝ := fun p => if p.Prime ∧ (p + h).Prime then (1 : ℝ) / p else 0 with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p => by
    simp only [hf]; split_ifs <;> positivity
  have hC0 : 0 ≤ C := by
    have h := hC 3 le_rfl
    have hl : 0 < Real.log (3 : ℕ) := Real.log_pos (by norm_num)
    have : 0 ≤ C * (3 : ℕ) / Real.log (3 : ℕ) ^ 2 := le_trans (Nat.cast_nonneg _) h
    by_contra hneg
    push Not at hneg
    have : C * (3 : ℕ) / Real.log (3 : ℕ) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by norm_num)) (by positivity)
    linarith
  have hS : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  set B := 2 * C / Real.log 2 ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hdy : ∀ K : ℕ, ∑ p ∈ range (2 ^ K), f p ≤
      f 0 + B * ∑ k ∈ range K, 1 / ((k : ℝ) + 1) ^ 2 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)),
        Finset.sum_range_succ, mul_add]
      have := block_le hC hC0 K
      linarith
  refine summable_of_sum_range_le hf0 (c := f 0 + B * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) ?_
  intro n
  have hn : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  calc ∑ p ∈ range n, f p ≤ ∑ p ∈ range (2 ^ n), f p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun i _ _ => hf0 i)
    _ ≤ f 0 + B * ∑ k ∈ range n, 1 / ((k : ℝ) + 1) ^ 2 := hdy n
    _ ≤ _ := by
        gcongr
        exact hS.sum_le_tsum _ (fun i _ => by positivity)

/-! ### Sanity check: the case `h = 2` -/

lemma gapCount_two (N : ℕ) : gapCount 2 N = LeanLab.Brun1919.twinCount N := by
  unfold gapCount LeanLab.Brun1919.twinCount
  congr 1

/-- The `h = 2` case of `brun_gap` recovers `LeanLab.Brun1919.brun_smaller`. -/
theorem brun_smaller_of_brun_gap :
    Summable (fun p : ℕ => if LeanLab.Brun1919.IsTwin p then (1 : ℝ) / p else 0) := by
  refine (brun_gap 2 even_two two_ne_zero).congr fun p => ?_
  by_cases hp : LeanLab.Brun1919.IsTwin p
  · have hp' : p.Prime ∧ (p + 2).Prime := hp
    rw [ite_eq_left hp', ite_eq_left hp]
  · have hp' : ¬ (p.Prime ∧ (p + 2).Prime) := hp
    rw [ite_eq_right hp', ite_eq_right hp]

/-- `twinUpper`-style bound recovered from `gapUpper` at `h = 2`. -/
theorem twinUpper_of_gapUpper : LeanLab.Brun1919.TwinUpper := by
  obtain ⟨C, hC⟩ := gapUpper 2 even_two two_ne_zero
  exact ⟨C * singProd 2, fun N hN => by rw [← gapCount_two]; exact hC N hN⟩

end LeanLab.BrunGap
