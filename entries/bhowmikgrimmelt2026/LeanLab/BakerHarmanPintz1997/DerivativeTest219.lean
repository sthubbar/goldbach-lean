module

public import LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

/-!
Baker, Harman and Pintz 1997, page 21, display 3.35.
Connect the proved discrete second derivative test to interval differencing.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BakerHarmanPintz1997.DerivativeTest219
open Finset PortedVanDerCorput

/-- Page 21. The second derivative test on an arbitrary integer interval. -/
theorem second_derivative_int (f : ℤ → ℝ) (p q : ℤ) (hpq : p ≤ q)
    {lam c : ℝ} (hlam : 0 < lam) (hc : 1 ≤ c)
    (hlo : ∀ n ∈ Ico p q, lam ≤ (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n))
    (hhi : ∀ n ∈ Ico p q, (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam) :
    ‖∑ n ∈ Icc p q, eK (f n)‖ ≤
      8 * (c * ((q : ℝ) - p + 1) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  let b : ℕ := (q - p + 1).toNat
  have hb : (b : ℤ) = q - p + 1 := Int.toNat_of_nonneg (by omega)
  let g : ℕ → ℝ := fun n => f (p + n - 1)
  have hlo' : ∀ n : ℕ, 0 < n → n < b →
      lam ≤ (g (n + 1 + 1) - g (n + 1)) - (g (n + 1) - g n) := by
    intro n hn hn'
    have hh := hlo (p + n - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
    simpa only [g, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh
  have hhi' : ∀ n : ℕ, 0 < n → n < b →
      (g (n + 1 + 1) - g (n + 1)) - (g (n + 1) - g n) ≤ c * lam := by
    intro n hn hn'
    have hh := hhi (p + n - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
    simpa only [g, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh
  have hs := vdC_second_derivative (Nat.zero_le b) hlam hc hlo' hhi'
  have heq : (∑ n ∈ Ioc 0 b, eK (g n)) = ∑ n ∈ Icc p q, eK (f n) := by
    apply sum_bij (fun (n : ℕ) (_ : n ∈ Ioc 0 b) => p + (n : ℤ) - 1)
    · intro n hn
      have := mem_Ioc.mp hn
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn m hm hnm
      omega
    · intro m hm
      have hm' := mem_Icc.mp hm
      refine ⟨(m - p + 1).toNat, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rfl
  rw [heq] at hs
  have hbR : (b : ℝ) = (q : ℝ) - p + 1 := by exact_mod_cast hb
  simpa only [hbR, Nat.cast_zero, sub_zero] using hs

/-- Page 21. Kusmin Landau on arbitrary integer intervals for the low frequency branch. -/
theorem kusmin_landau_int (f : ℤ → ℝ) (p q : ℤ) (hpq : p ≤ q)
    {δ : ℝ} {m : ℤ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hlo : ∀ n ∈ Icc p q, (m : ℝ) + δ ≤ f (n + 1) - f n)
    (hhi : ∀ n ∈ Icc p q, f (n + 1) - f n ≤ (m : ℝ) + 1 - δ)
    (hmono : ∀ n ∈ Ico p q, f (n + 1) - f n ≤ f (n + 1 + 1) - f (n + 1)) :
    ‖∑ n ∈ Icc p q, eK (f n)‖ ≤ 1 / δ := by
  let b : ℕ := (q - p + 1).toNat
  have hb : (b : ℤ) = q - p + 1 := Int.toNat_of_nonneg (by omega)
  let g : ℕ → ℝ := fun n => f (p + n - 1)
  have hlo' : ∀ n : ℕ, 0 < n → n ≤ b → (m : ℝ) + δ ≤ g (n + 1) - g n := by
    intro n hn hn'
    have hh := hlo (p + n - 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    simpa only [g, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh
  have hhi' : ∀ n : ℕ, 0 < n → n ≤ b → g (n + 1) - g n ≤ (m : ℝ) + 1 - δ := by
    intro n hn hn'
    have hh := hhi (p + n - 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    simpa only [g, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh
  have hm' : ∀ n : ℕ, 0 < n → n < b → g (n + 1) - g n ≤ g (n + 2) - g (n + 1) := by
    intro n hn hn'
    have hh := hmono (p + n - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
    simpa only [g, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      Nat.cast_ofNat, show (2 : ℤ) = 1 + 1 by norm_num] using hh
  have hs := kusmin_landau hδ0 hδ hlo' hhi' hm'
  have heq : (∑ n ∈ Ioc 0 b, eK (g n)) = ∑ n ∈ Icc p q, eK (f n) := by
    apply sum_bij (fun (n : ℕ) (_ : n ∈ Ioc 0 b) => p + (n : ℤ) - 1)
    · intro n hn
      have := mem_Ioc.mp hn
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn k hk heq
      omega
    · intro k hk
      have hk' := mem_Icc.mp hk
      refine ⟨(k - p + 1).toNat, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rfl
  rwa [heq] at hs

/-- Page 21. Second difference estimates for every shift list imply the iterated sum bound. -/
theorem iterated_of_second_difference_bounds (d : ℕ) (f : ℝ → ℝ) (p q : ℤ)
    (L : ℕ) (U eps c : ℝ) (lam : List ℤ → ℝ)
    (hL : 1 ≤ L) (hU : 0 < U) (hLU : (L : ℝ) ≤ U)
    (hsize : ((Icc p q).card : ℝ) ≤ U) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ d)) (hc : 1 ≤ c)
    (hlam : ∀ hs : List ℤ, hs.length = d →
      (∀ h ∈ hs, 1 ≤ h ∧ h < L) → 0 < lam hs)
    (hdiff : ∀ hs : List ℤ, hs.length = d →
      (∀ h ∈ hs, 1 ≤ h ∧ h < L) → ∀ n ∈ Ico p (q - hs.sum),
      let g := backwardDifferences (hs.map (fun h : ℤ => (h : ℝ))) f
      lam hs ≤ (g (n + 1 + 1) - g (n + 1)) - (g (n + 1) - g n) ∧
      (g (n + 1 + 1) - g (n + 1)) - (g (n + 1) - g n) ≤ c * lam hs)
    (hterminal : ∀ hs : List ℤ, hs.length = d →
      (∀ h ∈ hs, 1 ≤ h ∧ h < L) →
      8 * (c * U * Real.sqrt (lam hs) + 1 / Real.sqrt (lam hs)) ≤
        U * eps ^ (2 ^ d)) :
    ‖∑ n ∈ Icc p q, eK (f n)‖ ≤ 4 * U * eps := by
  apply iterated_interval_vdc d f p q L U eps hL hU hLU hsize heps heps1 hLin
  intro hs hlen hhs
  by_cases hpq : p ≤ q - hs.sum
  · have hb := second_derivative_int
      (fun n : ℤ => backwardDifferences (hs.map (fun h : ℤ => (h : ℝ))) f n)
      p (q - hs.sum) hpq (hlam hs hlen hhs) hc
      (fun n hn => by simpa only [Int.cast_add, Int.cast_one] using (hdiff hs hlen hhs n hn).1)
      (fun n hn => by simpa only [Int.cast_add, Int.cast_one] using (hdiff hs hlen hhs n hn).2)
    have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun h hh => (by have := (hhs h hh).1; omega))
    have hcard : (((Icc p (q - hs.sum)).card : ℕ) : ℝ) ≤ U :=
      (show (((Icc p (q - hs.sum)).card : ℕ) : ℝ) ≤ ((Icc p q).card : ℝ) by
        exact_mod_cast card_le_card (Icc_subset_Icc (le_refl p) (by omega : q - hs.sum ≤ q))).trans hsize
    have hlenR : ((q - hs.sum : ℤ) : ℝ) - p + 1 ≤ U := by
      have hz : 0 ≤ q - hs.sum + 1 - p := by omega
      have hzcast : ((q - hs.sum + 1 - p).toNat : ℝ) = ((q - hs.sum + 1 - p : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hz
      rw [Int.card_Icc, hzcast] at hcard
      push_cast at hcard ⊢
      linarith
    calc
      _ ≤ 8 * (c * (((q - hs.sum : ℤ) : ℝ) - p + 1) * Real.sqrt (lam hs) +
          1 / Real.sqrt (lam hs)) := hb
      _ ≤ 8 * (c * U * Real.sqrt (lam hs) + 1 / Real.sqrt (lam hs)) := by
        gcongr
      _ ≤ _ := hterminal hs hlen hhs
  · rw [Icc_eq_empty_of_lt (by omega), sum_empty, norm_zero]
    positivity

end LeanLab.BakerHarmanPintz1997.DerivativeTest219
