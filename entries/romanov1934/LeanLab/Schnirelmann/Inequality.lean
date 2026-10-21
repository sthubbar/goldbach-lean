module

public import Mathlib

/-!
Schnirelmann's inequality and Schnirelmann's basis theorem.
Mathlib lists both as TODO in Mathlib/Combinatorics/Schnirelmann.lean.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Source: L. G. Schnirelmann 1930, as in Nathanson, Additive Number Theory: The Classical Bases,
GTM 164, Chapter 7.
-/

@[expose] public section

open Finset
open scoped Pointwise Classical

namespace LeanLab.Schnirelmann

noncomputable section

/-- Count of elements of `S` in `{1, ..., n}`. -/
def cnt (S : Set ℕ) (n : ℕ) : ℕ := #{a ∈ Ioc 0 n | a ∈ S}

lemma cnt_split (S : Set ℕ) {m n : ℕ} (hmn : m ≤ n) :
    cnt S n = cnt S m + #{a ∈ Ioc m n | a ∈ S} := by
  unfold cnt
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le m) hmn, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)

lemma cnt_succ_of_mem (S : Set ℕ) {n : ℕ} (h : n + 1 ∈ S) : cnt S (n + 1) = cnt S n + 1 := by
  rw [cnt_split S (Nat.le_succ n)]
  congr 1
  rw [Finset.card_eq_one]
  refine ⟨n + 1, ?_⟩
  ext x; simp only [mem_filter, mem_Ioc, mem_singleton]; constructor
  · rintro ⟨⟨h1, h2⟩, _⟩; omega
  · rintro rfl; exact ⟨⟨by omega, le_rfl⟩, h⟩

lemma cnt_succ_le (S : Set ℕ) (n : ℕ) : cnt S (n + 1) ≤ cnt S n + 1 := by
  rw [cnt_split S (Nat.le_succ n)]
  gcongr
  calc #{a ∈ Ioc n (n + 1) | a ∈ S} ≤ #(Ioc n (n + 1)) := card_filter_le _ _
    _ = 1 := by simp

/-- Gap step: if no element of `A` lies in `(a, n]` and `a ∈ A`, then `a + B` fills
at least `cnt B (n - a)` places of `A + B` in `(a, n]`. -/
lemma cnt_add_gap (A B : Set ℕ) {a n : ℕ} (ha : a ∈ A) (han : a ≤ n) :
    cnt (A + B) a + cnt B (n - a) ≤ cnt (A + B) n := by
  rw [cnt_split (A + B) han]
  gcongr
  unfold cnt
  apply Finset.card_le_card_of_injOn (fun b => a + b)
  · intro b hb
    simp only [coe_filter, mem_Ioc, Set.mem_setOf_eq] at hb ⊢
    refine ⟨⟨by omega, by omega⟩, ⟨a, ha, b, hb.2, rfl⟩⟩
  · intro x _ y _ h; simpa using h

/-- The key counting inequality, by strong induction on `n`. -/
lemma key_count (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) :
    ∀ n : ℕ, (cnt A n : ℝ) + schnirelmannDensity B * (n - cnt A n) ≤ cnt (A + B) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cnt]
  by_cases hnA : n ∈ A
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := cnt_succ_of_mem A hnA
    have hS : m + 1 ∈ A + B := ⟨m + 1, hnA, 0, hB, rfl⟩
    have h2 := cnt_succ_of_mem (A + B) hS
    have := ih m (by omega)
    rw [h1, h2]; push_cast
    linarith
  · -- largest element of `A` below `n`
    set T := (range n).filter (· ∈ A) with hT
    have hTne : T.Nonempty := ⟨0, by simp [hT, hA, hn]⟩
    set a := T.max' hTne with ha_def
    have haT : a ∈ T := T.max'_mem hTne
    simp only [hT, mem_filter, mem_range] at haT
    obtain ⟨han, haA⟩ := haT
    have hgap : ∀ x, a < x → x ≤ n → x ∉ A := by
      intro x hax hxn hxA
      rcases Nat.lt_or_ge x n with hxn' | hxn'
      · have : x ≤ a := T.le_max' x (by simp [hT, hxn', hxA])
        omega
      · exact hnA (by rwa [show x = n by omega] at hxA)
    have hcA : cnt A n = cnt A a := by
      rw [cnt_split A han.le]
      simp only [add_eq_left, card_eq_zero, filter_eq_empty_iff, mem_Ioc]
      intro x hx; exact hgap x hx.1 hx.2
    have hgapS := cnt_add_gap A B haA han.le
    have hIH := ih a han
    have hBd : schnirelmannDensity B * ((n - a : ℕ) : ℝ) ≤ cnt B (n - a) :=
      schnirelmannDensity_mul_le_card_filter
    rw [hcA]
    have hcast : ((n - a : ℕ) : ℝ) = (n : ℝ) - a := by push_cast [Nat.cast_sub han.le]; ring
    rw [hcast] at hBd
    have : ((cnt (A + B) a + cnt B (n - a) : ℕ) : ℝ) ≤ cnt (A + B) n := by exact_mod_cast hgapS
    push_cast at this
    nlinarith

/-- **Schnirelmann's inequality.** If `0 ∈ A` and `0 ∈ B` then
`σ(A + B) ≥ σA + σB - σA σB`. -/
theorem schnirelmann_inequality (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) :
    schnirelmannDensity A + schnirelmannDensity B
      - schnirelmannDensity A * schnirelmannDensity B ≤ schnirelmannDensity (A + B) := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk := key_count A B hA hB n
  have hAd : schnirelmannDensity A * n ≤ cnt A n := schnirelmannDensity_mul_le_card_filter
  have hB1 : schnirelmannDensity B ≤ 1 := schnirelmannDensity_le_one
  rw [le_div_iff₀ hnR]
  change _ ≤ (cnt (A + B) n : ℝ)
  nlinarith

/-- `1 - σ(A + B) ≤ (1 - σA)(1 - σB)`, the form used for iteration. -/
theorem one_sub_density_add_le (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) :
    1 - schnirelmannDensity (A + B) ≤
      (1 - schnirelmannDensity A) * (1 - schnirelmannDensity B) := by
  have := schnirelmann_inequality A B hA hB
  nlinarith

lemma zero_mem_nsmul (A : Set ℕ) (hA : 0 ∈ A) : ∀ k : ℕ, (0 : ℕ) ∈ k • A
  | 0 => by simp
  | k + 1 => by
    rw [succ_nsmul]; exact ⟨0, zero_mem_nsmul A hA k, 0, hA, rfl⟩

lemma one_sub_density_nsmul_le (A : Set ℕ) (hA : 0 ∈ A) :
    ∀ k : ℕ, 1 - schnirelmannDensity ((k + 1) • A) ≤ (1 - schnirelmannDensity A) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
    have ih := one_sub_density_nsmul_le A hA k
    rw [succ_nsmul _ (k + 1)]
    have h := one_sub_density_add_le ((k + 1) • A) A (zero_mem_nsmul A hA _) hA
    have h0 : 0 ≤ 1 - schnirelmannDensity A := by linarith [schnirelmannDensity_le_one (A := A)]
    calc 1 - schnirelmannDensity ((k + 1) • A + A)
        ≤ (1 - schnirelmannDensity ((k + 1) • A)) * (1 - schnirelmannDensity A) := h
      _ ≤ (1 - schnirelmannDensity A) ^ (k + 1) * (1 - schnirelmannDensity A) := by
          gcongr
      _ = (1 - schnirelmannDensity A) ^ (k + 1 + 1) := by ring

/-- **Schnirelmann's basis theorem.** A set containing `0` with positive Schnirelmann density
is an additive basis of finite order. -/
theorem exists_nsmul_eq_univ (A : Set ℕ) (hA : 0 ∈ A) (hpos : 0 < schnirelmannDensity A) :
    ∃ h : ℕ, h • A = Set.univ := by
  have h1 : 1 - schnirelmannDensity A < 1 := by linarith
  have h0 : 0 ≤ 1 - schnirelmannDensity A := by linarith [schnirelmannDensity_le_one (A := A)]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 2 by norm_num) h1
  have hk' : (1 - schnirelmannDensity A) ^ (k + 1) ≤ 1 / 2 :=
    le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one h0 h1.le (Nat.le_succ k)) hk)
  have hd := one_sub_density_nsmul_le A hA k
  refine ⟨2 * (k + 1), ?_⟩
  rw [two_mul, add_nsmul]
  apply add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
    (zero_mem_nsmul A hA _) (zero_mem_nsmul A hA _)
  linarith

end

end LeanLab.Schnirelmann
