module

public import LeanLab.SchnirelmannGoldbach.Statements

/-!
S5 plus S6: positive Schnirelmann density of {0, 1} ∪ G implies Schnirelmann's theorem
on sums of a bounded number of primes. No placeholder proofs.
AI-written Lean code, Claude, 2026-10-16.
-/

@[expose] public section

open Finset
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach

/-- Membership in `h • A` gives a list of `h` elements of `A`. -/
lemma exists_list_of_mem_nsmul (A : Set ℕ) :
    ∀ h n, n ∈ h • A → ∃ l : List ℕ, l.length = h ∧ (∀ a ∈ l, a ∈ A) ∧ l.sum = n
  | 0, n, hn => by
    simp only [zero_smul, Set.mem_zero] at hn
    exact ⟨[], rfl, by simp, by simp [hn]⟩
  | h + 1, n, hn => by
    rw [succ_nsmul] at hn
    obtain ⟨x, hx, a, ha, rfl⟩ := hn
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul A h x hx
    exact ⟨a :: l, by simp [hl], by
      intro b hb; rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hlA b hb, by simp [hls, add_comm]⟩

/-- Every `e ≥ 2` is a sum of at most `e` primes, using 2 and 3. -/
lemma small_sum (e : ℕ) (he : 2 ≤ e) : ∃ k ≤ e, SumOfPrimes k e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  rcases (show e = 2 ∨ e = 3 ∨ 4 ≤ e by omega) with rfl | rfl | h4
  · exact ⟨1, by omega, [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by omega, [3], rfl, by simp [Nat.prime_three], rfl⟩
  · obtain ⟨k, hk, l, hl, hlp, hls⟩ := ih (e - 2) (by omega) (by omega)
    refine ⟨k + 1, by omega, 2 :: l, by simp [hl], ?_, by simp [hls]; omega⟩
    intro p hp; rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact hlp p hp

lemma list_step (l : List ℕ) (hl : ∀ a ∈ l, a ∈ ({0, 1} ∪ G : Set ℕ)) :
    ∀ e, 2 ≤ e → ∃ k ≤ 2 * l.length + e, SumOfPrimes k (l.sum + e) := by
  induction l with
  | nil => intro e he; simpa using small_sum e he
  | cons a l ih =>
    intro e he
    have ha := hl a (by simp)
    have ih' := ih (fun b hb => hl b (by simp [hb]))
    rcases ha with ha | ha
    · rcases ha with rfl | rfl
      · obtain ⟨k, hk, hs⟩ := ih' e he
        exact ⟨k, by simp; omega, by simpa using hs⟩
      · obtain ⟨k, hk, hs⟩ := ih' (e + 1) (by omega)
        exact ⟨k, by simp; omega, by simpa [add_comm, add_left_comm, add_assoc] using hs⟩
    · obtain ⟨p, q, hp, hq, rfl⟩ := ha
      obtain ⟨k, hk, l', hl', hlp, hls⟩ := ih' e he
      refine ⟨k + 2, by simp; omega, p :: q :: l', by simp [hl'], ?_, by simp [hls]; ring⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hp
      · exact hq
      · exact hlp x hx

/-- **S5 + S6.** If `{0, 1} ∪ G` has positive Schnirelmann density then every `n ≥ 2` is a sum
of a bounded number of primes. -/
theorem schnirelmann_goldbach_of_pos
    (hpos : 0 < schnirelmannDensity ({0, 1} ∪ G : Set ℕ)) :
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n := by
  have hpos' : 0 < @schnirelmannDensity ({0, 1} ∪ G : Set ℕ) (Classical.decPred _) := by
    convert hpos
  obtain ⟨h, hh⟩ := LeanLab.Schnirelmann.exists_nsmul_eq_univ ({0, 1} ∪ G : Set ℕ)
    (Or.inl (Or.inl rfl)) hpos'
  refine ⟨2 * h + 2, fun n hn => ?_⟩
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by omega, [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by omega, [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ h • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ h (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by omega, hs⟩

/-- **S3 implies S4.** Positive lower density of Goldbach sums gives positive Schnirelmann
density of `{0, 1} ∪ G`, since `1` is in the set and covers the small range. -/
theorem S4_of_S3 (h3 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * N ≤ #{n ∈ Finset.Icc 1 N | n ∈ G}) :
    0 < schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  obtain ⟨c, hc, N₀, hN⟩ := h3
  set δ : ℝ := min c (1 / ((N₀ : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := lt_min hc (by positivity)
  refine lt_of_lt_of_le hδpos ?_
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnR]
  rcases Nat.lt_or_ge n N₀ with hlt | hge
  · -- `1` is counted
    have h1 : (1 : ℝ) ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
      have : 1 ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
        apply Finset.card_pos.mpr
        exact ⟨1, by simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, hn⟩,
          Or.inl (Or.inr rfl)⟩⟩
      exact_mod_cast this
    have hnN : (n : ℝ) ≤ N₀ := by exact_mod_cast hlt.le
    calc δ * n ≤ (1 / ((N₀ : ℝ) + 1)) * n := by gcongr; exact min_le_right _ _
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
      _ ≤ _ := h1
  · have h := hN n hge
    have hsub : #{a ∈ Finset.Icc 1 n | a ∈ G} ≤
        #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
      apply Finset.card_le_card
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at ha ⊢
      exact ⟨⟨by omega, ha.1.2⟩, Or.inr ha.2⟩
    have hsubR : (#{a ∈ Finset.Icc 1 n | a ∈ G} : ℝ) ≤
        #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by exact_mod_cast hsub
    calc δ * n ≤ c * n := by gcongr; exact min_le_left _ _
      _ ≤ _ := h.trans hsubR

/-- **Reduction.** Schnirelmann's bounded-primes theorem follows from S3 alone. -/
theorem schnirelmann_goldbach_of_S3 (h3 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * N ≤ #{n ∈ Finset.Icc 1 N | n ∈ G}) :
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n :=
  schnirelmann_goldbach_of_pos (S4_of_S3 h3)

end LeanLab.SchnirelmannGoldbach
