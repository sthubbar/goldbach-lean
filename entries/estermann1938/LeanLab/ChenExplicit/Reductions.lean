module

public import LeanLab.ChenExplicit.Statements

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Proved links between the explicit Chen statements. Nothing here proves Chen's theorem itself:
the analytic inputs `Yamada`, `BJS3`, `BJS4` stay hypotheses.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

/-- `1 / (n - 1)²` is summable over `ℕ`. -/
lemma summable_inv_sub_one_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) - 1) ^ 2) := by
  rw [← summable_nat_add_iff 2]
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine this.congr fun n => ?_
  push_cast; ring_nf

/-- **The twin prime constant is positive.** -/
theorem twinC_pos : 0 < twinC := by
  set f : {p : ℕ // p.Prime ∧ 2 < p} → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2 with hf
  have hge : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, (2 : ℝ) ≤ (p : ℝ) - 1 := by
    intro p
    have : (3 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.2
    linarith
  have hpos : ∀ p, 0 < f p := by
    intro p
    have h2 := hge p
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    simp only [hf]; linarith
  have hs : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p : ℝ) - 1) ^ 2)) :=
    (summable_inv_sub_one_sq.subtype _).neg
  have hlog : Summable (fun p => Real.log (f p)) := by
    have := Real.summable_log_one_add_of_summable hs
    refine this.congr fun p => ?_
    simp only [hf]; ring_nf
  have := Real.rexp_tsum_eq_tprod hpos hlog
  unfold twinC
  rw [← this]
  exact Real.exp_pos _

/-- The product defining `twinC` converges, so `tprod` is not the junk value `1`. -/
theorem twinC_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p : ℝ) - 1) ^ 2)) :=
    (summable_inv_sub_one_sq.subtype _).neg
  exact (Real.multipliable_one_add_of_summable hs).congr fun p => by ring

/-- The odd local factor `∏_{p>2, p ∣ N} (p-1)/(p-2)` is at least `1`. -/
lemma one_le_oddFactor (N : ℕ) :
    1 ≤ ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  apply Finset.one_le_prod₀
  intro p hp
  simp only [mem_filter] at hp
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
  rw [le_div_iff₀ (by linarith)]; linarith

/-- **`U_N > 0`.** -/
theorem U_pos (N : ℕ) : 0 < U N := by
  unfold U
  have := twinC_pos
  have := one_le_oddFactor N
  positivity

/-- A strict lower bound by a nonnegative quantity gives a representation. -/
lemma chenAbove_of_count {T : ℝ} (c : ℝ) (hc : 0 < c)
    (h : ∀ N : ℕ, Even N → T < N → c * U N * N / Real.log N ^ 2 < chenCount N) :
    ChenAbove T := by
  intro N hN hT
  have h1 := h N hN hT
  have h0 : 0 ≤ c * U N * N / Real.log N ^ 2 := by have := U_pos N; positivity
  have hpos : 0 < chenCount N := by exact_mod_cast h0.trans_lt h1
  unfold chenCount at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  simp only [mem_filter, mem_range] at hp
  exact ⟨p, N - p, hp.2.1, by omega, hp.2.2⟩

/-- **Yamada's Theorem 1.1 implies Chen above `exp exp 36`.** -/
theorem chenAbove_of_yamada (h : Yamada) : ChenAbove (Real.exp (Real.exp 36)) :=
  chenAbove_of_count _ (by norm_num) h

/-- **BJS Theorem 3 implies Chen above `exp exp 32.7`.** -/
theorem chenAbove_of_BJS3 (h : BJS3) : ChenAbove (Real.exp (Real.exp (327 / 10))) :=
  chenAbove_of_count _ (by norm_num) h

/-- A squarefree number with at most two prime factors is a `P₂`. -/
lemma isAtMostAlmostPrime_two_of_squarefree {m : ℕ} (hm : Squarefree m) (h : ω m ≤ 2) :
    Nat.IsAtMostAlmostPrime 2 m := by
  have hm0 : m ≠ 0 := hm.ne_zero
  refine ⟨hm0, ?_⟩
  rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hm0).mpr hm]
  exact h

/-- **BJS Corollary 4 implies Chen above `exp exp 32.7`.** -/
theorem chenAbove_of_BJS4 (h : BJS4) : ChenAbove (Real.exp (Real.exp (327 / 10))) := by
  intro N hN hT
  obtain ⟨p, m, hp, hNm, hsq, hω⟩ := h N hN hT
  exact ⟨p, m, hp, hNm, isAtMostAlmostPrime_two_of_squarefree hsq hω⟩

theorem BJS4_of_strong (h : BJS4strong) : BJS4 := by
  intro N hN hT
  obtain ⟨p, m, hp, hNm, _, hsq, hω⟩ := h N hN hT
  exact ⟨p, m, hp, hNm, hsq, hω⟩

/-- **BJS Corollary 4 gives Theorem 5 above `exp exp 32.7`**, with room to spare: `Ω m ≤ 2`. -/
theorem BJS5_large_of_BJS4 (h : BJS4) :
    ∀ N : ℕ, Even N → Real.exp (Real.exp (327 / 10)) < N →
      ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ m ≠ 0 ∧ (Ω m : ℝ) ≤ Real.exp (293 / 10) := by
  intro N hN hT
  obtain ⟨p, m, hp, hNm, hsq, hω⟩ := h N hN hT
  obtain ⟨hm0, hΩ⟩ := isAtMostAlmostPrime_two_of_squarefree hsq hω
  refine ⟨p, m, hp, hNm, hm0, ?_⟩
  have h2 : (Ω m : ℝ) ≤ 2 := by exact_mod_cast hΩ
  have : (2 : ℝ) ≤ Real.exp (293 / 10) := by
    have := Real.add_one_le_exp (293 / 10 : ℝ); linarith
  linarith

/-- On even `N` both bounds hold above `exp exp 36`; Yamada's constant `0.007` is the larger. -/
lemma yamada_const_gt_BJS3_const : (2 / 10000 : ℝ) < 7 / 1000 := by norm_num

end LeanLab.ChenExplicit
