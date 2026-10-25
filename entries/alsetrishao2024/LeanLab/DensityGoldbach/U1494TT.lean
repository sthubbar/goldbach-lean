module

public import LeanLab.DensityGoldbach.U1467Prop31

/-!
Unit U-1494, run 20261022T1603Z-23862. P0047 Alsetri and Shao 2024, Theorem 1.2.

The TT* large spectrum lemma on `Z_N`, deterministic and fully general: if `0 ≤ f ≤ ν`,
`E ν ≤ A`, `|ν̂(s)| ≤ c` for every `s ≠ 0`, and `S` is a set of frequencies with `|f̂(r)| ≥ δ` on
`S`, then `(|S| δ)² ≤ A (|S| A + |S|² c)`.

Proof: pick unimodular `u_r` with `u_r f̂(r) = |f̂(r)|`, put `g(n) = Σ_{r ∈ S} u_r e(-rn/N)`; then
`|S| δ ≤ E f g ≤ E ν |g|`, Cauchy-Schwarz with weight `ν`, and `E ν |g|² = Σ_{r,r'} u_r ū_{r'}
ν̂(r - r')`, the diagonal costing `|S| E ν` and the rest `|S|² c`.

This is the standard argument, see Green 2005, Section 4, and Bourgain 1989, before the
enveloping sieve input; it is NOT new.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical ComplexConjugate

noncomputable section
namespace LeanLab.DensityGoldbach.U1494
open LeanLab.DensityGoldbach.U1446

variable {N : ℕ} [NeZero N]

/-- `E_n ν(n) |g(n)|²` expanded through `ν̂`. -/
lemma weighted_sq_expand (ν : ZMod N → ℝ) (S : Finset (ZMod N)) (u : ZMod N → ℂ) :
    (((1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖∑ r ∈ S, u r * ZMod.stdAddChar (-(r * n))‖ ^ 2 : ℝ)
      : ℂ) = ∑ r ∈ S, ∑ r' ∈ S, u r * conj (u r') * hatE N ν (r - r') := by
  have key : ∀ n : ZMod N, ((ν n * ‖∑ r ∈ S, u r * ZMod.stdAddChar (-(r * n))‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ S, ∑ r' ∈ S, u r * conj (u r') *
        ((ν n : ℂ) * ZMod.stdAddChar (-((r - r') * n))) := by
    intro n
    push_cast
    rw [← Complex.mul_conj', map_sum, sum_mul_sum]
    simp_rw [mul_sum]
    refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
    rw [map_mul, ← AddChar.map_neg_eq_conj, neg_neg]
    have : ZMod.stdAddChar (-((r - r') * n)) =
        ZMod.stdAddChar (-(r * n)) * ZMod.stdAddChar (r' * n) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this]; ring
  push_cast
  rw [mul_comm]
  have key' := fun n => key n
  push_cast at key'
  simp_rw [key']
  unfold hatE
  rw [sum_comm, sum_mul]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_comm, sum_mul]
  refine sum_congr rfl fun r' _ => ?_
  rw [← mul_sum]
  ring

/-- **TT* large spectrum lemma.** -/
theorem tt_star (f ν : ZMod N → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ ν n) (A c : ℝ)
    (hA : avg N ν ≤ A) (hc0 : 0 ≤ c) (hc : ∀ s : ZMod N, s ≠ 0 → ‖hatE N ν s‖ ≤ c)
    (δ : ℝ) (hδ : 0 < δ) (S : Finset (ZMod N)) (hS : ∀ r ∈ S, δ ≤ ‖hatE N f r‖) :
    ((S.card : ℝ) * δ) ^ 2 ≤ A * ((S.card : ℝ) * A + (S.card : ℝ) ^ 2 * c) := by
  have hν0 : ∀ n, 0 ≤ ν n := fun n => (hf n).1.trans (hf n).2
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have havg0 : 0 ≤ avg N ν := by
    unfold avg
    exact mul_nonneg (by positivity) (sum_nonneg fun n _ => hν0 n)
  have hA0 : 0 ≤ A := havg0.trans hA
  set u : ZMod N → ℂ := fun r => conj (hatE N f r) / (‖hatE N f r‖ : ℂ) with hu
  have hu1 : ∀ r, ‖u r‖ ≤ 1 := by
    intro r
    simp only [u, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  have huf : ∀ r ∈ S, u r * hatE N f r = (‖hatE N f r‖ : ℂ) := by
    intro r hr
    have hne : (‖hatE N f r‖ : ℂ) ≠ 0 := by
      exact_mod_cast (hδ.trans_le (hS r hr)).ne'
    simp only [u]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj', div_eq_iff hne]
    push_cast; ring
  set g : ZMod N → ℂ := fun n => ∑ r ∈ S, u r * ZMod.stdAddChar (-(r * n)) with hg
  -- Step 1: `Σ_S |f̂| = E f g`
  have h1 : ((∑ r ∈ S, ‖hatE N f r‖ : ℝ) : ℂ) =
      (1 / (N : ℂ)) * ∑ n : ZMod N, (f n : ℂ) * g n := by
    push_cast
    rw [← sum_congr rfl huf]
    simp only [g, hatE, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => sum_congr rfl fun n _ => ?_
    ring
  -- Step 2: `Σ_S |f̂| ≤ E ν |g|`
  have h2 : ∑ r ∈ S, ‖hatE N f r‖ ≤ (1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖ := by
    have e := congrArg norm h1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sum_nonneg fun r _ => norm_nonneg _)] at e
    rw [e, norm_mul]
    have hN' : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by rw [norm_div, norm_one]; simp
    rw [hN']
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n).1]
    exact mul_le_mul_of_nonneg_right (hf n).2 (norm_nonneg _)
  -- Step 3: Cauchy-Schwarz with weight `ν`
  have h3 : (∑ n : ZMod N, ν n * ‖g n‖) ^ 2 ≤
      (∑ n : ZMod N, ν n) * ∑ n : ZMod N, ν n * ‖g n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun n => Real.sqrt (ν n))
      (fun n => Real.sqrt (ν n) * ‖g n‖)
    have ea : ∀ n, Real.sqrt (ν n) * (Real.sqrt (ν n) * ‖g n‖) = ν n * ‖g n‖ := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (hν0 n)]
    have eb : ∀ n, Real.sqrt (ν n) ^ 2 = ν n := fun n => Real.sq_sqrt (hν0 n)
    have ec : ∀ n, (Real.sqrt (ν n) * ‖g n‖) ^ 2 = ν n * ‖g n‖ ^ 2 := fun n => by
      rw [mul_pow, eb]
    simp only [ea, eb, ec] at this
    exact this
  -- Step 4: expand and bound `E ν |g|²`
  set Q := (1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖ ^ 2 with hQ
  have h4 : Q ≤ (S.card : ℝ) * A + (S.card : ℝ) ^ 2 * c := by
    have e := weighted_sq_expand ν S u
    have hQ0 : 0 ≤ Q := mul_nonneg (by positivity)
      (sum_nonneg fun n _ => mul_nonneg (hν0 n) (by positivity))
    have hQn : Q = ‖((Q : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ0]
    rw [hQn]
    change ‖(((1 / (N : ℝ)) * ∑ n : ZMod N, ν n *
      ‖∑ r ∈ S, u r * ZMod.stdAddChar (-(r * n))‖ ^ 2 : ℝ) : ℂ)‖ ≤ _
    rw [e]
    have hpt : ∀ r ∈ S, ∀ r' ∈ S, ‖u r * conj (u r') * hatE N ν (r - r')‖ ≤
        (if r' = r then A else 0) + c := by
      intro r _ r' _
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hn : ‖hatE N ν (r - r')‖ ≤ (if r' = r then A else 0) + c := by
        by_cases h : r' = r
        · subst h
          rw [if_pos rfl, sub_self, hatE_zero, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg havg0]
          linarith
        · rw [if_neg h, zero_add]
          exact hc _ (sub_ne_zero.2 (Ne.symm h))
      have hb : 0 ≤ (if r' = r then A else 0) + c := by split_ifs <;> linarith
      calc ‖u r‖ * ‖u r'‖ * ‖hatE N ν (r - r')‖ ≤ 1 * 1 * ‖hatE N ν (r - r')‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul (hu1 r) (hu1 r') (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul, one_mul]; exact hn
    calc ‖∑ r ∈ S, ∑ r' ∈ S, u r * conj (u r') * hatE N ν (r - r')‖
        ≤ ∑ r ∈ S, ∑ r' ∈ S, ((if r' = r then A else 0) + c) :=
          (norm_sum_le _ _).trans (sum_le_sum fun r hr =>
            (norm_sum_le _ _).trans (sum_le_sum fun r' hr' => hpt r hr r' hr'))
      _ = ∑ r ∈ S, (A + (S.card : ℝ) * c) := by
          refine sum_congr rfl fun r hr => ?_
          rw [sum_add_distrib, sum_ite_eq' S r (fun _ => A), if_pos hr, sum_const, nsmul_eq_mul]
      _ = (S.card : ℝ) * A + (S.card : ℝ) ^ 2 * c := by
          rw [sum_const, nsmul_eq_mul]; ring
  -- assemble
  have hSδ : (S.card : ℝ) * δ ≤ ∑ r ∈ S, ‖hatE N f r‖ := by
    have := sum_le_sum hS
    rwa [sum_const, nsmul_eq_mul] at this
  have hP : 0 ≤ (S.card : ℝ) * δ := by positivity
  have hstep : ((S.card : ℝ) * δ) ^ 2 ≤ ((1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖) ^ 2 :=
    pow_le_pow_left₀ hP (hSδ.trans h2) 2
  have hav : (1 / (N : ℝ)) * ∑ n : ZMod N, ν n = avg N ν := rfl
  have hQ0 : 0 ≤ Q := mul_nonneg (by positivity)
    (sum_nonneg fun n _ => mul_nonneg (hν0 n) (by positivity))
  calc ((S.card : ℝ) * δ) ^ 2 ≤ ((1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖) ^ 2 := hstep
    _ = (1 / (N : ℝ)) ^ 2 * (∑ n : ZMod N, ν n * ‖g n‖) ^ 2 := by ring
    _ ≤ (1 / (N : ℝ)) ^ 2 * ((∑ n : ZMod N, ν n) * ∑ n : ZMod N, ν n * ‖g n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = avg N ν * Q := by rw [← hav, hQ]; ring
    _ ≤ A * ((S.card : ℝ) * A + (S.card : ℝ) ^ 2 * c) :=
        mul_le_mul hA h4 hQ0 hA0

/-- The count form: if moreover `A c ≤ δ²/2`, then `|S| ≤ 2 A² / δ²`. -/
theorem tt_star_count (f ν : ZMod N → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ ν n) (A c : ℝ)
    (hA : avg N ν ≤ A) (hc0 : 0 ≤ c) (hc : ∀ s : ZMod N, s ≠ 0 → ‖hatE N ν s‖ ≤ c)
    (δ : ℝ) (hδ : 0 < δ) (hAc : A * c ≤ δ ^ 2 / 2)
    (S : Finset (ZMod N)) (hS : ∀ r ∈ S, δ ≤ ‖hatE N f r‖) :
    (S.card : ℝ) * δ ^ 2 ≤ 2 * A ^ 2 := by
  have h := tt_star f ν hf A c hA hc0 hc δ hδ S hS
  set R := (S.card : ℝ)
  have hR : 0 ≤ R := Nat.cast_nonneg _
  rcases hR.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  · -- `R² δ² ≤ R A² + R² A c`, divide by `R`
    have h' : R * (R * δ ^ 2) ≤ R * (A ^ 2 + R * (A * c)) := by nlinarith
    have h'' := le_of_mul_le_mul_left h' hpos
    have : R * (A * c) ≤ R * (δ ^ 2 / 2) := mul_le_mul_of_nonneg_left hAc hR
    nlinarith

end LeanLab.DensityGoldbach.U1494
