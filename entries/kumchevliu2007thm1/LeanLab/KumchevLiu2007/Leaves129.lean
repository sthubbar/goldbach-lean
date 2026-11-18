module

public import LeanLab.KumchevLiu2007.Decomp1534a
public import LeanLab.KumchevLiu2007.Decomp1534c
public import LeanLab.KumchevLiu2007.Decomp506a
public import LeanLab.KumchevLiu2007.Decomp506b
public import LeanLab.KumchevLiu2007.Trunc129Sifted
public import LeanLab.KumchevLiu2007.Trunc129Window
public import LeanLab.KumchevLiu2007.Trunc129Main

/-!
Kumchev and Liu, arXiv 0801.0130, paper P0088. Branch repair of Task129,
2026-11-13.

The branch claude/KumchevLiu2007-residual_input-p3 added three open leaves to the
existing file `Decomp129`, which the lab rule forbids for an existing file. They
live here instead, each on a theorem whose doc comment starts with LEAF, and
`Decomp129` proves its own three steps by applying them, so the statements of
those steps are unchanged. All three are proved in this copy.

This file declares nothing: no def, abbrev, structure, instance, notation or
axiom. The four definitions of `Decomp129` that the leaves mention (the window
Y, the window pair set, the sieve level and the sifted pair count, the partial
product and the sieve product, the main term and the residual) are written out
in full in each statement. `Decomp129` imports this file and so cannot supply
them, and a copy would be a new definition. Writing them out keeps the two
statements definitionally equal, which is what `Decomp129` uses.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Task129L

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: Page 16 display 57 and page 17 display 58. Lemma 3.7, the Rosser
Iwaniec upper bound sieve cited from Iwaniec Theorem 1, applied with D = Y to
the 1/9 and z = exp of L to the 1 - delta/2 to the sequence A of page 16, with N
of display 57 at most a constant times Y to the 1/2 L to the -2 log L by the
prime number theorem and the remainder sum bounded through Bombieri Vinogradov
and Cauchy's inequality. The left side is the sifted pair count, which is at
most the sum of Phi(m, z) over A for large X. A can be taken arbitrarily large.
Here windowY, sieveLevel, sieveV and siftedPairs are written out.
CITED: the upper bound sieve of Lemma 3.7 is not in Mathlib and not in the
imports of Decomp129. -/
theorem sifted_sieve_input (A B δ ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) →
      (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => (∀ p : ℕ, p.Prime → p ∣ v.1 → (Real.exp (Real.log X ^ (1 - δ / 2))) ≤ (p : ℝ)) ∧
      ¬ v.2.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) ≤
        K * ((X ^ (7 / 12 + ε / 2)) ^ (1 / 2 : ℝ) * Real.log X ^ (-2 : ℝ) *
            Real.log (Real.log X) * ∏ p ∈ (Finset.range (⌊(Real.exp (Real.log X ^ (1 - δ / 2)))⌋₊ + 1)).filter Nat.Prime,
      (1 - if p ∣ n then 0 else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / (Nat.totient p : ℝ)) +
          (X ^ (7 / 12 + ε / 2)) ^ (1 / 2 : ℝ) * Real.log X ^ (-A)) := by
  exact Task506b.sifted_sieve_bound A B δ ε hA hB hδ hδ1 hε hε1

/-- LEAF: Lemma 3.8 on page 14, display 49, for j = 2, a local twin of
Task129b.lemma38_two with the partial product of page 13 display 45 in place of
the identical Task129b.product2 and the interval numbers unfolded. The proof
chain of Task342e.lemma38_two_proved imports Decomp129, so neither Decomp129 nor
this file can import it: it would close the cycle from Decomp129 to this file to
Task342e to Decomp129. The clean downstream supply is
Supply129r.lemma38_two_local_supply. Here series2 and partialProduct2 are
written out. CITED. -/
theorem lemma38_two_local (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖(∑ q ∈ Finset.Icc 1 ⌊(P)⌋₊, U1534.A2 n q) - ∏ p ∈ (Finset.range (⌊(Q)⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  exact Task506aTask342e.lemma38_two_proved A ε hA hε

/-- Page 2 display 1 and page 16 Proposition 2. When 1 < X, the interval hypothesis
X ^ (7 / 18 + ε) ≤ H ≤ X forces ε ≤ 11 / 18. -/
theorem large_eps_vacuous_agy61 {X H ε : ℝ} (hX1 : 1 < X)
    (hH1 : X ^ (7 / 18 + ε) ≤ H) (hH2 : H ≤ X) : ε ≤ 11 / 18 := by
  have hle : X ^ (7 / 18 + ε) ≤ X ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact hH1.trans hH2
  have hexp : 7 / 18 + ε ≤ 1 := (Real.rpow_le_rpow_left_iff hX1).mp hle
  linarith

/-- Page 2 display 5 and page 16 Proposition 2. Above X + Y, the unfolded window
pair finset is empty because v.1 < X and v.2 < sqrt Y force v.1 + v.2 ^ 2 < X + Y. -/
theorem window_empty_above_agy61 (X Y : ℝ) (n : ℕ) (hY : 0 ≤ Y) (hn : X + Y ≤ (n : ℝ)) :
    (((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro v _ hv
  rcases hv with ⟨_, hv1, _, hv2, hsum⟩
  have hsq : (v.2 : ℝ) ^ 2 < Y := by
    have h0 : 0 ≤ (v.2 : ℝ) := Nat.cast_nonneg v.2
    have hmul : (v.2 : ℝ) * (v.2 : ℝ) < Real.sqrt Y * Real.sqrt Y :=
      mul_lt_mul'' hv2 hv2 h0 h0
    nlinarith [Real.mul_self_sqrt hY]
  have hsumR : (v.1 : ℝ) + (v.2 : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast hsum
  linarith

/-- Page 16 Proposition 2. When H is at most the Proposition 2 subwindow length
(X ^ (7 / 12 + ε / 2)) ^ (1 - ε), no integer n ≤ ⌊X + H⌋₊ satisfies
X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < n, so the exceptional count vanishes. -/
theorem cntIoc_zero_of_le_subwindow_agy61 (P : ℕ → Prop) (X H ε : ℝ)
    (hXH : 0 ≤ X + H) (hH : H ≤ (X ^ (7 / 12 + ε / 2)) ^ (1 - ε)) :
    cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧ P n) X H = 0 := by
  unfold cntIoc
  apply Finset.card_eq_zero.mpr
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
  intro hn _ hgt
  have hnle : (n : ℝ) ≤ X + H := by
    have h1 : n ≤ ⌊X + H⌋₊ := Nat.lt_succ_iff.mp hn
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hXH)
  intro _
  linarith

/-- Page 16 Proposition 2 and page 2 Theorem 1. The full range residual extension
reduces to the active transition regime ε ≤ 11 / 18, (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < H,
and n strictly below X + X ^ (7 / 12 + ε / 2), because outside this regime the
hypotheses are vacuous, the subwindow covers the interval, or the window pair set is empty. -/
theorem residual_full_range_extension_of_transition_agy61 (A : ℝ) (_hA : 0 < A)
    (htrans : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 11 / 18 →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < H → H ≤ X →
        (cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧
          (n : ℝ) < X + X ^ (7 / 12 + ε / 2) ∧ InH2 n ∧
          K * ‖((((∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) : ℝ) : ℂ) * (∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q))‖ * Real.log X ^ (-1 + δ) <
          |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))|) X H : ℝ) ≤
          C * H / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧ InH2 n ∧
          K * ‖((((∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) : ℝ) : ℂ) * (∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q))‖ * Real.log X ^ (-1 + δ) <
          |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))|) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, hB⟩ := htrans
  refine ⟨B0, hB0, fun B hB0B δ ε hδ hε => ?_⟩
  by_cases hε1 : ε ≤ 11 / 18
  · obtain ⟨C, K, X0, hC, hK, hX0, hmain⟩ := hB B hB0B δ ε hδ hε hε1
    refine ⟨C, K, X0, hC, hK, hX0, fun X H hX hH1 hH2 => ?_⟩
    have hX2 : 2 ≤ X := hX0.trans hX
    have hXp : 0 < X := by linarith
    have hHp : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hH1
    have hLp : 0 < Real.log X := Real.log_pos (by linarith)
    by_cases hHsub : H ≤ (X ^ (7 / 12 + ε / 2)) ^ (1 - ε)
    · rw [cntIoc_zero_of_le_subwindow_agy61 _ X H ε (by linarith) hHsub]
      simp only [Nat.cast_zero]
      positivity
    · have hHsub' : (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < H := lt_of_not_ge hHsub
      have hmono : cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧ InH2 n ∧
          K * ‖((((∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) : ℝ) : ℂ) * (∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q))‖ * Real.log X ^ (-1 + δ) <
          |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))|) X H ≤
        cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧
          (n : ℝ) < X + X ^ (7 / 12 + ε / 2) ∧ InH2 n ∧
          K * ‖((((∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) : ℝ) : ℂ) * (∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q))‖ * Real.log X ^ (-1 + δ) <
          |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))|) X H := by
        apply U1534.cnt_mono
        intro n hn
        refine ⟨hn.1, ?_, hn.2.1, hn.2.2⟩
        by_contra hge
        have hge' : X + X ^ (7 / 12 + ε / 2) ≤ (n : ℝ) := le_of_not_gt hge
        have hY0 : 0 ≤ X ^ (7 / 12 + ε / 2) := Real.rpow_nonneg hXp.le _
        have hemp := window_empty_above_agy61 X (X ^ (7 / 12 + ε / 2)) n hY0 hge'
        have hbad := hn.2.2
        rw [hemp] at hbad
        simp at hbad
      exact (Nat.cast_le.mpr hmono).trans (hmain X H hX hH1 hHsub' hH2)
  · refine ⟨1, 1, 2, zero_lt_one, zero_lt_one, le_rfl, fun X H hX hH1 hH2 => ?_⟩
    exfalso
    exact hε1 (large_eps_vacuous_agy61 (by linarith) hH1 hH2)

/-- LEAF: Proposition 2 on page 16 is stated only for H at most Y to the
1 - epsilon, while Theorem 1 on page 2 allows H up to X. This is the remaining
range X + Y to the 1 - epsilon < n at most X + H, with the windows of page 2
displays 4 to 6 still anchored at X. The written paper has no proof of this
range; PROGRESS.md records it as BLOCKED NO WRITTEN PROOF. Here windowY, main2
and residualCount are written out. -/
theorem residual_full_range_extension (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧ InH2 n ∧
          K * ‖((((∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) : ℝ) : ℂ) * (∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q))‖ * Real.log X ^ (-1 + δ) <
          |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))|) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  -- PROVED 2026-11-17: the transition regime is supplied by the truncated window sieve
  -- route of Trunc129BV, Trunc129Sieve, Trunc129Mass, Trunc129Sifted, Trunc129Window and
  -- Trunc129Main, pages 16 and 17 displays 56 to 59 rerun on the truncated window.
  exact residual_full_range_extension_of_transition_agy61 A hA
    (Trunc129.transition_of_inputs A hA
      (fun A' B δ ε hA' hB hδ hδ1 hε hε1 =>
        Trunc129.trunc_sifted_sieve_bound A' B δ ε hA' hB hδ hδ1 hε hε1)
      (fun B δ ε hB hδ hε hε1 => Trunc129.trunc_residual_le_sifted B δ ε hB hδ hε hε1)
      (fun ε hε hε1 => Trunc129.trunc_integerMain_lower ε hε hε1))


end LeanLab.KumchevLiu2007.Task129L
