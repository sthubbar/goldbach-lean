module

public import LeanLab.BhowmikGrimmelt2026.Theorem31Inputs150
public import LeanLab.BhowmikGrimmelt2026.RouteCount508
public import LeanLab.BhowmikGrimmelt2026.SPLIT_primitive_psi_zero_expansion508

/-!
BhowmikGrimmelt2026, P0029, Theorem 3.1 finish wiring. PREP 2026-11-21, branch
claude/BhowmikGrimmelt2026-route_finish.

`theorem31_finish150` proves exactly the sealed proposition `Theorem31` of Statements.lean, the
statement of `theorem31_decomposed150`, CONDITIONAL ON the cited Davenport chapter 19 half weighted
truncated explicit formula for primitive nonprincipal characters, taken as the explicit hypothesis
`hDav` whose text is word for word the statement of `davenport_integer_half_formula592` of
SPLIT_davenport_integer_formula592.lean. Davenport, Multiplicative Number Theory, second edition,
chapter 19, pages 117 and 118, is CITED-LEFT and not split here.

The two open route leaves are wired as follows.
* `oscillatory_zero_modes508` is replaced by `oscillatory_zero_modes508_route_count` of
  RouteCount508.lean, the same statement word for word.
* `primitive_psi_zero_expansion508` is replaced by an adapted copy of
  `primitive_psi_zero_expansion508_split` with `hDav` in place of the Davenport leaf.
Every intermediate theorem between those leaves and `Theorem31` is an ADAPTED COPY whose proof
text is the original with one leaf name swapped; no statement on main changes. The final step
reuses `theorem31_of_inputs_full150` of Theorem31Inputs150.lean with `hardy_critical_line_zero150`
and `arc_tails_sup150`.

This file opens no leaf and adds no new definition. Binary Goldbach is OPEN: Theorem 3.1 bounds the
exceptional set under a zero hypothesis unproved for every Θ below one. AI wrote the Lean code.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

/-- ADAPTED COPY of `davenport_integer_formula592` of SPLIT_davenport_integer_formula592.lean, Davenport
second edition page 117, with the cited half weighted formula taken as the hypothesis `hDav`.
Statement otherwise unchanged. -/
theorem davenport_integer_formula_of592 (hDav :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖(∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  obtain ⟨D, hD, hhalf⟩ := hDav
  refine ⟨D + 1, by linarith, ?_⟩
  intro q _ χ hprim hχ T hT Z hzeros n hn
  let P : ℂ := ∑ m ∈ Finset.range (n + 1),
    (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)
  let P₀ : ℂ := (∑ m ∈ Finset.range n,
    (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
    (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)
  let E : ℝ := (n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 + Real.log q + Real.log n
  have hendpoint : ‖P - P₀‖ ≤ Real.log n / 2 := sharp_half_weight_error541 χ n
  have hf := hhalf q χ hprim hχ T hT Z hzeros n hn
  change ‖P₀ + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
    (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
    ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤ D * E at hf
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hT0 : 0 < T := by linarith
  have hbudget : Real.log n ≤ E := by
    have hnonneg : 0 ≤ (n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 := by positivity
    dsimp [E]
    linarith
  change ‖P + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
    (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
    ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤ (D + 1) * E
  have heq : P + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
      (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
      (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ) =
      (P - P₀) + (P₀ + (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
      (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
      (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ)) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hendpoint hf).trans (by nlinarith))

/-- ADAPTED COPY of `nonprincipal_psi_zero_bound508`, P0029 page 11 display 3.5, step 2 of the split of
`primitive_psi_zero_expansion508`, with `davenport_integer_formula592` replaced by its copy above. -/
theorem nonprincipal_psi_zero_bound_of508 (hDav :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n)) (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨D, hD, hformula⟩ := davenport_integer_formula_of592 hDav
  obtain ⟨B, hB, hlow⟩ := low_reciprocal_bound592 Θ hΘ hZ
  obtain ⟨A, hA, hedge⟩ := boundary_zero_bound592
  obtain ⟨C₁, hC₁, hone⟩ := psi_one_bound592 Θ hΘ hZ
  refine ⟨max C₁ (20 * D + 4 * B + 8 * A), le_trans hC₁ (le_max_left _ _), ?_⟩
  intro X hX q _ hq χ hprim hχ T hT Z hzeros n hn hnX
  by_cases hn1 : n = 1
  · subst n
    simpa only [Nat.cast_one] using ((hone X hX q hq χ T hT Z hzeros).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₁ (20 * D + 4 * B + 8 * A))
        (sq_nonneg (Real.log (X : ℝ)))))
  have hn2 : 2 ≤ n := by omega
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hT2 : 2 ≤ T := hXr.trans hT.1
  have hnTr : (n : ℝ) ≤ T := (by exact_mod_cast hnX : (n : ℝ) ≤ X).trans hT.1
  obtain ⟨hbudget, hlowlog, hedgelog⟩ := davenport_log_budget592 hX hq hn hnX hT
  have hf := hformula q χ hprim hχ T hT2 Z hzeros n hn2
  have hl := hlow q χ (Z.filter (fun ρ => |ρ.im| < 1)) (by
    intro ρ hρ
    obtain ⟨hzmem, him⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, h0, h1, _⟩ := (hzeros ρ).mp hzmem
    exact ⟨hz, h0, h1, him.le⟩)
  have he := hedge q χ T (by linarith) n hn hnTr
    (Z.filter (fun ρ => ¬ |ρ.im| < T)) (by
      intro ρ hρ
      obtain ⟨hzmem, him⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, h0, h1, himT⟩ := (hzeros ρ).mp hzmem
      exact ⟨hz, h0, h1, le_antisymm himT (le_of_not_gt him)⟩)
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ : ℂ => |ρ.im| < T)
    (fun ρ => (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ)
  have heq : (∑ m ∈ Finset.range (n + 1),
      (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
      ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ =
      ((∑ m ∈ Finset.range (n + 1),
        (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T), (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ) +
      (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ) +
      ∑ ρ ∈ Z.filter (fun ρ => ¬ |ρ.im| < T), (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ := by
    rw [← hsplit]
    ring
  rw [heq]
  have htri (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le (a + b) c).trans (add_le_add (norm_add_le a b) (le_refl ‖c‖))
  have hsum := add_le_add (add_le_add hf hl) he
  have hfinal : D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 + Real.log q + Real.log n) +
      B * Real.log (2 * (q : ℝ)) + A * Real.log ((q : ℝ) * (T + 2)) ≤
      (20 * D + 4 * B + 8 * A) * Real.log X ^ 2 := by
    have hd := mul_le_mul_of_nonneg_left hbudget hD
    have hb := mul_le_mul_of_nonneg_left hlowlog hB
    have ha := mul_le_mul_of_nonneg_left hedgelog hA
    nlinarith
  exact ((htri _ _ _).trans (hsum.trans hfinal)).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

/-- ADAPTED COPY of `primitive_psi_zero_expansion508_split`: the statement of the leaf
`primitive_psi_zero_expansion508`, P0029 page 11 display 3.5, with `hDav` added. -/
theorem primitive_psi_zero_expansion_of508 (hDav :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n)) (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨C₂, hC₂, hnp⟩ := nonprincipal_psi_zero_bound_of508 hDav Θ hΘ hZ
  obtain ⟨C₃, hC₃, hpr⟩ := principal_psi_zero_bound508 Θ hΘ hZ
  refine ⟨max C₂ C₃, hC₂.trans (le_max_left C₂ C₃), ?_⟩
  intro X hX q _ hqQ χ hprim
  obtain ⟨T, hT, Z, hchar⟩ := zero_set_window508 χ hX hprim
  refine ⟨T, hT, Z, hchar, ?_⟩
  intro n hn1 hnX
  have hlog : (0 : ℝ) ≤ Real.log X ^ 2 := sq_nonneg (Real.log X)
  rcases eq_or_ne χ 1 with h1 | h1
  · subst h1
    have hmain : (if (1 : DirichletCharacter ℂ q) = 1 then (n : ℂ) else 0) = (n : ℂ) := by
      simp
    rw [hmain]
    exact (hpr X hX q hqQ 1 hprim rfl T hT Z hchar n hn1 hnX).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₂ C₃) hlog)
  · have hmain : (if χ = 1 then (n : ℂ) else 0) = 0 := by
      simp only [ite_eq_right h1]
    rw [hmain, sub_zero]
    exact (hnp X hX q hqQ χ hprim h1 T hT Z hchar n hn1 hnX).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₂ C₃) hlog)

/-- ADAPTED COPY of `psi_zero_expansion504`, P0029 page 11 display 3.5, the induction from primitive
characters to all characters, with the primitive leaf replaced by its copy above. -/
theorem psi_zero_expansion_of504 (hDav :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n)) (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨C, hC, hprimitive⟩ := primitive_psi_zero_expansion_of508 hDav Θ hΘ hZ
  refine ⟨C + 1 / Real.log 2, by positivity, ?_⟩
  intro X hX q _ hq χ
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd := χ.conductor_dvd_level
  have hr : χ.conductor ≤ Nat.sqrt X :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hd).trans hq
  obtain ⟨T, hT, Z, hmem, hbound⟩ := hprimitive X hX χ.conductor hr
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  have hz (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
      DirichletCharacter.LFunction χ ρ = 0 ↔
        DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      character_zero_changeLevel508 hd χ.primitiveCharacter h0 h1
  have hm (ρ : ℂ) (hρ : ρ ∈ Z) : mult χ ρ = mult χ.primitiveCharacter ρ := by
    have hh := (hmem ρ).mp hρ
    simpa only [χ.changeLevel_primitiveCharacter] using
      character_mult_changeLevel508 hd χ.primitiveCharacter hh.2.1 hh.2.2.1
  have hmain : χ = 1 ↔ χ.primitiveCharacter = 1 := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      (DirichletCharacter.changeLevel_eq_one_iff (χ := χ.primitiveCharacter) hd)
  refine ⟨T, hT, Z, ?_, ?_⟩
  · intro ρ
    rw [hmem]
    constructor
    · rintro ⟨hL, h0, h1, hT'⟩
      exact ⟨(hz ρ h0 h1).mpr hL, h0, h1, hT'⟩
    · rintro ⟨hL, h0, h1, hT'⟩
      exact ⟨(hz ρ h0 h1).mp hL, h0, h1, hT'⟩
  · intro n hn hnX
    have hmode : (∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) =
        ∑ ρ ∈ Z, (mult χ.primitiveCharacter ρ : ℂ) * (n : ℂ) ^ ρ / ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hm ρ hρ]
    have he :
        (∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
        (if χ = 1 then (n : ℂ) else 0) +
        ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ =
        ((∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
          ∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor)) +
        ((∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor)) -
        (if χ.primitiveCharacter = 1 then (n : ℂ) else 0) +
        ∑ ρ ∈ Z, (mult χ.primitiveCharacter ρ : ℂ) * (n : ℂ) ^ ρ / ρ) := by
      rw [hmode]
      have hmainval : (if χ = 1 then (n : ℂ) else 0) =
          (if χ.primitiveCharacter = 1 then (n : ℂ) else 0) := by
        by_cases hc : χ = 1
        · simp only [hc, hmain.mp hc, ite_true]
        · simp only [hc, hmain.not.mp hc, ite_false]
      rw [hmainval]
      ring
    have hdiff := psi_changeLevel_bound508 hd χ.primitiveCharacter n X
      (Nat.pos_of_ne_zero (NeZero.ne q)) hn hnX (hq.trans (Nat.sqrt_le_self X))
    rw [χ.changeLevel_primitiveCharacter] at hdiff
    rw [he]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ Real.log X ^ 2 / Real.log 2 + C * Real.log X ^ 2 :=
        add_le_add hdiff (hbound n hn hnX)
      _ = _ := by ring

/-- ADAPTED COPY of `sharp_rational_arc508`, P0029 pages 11 and 12 displays 3.5 through 3.7, with the
open leaf `oscillatory_zero_modes508` replaced by `oscillatory_zero_modes508_route_count` of
RouteCount508.lean, whose statement is word for word the same. -/
theorem sharp_rational_arc_count508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    (hpsi : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt X → ∀ a : ℕ, Nat.Coprime a q →
      ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
        ‖Ssum X ((a : ℝ) / q + β) -
          ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β‖ ≤
        C * (X : ℝ) ^ (Θ + ε) *
          (Real.sqrt q * Real.sqrt (1 + |β| * X)) := by
  classical
  intro ε hε
  obtain ⟨Cψ, hCψ, hψ⟩ := hpsi
  obtain ⟨Cz, hCz, hz⟩ := oscillatory_zero_modes508_route_count Θ hΘ hZ ε hε
  let K : ℝ := (2 / ε) ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : 1 / 2 ≤ Θ := zeroBound_lower150 hZ
  let A : ℝ := 10 * Real.pi * Cψ * K
  let E : ℝ := K / Real.log 2
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCψ) hK
  have hE : 0 ≤ E := div_nonneg hK hL.le
  refine ⟨Cz + A + E, by positivity, ?_⟩
  intro X hX q hq hqQ a ha β hβ
  haveI : NeZero q := ⟨by omega⟩
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hxp : 0 < (X : ℝ) := lt_of_lt_of_le zero_lt_one hx
  let W : ℝ := (X : ℝ) ^ (Θ + ε)
  let F : ℝ := Real.sqrt q * Real.sqrt (1 + |β| * X)
  have hW : 0 ≤ W := Real.rpow_nonneg hxp.le _
  have hF : 1 ≤ F := by
    have hsq : (1 : ℝ) ≤ Real.sqrt q := Real.le_sqrt_of_sq_le (by
      norm_num
      exact_mod_cast hq)
    have hsf : (1 : ℝ) ≤ Real.sqrt (1 + |β| * X) :=
      Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (abs_nonneg β) (Nat.cast_nonneg X)])
    dsimp [F]
    nlinarith
  have hWF : W ≤ W * F := by nlinarith
  have hrem : Real.sqrt X * Real.log X ^ 2 ≤ K * W :=
    sqrt_log_power_budget508 hx hhalf hε
  have hlog : Real.log X ^ 2 ≤ K * W :=
    (log_sq_power_budget508 hx hε).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hK)
  have hunit : IsUnit ((a : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime a q).mpr ha
  have hb := sharp_rational_mode_reduction508 (a : ℤ) hunit
    (by omega : 1 ≤ X) hq hqQ hβ (mul_nonneg hCψ (sq_nonneg (Real.log X)))
    (mul_nonneg (mul_nonneg hCz hW) (Real.sqrt_nonneg (1 + |β| * X))) (by
      intro χ
      obtain ⟨T, hT, Z, hspec, hr⟩ := hψ X hX q hqQ χ
      refine ⟨Z, ?_, hz X hX q hqQ χ T hT Z hspec β hβ⟩
      intro n hnX
      by_cases hn : n = 0
      · rw [hn, sharp_remainder_zero508 χ Z (fun ρ hρ => ((hspec ρ).mp hρ).2.1)]
        simpa only [norm_zero] using mul_nonneg hCψ (sq_nonneg (Real.log X))
      · simpa only [sharpRemainder508, psiCharacter502, zeroPartial508, mul_div_assoc] using
          hr n (by omega) hnX)
  have hrb : 10 * Real.pi * (Cψ * Real.log X ^ 2) * Real.sqrt X ≤ A * (W * F) := by
    calc
      _ = (10 * Real.pi * Cψ) * (Real.sqrt X * Real.log X ^ 2) := by ring
      _ ≤ (10 * Real.pi * Cψ) * (K * W) := mul_le_mul_of_nonneg_left hrem
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCψ)
      _ = A * W := by dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWF hA
  have hlb : Real.log X ^ 2 / Real.log 2 ≤ E * (W * F) := by
    calc
      _ ≤ (K * W) / Real.log 2 := div_le_div_of_nonneg_right hlog hL.le
      _ = E * W := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWF hE
  have hc : Real.sqrt q * (Cz * W * Real.sqrt (1 + |β| * X)) = Cz * (W * F) := by
    dsimp [F]
    ring
  change _ ≤ (Cz + A + E) * W * F
  convert hb.trans (add_le_add (add_le_add (le_of_eq hc) hrb) hlb) using 1
  ring

/-- ADAPTED COPY of `major_arc_partial_summation504`, P0029 pages 11 and 12, the Dirichlet arc assembly,
through `sharp_rational_arc_count508`. -/
theorem major_arc_partial_summation_count504 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    (hpsi : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε) := by
  intro ε hε
  obtain ⟨C, hC, hlocal⟩ := sharp_rational_arc_count508 Θ hΘ hZ hpsi ε hε
  refine ⟨C * Real.sqrt 5, ?_⟩
  intro X hX α hα
  obtain ⟨q, hq, hαq⟩ := exists_arc502 (by omega : 1 ≤ X) α
  have hq1 := (Finset.mem_Icc.mp hq).1
  have hqQ := (Finset.mem_Icc.mp hq).2
  haveI : NeZero q := ⟨by omega⟩
  let a : ℕ := (nint150 ((q : ℝ) * α)).toNat
  let β : ℝ := α - (a : ℝ) / q
  have haZ : (a : ℤ) = nint150 ((q : ℝ) * α) :=
    Int.toNat_of_nonneg (nint_mem150 (q := q) hα).1
  have har : (a : ℝ) = (nint150 ((q : ℝ) * α) : ℝ) := by exact_mod_cast haZ
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq1
  have hβq : (q : ℝ) * |β| = |(q : ℝ) * α - nint150 ((q : ℝ) * α)| := by
    calc
      _ = |(q : ℝ) * β| := by rw [abs_mul, abs_of_pos hqp]
      _ = _ := by
        congr 1
        dsimp [β]
        rw [har]
        field_simp
  have hb1 : |β| ≤ (1 / (Nat.sqrt X : ℝ)) / q :=
    (le_div_iff₀ hqp).mpr (by rw [mul_comm, hβq]; exact hαq.1)
  have hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) := by
    simpa only [div_div, mul_comm] using hb1
  have hcop : Nat.Coprime a q := assigned_coprime504 hq1 hα hαq
  have hV : VX150 X α =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β := by
    rw [VX_eq_arcTerm502 hq hαq]
    change ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) *
      TX150 X (α - (nint150 ((q : ℝ) * α) : ℝ) / q) = _
    rw [← har]
  have hh := hlocal X hX q hq1 hqQ a hcop β hβ
  have hαeq : (a : ℝ) / q + β = α := by dsimp [β]; ring
  rw [hαeq] at hh
  rw [hV]
  calc
    _ ≤ C * (X : ℝ) ^ (Θ + ε) *
        (Real.sqrt q * Real.sqrt (1 + |β| * X)) := hh
    _ ≤ C * (X : ℝ) ^ (Θ + ε) *
        (Real.sqrt 5 * (X : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (gauss_arc_scale508 (by omega) hq1 hqQ hβ) (by positivity)
    _ = _ := by
      have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
      have he : (X : ℝ) ^ (Θ + 1 / 4 + ε) =
          (X : ℝ) ^ (Θ + ε) * (X : ℝ) ^ (1 / 4 : ℝ) := by
        rw [show Θ + 1 / 4 + ε = (Θ + ε) + 1 / 4 by ring, Real.rpow_add hxp]
      rw [he]
      ring

/-- ADAPTED COPY of `major_arc_uniform150` of MeanSquareLeaves150.lean, P0029 pages 11 and 12 display
3.5 with 3.6 and 3.7, CONDITIONAL ON `hDav`. -/
theorem major_arc_uniform_of150 (hDav :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n)) (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := major_arc_partial_summation_count504 Θ hΘ hZ
    (psi_zero_expansion_of504 hDav Θ hΘ hZ) ε hε
  refine ⟨max 1 C, fun X hX α hα => ?_⟩
  by_cases hX2 : 2 ≤ X
  · exact (hC X hX2 α hα).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) (by positivity))
  · have hX1 : X = 1 := by omega
    subst X
    rw [major_error_one504]
    simpa using le_max_left (1 : ℝ) C

/-- P0029 Theorem 3.1, the exact statement of `theorem31_decomposed150`, with no open leaf of its
own, CONDITIONAL ON `hDav`, the cited Davenport chapter 19 half weighted explicit formula, stated
exactly as `davenport_integer_half_formula592`. -/
theorem theorem31_finish150 (hDav :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n)) :
    Theorem31 :=
  theorem31_of_inputs_full150 (major_arc_uniform_of150 hDav) hardy_critical_line_zero150
    arc_tails_sup150

end LeanLab.BhowmikGrimmelt2026
