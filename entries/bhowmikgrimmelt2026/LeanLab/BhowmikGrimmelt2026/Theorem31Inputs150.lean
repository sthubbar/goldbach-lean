module

public import LeanLab.BhowmikGrimmelt2026.Decomp150a

/-!
Theorem 3.1 of P0029, Bhowmik and Grimmelt 2026 survey, pages 9 to 13, packaged with its cited
inputs as explicit hypotheses.  ROUTE BURST session 5, 20261112.

The proposition `Theorem31` of Statements.lean is derived here from three inputs, each written out
in full as an explicit hypothesis of every result that uses it, since a repair pass may introduce
no definition, not even a proposition:
* verbatim the statement of the leaf `major_arc_uniform150` of Decomp150a.lean, P0029 pages 11 and
  12, display 3.5 with 3.6 and 3.7, Hardy and Littlewood 1923;
* Hardy 1914: the Riemann zeta function has a zero on the critical line;
* verbatim the statement of the elementary leaf `arc_tails_sup150`, page 12, which a parallel burst
  branch is proving.

`theorem31_of_inputs_full150` has no unproved step: it is PROVED, CONDITIONAL ON these three inputs.
The chain `arc_tails150`, `major_coefficients150`, `major_minor_mean_square150`,
`mean_square150_even_part`, `mean_square150`, `theorem31_decomposed150` of Decomp150a.lean is
re-derived below as ADAPTED COPIES whose proof text is the original with each unproved leaf replaced
by the matching hypothesis; every PROVED lemma is reused by name.

Binary Goldbach is OPEN.  Theorem 3.1 bounds the exceptional set under a zero hypothesis that is
itself unproved for any `Θ < 1`.  AI wrote the Lean code.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

/-! ### The three cited inputs as propositions -/

/-- PROVED sanity check: the existing leaf `arc_tails_sup150` has exactly the statement
hypothesis below.
In the lab its axioms showed the placeholder axiom through that leaf until the arc branch merged. -/
theorem arcTailsSup150_of_leaf : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε)) :=
  arc_tails_sup150

/-- PROVED, CONDITIONAL ON Hardy 1914.  P0029 page 12: `ZeroBound Θ` forces `1/2 ≤ Θ`, since the
modulus one character has `L(s, χ) = ζ(s)` and Hardy gives a zero with real part `1/2`.
This DUPLICATES the lemma deriving `zeroBound_lower150` on the sibling branch
claude/BhowmikGrimmelt2026-zeroBound_lower150-p2, so the two branches merge independently. -/
theorem zeroBound_lower_of_hardy150 (hH : (∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0)) {Θ : ℝ}
    (hZ : ZeroBound Θ) : 1 / 2 ≤ Θ := by
  obtain ⟨t, hs⟩ := hH
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hre : s.re = 1 / 2 := by simp [hsdef]
  have h0 : 0 < s.re := by rw [hre]; norm_num
  have h1 : s.re < 1 := by rw [hre]; norm_num
  have : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have h := hZ 1 (1 : DirichletCharacter ℂ 1) s
    (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hs) h0 h1
  rwa [hre] at h

/-! ### Adapted copies of the Decomp150a chain

Each proof below is an ADAPTED COPY of the Decomp150a.lean proof named in its docstring, with the
unproved leaves `major_arc_uniform150`, `arc_tails_sup150`, `zeroBound_lower150` replaced by the
hypotheses `hMA`, `hAT` and `zeroBound_lower_of_hardy150 hH`.  The statements are those of the
originals with the hypotheses added. -/

/-- ADAPTED COPY of `arc_tails150`, P0029 page 12, with `arc_tails_sup150` replaced by `hAT`. -/
theorem arc_tails_of150 (hAT : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ ^ 2 ≤ C * (X : ℝ) ^ (2 + ε) := by
  intro ε hε
  obtain ⟨C1, h1⟩ := hAT (ε / 2) (by linarith)
  obtain ⟨C2, h2⟩ := integral_norm_VW_le150 (ε / 2) (by linarith)
  refine ⟨|C1| * |C2|, fun X hX => ?_⟩
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set P : ℝ := (X : ℝ) ^ (1 + ε / 2) with hP
  have hP0 : 0 ≤ P := by positivity
  have hB : ∀ α ∈ Set.Icc (0 : ℝ) 1, ‖VX150 X α ^ 2 - WX150 X α‖ ≤ |C1| * P :=
    fun α hα => (h1 X hX α hα).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
  have hI : (∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖) ≤ |C2| * P :=
    (h2 X hX).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
  have hPP : P * P = (X : ℝ) ^ (2 + ε) := by
    rw [hP, ← Real.rpow_add (by linarith : (0 : ℝ) < X)]; congr 1; ring
  calc _ ≤ |C1| * P * ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ :=
        integral_sq_VW_le_sup150 X _ hB
    _ ≤ |C1| * P * (|C2| * P) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = |C1| * |C2| * (P * P) := by ring
    _ = |C1| * |C2| * (X : ℝ) ^ (2 + ε) := by rw [hPP]

/-- ADAPTED COPY of `major_coefficients150`, P0029 page 12, with `arc_tails150` replaced by
`arc_tails_of150 hAT`. -/
theorem major_coefficients_of150 (hAT : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
        ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) - (truncMain150 N : ℂ)‖ ^ 2 ≤
          C * (X : ℝ) ^ (2 + ε) := by
  intro ε hε
  obtain ⟨Ca, ha⟩ := arc_tails_of150 hAT ε hε
  obtain ⟨Cb, hb⟩ := truncation_level150 ε hε
  refine ⟨2 * Ca + 2 * Cb, fun X hX => ?_⟩
  set F := (Finset.Icc 1 X).filter (fun N => Even N) with hFdef
  have hpt : ∀ N ∈ F,
      ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) - (truncMain150 N : ℂ)‖ ^ 2 ≤
        2 * ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) -
          ∫ α in (0 : ℝ)..1, WX150 X α * ee (-((N : ℝ) * α))‖ ^ 2 +
        2 * ‖((N : ℂ) - 1) * (∑ q ∈ Finset.Icc 1 (Nat.sqrt X), wq150 q * ramanujan q (-(N : ℤ))) -
          (truncMain150 N : ℂ)‖ ^ 2 := by
    intro N hN
    have hN' := Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1
    rw [← coeff_WX150 hN'.1 hN'.2]
    exact norm_sub_sq_le_two150 _ _ _
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h1 := (bessel_VW150 X F).trans (ha X hX)
  have h2 := hb X hX
  calc _ ≤ _ := hsum
    _ ≤ 2 * (Ca * (X : ℝ) ^ (2 + ε)) + 2 * (Cb * (X : ℝ) ^ (2 + ε)) := by linarith
    _ = (2 * Ca + 2 * Cb) * (X : ℝ) ^ (2 + ε) := by ring

/-- ADAPTED COPY of `major_minor_mean_square150`, P0029 pages 12 and 13, with
`major_arc_uniform150`, `major_coefficients150` and `zeroBound_lower150` replaced by `hMA`,
`major_coefficients_of150 hAT` and `zeroBound_lower_of_hardy150 hH`. -/
theorem major_minor_mean_square_of150
    (hMA : (∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
        ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε))) (hH : (∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0)) (hAT : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε)))
    (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (r2 N - truncMain150 N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  intro ε hε
  obtain ⟨C1, h1⟩ := hMA Θ hΘ hZ (ε / 4) (by linarith)
  obtain ⟨C2, h2⟩ := major_model_L2_150 (ε / 2) (by linarith)
  obtain ⟨C3, h3⟩ := major_coefficients_of150 hAT ε hε
  have hhalf : (1 : ℝ) / 2 ≤ Θ := zeroBound_lower_of_hardy150 hH hZ
  refine ⟨4 * C1 ^ 2 * (16 / ε ^ 2 + |C2|) + 2 * |C3|, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
  set F := (Finset.Icc 1 X).filter (fun N => Even N) with hFdef
  have hF : ∀ N ∈ F, N ≤ X := fun N hN => (Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1).2
  set B := C1 * (X : ℝ) ^ (Θ + 1 / 4 + ε / 4) with hBdef
  have hM : ∀ α, ‖VX150 X α‖ ≤ ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ * X :=
    norm_VX_le150 X
  have hbes := bessel_model150 X (VX150 X) (measurable_VX150 X) _ hM B (h1 X hX) F hF
  -- the three integrals
  have hS2 : (∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2) ≤ 16 / ε ^ 2 * (X : ℝ) ^ (1 + ε / 2) := by
    rw [integral_norm_sq_Ssum150]
    refine (sum_vonMangoldt_sq_le150 X).trans ?_
    have hl : Real.log X ≤ (X : ℝ) ^ (ε / 4) / (ε / 4) :=
      Real.log_le_rpow_div hX0 (by linarith)
    have hl0 : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hsq : Real.log X ^ 2 ≤ ((X : ℝ) ^ (ε / 4) / (ε / 4)) ^ 2 := pow_le_pow_left₀ hl0 hl 2
    have he : ((X : ℝ) ^ (ε / 4) / (ε / 4)) ^ 2 = 16 / ε ^ 2 * (X : ℝ) ^ (ε / 2) := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hX0]
      field_simp
      ring_nf
    have hXe : (X : ℝ) * (X : ℝ) ^ (ε / 2) = (X : ℝ) ^ (1 + ε / 2) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    calc (X : ℝ) * Real.log X ^ 2 ≤ (X : ℝ) * (16 / ε ^ 2 * (X : ℝ) ^ (ε / 2)) := by
          rw [← he]; exact mul_le_mul_of_nonneg_left hsq hX0
      _ = 16 / ε ^ 2 * (X : ℝ) ^ (1 + ε / 2) := by rw [← hXe]; ring
  have hV2 : (∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2) ≤ |C2| * (X : ℝ) ^ (1 + ε / 2) :=
    (h2 X hX).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hB2 : B ^ 2 = C1 ^ 2 * (X : ℝ) ^ (2 * Θ + 1 / 2 + ε / 2) := by
    have hp : ((X : ℝ) ^ (Θ + 1 / 4 + ε / 4)) ^ 2 = (X : ℝ) ^ (2 * Θ + 1 / 2 + ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
      congr 1
      push_cast; ring
    rw [hBdef, mul_pow, hp]
  have hfirst : 2 * B ^ 2 * ((∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2) +
      ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2) ≤
      2 * C1 ^ 2 * (16 / ε ^ 2 + |C2|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    have hsum : (∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2) + ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2 ≤
        (16 / ε ^ 2 + |C2|) * (X : ℝ) ^ (1 + ε / 2) := by linarith
    have hexp : (X : ℝ) ^ (2 * Θ + 1 / 2 + ε / 2) * (X : ℝ) ^ (1 + ε / 2) =
        (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1; ring
    rw [hB2]
    calc 2 * (C1 ^ 2 * (X : ℝ) ^ (2 * Θ + 1 / 2 + ε / 2)) *
          ((∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2) + ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2)
        ≤ 2 * (C1 ^ 2 * (X : ℝ) ^ (2 * Θ + 1 / 2 + ε / 2)) *
          ((16 / ε ^ 2 + |C2|) * (X : ℝ) ^ (1 + ε / 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * C1 ^ 2 * (16 / ε ^ 2 + |C2|) *
          ((X : ℝ) ^ (2 * Θ + 1 / 2 + ε / 2) * (X : ℝ) ^ (1 + ε / 2)) := by ring
      _ = 2 * C1 ^ 2 * (16 / ε ^ 2 + |C2|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by rw [hexp]
  have hthird : C3 * (X : ℝ) ^ (2 + ε) ≤ |C3| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    have hmono : (X : ℝ) ^ (2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    calc C3 * (X : ℝ) ^ (2 + ε) ≤ |C3| * (X : ℝ) ^ (2 + ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C3| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
          mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
  have h3X := h3 X hX
  -- pointwise triangle inequality
  have hpt : ∀ N ∈ F, (r2 N - truncMain150 N) ^ 2 ≤
      2 * ‖(r2 N : ℂ) - ∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))‖ ^ 2 +
      2 * ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) - (truncMain150 N : ℂ)‖ ^ 2 := by
    intro N _
    have he : (r2 N - truncMain150 N) ^ 2 = ‖(r2 N : ℂ) - (truncMain150 N : ℂ)‖ ^ 2 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [he]
    exact norm_sub_sq_le_two150 _ _ _
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  calc ∑ N ∈ F, (r2 N - truncMain150 N) ^ 2
      ≤ 2 * (2 * B ^ 2 * ((∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2) +
          ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2)) + 2 * (C3 * (X : ℝ) ^ (2 + ε)) := by
        linarith
    _ ≤ 2 * (2 * C1 ^ 2 * (16 / ε ^ 2 + |C2|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) +
          2 * (|C3| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) := by linarith
    _ = (4 * C1 ^ 2 * (16 / ε ^ 2 + |C2|) + 2 * |C3|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

/-- ADAPTED COPY of `mean_square150_even_part`, P0029 page 13. -/
theorem mean_square150_even_part_of
    (hMA : (∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
        ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε))) (hH : (∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0)) (hAT : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε)))
    (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  intro ε hε
  obtain ⟨CB, hB⟩ := major_minor_mean_square_of150 hMA hH hAT Θ hΘ hZ ε hε
  obtain ⟨CA, hA⟩ := singular_truncation150 (ε / 2) (by linarith)
  have hhalf : (1 : ℝ) / 2 ≤ Θ := zeroBound_lower_of_hardy150 hH hZ
  refine ⟨2 * CB + 2 * CA ^ 2, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have e : ((X : ℝ) ^ (1 / 2 + ε / 2)) ^ 2 = (X : ℝ) ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    congr 1
    push_cast
    ring
  have hpt : ∀ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
      (E2 N) ^ 2 ≤ 2 * (r2 N - truncMain150 N) ^ 2 + 2 * (CA ^ 2 * (X : ℝ) ^ (1 + ε)) := by
    intro N hN
    have hN' := (Finset.mem_filter.mp hN).1
    rw [Finset.mem_Icc] at hN'
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN'.1
    have hNX : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hN'.2
    have hsq : (E2 N) ^ 2 ≤ 2 * (r2 N - truncMain150 N) ^ 2 +
        2 * (truncMain150 N - (N : ℝ) * singular N) ^ 2 := by
      unfold E2
      exact sq_sub_le_two150 _ _ _
    have habs := hA N hN'.1
    have hpow : (N : ℝ) ^ (1 / 2 + ε / 2) ≤ (X : ℝ) ^ (1 / 2 + ε / 2) :=
      Real.rpow_le_rpow (by linarith) hNX (by linarith)
    have hb : |truncMain150 N - (N : ℝ) * singular N| ≤ |CA| * (X : ℝ) ^ (1 / 2 + ε / 2) := by
      calc |truncMain150 N - (N : ℝ) * singular N| ≤ CA * (N : ℝ) ^ (1 / 2 + ε / 2) := habs
        _ ≤ |CA| * (N : ℝ) ^ (1 / 2 + ε / 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |CA| * (X : ℝ) ^ (1 / 2 + ε / 2) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    have hsq2 : (truncMain150 N - (N : ℝ) * singular N) ^ 2 ≤ CA ^ 2 * (X : ℝ) ^ (1 + ε) := by
      have h1 : (truncMain150 N - (N : ℝ) * singular N) ^ 2 ≤
          (|CA| * (X : ℝ) ^ (1 / 2 + ε / 2)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have h2 : (|CA| * (X : ℝ) ^ (1 / 2 + ε / 2)) ^ 2 = CA ^ 2 * (X : ℝ) ^ (1 + ε) := by
        rw [mul_pow, sq_abs, e]
      linarith
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (((Finset.Icc 1 X).filter (fun N => Even N)).card : ℝ) ≤ (X : ℝ) := by
    have : ((Finset.Icc 1 X).filter (fun N => Even N)).card ≤ X := by
      calc ((Finset.Icc 1 X).filter (fun N => Even N)).card ≤ (Finset.Icc 1 X).card :=
            Finset.card_filter_le _ _
        _ = X := by simp
    exact_mod_cast this
  have hB' := hB X hX
  have hXe : (X : ℝ) * (X : ℝ) ^ (1 + ε) = (X : ℝ) ^ (2 + ε) := by
    have h := Real.rpow_add hXpos (1 + ε) 1
    rw [Real.rpow_one] at h
    rw [show (2 : ℝ) + ε = (1 + ε) + 1 by ring, h]
    ring
  have hexp : (X : ℝ) ^ (2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hnn : 0 ≤ 2 * (CA ^ 2 * (X : ℝ) ^ (1 + ε)) := by positivity
  have hc : (((Finset.Icc 1 X).filter (fun N => Even N)).card : ℝ) *
      (2 * (CA ^ 2 * (X : ℝ) ^ (1 + ε))) ≤ 2 * CA ^ 2 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    calc (((Finset.Icc 1 X).filter (fun N => Even N)).card : ℝ) *
          (2 * (CA ^ 2 * (X : ℝ) ^ (1 + ε)))
        ≤ (X : ℝ) * (2 * (CA ^ 2 * (X : ℝ) ^ (1 + ε))) :=
          mul_le_mul_of_nonneg_right hcard hnn
      _ = 2 * CA ^ 2 * ((X : ℝ) * (X : ℝ) ^ (1 + ε)) := by ring
      _ = 2 * CA ^ 2 * (X : ℝ) ^ (2 + ε) := by rw [hXe]
      _ ≤ 2 * CA ^ 2 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hfin : (2 * CB + 2 * CA ^ 2) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) =
      2 * (CB * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) + 2 * CA ^ 2 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    ring
  rw [hfin]
  linarith

/-- ADAPTED COPY of `mean_square150`, P0029 page 13 display 3.8. -/
theorem mean_square_of150
    (hMA : (∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
        ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε))) (hH : (∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0)) (hAT : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε))) :
    MeanSquare38 := by
  intro Θ hΘ hZ ε hε
  obtain ⟨Ce, heEven⟩ := mean_square150_even_part_of hMA hH hAT Θ hΘ hZ ε hε
  obtain ⟨Co, hoPos, hoOdd⟩ := meanSquare38_odd_energy
  refine ⟨Ce + Co, ?_⟩
  intro X hX
  have hhalf : (1 : ℝ) / 2 ≤ Θ := zeroBound_lower_of_hardy150 hH hZ
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hexp : (2 : ℝ) ≤ 3 / 2 + 2 * Θ + ε := by linarith
  have hmono : (X : ℝ) ^ (2 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hexp
  have hmono' : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    simpa using hmono
  have hsplit :
      (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
      ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2 :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 X)
      (p := fun N => Even N) (f := fun N => (E2 N) ^ 2)
  have hodd :
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 ≤
        Co * (X : ℝ) ^ 2 := by
    have hEq :
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Odd N), (r2 N) ^ 2 := by
      refine Finset.sum_congr ?_ ?_
      · ext N
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, Nat.not_even_iff_odd.mp h.2⟩,
          fun h => ⟨h.1, Nat.not_even_iff_odd.mpr h.2⟩⟩
      · intro N hN
        rw [Finset.mem_filter] at hN
        have h0 : singular N = 0 := meanSquare38_odd_singular N hN.2
        simp only [E2, h0, mul_zero, sub_zero]
    rw [hEq]
    exact hoOdd X hX
  have heven := heEven X hX
  calc ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2
      = (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
          ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 := hsplit.symm
    _ ≤ Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Co * (X : ℝ) ^ 2 := by linarith
    _ ≤ Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Co * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
      have hCo := mul_le_mul_of_nonneg_left hmono' hoPos.le
      linarith
    _ = (Ce + Co) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

/-- P0029 Theorem 3.1, PROVED, CONDITIONAL ON the three inputs, written out as hypotheses.  ADAPTED COPY of `theorem31_decomposed150`; the PROVED leaves
`exceptional_gap150` and `moment_to_count150` are reused by name.  No unproved step. -/
theorem theorem31_of_inputs_full150
    (hMA : (∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
        ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε))) (hH : (∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0)) (hAT : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε))) :
    Theorem31 := by
  intro Θ hΘ hZ ε hε
  have hhalf := zeroBound_lower_of_hardy150 hH hZ
  have hmean := mean_square_of150 hMA hH hAT Θ hΘ hZ ε hε
  classical
  have hgap : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → (Even N ∧ ¬ IsGoldbachSum N) → c * N ≤ |E2 N| := by
    obtain ⟨c, hc, N₀, h⟩ := exceptional_gap150
    exact ⟨c, hc, N₀, fun N hN hb => h N hN hb.1 hb.2⟩
  have h := moment_to_count150 (3 / 2 + 2 * Θ + ε) (by linarith)
    (fun N => Even N ∧ ¬ IsGoldbachSum N) E2 hgap hmean
  change PowerBound (3 / 2 + 2 * Θ + ε - 2) at h
  have he : (3 / 2 + 2 * Θ + ε - 2 : ℝ) = 2 * Θ - 1 / 2 + ε := by ring
  rwa [he] at h

/-- P0029 Theorem 3.1 from the two cited inputs only, through the existing leaf
`arc_tails_sup150`.  In the lab its axioms showed the placeholder axiom through `arc_tails_sup150` until the arc branch
merges; after that it is PROVED, CONDITIONAL ON the first and second inputs. -/
theorem theorem31_of_inputs150 (hMA : (∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
        ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε))) (hH : (∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0)) :
    Theorem31 :=
  theorem31_of_inputs_full150 hMA hH arc_tails_sup150

end LeanLab.BhowmikGrimmelt2026
