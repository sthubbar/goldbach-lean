module

public import LeanLab.Linnik1951.SPLIT_lineBound_lnL1622

/-!
Falsification support for continuous_lnL_line1622 in SPLIT_lineBound_lnL1622.lean.
Complex.log is the principal branch: its imaginary part is Complex.arg, with values in
the half open interval from minus pi to pi, and it jumps across the negative real axis.
The theorem below is the standard fact behind that jump, read along the line
1/2 + 1/ln N + i t of P0093 page 156 Lemma 2: if the L-function takes a negative real
value at a height t0 and has negative imaginary part at heights arbitrarily close to t0,
then the principal logarithm of the L-function along the line is not continuous.
It reduces the negation of continuous_lnL_line1622 to one sign pattern of L-values.
It is CONDITIONAL ON that sign pattern, which is a hypothesis here and is not proved in
Lean. No statement on main is changed. AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- Standard fact on the principal branch. A function into the complex numbers that
takes a negative real value at t0 and has negative imaginary part at points arbitrarily
close to t0 does not have a continuous principal logarithm: the argument is pi at t0 and
negative at those nearby points. -/
theorem not_continuous_log_of_crossing1117 (f : ℝ → ℂ) (t0 : ℝ)
    (hre : (f t0).re < 0) (him : (f t0).im = 0)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t - t0| < ε ∧ (f t).im < 0) :
    ¬ Continuous fun t : ℝ => Complex.log (f t) := by
  intro hc
  have harg : Continuous fun t : ℝ => (f t).arg := by
    have h := Complex.continuous_im.comp hc
    simpa [Function.comp_def, Complex.log_im] using h
  have hpi : (f t0).arg = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩
  have hpos : ∀ᶠ t in nhds t0, 0 < (f t).arg := by
    have h := harg.continuousAt (x := t0)
    exact h.eventually (lt_mem_nhds (by show 0 < (f t0).arg; rw [hpi]; exact Real.pi_pos))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hpos
  obtain ⟨t, ht, hneg⟩ := hnear ε hε
  have h1 : 0 < (f t).arg := hball (by simpa [Real.dist_eq] using ht)
  have h2 : (f t).arg < 0 := Complex.arg_neg_iff.mpr hneg
  linarith

/-- The same fact along the line of P0093 page 156 Lemma 2. If the L-function of a
character takes a negative real value at the height t0 of the line 1/2 + 1/ln N + i t
and has negative imaginary part at heights arbitrarily close to t0, then the conclusion
of continuous_lnL_line1622 fails for that N and that character. CONDITIONAL ON the sign
pattern of the L-values, which is a hypothesis. -/
theorem not_continuous_lnL_line_of_crossing1117 (N : ℕ) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t0 : ℝ)
    (hre : (DirichletCharacter.LFunction χ (mellinLine1622 N t0)).re < 0)
    (him : (DirichletCharacter.LFunction χ (mellinLine1622 N t0)).im = 0)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t - t0| < ε ∧
      (DirichletCharacter.LFunction χ (mellinLine1622 N t)).im < 0) :
    ¬ Continuous fun t : ℝ =>
      Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t)) :=
  not_continuous_log_of_crossing1117
    (fun t => DirichletCharacter.LFunction χ (mellinLine1622 N t)) t0 hre him hnear

end LeanLab.Linnik1951
