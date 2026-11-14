module

public import Mathlib

/-!
Li-Liu, arXiv 2610.15784, Section 5, the step from (44) to (46): the function
g(u) = log cosh √u on [0, ∞) is concave, nondecreasing, and has derivative
tanh √u/(2√u) ∈ [0, 1/2], read by WebFetch on arxiv.org/html/2610.15784, 2026-10-21.

PROVED unconditional here: `sinh_le_mul_cosh`, sinh t ≤ t cosh t for t ≥ 0;
`self_le_sinh_mul_cosh`, t ≤ sinh t cosh t for t ≥ 0; `hasDerivAt_g`; `k_antitone`,
sinh t/(2t cosh t) is antitone on t > 0; `concaveOn_g`; `monotoneOn_g`;
`g_sub_le`, g(b) - g(a) ≤ (b - a)/2 for 0 ≤ a ≤ b. The paper states the tangent-line form;
here concavity is used through Jensen, `ConcaveOn.le_map_sum`, which gives the same bound.

Unit U-1420, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics.
Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1420LogCosh

open Set Real

/-- `g(u) = log cosh √u`. -/
noncomputable def g (u : ℝ) : ℝ := Real.log (Real.cosh (Real.sqrt u))

/-- `sinh t ≤ t cosh t` for `t ≥ 0`, i.e. `tanh t ≤ t`. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  set F : ℝ → ℝ := fun s => s * Real.cosh s - Real.sinh s with hF
  have hd : ∀ s, HasDerivAt F (s * Real.sinh s) s := by
    intro s
    have h := ((hasDerivAt_id' s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)
    exact h.congr_deriv (by ring)
  have hmono : MonotoneOn F (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (by fun_prop : Continuous F).continuousOn
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact mul_nonneg (le_of_lt hs) (Real.sinh_nonneg_iff.2 (le_of_lt hs))
  have := hmono (mem_Ici.2 (le_refl (0 : ℝ))) (show t ∈ Ici (0 : ℝ) from ht) ht
  simp [hF] at this
  linarith

/-- `t ≤ sinh t cosh t` for `t ≥ 0`, from `2t ≤ sinh 2t`. -/
theorem self_le_sinh_mul_cosh {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t * Real.cosh t := by
  have := Real.self_le_sinh_iff.2 (show 0 ≤ 2 * t by linarith)
  rw [Real.sinh_two_mul] at this
  linarith

/-- `k(t) = sinh t/(2 t cosh t)`, the derivative of `g` at `u = t²`. -/
noncomputable def k (t : ℝ) : ℝ := Real.sinh t / (2 * t * Real.cosh t)

lemma hasDerivAt_g {u : ℝ} (hu : 0 < u) : HasDerivAt g (k (Real.sqrt u)) u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have h := ((Real.hasDerivAt_sqrt hu.ne').cosh).log (Real.cosh_pos _).ne'
  unfold g k
  convert h using 1
  field_simp

lemma k_le_half {t : ℝ} (ht : 0 < t) : k t ≤ 1 / 2 := by
  unfold k
  rw [div_le_iff₀ (by have := Real.cosh_pos t; positivity)]
  have := sinh_le_mul_cosh ht.le
  linarith

lemma k_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ k t := by
  unfold k
  have := Real.sinh_nonneg_iff.2 ht.le
  have := Real.cosh_pos t
  positivity

/-- `k` is antitone on `t > 0`: `k' = 2(t - sinh t cosh t)/(2t cosh t)² ≤ 0`. -/
theorem k_antitone : AntitoneOn k (Ioi 0) := by
  have hd : ∀ t, 0 < t → HasDerivAt k
      ((Real.cosh t * (2 * t * Real.cosh t) - Real.sinh t * (2 * Real.cosh t +
        2 * t * Real.sinh t)) / (2 * t * Real.cosh t) ^ 2) t := by
    intro t ht
    have hden : HasDerivAt (fun s => 2 * s * Real.cosh s)
        (2 * Real.cosh t + 2 * t * Real.sinh t) t := by
      have := ((hasDerivAt_id' t).const_mul 2).mul (Real.hasDerivAt_cosh t)
      exact this.congr_deriv (by ring)
    have hne : 2 * t * Real.cosh t ≠ 0 := by have := Real.cosh_pos t; positivity
    exact (Real.hasDerivAt_sinh t).div hden hne
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro t ht; exact (hd t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro t ht
    rw [(hd t ht).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h1 := self_le_sinh_mul_cosh (le_of_lt ht)
    have h2 := Real.cosh_sq t
    have h4 : Real.cosh t * (2 * t * Real.cosh t) - Real.sinh t * (2 * Real.cosh t +
        2 * t * Real.sinh t) = 2 * t - 2 * (Real.sinh t * Real.cosh t) := by
      linear_combination (2 * t) * h2
    rw [h4]
    linarith

lemma continuousOn_g : ContinuousOn g (Ici 0) :=
  (Real.continuous_cosh.comp Real.continuous_sqrt).continuousOn.log
    (fun _ _ => (Real.cosh_pos _).ne')

lemma continuous_g : Continuous g :=
  (Real.continuous_cosh.comp Real.continuous_sqrt).log (fun _ => (Real.cosh_pos _).ne')

/-- `g(u) = log cosh √u` is concave on `[0, ∞)`. -/
theorem concaveOn_g : ConcaveOn ℝ (Ici 0) g := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) continuousOn_g ?_ ?_
  · rw [interior_Ici]; intro u hu; exact (hasDerivAt_g hu).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    rw [(hasDerivAt_g ha).deriv, (hasDerivAt_g hb).deriv]
    exact k_antitone (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb) (Real.sqrt_le_sqrt hab)

/-- `g` is nondecreasing on `[0, ∞)`. -/
theorem monotoneOn_g : MonotoneOn g (Ici 0) := by
  intro a _ b _ hab
  unfold g
  refine Real.log_le_log (Real.cosh_pos _) (Real.cosh_le_cosh.2 ?_)
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hab

/-- `g(b) - g(a) ≤ (b - a)/2` for `0 ≤ a ≤ b`, from `0 ≤ g' ≤ 1/2`. -/
theorem g_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : g b - g a ≤ 1 / 2 * (b - a) := by
  refine (convex_Ici 0).image_sub_le_mul_sub_of_deriv_le continuousOn_g ?_ ?_ a ha b
    (ha.trans hab) hab
  · rw [interior_Ici]; intro u hu; exact (hasDerivAt_g hu).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro u hu
    rw [(hasDerivAt_g hu).deriv]
    exact k_le_half (Real.sqrt_pos.2 hu)

/-- For any `m, V ≥ 0`: `g(m) ≤ g(V) + max(0, m - V)/2`, used with `m - V ≤ (ξ² + η²)/L`. -/
theorem g_le_of_le {m V δ : ℝ} (hm : 0 ≤ m) (hV : 0 ≤ V) (hδ : 0 ≤ δ) (hmV : m - V ≤ δ) :
    g m ≤ g V + 1 / 2 * δ := by
  rcases le_total m V with h | h
  · have := monotoneOn_g hm hV h
    linarith
  · have := g_sub_le hV h
    linarith

/-- `log cosh w = g(w²)`. -/
lemma log_cosh_eq_g (w : ℝ) : Real.log (Real.cosh w) = g (w ^ 2) := by
  unfold g
  rw [Real.sqrt_sq_eq_abs, Real.cosh_abs]

end LeanLab.Linnik.U1420LogCosh
