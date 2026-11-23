module

public import LeanLab.PNTPort.ExplicitPsi1.CharPerronHalf1122
public import LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122
public import LeanLab.PNTPort.ExplicitPsi1.CharRect1122
public import LeanLab.PNTPort.ExplicitPsi1.CharGoodHeight1122
public import LeanLab.PNTPort.ExplicitPsi1.CharBRegroup1122
public import LeanLab.PNTPort.ExplicitPsi1.CharContour1122

/-!
# Assembly of the half weighted integer explicit formula for primitive characters

ROUTE BURST burst-20261122, port of Davenport, Multiplicative Number Theory, second edition,
chapter 19, pages 115 to 118. AI wrote the Lean code in this file. Binary Goldbach is OPEN.

Goal: `davenport_half_formula_assembled`, the statement of the BhowmikGrimmelt2026 leaf
`davenport_integer_half_formula592` with `mult χ ρ` unfolded to
`analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ`, so that a later small file closes that
leaf by `exact`. This file does not import any BhowmikGrimmelt2026 module.

Proved pieces used:
* `CharPerronHalf1122.char_perron_half1122`, the half weighted Perron formula, Davenport ch. 17
  and ch. 19 p. 116;
* `CharTrivial1122.exists_b_even`, `CharTrivial1122.trivial_sum_le`, the constant `b(χ)` and the
  trivial zero sums, ch. 19 pp. 115 to 117;
* `CharRect1122.charZeros_rect_finite`, finiteness of the zeros in a rectangle.

Leaves, each a cited step of Davenport ch. 19:
* `good_height`, p. 116, the choice of a modified height, PROVED: it is
  `char_good_height_pm1122` of `CharGoodHeight1122.lean`.
* `contour_good_height_leaf`, PROVED in session S73 as `CharContour1122.contour_bound`:
  pp. 116 and 117, the contour shift at a good height, the horizontal integrals, the far left
  segments and the left edge, leading to display (4).
* `window_switch`, PROVED: p. 117, replacing the good height by `T`, the zeros with
  `T ≤ |γ| < T'` being `O(log qT)` in number by ch. 16 display (3).
* p. 118, `b(χ) = O(log q) - Σ_{|γ|<1} 1/ρ`: PROVED as `CharBRegroup1122.b_regroup`, the
  statement of `CharTrivial1122.b_regroup_leaf`.
-/

@[expose] public section

namespace LeanLab.PNTPort.ExplicitPsi1.CharHalfAssembly1122

open Complex Filter Topology Set

/-- The truncated Perron integral of Davenport ch. 19 p. 116 at `x = n`, `c = 1 + 1/log n`:
`(1/2π) ∫_{-T}^{T} -(L'/L)(c + it, χ) n^(c+it)/(c + it) dt`, exactly as in
`char_perron_half1122`. -/
noncomputable def perronJ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) (T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
    -(deriv (DirichletCharacter.LFunction χ)
        (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
      DirichletCharacter.LFunction χ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I)) *
    (n : ℂ) ^ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
      (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I))

open Classical in
/-- The term `(1 - a) log x` of Davenport ch. 19 p. 117 display (4), at `x = n`: `log n` when
`χ` is even, `a = 0`, and `0` when `χ` is odd, `a = 1`. -/
noncomputable def zeroLog {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  if χ.Even then Real.log n else 0

open Classical in
/-- The trivial zero sum `Σ_{m ≥ 1} x^(a - 2m)/(2m - a)` of Davenport ch. 19 p. 117 display (4),
at `x = n`, in the closed forms of `CharTrivial1122.hasSum_trivial_even_real` and
`hasSum_trivial_odd_real`. -/
noncomputable def trivSum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  if χ.Even then -(1 / 2) * Real.log (1 - ((n : ℝ)⁻¹) ^ 2)
  else (1 / 2) * (Real.log (1 + (n : ℝ)⁻¹) - Real.log (1 - (n : ℝ)⁻¹))

/-- The constant `b(χ)` of Davenport ch. 19 p. 116: `L'(0, χ)/L(0, χ)` for odd `χ` and the
constant term of `L'/L` at `0` for even `χ`, in the form used by `CharTrivial1122.b_regroup_leaf` and `CharBRegroup1122.b_regroup`. -/
def IsB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℂ) : Prop :=
  (χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
      DirichletCharacter.LFunction χ 0) ∨
    (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))

/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 116, the choice of a
modified value of `T` by the lemma of §16: `L'/L(σ ± iT, χ) = O(log² qT)`, here on
`-1/2 ≤ σ ≤ 2`. PROVED: this is `LeanLab.PNTPort.ExplicitPsi1.char_good_height_pm1122`. -/
theorem good_height : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1),
      ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
        χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤
          C * Real.log ((q : ℝ) * T) ^ 2 :=
  char_good_height_pm1122

/- Route notes for `contour_good_height_leaf`: the residue sum over `[-U, c] × [-T', T']`,
`U → ∞` through half odd integers, is `-Σ_{|γ|<T'} m(ρ) n^ρ/ρ - (1 - a) log n - b(χ) +
Σ_{m ≥ 1} n^(a-2m)/(2m - a)`; the horizontal integrals are `O(K n/(T' log n))` on
`-1/2 ≤ σ ≤ c`, `O(n/T')` on `2 ≤ σ ≤ c`, and `O(log qT'/(T' n log n))` on `σ ≤ -1/2` by
`L'/L(s, χ) = O(log q|s|)`, p. 117; the left edge tends to `0`. Ported ingredients:
`CharRect1122.char_rect_explicit`, `CharEdges1122.char_horizontal_edge1122`,
`CharTrivial1122Rect.tendsto_rect_left_char`, `CharTrivial1122Left.left_edge_tendsto_zero_of_leaf`. -/

/-- PROVED, formerly a LEAF of class HARD, burst-20261122 session S73: Davenport, Multiplicative
Number Theory, second edition, ch. 19 pp. 116 and 117, the contour argument leading to display (4)
at a good height `T'`, with `|L'/L| ≤ K` on the horizontal segments as given by `good_height`.
It is `CharContour1122.contour_bound`. See the route notes above. -/
theorem contour_good_height_leaf : ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ T' K : ℝ, 2 ≤ T' → 0 ≤ K →
      (∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
        χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤ K) →
      ∀ b : ℂ, IsB χ b → ∀ n : ℕ, 2 ≤ n → ∀ Z' : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z' ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T') →
      ‖perronJ χ n T' +
          (∑ ρ ∈ Z', (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
            (n : ℂ) ^ ρ / ρ) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ ≤
        D * ((K + 1) * n / T' + Real.log ((q : ℝ) * T') / T' + Real.log n) := by
  obtain ⟨D, hD, h⟩ := CharContour1122.contour_bound
  exact ⟨D, hD, fun q _ χ hp hχ T' K hT hK hg b hb n hn Z' hZ =>
    h q χ hp hχ T' K hT hK hg b hb n hn Z' hZ⟩

/-- One window term: `‖m n^ρ/ρ‖ ≤ m n/T` for `Re ρ < 1`, `|Im ρ| ≥ T > 0`. -/
lemma term_le {f : ℂ → ℂ} {n : ℕ} (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hre : ρ.re < 1) (him : T ≤ |ρ.im|) :
    ‖(analyticOrderNatAt f ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤
      (analyticOrderNatAt f ρ : ℝ) * ((n : ℝ) / T) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hpow : ‖(n : ℂ) ^ ρ‖ ≤ n := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    calc (n : ℝ) ^ ρ.re ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hre.le
      _ = n := Real.rpow_one _
  have hρ : T ≤ ‖ρ‖ := him.trans (Complex.abs_im_le_norm ρ)
  have hρ0 : 0 < ‖ρ‖ := lt_of_lt_of_le hT hρ
  rw [norm_div, norm_mul, Complex.norm_natCast, div_le_iff₀ hρ0]
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt f ρ : ℝ) := Nat.cast_nonneg _
  calc (analyticOrderNatAt f ρ : ℝ) * ‖(n : ℂ) ^ ρ‖ ≤ (analyticOrderNatAt f ρ : ℝ) * n :=
        mul_le_mul_of_nonneg_left hpow hm
    _ = (analyticOrderNatAt f ρ : ℝ) * ((n : ℝ) / T) * T := by field_simp
    _ ≤ (analyticOrderNatAt f ρ : ℝ) * ((n : ℝ) / T) * ‖ρ‖ :=
        mul_le_mul_of_nonneg_left hρ (by positivity)

/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 117, passing from the
modified height `T'` back to `T`: by ch. 16 display (3), p. 102, the zeros with
`T ≤ |γ| < T'`, `T' ≤ T + 4`, counted with multiplicity, are `O(log qT)` in number, and each
term satisfies `|n^ρ/ρ| ≤ n/T`. PROVED from the multiplicity window count
`BhowmikGrimmelt2026.zero_window_count_full508` over four unit windows. -/
theorem window_switch : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ T T' : ℝ, 2 ≤ T → T ≤ T' →
      T' ≤ T + 4 → ∀ n : ℕ, 2 ≤ n → ∀ W : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ W ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T ≤ |ρ.im| ∧ |ρ.im| < T') →
      ‖∑ ρ ∈ W, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
          (n : ℂ) ^ ρ / ρ‖ ≤ A * ((n : ℝ) / T * Real.log ((q : ℝ) * T)) := by
  obtain ⟨A0, hA0, hA⟩ := LeanLab.BhowmikGrimmelt2026.zero_window_count_full508
  refine ⟨8 * A0, by positivity, ?_⟩
  intro q _ χ _ hne T T' hT hTT' hT' n hn W hW
  set f := DirichletCharacter.LFunction χ
  have hq2 : 2 ≤ q := by
    have h1 := LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.modulus_ne_one hne
    have := NeZero.ne q
    omega
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- the window bound in the form needed
  have hlog : ∀ t : ℝ, |t| ≤ T + 3 → Real.log ((q : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((q : ℝ) * T) := by
    intro t ht
    have h4 : (4 : ℝ) ≤ q * T := by nlinarith
    have hlq : Real.log 4 ≤ Real.log ((q : ℝ) * T) := Real.log_le_log (by norm_num) h4
    have hl4 : (1 : ℝ) < Real.log 4 := by
      have := Real.log_two_gt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have hle : (q : ℝ) * (|t| + 2) ≤ ((q : ℝ) * T) ^ 2 := by nlinarith [abs_nonneg t]
    calc Real.log ((q : ℝ) * (|t| + 2)) ≤ Real.log (((q : ℝ) * T) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * Real.log ((q : ℝ) * T) := by rw [Real.log_pow]; norm_num
  have hcount : ∀ t : ℝ, |t| ≤ T + 3 → ∀ S ⊆ W, (∀ ρ ∈ S, |ρ.im - t| ≤ 1) →
      ∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ) ≤ 2 * A0 * Real.log ((q : ℝ) * T) := by
    intro t ht S hS hSt
    have h := hA q χ t S fun ρ hρ => by
      obtain ⟨hz, h0, h1, -, -⟩ := (hW ρ).1 (hS hρ)
      exact ⟨hz, h0, h1, hSt ρ hρ⟩
    calc _ ≤ A0 * Real.log ((q : ℝ) * (|t| + 2)) := h
      _ ≤ A0 * (2 * Real.log ((q : ℝ) * T)) := mul_le_mul_of_nonneg_left (hlog t ht) hA0
      _ = _ := by ring
  -- four windows
  classical
  let P1 : ℂ → Prop := fun ρ => 0 ≤ ρ.im
  let P2 : ℂ → Prop := fun ρ => |ρ.im| ≤ T + 2
  have hsplit : ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℝ) =
      ∑ ρ ∈ (W.filter P1).filter P2, (analyticOrderNatAt f ρ : ℝ) +
      ∑ ρ ∈ (W.filter P1).filter (fun ρ => ¬ P2 ρ), (analyticOrderNatAt f ρ : ℝ) +
      (∑ ρ ∈ (W.filter (fun ρ => ¬ P1 ρ)).filter P2, (analyticOrderNatAt f ρ : ℝ) +
      ∑ ρ ∈ (W.filter (fun ρ => ¬ P1 ρ)).filter (fun ρ => ¬ P2 ρ),
        (analyticOrderNatAt f ρ : ℝ)) := by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.sum_filter_add_sum_filter_not,
      Finset.sum_filter_add_sum_filter_not]
  have hmem : ∀ ρ ∈ W, T ≤ |ρ.im| ∧ |ρ.im| < T + 4 := fun ρ hρ => by
    obtain ⟨-, -, -, h1, h2⟩ := (hW ρ).1 hρ
    exact ⟨h1, by linarith⟩
  have sub1 : ∀ (Q R : ℂ → Prop) [DecidablePred Q] [DecidablePred R],
      (W.filter Q).filter R ⊆ W := fun Q R _ _ ρ h =>
    (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1
  have w1 := hcount (T + 1) (by rw [abs_of_pos (by linarith)]; linarith) _ (sub1 P1 P2)
    fun ρ hρ => by
      simp only [Finset.mem_filter, P1, P2] at hρ
      obtain ⟨⟨hρW, hp⟩, hq'⟩ := hρ
      have := hmem ρ hρW
      rw [abs_of_nonneg hp] at this hq'
      rw [abs_le]; constructor <;> linarith
  have w2 := hcount (T + 3) (by rw [abs_of_pos (by linarith)]) _ (sub1 P1 (fun ρ => ¬ P2 ρ))
    fun ρ hρ => by
      simp only [Finset.mem_filter, P1, P2, not_le] at hρ
      obtain ⟨⟨hρW, hp⟩, hq'⟩ := hρ
      have := hmem ρ hρW
      rw [abs_of_nonneg hp] at this hq'
      rw [abs_le]; constructor <;> linarith
  have w3 := hcount (-(T + 1)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) _
    (sub1 (fun ρ => ¬ P1 ρ) P2)
    fun ρ hρ => by
      simp only [Finset.mem_filter, P1, P2, not_le] at hρ
      obtain ⟨⟨hρW, hp⟩, hq'⟩ := hρ
      have := hmem ρ hρW
      rw [abs_of_neg hp] at this hq'
      rw [abs_le]; constructor <;> linarith
  have w4 := hcount (-(T + 3)) (by rw [abs_neg, abs_of_pos (by linarith)]) _
    (sub1 (fun ρ => ¬ P1 ρ) (fun ρ => ¬ P2 ρ))
    fun ρ hρ => by
      simp only [Finset.mem_filter, P1, P2, not_le] at hρ
      obtain ⟨⟨hρW, hp⟩, hq'⟩ := hρ
      have := hmem ρ hρW
      rw [abs_of_neg hp] at this hq'
      rw [abs_le]; constructor <;> linarith
  have htot : ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℝ) ≤ 8 * A0 * Real.log ((q : ℝ) * T) := by
    rw [hsplit]; linarith
  have hterm : ∀ ρ ∈ W, ‖(analyticOrderNatAt f ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤
      (analyticOrderNatAt f ρ : ℝ) * ((n : ℝ) / T) := fun ρ hρ => by
    obtain ⟨-, -, h1, h2, -⟩ := (hW ρ).1 hρ
    exact term_le hn hT0 h1 h2
  calc _ ≤ ∑ ρ ∈ W, ‖(analyticOrderNatAt f ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℝ) * ((n : ℝ) / T) := Finset.sum_le_sum hterm
    _ = (∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℝ)) * ((n : ℝ) / T) := by rw [Finset.sum_mul]
    _ ≤ 8 * A0 * Real.log ((q : ℝ) * T) * ((n : ℝ) / T) :=
        mul_le_mul_of_nonneg_right htot (by positivity)
    _ = _ := by ring


/-! ## Elementary helpers -/

/-- A good height for every `T ≥ 2`: apply `good_height` at `max T 5`. -/
theorem good_height_ge_two : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → ∃ T' : ℝ,
      T ≤ T' ∧ T' ≤ T + 4 ∧ 5 ≤ T' ∧
      ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
        χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤
          C * Real.log ((q : ℝ) * max T 5) ^ 2 := by
  obtain ⟨C, hC, hG⟩ := good_height
  refine ⟨C, hC, fun q _ χ hχ T hT => ?_⟩
  obtain ⟨T', ⟨h1, h2⟩, hb⟩ := hG q χ hχ (max T 5) (le_max_right _ _)
  refine ⟨T', (le_max_left _ _).trans h1, ?_, (le_max_right _ _).trans h1, hb⟩
  rcases le_total T 5 with h | h
  · rw [max_eq_right h] at h2; linarith
  · rw [max_eq_left h] at h2; linarith

/-- The trivial zero sum lies in `[0, 1]` for `n ≥ 2`. -/
theorem trivSum_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 2 ≤ n) :
    |trivSum χ n| ≤ 1 := by
  have hx : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / ((n : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  obtain ⟨⟨e0, e1⟩, ⟨o0, o1⟩⟩ := CharTrivial1122.trivial_sum_le hx
  unfold trivSum
  split_ifs
  · rw [abs_of_nonneg e0]; linarith
  · rw [abs_of_nonneg o0]; linarith

/-- `zeroLog χ n` lies in `[0, log n]`. -/
theorem zeroLog_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 2 ≤ n) :
    |zeroLog χ n| ≤ Real.log n := by
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  unfold zeroLog
  split_ifs
  · rw [abs_of_nonneg hl]
  · simpa using hl

/-- The constant `b(χ)` exists for every primitive `χ ≠ 1`. -/
theorem exists_isB {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) : ∃ b : ℂ, IsB χ b := by
  rcases χ.even_or_odd with he | ho
  · obtain ⟨b, hb⟩ := CharTrivial1122.exists_b_even hprim hχ he
    exact ⟨b, Or.inr ⟨he, hb⟩⟩
  · exact ⟨_, Or.inl ⟨ho, rfl⟩⟩

/-! ## The assembly -/

set_option maxHeartbeats 1000000 in
/-- PROVED: `contour_good_height_leaf`, `good_height`, `window_switch`
and `CharBRegroup1122.b_regroup` are all PROVED. Davenport, Multiplicative Number
Theory, second edition, ch. 19 p. 117 display (4) with the error (6) at an integer `x = n`,
and p. 118 for `b(χ)`: the half weighted integer character sum plus the zero sum up to height
`T` minus the low reciprocal sum is `O(n/T log² qnT + log q + log n)`, uniformly. This is the
statement of `BhowmikGrimmelt2026.davenport_integer_half_formula592` with `mult χ ρ` unfolded. -/
theorem davenport_half_formula_assembled :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1),
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  obtain ⟨CP, hCP, hP⟩ := CharPerronHalf1122.char_perron_half1122
  obtain ⟨CG, hCG, hG⟩ := good_height_ge_two
  obtain ⟨DC, hDC, hC⟩ := contour_good_height_leaf
  obtain ⟨AW, hAW, hW⟩ := window_switch
  obtain ⟨Cb, hCb, hB⟩ := CharBRegroup1122.b_regroup
  set a1 : ℝ := CP + DC * (4 * CG + 1) + AW with ha1
  set a2 : ℝ := Cb + DC with ha2
  set a3 : ℝ := CP + 3 * DC + 3 with ha3
  refine ⟨a1 + a2 + a3, by rw [ha1, ha2, ha3]; positivity, ?_⟩
  intro q _ χ hprim hχ T hT Z hZ n hn
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hnpos : 0 < n := by omega
  have hT0 : 0 < T := by linarith
  -- real facts
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log n := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
    linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set L : ℝ := Real.log ((q : ℝ) * n * T) with hL
  have hqT2 : 2 ≤ (q : ℝ) * T := by nlinarith
  have hqnT' : (q : ℝ) * n * T = (n : ℝ) * ((q : ℝ) * T) := by ring
  have hqnT : 4 ≤ (q : ℝ) * n * T := by rw [hqnT']; nlinarith
  have hnqnT : (n : ℝ) ≤ (q : ℝ) * n * T := by rw [hqnT']; nlinarith
  have hqTqnT : (q : ℝ) * T ≤ (q : ℝ) * n * T := by rw [hqnT']; nlinarith
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h4 : Real.log 4 ≤ Real.log ((q : ℝ) * n * T) := Real.log_le_log (by norm_num) hqnT
    have : (1 : ℝ) < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hnL : Real.log n ≤ L := by
    rw [hL]; exact Real.log_le_log (by linarith) hnqnT
  have hqTL : Real.log ((q : ℝ) * T) ≤ L := by
    rw [hL]; exact Real.log_le_log (by positivity) hqTqnT
  have hqT0 : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by linarith)
  have hmaxL : Real.log ((q : ℝ) * max T 5) ≤ 2 * L := by
    have hm : max T 5 ≤ 3 * T := max_le (by linarith) (by linarith)
    have hm' : (q : ℝ) * max T 5 ≤ (q : ℝ) * (3 * T) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have h3 : Real.log ((q : ℝ) * max T 5) ≤ Real.log (3 * ((q : ℝ) * n * T)) :=
      Real.log_le_log (mul_pos (by positivity) (lt_of_lt_of_le (by norm_num) (le_max_right T 5)))
        (by have := hqTqnT; linarith)
    rw [Real.log_mul (x := 3) (y := (q : ℝ) * n * T) (by norm_num) (by positivity)] at h3
    have : Real.log 3 ≤ Real.log ((q : ℝ) * n * T) := Real.log_le_log (by norm_num) (by linarith)
    rw [hL]; linarith
  have hmax0 : 0 ≤ Real.log ((q : ℝ) * max T 5) := by
    have h5 : (5 : ℝ) ≤ max T 5 := le_max_right T 5
    exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 (by linarith))
  have hK : CG * Real.log ((q : ℝ) * max T 5) ^ 2 ≤ 4 * CG * L ^ 2 := by
    have : Real.log ((q : ℝ) * max T 5) ^ 2 ≤ (2 * L) ^ 2 := by
      exact pow_le_pow_left₀ hmax0 hmaxL 2
    nlinarith
  set X : ℝ := (n : ℝ) / T * L ^ 2 with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- the good height
  obtain ⟨T', hTT', hT'4, hT'5, hgood⟩ := hG q χ hprim T hT
  -- the zeros up to height `T'`
  have hfin : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T'}.Finite := by
    refine (CharRect1122.charZeros_rect_finite χ hχ 1 T').subset ?_
    rintro ρ ⟨h0, hr0, hr1, hi⟩
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, h0⟩
    · show ρ.re ∈ uIcc (-1 / 2 : ℝ) 1
      rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, hr1.le⟩
    · show ρ.im ∈ uIcc (-T') T'
      rw [abs_lt] at hi
      rw [uIcc_of_le (by linarith)]; exact ⟨hi.1.le, hi.2.le⟩
  set Z' := hfin.toFinset with hZ'
  have hZ'mem : ∀ ρ : ℂ, ρ ∈ Z' ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' := fun ρ => by
    rw [hZ', Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  set W := Z'.filter (fun ρ => ¬ |ρ.im| < T) with hWdef
  have hWmem : ∀ ρ : ℂ, ρ ∈ W ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T ≤ |ρ.im| ∧ |ρ.im| < T' := fun ρ => by
    rw [hWdef, Finset.mem_filter, hZ'mem, not_lt]
    tauto
  have hsplitZ : Z'.filter (fun ρ => |ρ.im| < T) = Z.filter (fun ρ => |ρ.im| < T) := by
    ext ρ
    rw [Finset.mem_filter, Finset.mem_filter, hZ'mem, hZ]
    constructor
    · rintro ⟨⟨h0, h1, h2, _⟩, h4⟩; exact ⟨⟨h0, h1, h2, h4.le⟩, h4⟩
    · rintro ⟨⟨h0, h1, h2, _⟩, h4⟩; exact ⟨⟨h0, h1, h2, by linarith⟩, h4⟩
  have hZ1mem : ∀ ρ : ℂ, ρ ∈ Z.filter (fun ρ => |ρ.im| < 1) ↔
      DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 := fun ρ => by
    rw [Finset.mem_filter, hZ]
    constructor
    · rintro ⟨⟨h0, h1, h2, _⟩, h4⟩; exact ⟨h0, h1, h2, h4⟩
    · rintro ⟨h0, h1, h2, h4⟩; exact ⟨⟨h0, h1, h2, by linarith⟩, h4⟩
  -- the constant `b(χ)`
  obtain ⟨b, hb⟩ := exists_isB hprim hχ
  -- notation
  set f : ℂ → ℂ := fun ρ =>
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (n : ℂ) ^ ρ / ρ with hf
  set P₀ : ℂ := (∑ m ∈ Finset.range n,
      (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
      (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) with hP₀
  set J : ℂ := perronJ χ n T' with hJ
  set SZ : ℂ := ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T), f ρ with hSZ
  set SW : ℂ := ∑ ρ ∈ W, f ρ with hSW
  set S1 : ℂ := ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1),
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ with hS1
  change ‖P₀ + SZ - S1‖ ≤ (a1 + a2 + a3) * (X + Real.log q + Real.log n)
  have hsum : ∑ ρ ∈ Z', f ρ = SZ + SW := by
    rw [← Finset.sum_filter_add_sum_filter_not Z' (fun ρ => |ρ.im| < T), hsplitZ]
  -- the five bounds
  have hT'0 : 0 < T' := by linarith
  have hPer : ‖P₀ - J‖ ≤ CP * ((n : ℝ) * Real.log n ^ 2 / T' + Real.log n) :=
    hP q χ n hn T' (by linarith)
  have hK0 : 0 ≤ CG * Real.log ((q : ℝ) * max T 5) ^ 2 := by positivity
  have hCon : ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ ≤
      DC * ((CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * n / T' +
        Real.log ((q : ℝ) * T') / T' + Real.log n) := by
    have h := hC q χ hprim hχ T' _ (by linarith) hK0 hgood b hb n hn Z' hZ'mem
    rw [← hsum]
    exact h
  have hWb : ‖SW‖ ≤ AW * ((n : ℝ) / T * Real.log ((q : ℝ) * T)) :=
    hW q χ hprim hχ T T' hT hTT' hT'4 n hn W hWmem
  have hbb : ‖b + S1‖ ≤ Cb * Real.log q := hB q χ hprim hχ b hb _ hZ1mem
  have htriv := trivSum_bound χ hn
  have hzl := zeroLog_bound χ hn
  clear_value f P₀ J SZ SW S1
  -- the identity
  have hid : P₀ + SZ - S1 = (P₀ - J) + (J + (SZ + SW) + (zeroLog χ n : ℂ) + b -
      (trivSum χ n : ℂ)) - SW - (zeroLog χ n : ℂ) - (b + S1) + (trivSum χ n : ℂ) := by ring
  have hnT : (n : ℝ) / T' ≤ (n : ℝ) / T := div_le_div_of_nonneg_left (by positivity) hT0 hTT'
  -- bound 1: Perron
  have b1 : ‖P₀ - J‖ ≤ CP * X + CP * Real.log n := by
    refine hPer.trans ?_
    have : (n : ℝ) * Real.log n ^ 2 / T' ≤ X := by
      rw [hX, mul_div_right_comm]
      have h1 : Real.log n ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlogn hnL 2
      have h2 : (n : ℝ) / T' * Real.log n ^ 2 ≤ (n : ℝ) / T * Real.log n ^ 2 :=
        mul_le_mul_of_nonneg_right hnT (by positivity)
      have h3 : (n : ℝ) / T * Real.log n ^ 2 ≤ (n : ℝ) / T * L ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left this hCP
    linarith
  -- bound 2: contour
  have b2 : ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ ≤
      DC * (4 * CG + 1) * X + DC * Real.log q + 3 * DC * Real.log n := by
    refine hCon.trans ?_
    have e1 : (CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * n / T' ≤ (4 * CG + 1) * X := by
      have hA : CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1 ≤ (4 * CG + 1) * L ^ 2 := by
        have hL2 : 1 ≤ L ^ 2 := by linarith
        linarith
      have := mul_le_mul hA hnT (by positivity) (by positivity)
      have e : (CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * n / T' =
          (CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * ((n : ℝ) / T') := by ring
      rw [e, hX]
      linarith
    have e2 : Real.log ((q : ℝ) * T') / T' ≤ Real.log q + 2 * Real.log n := by
      rw [Real.log_mul (by positivity) (by positivity), add_div]
      have h1 : Real.log q / T' ≤ Real.log q := div_le_self hlogq (by linarith)
      have h2 : Real.log T' / T' ≤ 1 := by
        rw [div_le_one hT'0]
        have := Real.log_le_sub_one_of_pos hT'0
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) (le_refl (Real.log n))) hDC
    linarith
  -- bound 3: window
  have b3 : ‖SW‖ ≤ AW * X := by
    refine hWb.trans (mul_le_mul_of_nonneg_left ?_ hAW)
    rw [hX]
    exact mul_le_mul_of_nonneg_left (hqTL.trans hLL) (by positivity)
  -- bound 4, 5, 6
  have b4 : ‖(zeroLog χ n : ℂ)‖ ≤ Real.log n := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hzl
  have b5 : ‖b + S1‖ ≤ Cb * Real.log q := hbb
  have b6 : ‖(trivSum χ n : ℂ)‖ ≤ 2 * Real.log n := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  -- combine
  rw [hid]
  have htri : ‖(P₀ - J) + (J + (SZ + SW) + (zeroLog χ n : ℂ) + b -
      (trivSum χ n : ℂ)) - SW - (zeroLog χ n : ℂ) - (b + S1) + (trivSum χ n : ℂ)‖ ≤
      ‖P₀ - J‖ + ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ + ‖SW‖ +
        ‖(zeroLog χ n : ℂ)‖ + ‖b + S1‖ + ‖(trivSum χ n : ℂ)‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine htri.trans ?_
  have hsum6 : ‖P₀ - J‖ + ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ +
      ‖SW‖ + ‖(zeroLog χ n : ℂ)‖ + ‖b + S1‖ + ‖(trivSum χ n : ℂ)‖ ≤
      a1 * X + a2 * Real.log q + a3 * Real.log n := by
    rw [ha1, ha2, ha3]; linarith
  refine hsum6.trans ?_
  have ha10 : 0 ≤ a1 := by rw [ha1]; positivity
  have ha20 : 0 ≤ a2 := by rw [ha2]; positivity
  have ha30 : 0 ≤ a3 := by rw [ha3]; positivity
  nlinarith [mul_nonneg ha10 hlogq, mul_nonneg ha10 hlogn, mul_nonneg ha20 hX0,
    mul_nonneg ha20 hlogn, mul_nonneg ha30 hX0, mul_nonneg ha30 hlogq]

end LeanLab.PNTPort.ExplicitPsi1.CharHalfAssembly1122
