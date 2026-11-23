module

public import LeanLab.LanguascoPerelli1996.Theorem2Data597
public import LeanLab.LanguascoPerelli1996.Arithmetic597

/-!
P0071 pages 353 and 354, Theorem 2, and page 359, corrected log fourth power.
KPP1993 pages 279 through 281, displays 12 through 18.
KPP1995 corrigendum pages 215 and 216, corrected display 18.
All analytic admissions are named cited leaves.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.Decomp597a
open Real Filter Topology ArithmeticFunction MeasureTheory Finset

/-- P0071 page 353, P equals Q times log to minus ten of X. -/
noncomputable def cutoff (X Q : ℝ) : ℝ := Q / Real.log X ^ 10

/-- P0071 page 353, the even integers in the short interval. -/
noncomputable def evenInterval (X H : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈X⌉₊ ⌊X + H⌋₊).filter Even

/-- KPP1993 page 277, translated reduced Farey fractions of bounded denominator. -/
noncomputable def fareyPoints (N : ℕ) : Finset ℚ :=
  (Finset.Icc 1 N).biUnion fun q =>
    ((Finset.Icc (-(q : ℤ)) (2 * q)).filter fun a => a.natAbs.Coprime q).image
      fun a : ℤ => (a : ℚ) / q

/-- KPP1993 page 277, predecessor in the translated Farey sequence. -/
noncomputable def fareyPrev (N : ℕ) (r : ℚ) : ℚ :=
  let s := (fareyPoints N).filter fun t => t < r
  if h : s.Nonempty then s.max' h else r - 1

/-- KPP1993 page 277, successor in the translated Farey sequence. -/
noncomputable def fareyNext (N : ℕ) (r : ℚ) : ℚ :=
  let s := (fareyPoints N).filter fun t => r < t
  if h : s.Nonempty then s.min' h else r + 1

/-- KPP1993 page 277, the mediant endpoint between adjacent reduced fractions. -/
def mediant (r s : ℚ) : ℚ :=
  (r.num + s.num : ℤ) / ((r.den + s.den : ℕ) : ℚ)

/-- P0071 page 353, one actual Farey arc coefficient of the stopped S squared. -/
noncomputable def arcCoefficient (X Q : ℝ) (m : ℕ) (r : ℚ) : ℂ :=
  ∫ α in (mediant (fareyPrev ⌊Q⌋₊ r) r : ℝ)..(mediant r (fareyNext ⌊Q⌋₊ r) : ℝ),
    S X α ^ 2 * e (-(m : ℝ) * α)

/-- P0071 page 353, the major arc coefficient over reduced centers from zero inclusive to one exclusive. -/
noncomputable def majorCoefficient (X Q : ℝ) (m : ℕ) : ℂ :=
  ∑ r ∈ (fareyPoints ⌊Q⌋₊).filter (fun r => 0 ≤ r ∧ r < 1 ∧ (r.den : ℝ) ≤ cutoff X Q),
    arcCoefficient X Q m r

/-- P0071 page 353, the full Fourier coefficient of the actual stopped S squared. -/
noncomputable def fullCoefficient (X : ℝ) (m : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1, S X α ^ 2 * e (-(m : ℝ) * α)

/-- P0071 page 353, complementary minor arc coefficient after one period is dissected. -/
noncomputable def minorCoefficient (X Q : ℝ) (m : ℕ) : ℂ :=
  fullCoefficient X m - majorCoefficient X Q m

/-- P0071 page 353, the actual stopped integer representation count I of m. -/
noncomputable def representationCount (X : ℝ) (m : ℕ) : ℕ :=
  (((Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊) ×ˢ (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊)).filter
    fun p => p.1 + p.2 = m).card

/-- KPP1993 page 277 display 3, Ramanujan sum at minus m. -/
noncomputable def ramanujan (q m : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), e (-(m : ℝ) * a / q)

/-- KPP1993 page 279 display 11, actual Ramanujan singular series tail. -/
noncomputable def tail (P : ℝ) (m : ℕ) : ℂ :=
  ∑' q : ℕ, if P < (q : ℝ) then (muPhi q : ℂ) ^ 2 * ramanujan q m else 0

/-- P0071 page 353, the stopped representation count times the full Ramanujan series. -/
noncomputable def mainTerm (X : ℝ) (m : ℕ) : ℂ :=
  (representationCount X m : ℂ) * ∑' q : ℕ, (muPhi q : ℂ) ^ 2 * ramanujan q m

/-- KPP1993 page 279 display 11 and P0071 page 353 display 8, the exact major arc error. -/
noncomputable def majorError (X Q : ℝ) (m : ℕ) : ℂ :=
  mainTerm X m - (representationCount X m : ℂ) * tail (cutoff X Q) m - majorCoefficient X Q m

/-- KPP1993 page 280 display 14, the large divisor envelope. -/
noncomputable def largeDivisor (P : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d : ℕ => Squarefree d ∧ P < (d : ℝ)), 1 / (Nat.totient d : ℝ)

/-- KPP1993 page 280 display 14, the small divisor envelope including its inverse P factor. -/
noncomputable def smallDivisor (P : ℝ) (m : ℕ) : ℝ :=
  (1 / P) * ∑ d ∈ m.divisors.filter (fun d : ℕ => Squarefree d ∧ (d : ℝ) ≤ P), (d : ℝ) / Nat.totient d

/-- P0071 page 353 display 7, exact coefficient identity behind KPP1993 display 13. -/
theorem coefficient_split (X Q : ℝ) (m : ℕ) :
    fullCoefficient X m - mainTerm X m + majorError X Q m =
      minorCoefficient X Q m - (representationCount X m : ℂ) * tail (cutoff X Q) m := by
  unfold majorError minorCoefficient
  ring

/-- P0071 page 353 display 7, the proved finite norm split with its implicit constant two. -/
theorem display13 (X Q H : ℝ) :
    ∑ m ∈ evenInterval X H, ‖fullCoefficient X m - mainTerm X m + majorError X Q m‖ ^ 2 ≤
      2 * (∑ m ∈ evenInterval X H, ‖minorCoefficient X Q m‖ ^ 2) +
      2 * ∑ m ∈ evenInterval X H,
        ‖(representationCount X m : ℂ) * tail (cutoff X Q) m‖ ^ 2 :=
  Arithmetic597.display13 _ _ _ _ _ _ (fun m _ => coefficient_split X Q m)




/-- P0071 page 353, the stopped integer representation count is at most 2X. -/
theorem representationCount_le {X : ℝ} (hX : 4 ≤ X) (m : ℕ) :
    (representationCount X m : ℝ) ≤ 2 * X := by
  let s := (((Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊) ×ˢ (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊)).filter
    fun p => p.1 + p.2 = m)
  have hc : s.card ≤ (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq heq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      apply Prod.ext heq
      omega
  have hceil : 1 ≤ ⌈X / 4⌉₊ := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hcard : (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊).card ≤ ⌊2 * X⌋₊ := by
    rw [Nat.card_Icc]
    omega
  have hh : representationCount X m ≤ ⌊2 * X⌋₊ := hc.trans hcard
  have hhR : (representationCount X m : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hh
  exact hhR.trans (Nat.floor_le (by linarith : 0 ≤ 2 * X))

/-- P0071 page 353 before display 7, the actual stopped representation count has size at least X over four. -/
theorem representationCount_lower {X : ℝ} (hX : 16 ≤ X) {m : ℕ}
    (hmX : X ≤ (m : ℝ)) (hm2X : (m : ℝ) ≤ 2 * X) :
    X / 4 ≤ (representationCount X m : ℝ) := by
  let l := ⌈X / 4⌉₊
  let b := ⌊2 * X⌋₊
  have hlR : (l : ℝ) < X / 4 + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ X / 4)
  have hml : 2 * l ≤ m := by
    have hh : (2 : ℝ) * l ≤ m := by linarith
    exact_mod_cast hh
  have hmb : m ≤ b := Nat.le_floor hm2X
  have heq : representationCount X m = (Finset.Icc l (m - l)).card := by
    unfold representationCount
    change (((Finset.Icc l b ×ˢ Finset.Icc l b).filter fun p => p.1 + p.2 = m).card) = _
    symm
    apply Finset.card_bij (fun n _ => (n, m - n))
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      have hn0 : n ≤ m := by omega
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega
      · simp only
        omega
    · intro n hn k hk he
      exact congrArg Prod.fst he
    · intro p hp
      obtain ⟨hp, hsum⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hp1l, hp1b⟩ := Finset.mem_Icc.mp hp1
      obtain ⟨hp2l, hp2b⟩ := Finset.mem_Icc.mp hp2
      refine ⟨p.1, Finset.mem_Icc.mpr ⟨hp1l, by omega⟩, ?_⟩
      apply Prod.ext
      · rfl
      · simp only
        omega
  have hcount : representationCount X m = m + 1 - 2 * l := by
    rw [heq, Nat.card_Icc]
    omega
  have hs : 2 * l ≤ m + 1 := by omega
  rw [hcount, Nat.cast_sub hs]
  push_cast
  linarith

/-- P0071 page 353, the cutoff tends past exp of one uniformly in the allowed Q range. -/
theorem eventual_cutoff {ε0 : ℝ} (hε0 : 0 < ε0) (Q : ℝ → ℝ)
    (hQ : ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → X ^ ε0 ≤ Q X ∧ Q X ≤ X ^ (1 / 2 : ℝ) / 2) :
    ∀ᶠ X : ℝ in atTop,
      16 ≤ X ∧ 1 ≤ Real.log X ∧ 0 < Q X ∧ Real.exp 1 ≤ cutoff X (Q X) ∧
      cutoff X (Q X) ≤ Q X ∧ Q X ≤ X ∧ Real.log (cutoff X (Q X)) ≤ Real.log X ∧
      2 ≤ 4 * Q X ^ 2 ∧ 4 * Q X ^ 2 ≤ X ∧ cutoff X (Q X) ^ 2 ≤ 4 * Q X ^ 2 := by
  obtain ⟨X1, hRange⟩ := hQ
  have hh : 0 < ε0 / 2 := by positivity
  filter_upwards [eventually_ge_atTop X1, eventually_ge_atTop (16 : ℝ),
    Arithmetic597.eventually_log_pow_le_rpow 10 hh,
    (tendsto_rpow_atTop hh).eventually_ge_atTop (Real.exp 1)] with X hX1 hX hlogpow hpow
  obtain ⟨hlo, hhi⟩ := hRange X hX1
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hlog : 1 ≤ Real.log X := by
    have he : Real.exp 1 ≤ X := le_trans Real.exp_one_lt_three.le (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hQpos : 0 < Q X := (Real.rpow_pos_of_pos hXpos _).trans_le hlo
  have hLpos : 0 < Real.log X ^ 10 := by positivity
  have hpowmul : X ^ (ε0 / 2) * X ^ (ε0 / 2) = X ^ ε0 := by
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  have hcut : Real.exp 1 ≤ cutoff X (Q X) := by
    apply (le_div_iff₀ hLpos).2
    calc
      _ ≤ X ^ (ε0 / 2) * X ^ (ε0 / 2) :=
        mul_le_mul hpow hlogpow (by positivity) (by positivity)
      _ = X ^ ε0 := hpowmul
      _ ≤ Q X := hlo
  have hLone : 1 ≤ Real.log X ^ 10 := one_le_pow₀ hlog
  have hPQ : cutoff X (Q X) ≤ Q X := by
    exact div_le_self hQpos.le hLone
  have hQX : Q X ≤ X := by
    have hroot : X ^ (1 / 2 : ℝ) ≤ X := by
      simpa using Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1 / 2 : ℝ) ≤ 1)
    linarith
  have hPpos : 0 < cutoff X (Q X) := (Real.exp_pos 1).trans_le hcut
  have hlogP : Real.log (cutoff X (Q X)) ≤ Real.log X :=
    Real.log_le_log hPpos (hPQ.trans hQX)
  have hQone : 1 ≤ Q X := (le_trans (by linarith [Real.exp_one_gt_two] : (1 : ℝ) ≤ Real.exp 1) hcut).trans hPQ
  have hH : 4 * Q X ^ 2 ≤ X := Arithmetic597.short_interval_geometry hXpos.le hQpos.le hhi
  exact ⟨hX, hlog, hQpos, hcut, hPQ, hQX, hlogP, by nlinarith, hH, by nlinarith⟩

/-- P0071 page 353 display 9, Bound5 at minor denominators supplies one uniform envelope. -/
theorem minor_remainder_envelope {Q : ℝ → ℝ} (h5 : Bound5 Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 0 < X → 0 < Q X → 0 < cutoff X (Q X) →
      ∀ (q : ℕ) [NeZero q], cutoff X (Q X) < (q : ℝ) → (q : ℝ) ≤ Q X →
      ∀ a : ℕ, a.Coprime q →
        Ival X (Q X) q a ≤ B * X ^ (1 + δ) / (cutoff X (Q X) * Q X) := by
  obtain ⟨C, X0, hc⟩ := h5 δ hδ
  refine ⟨max C 0, X0, le_max_right _ _, ?_⟩
  intro X hX hXpos hQpos hPpos q inst hPq hq a ha
  calc
    _ ≤ C * X ^ (1 + δ) / (q * Q X) := hc X hX q hq a ha
    _ ≤ max C 0 * X ^ (1 + δ) / (q * Q X) := by
      gcongr
      exact le_max_left _ _
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (mul_pos hPpos hQpos) (by nlinarith)

end LeanLab.LanguascoPerelli1996.Decomp597a
