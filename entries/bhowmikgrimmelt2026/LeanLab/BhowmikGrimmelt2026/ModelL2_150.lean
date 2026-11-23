module

public import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150
public import LeanLab.HeathBrown1985.DivisorEps

/-!
ROUTE BURST 7, 20261112. The size of the major arc model, P0029 Bhowmik and Grimmelt 2026,
page 12: the main term of 3.5 on the arc around `a/q` has size `N/φ(q)`, and in mean square
`∫_0^1 |V(α)|² dα ≪ X^{1+ε}` for the model `V = VX150 X` of MeanSquareCore150.lean.

Proof: the Dirichlet arcs of different denominators are disjoint, so `|V(α)|²` is the square of
one term; for `α ∈ [0, 1]` the nearest integer `a` to `qα` lies in `[0, q]`, so that term is at
most `φ(q)^{-2} Σ_{a=0}^{q} |T(α - a/q)|²`; `∫_0^1 |T(α - c)|² dα = X`; and
`Σ_{q ≤ Q} (q+1)/φ(q)² ≪ Q^{4/k}` from `n ≤ φ(n) d(n)`, the divisor bound
`d(n) ≪ n^{1/k}` of HeathBrown1985/DivisorEps.lean, and `Σ_{q ≤ Q} 1/q ≤ 1 + log Q`.

Copies, said plainly: `le_totient_mul_card_divisors_m150` and `totient_rpow_bound_m150` are
verbatim copies of the private lemmas `le_totient_mul_card_divisors` and `totient_rpow_bound`
of SingularTail150.lean, which cannot be used from here because they are private.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-! ### Copies from SingularTail150.lean -/

/-- `n ≤ φ(n) d(n)`. Verbatim copy of the private lemma of SingularTail150.lean. -/
private lemma le_totient_mul_card_divisors_m150 (n : ℕ) :
    n ≤ Nat.totient n * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hid := Nat.totient_mul_prod_primeFactors n
  have h2 : ∏ p ∈ n.primeFactors, p ≤
      2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h3 : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
    rw [Nat.card_divisors hn.ne', ← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have hp' : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
    have : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    omega
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ Nat.totient n * (n.divisors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
      _ = (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

/-- `n ^ a / φ(n)² ≤ D² n ^ (a - 2 + 2/k)`. Verbatim copy of the private lemma of
SingularTail150.lean. -/
private lemma totient_rpow_bound_m150 (k : ℕ) (hk : 1 ≤ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ℝ,
      (n : ℝ) ^ a / (Nat.totient n : ℝ) ^ 2 ≤ D ^ 2 * (n : ℝ) ^ (a - 2 + 2 * (k : ℝ)⁻¹) := by
  obtain ⟨D, hD, hDb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨D, hD, fun n hn a => ?_⟩
  set t : ℝ := (k : ℝ)⁻¹ with ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have h1 : (n : ℝ) ≤ (Nat.totient n : ℝ) * (D * (n : ℝ) ^ t) := by
    have h0 := le_totient_mul_card_divisors_m150 n
    have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * (n.divisors.card : ℝ) := by exact_mod_cast h0
    exact h'.trans (mul_le_mul_of_nonneg_left (hDb n hn) hφ.le)
  have hsplit : (n : ℝ) = (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t := by
    rw [← Real.rpow_add hnR]; simp
  have hnt : 0 < (n : ℝ) ^ t := Real.rpow_pos_of_pos hnR t
  have h2 : (n : ℝ) ^ (1 - t) ≤ D * (Nat.totient n : ℝ) := by
    have h4 : (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t ≤ (D * (Nat.totient n : ℝ)) * (n : ℝ) ^ t := by
      rw [← hsplit]; linarith [h1]
    exact le_of_mul_le_mul_right h4 hnt
  have h3 : (n : ℝ) ^ (2 - 2 * t) ≤ D ^ 2 * (Nat.totient n : ℝ) ^ 2 := by
    have e : (n : ℝ) ^ (2 - 2 * t) = ((n : ℝ) ^ (1 - t)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
      congr 1
      push_cast
      ring
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have e2 : (n : ℝ) ^ a = (n : ℝ) ^ (a - 2 + 2 * t) * (n : ℝ) ^ (2 - 2 * t) := by
    rw [← Real.rpow_add hnR]; congr 1; ring
  rw [e2, div_le_iff₀ (by positivity)]
  calc (n : ℝ) ^ (a - 2 + 2 * t) * (n : ℝ) ^ (2 - 2 * t)
      ≤ (n : ℝ) ^ (a - 2 + 2 * t) * (D ^ 2 * (Nat.totient n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = D ^ 2 * (n : ℝ) ^ (a - 2 + 2 * t) * (Nat.totient n : ℝ) ^ 2 := by ring

/-! ### The pieces -/

/-- `∫_0^1 |T(α - c)|² dα = X`, Parseval for the model sum. PROVED. -/
theorem integral_norm_sq_TX_shift150 (X : ℕ) (c : ℝ) :
    ∫ α in (0 : ℝ)..1, ‖TX150 X (α - c)‖ ^ 2 = X := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have e1 : ∀ α : ℝ, ((‖TX150 X (α - c)‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ Finset.Icc 1 X,
      ∑ m ∈ Finset.Icc 1 X, ee (-((((n : ℤ) - m : ℤ) : ℝ) * c)) *
        ee ((((n : ℤ) - m : ℤ) : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold TX150
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [conj_ee150, ← ee_add150, ← ee_add150]
    congr 1; push_cast; ring
  simp_rw [e1]
  rw [integral_double_sum150]
  push_cast
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_eq_single n
    (fun b _ hb => by rw [if_neg (by omega)]; simp) (fun h => by simp_all))]
  simp [ee]

/-- The Dirichlet arcs of different denominators are disjoint. PROVED. -/
theorem arcSet_disjoint150 (X : ℕ) {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hne : q ≠ q')
    {α : ℝ} (h : α ∈ arcSet150 X q) (h' : α ∈ arcSet150 X q') : False := by
  simp only [arcSet150, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at h h'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · linarith [h.1, h'.2 q (Finset.mem_Ico.mpr ⟨hq, hlt⟩)]
  · linarith [h'.1, h.2 q' (Finset.mem_Ico.mpr ⟨hq', hlt⟩)]

/-- `|V(α)|² ≤ Σ_q |1_{A_q}(α) term_q(α)|²`, since at most one term is nonzero. PROVED. -/
theorem norm_sq_VX_le_sum150 (X : ℕ) (α : ℝ) :
    ‖VX150 X α‖ ^ 2 ≤ ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ‖arcTerm150 X q α‖ ^ 2 := by
  unfold VX150
  by_cases hex : ∃ q0 ∈ Finset.Icc 1 (Nat.sqrt X), α ∈ arcSet150 X q0
  · obtain ⟨q0, hq0, hα⟩ := hex
    rw [Finset.sum_eq_single q0]
    · rw [Set.indicator_of_mem hα]
      exact Finset.single_le_sum (f := fun q => ‖arcTerm150 X q α‖ ^ 2)
        (fun _ _ => by positivity) hq0
    · intro b hb hbne
      have hb1 := (Finset.mem_Icc.mp hb).1
      have hq01 := (Finset.mem_Icc.mp hq0).1
      rw [Set.indicator_of_notMem]
      intro hbα
      exact arcSet_disjoint150 X hq01 hb1 (Ne.symm hbne) hα hbα
    · intro h; exact absurd hq0 h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun q hq => Set.indicator_of_notMem (hex q hq) _)]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- For `α ∈ [0, 1]` the nearest integer to `qα` lies in `[0, q]`. PROVED. -/
theorem nint_mem150 {q : ℕ} {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ nint150 ((q : ℝ) * α) ∧ nint150 ((q : ℝ) * α) ≤ q := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : 0 ≤ (q : ℝ) * α := mul_nonneg hq0 hα.1
  have h2 : (q : ℝ) * α ≤ q := by nlinarith [hα.2]
  unfold nint150
  constructor
  · exact Int.floor_nonneg.mpr (by linarith)
  · rw [Int.floor_le_iff]; push_cast; linarith

/-- The term on the arc of denominator `q` is at most `φ(q)^{-2} Σ_{a ≤ q} |T(α - a/q)|²` on
`[0, 1]`. PROVED. -/
theorem norm_sq_arcTerm_le150 (X : ℕ) {q : ℕ} (hq : 1 ≤ q) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ‖arcTerm150 X q α‖ ^ 2 ≤ ∑ a ∈ Finset.range (q + 1),
      1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2 := by
  obtain ⟨h0, hq'⟩ := nint_mem150 (q := q) hα
  set a0 := (nint150 ((q : ℝ) * α)).toNat with ha0
  have ha0cast : ((nint150 ((q : ℝ) * α) : ℤ) : ℝ) = (a0 : ℝ) := by
    rw [ha0]
    have := Int.toNat_of_nonneg h0
    exact_mod_cast this.symm
  have ha0mem : a0 ∈ Finset.range (q + 1) := by
    rw [Finset.mem_range]; omega
  have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcoef : ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ ^ 2 ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
    rw [norm_div, Complex.norm_natCast, div_pow, Complex.norm_intCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm : |((moebius q : ℤ) : ℝ)| ≤ 1 := by
      have := abs_moebius_le_one (n := q)
      exact_mod_cast this
    have := pow_le_pow_left₀ (abs_nonneg _) hm 2
    simpa using this
  calc ‖arcTerm150 X q α‖ ^ 2
      = ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ ^ 2 *
          ‖TX150 X (α - (a0 : ℝ) / q)‖ ^ 2 := by
        unfold arcTerm150
        rw [ha0cast, norm_mul, mul_pow]
    _ ≤ 1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a0 : ℝ) / q)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ ∑ a ∈ Finset.range (q + 1),
          1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2 :=
        Finset.single_le_sum (f := fun a : ℕ =>
          1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2)
          (fun _ _ => by positivity) ha0mem

/-- `∫_0^1 |V|² ≤ X Σ_{q ≤ Q} (q + 1)/φ(q)²`. PROVED. -/
theorem integral_norm_sq_VX_le_sum150 (X : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2 ≤
      (X : ℝ) * ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 := by
  set M := ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ * X
  have hVM : ∀ α, ‖VX150 X α‖ ≤ M := norm_VX_le150 X
  have hV2int : IntervalIntegrable (fun α => ‖VX150 X α‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := M ^ 2) ?_ (ae_of_all _ fun α => ?_)
    · exact ((measurable_VX150 X).norm.pow_const 2).aestronglyMeasurable.restrict
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
  have hTc : ∀ q a : ℕ, Continuous fun α : ℝ => ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2 :=
    fun q a => ((continuous_TX150 X).comp (continuous_id.sub continuous_const)).norm.pow 2
  have hRint : IntervalIntegrable (fun α => ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ∑ a ∈ Finset.range (q + 1),
        1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2) volume 0 1 :=
    (continuous_finsetSum _ fun q _ => continuous_finsetSum _ fun a _ =>
      continuous_const.mul (hTc q a)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on zero_le_one hV2int hRint (fun α hα => by
    refine (norm_sq_VX_le_sum150 X α).trans (Finset.sum_le_sum fun q hq => ?_)
    exact norm_sq_arcTerm_le150 X (Finset.mem_Icc.mp hq).1 hα)
  refine hmono.trans (le_of_eq ?_)
  have hIq : ∀ q ∈ Finset.Icc 1 (Nat.sqrt X), IntervalIntegrable (fun α => ∑ a ∈ Finset.range (q + 1),
      1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2) volume 0 1 :=
    fun q _ => (continuous_finsetSum _ fun a _ =>
      continuous_const.mul (hTc q a)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hIq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hIa : ∀ a ∈ Finset.range (q + 1), IntervalIntegrable (fun α =>
      1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2) volume 0 1 :=
    fun a _ => (continuous_const.mul (hTc q a)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hIa]
  simp_rw [intervalIntegral.integral_const_mul, integral_norm_sq_TX_shift150]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `Σ_{1 ≤ q ≤ Q} 1/q ≤ 1 + log Q`, from Mathlib's `harmonic_le_one_add_log`. PROVED. -/
theorem sum_inv_le_one_add_log150 (Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q ≤ 1 + Real.log Q := by
  have h : ∀ n : ℕ, ∑ q ∈ Finset.Icc 1 n, (1 : ℝ) / q = (harmonic n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      ring
  rw [h]
  exact_mod_cast harmonic_le_one_add_log Q

/-- `Σ_{1 ≤ q ≤ Q} (q + 1)/φ(q)² ≪_k Q^{4/k}`. PROVED. -/
theorem sum_totient_weight_le150 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q →
      ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 ≤
        C * (Q : ℝ) ^ (4 * (k : ℝ)⁻¹) := by
  obtain ⟨D, hD, hDb⟩ := totient_rpow_bound_m150 k hk
  set t : ℝ := 2 * (k : ℝ)⁻¹ with ht
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have ht0 : 0 < t := by positivity
  refine ⟨2 * D ^ 2 * (1 + 1 / t), by positivity, fun Q hQ => ?_⟩
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  -- pointwise
  have hpt : ∀ q ∈ Finset.Icc 1 Q, ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 ≤
      2 * D ^ 2 * (Q : ℝ) ^ t * (1 / q) := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hqpos : (0 : ℝ) < q := by linarith
    have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hb := hDb q hq1 1
    rw [Real.rpow_one] at hb
    have he : (1 : ℝ) - 2 + 2 * (k : ℝ)⁻¹ = t - 1 := by rw [ht]; ring
    rw [he] at hb
    have hqt : (q : ℝ) ^ (t - 1) = (q : ℝ) ^ t * (1 / q) := by
      rw [Real.rpow_sub hqpos, Real.rpow_one]; ring
    have hqQt : (q : ℝ) ^ t ≤ (Q : ℝ) ^ t :=
      Real.rpow_le_rpow hqpos.le (by exact_mod_cast hqQ) ht0.le
    have h2 : ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 ≤ 2 * ((q : ℝ) / (Nat.totient q : ℝ) ^ 2) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    calc ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 ≤ 2 * ((q : ℝ) / (Nat.totient q : ℝ) ^ 2) := h2
      _ ≤ 2 * (D ^ 2 * ((q : ℝ) ^ t * (1 / q))) := by rw [← hqt]; linarith
      _ ≤ 2 * (D ^ 2 * ((Q : ℝ) ^ t * (1 / q))) := by
          have : (q : ℝ) ^ t * (1 / q) ≤ (Q : ℝ) ^ t * (1 / q) :=
            mul_le_mul_of_nonneg_right hqQt (by positivity)
          have hD2 : 0 ≤ D ^ 2 := by positivity
          nlinarith
      _ = 2 * D ^ 2 * (Q : ℝ) ^ t * (1 / q) := by ring
  have hsum := Finset.sum_le_sum hpt
  rw [← Finset.mul_sum] at hsum
  have hharm := sum_inv_le_one_add_log150 Q
  have hlog : Real.log Q ≤ (Q : ℝ) ^ t / t := Real.log_le_rpow_div hQ0 ht0
  have hQt1 : (1 : ℝ) ≤ (Q : ℝ) ^ t := Real.one_le_rpow hQR ht0.le
  have hpow : (Q : ℝ) ^ t * (Q : ℝ) ^ t = (Q : ℝ) ^ (4 * (k : ℝ)⁻¹) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; rw [ht]; ring
  have hfin : (Q : ℝ) ^ t * (1 + Real.log Q) ≤ (1 + 1 / t) * (Q : ℝ) ^ (4 * (k : ℝ)⁻¹) := by
    rw [← hpow]
    have h1 : 1 + Real.log Q ≤ (Q : ℝ) ^ t + (Q : ℝ) ^ t / t := by linarith
    have hQtpos : 0 ≤ (Q : ℝ) ^ t := by positivity
    calc (Q : ℝ) ^ t * (1 + Real.log Q) ≤ (Q : ℝ) ^ t * ((Q : ℝ) ^ t + (Q : ℝ) ^ t / t) :=
          mul_le_mul_of_nonneg_left h1 hQtpos
      _ = (1 + 1 / t) * ((Q : ℝ) ^ t * (Q : ℝ) ^ t) := by field_simp
  have hc0 : 0 ≤ 2 * D ^ 2 := by positivity
  calc ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2
      ≤ 2 * D ^ 2 * (Q : ℝ) ^ t * ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q := hsum
    _ ≤ 2 * D ^ 2 * (Q : ℝ) ^ t * (1 + Real.log Q) :=
        mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = 2 * D ^ 2 * ((Q : ℝ) ^ t * (1 + Real.log Q)) := by ring
    _ ≤ 2 * D ^ 2 * ((1 + 1 / t) * (Q : ℝ) ^ (4 * (k : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hfin hc0
    _ = 2 * D ^ 2 * (1 + 1 / t) * (Q : ℝ) ^ (4 * (k : ℝ)⁻¹) := by ring

/-- P0029 page 12, the size of the main term in mean square: `∫_0^1 |V(α)|² dα ≪ X^{1+ε}`.
PROVED. -/
theorem integral_norm_sq_VX_le150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2 ≤ C * (X : ℝ) ^ (1 + ε) := by
  intro ε hε
  set k : ℕ := ⌈2 / ε⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 / ε : ℝ) < k := by
    have := Nat.le_ceil (2 / ε)
    rw [hk]; push_cast; linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs : 2 * (k : ℝ)⁻¹ ≤ ε := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hkpos]
    have := (div_lt_iff₀ hε).mp hkR
    linarith
  obtain ⟨C, hC0, hC⟩ := sum_totient_weight_le150 k hk1
  refine ⟨C, fun X hX => ?_⟩
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hQ1 : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa using hX)
  have hQR : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast hQ1
  have hQ2 : ((Nat.sqrt X : ℝ)) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  -- `Q^{4/k} = (Q²)^{2/k} ≤ X^{2/k} ≤ X^ε`
  have hQpow : (Nat.sqrt X : ℝ) ^ (4 * (k : ℝ)⁻¹) ≤ (X : ℝ) ^ ε := by
    have e : (Nat.sqrt X : ℝ) ^ (4 * (k : ℝ)⁻¹) = ((Nat.sqrt X : ℝ) ^ 2) ^ (2 * (k : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
    rw [e]
    calc ((Nat.sqrt X : ℝ) ^ 2) ^ (2 * (k : ℝ)⁻¹) ≤ (X : ℝ) ^ (2 * (k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hQ2 (by positivity)
      _ ≤ (X : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hXR hs
  have hmain := integral_norm_sq_VX_le_sum150 X
  have hw := hC (Nat.sqrt X) hQ1
  calc ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2
      ≤ (X : ℝ) * ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 :=
        hmain
    _ ≤ (X : ℝ) * (C * (X : ℝ) ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ hX0
        exact hw.trans (mul_le_mul_of_nonneg_left hQpow hC0)
    _ = C * (X : ℝ) ^ (1 + ε) := by
        rw [Real.rpow_add (by linarith), Real.rpow_one]; ring

end LeanLab.BhowmikGrimmelt2026
