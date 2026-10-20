module

public import Mathlib
public import LeanLab.HeathBrown1985.Statements
public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
# From residue classes to primitive characters

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `psi_orth`: `φ(q) ψ(x; q, a) = ∑_χ conj(χ a) ψ(x, χ)` for `(a, q) = 1`.
* `abs_psi_sub_le`: `|ψ(x; q, a) - x/φ(q)| ≤ (‖ψ(x, χ₀) - x‖ + ∑_{χ ≠ χ₀} ‖ψ(x, χ)‖) / φ(q)`.
* `norm_psiChi_sub_primitive`: `‖ψ(x, χ) - ψ(x, χ*)‖ ≤ ∑_{n ≤ x, (n, q) > 1} Λ(n)`, `χ*` the
  primitive character inducing `χ`, and the same bound for `‖ψ(x, χ₀) - ψ(x)‖`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset Real ArithmeticFunction

/-- `ψ(x, χ) = ∑_{n ≤ x} Λ(n) χ(n)`. -/
noncomputable def psiChi {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (vonMangoldt n : ℂ) * χ (n : ZMod q)

lemma isUnit_natCast_iff {q : ℕ} (n : ℕ) : IsUnit (n : ZMod q) ↔ n.Coprime q :=
  ZMod.isUnit_iff_coprime n q

/-- **Orthogonality.** -/
theorem psi_orth {q : ℕ} [NeZero q] (x : ℝ) {a : ℕ} (ha : a.Coprime q) :
    ((HeathBrown1985.psi x q a : ℝ) : ℂ) * q.totient =
      ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) * psiChi x χ := by
  have hu : IsUnit (a : ZMod q) := (isUnit_natCast_iff a).2 ha
  unfold psiChi HeathBrown1985.psi
  simp_rw [mul_sum]
  rw [sum_comm]
  have h : ∀ n ∈ Icc 1 ⌊x⌋₊, ∑ χ : DirichletCharacter ℂ q,
      (starRingEnd ℂ) (χ a) * ((vonMangoldt n : ℂ) * χ (n : ZMod q)) =
      if n % q = a % q then (vonMangoldt n : ℂ) * q.totient else 0 := by
    intro n _
    have : ∀ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) * ((vonMangoldt n : ℂ) * χ (n : ZMod q)) =
        (vonMangoldt n : ℂ) * (χ (a : ZMod q)⁻¹ * χ (n : ZMod q)) := by
      intro χ
      rw [LargeSieve.conj_char_of_isUnit χ hu]
      ring
    rw [sum_congr rfl (fun χ _ => this χ), ← mul_sum,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
    by_cases hn : n % q = a % q
    · have : (a : ZMod q) = n := (ZMod.natCast_eq_natCast_iff' a n q).2 hn.symm
      rw [if_pos this, if_pos hn]
    · have : ¬ (a : ZMod q) = n := fun h => hn ((ZMod.natCast_eq_natCast_iff' a n q).1 h).symm
      rw [if_neg this, if_neg hn, mul_zero]
  rw [sum_congr rfl h, ← sum_filter]
  push_cast
  rw [sum_mul]

/-- The residue class error through characters. -/
theorem abs_psi_sub_le {q : ℕ} [NeZero q] (x : ℝ) {a : ℕ} (ha : a.Coprime q) :
    |HeathBrown1985.psi x q a - x / q.totient| ≤
      (‖psiChi x (1 : DirichletCharacter ℂ q) - x‖ +
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖) / q.totient := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hu : IsUnit (a : ZMod q) := (isUnit_natCast_iff a).2 ha
  have horth := psi_orth (q := q) x ha
  rw [← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q)), MulChar.one_apply hu,
    map_one, one_mul] at horth
  have key : ((HeathBrown1985.psi x q a - x / q.totient : ℝ) : ℂ) * q.totient =
      (psiChi x (1 : DirichletCharacter ℂ q) - x) +
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
          (starRingEnd ℂ) (χ a) * psiChi x χ := by
    push_cast
    rw [sub_mul, horth, div_mul_cancel₀ _ (by exact_mod_cast hφ.ne')]
    ring
  have hnorm : |HeathBrown1985.psi x q a - x / q.totient| * q.totient ≤
      ‖psiChi x (1 : DirichletCharacter ℂ q) - x‖ +
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ := by
    have := congrArg norm key
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast] at this
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans ?_))
    apply sum_le_sum
    intro χ _
    rw [norm_mul]
    have h1 : ‖(starRingEnd ℂ) (χ a)‖ ≤ 1 := by
      rw [Complex.norm_conj]; exact DirichletCharacter.norm_le_one χ _
    calc ‖(starRingEnd ℂ) (χ a)‖ * ‖psiChi x χ‖ ≤ 1 * ‖psiChi x χ‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖psiChi x χ‖ := one_mul _
  rw [le_div_iff₀ hφ]
  exact hnorm

/-- Values off the units contribute only through `∑_{(n,q)>1} Λ(n)`. -/
theorem norm_psiChi_sub_primitive {q : ℕ} [NeZero q] (x : ℝ) (χ : DirichletCharacter ℂ q) :
    ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ≤
      ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), vonMangoldt n := by
  unfold psiChi
  rw [← sum_sub_distrib, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊)
    (fun n => ¬ Nat.Coprime n q)]
  have hgood : ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ ¬ Nat.Coprime n q),
      ((vonMangoldt n : ℂ) * χ (n : ZMod q) - (vonMangoldt n : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)) =
      0 := by
    apply sum_eq_zero
    intro n hn
    rw [mem_filter, not_not] at hn
    have hco : IsCoprime (n : ℤ) q := Nat.isCoprime_iff_coprime.2 hn.2
    have := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hco
    push_cast at this
    rw [this, sub_self]
  rw [hgood, add_zero]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro n hn
  rw [mem_filter] at hn
  have hnu : ¬ IsUnit (n : ZMod q) := fun h => hn.2 ((isUnit_natCast_iff n).1 h)
  rw [MulChar.map_nonunit _ hnu, mul_zero, zero_sub, norm_neg, norm_mul]
  have h0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  calc vonMangoldt n * ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ vonMangoldt n * 1 :=
        mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _) h0
    _ = vonMangoldt n := mul_one _

/-- The principal character against `ψ(x)`. -/
theorem norm_psiChi_one_sub {q : ℕ} [NeZero q] (x : ℝ) :
    ‖psiChi x (1 : DirichletCharacter ℂ q) - Chebyshev.psi x‖ ≤
      ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), vonMangoldt n := by
  have hpsi : (Chebyshev.psi x : ℂ) = ∑ n ∈ Icc 1 ⌊x⌋₊, (vonMangoldt n : ℂ) := by
    rw [Chebyshev.psi, show Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ by ext n; simp; omega]
    push_cast; rfl
  unfold psiChi
  rw [hpsi, ← sum_sub_distrib, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊)
    (fun n => ¬ Nat.Coprime n q)]
  have hgood : ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ ¬ Nat.Coprime n q),
      ((vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q) - (vonMangoldt n : ℂ)) = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [mem_filter, not_not] at hn
    rw [MulChar.one_apply ((isUnit_natCast_iff n).2 hn.2), mul_one, sub_self]
  rw [hgood, add_zero]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro n hn
  rw [mem_filter] at hn
  have hnu : ¬ IsUnit (n : ZMod q) := fun h => hn.2 ((isUnit_natCast_iff n).1 h)
  rw [MulChar.map_nonunit _ hnu, mul_zero, zero_sub, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]

end LeanLab.PNTPort.BV
