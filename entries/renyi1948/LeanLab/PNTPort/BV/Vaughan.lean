module

public import Mathlib

/-!
Vaughan's identity, pointwise.

Lab proof. AI wrote this file. Known mathematics: R. C. Vaughan, 1977.
No cited input: everything is proved from Mathlib.

With F = Λ·1_{≤u}, F' = Λ·1_{>u}, G = μ·1_{≤v}, ζ = 1, the ring identity
  Λ = F - F*G*ζ + G*log + F' - F'*(ζ*G)
holds in `ArithmeticFunction ℝ` because Λ*ζ = log. Evaluating at n and using that
(ζ*G)(k) = [k = 1] for k ≤ v gives the statement below.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanLab.PNTPort.BV

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Λ cut to `n ≤ u`. -/
noncomputable def vF (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ u then Λ n else 0, by simp⟩

/-- Λ cut to `u < n`. -/
noncomputable def vF' (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if u < n then Λ n else 0, by simp⟩

/-- μ cut to `n ≤ v`. -/
noncomputable def vG (v : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ v then (μ n : ℝ) else 0, by simp⟩

@[simp] lemma vF_apply (u n : ℕ) : vF u n = if n ≤ u then Λ n else 0 := rfl
@[simp] lemma vF'_apply (u n : ℕ) : vF' u n = if u < n then Λ n else 0 := rfl
@[simp] lemma vG_apply (v n : ℕ) : vG v n = if n ≤ v then (μ n : ℝ) else 0 := rfl

lemma af_sub_apply (f g : ArithmeticFunction ℝ) (n : ℕ) : (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, sub_eq_add_neg]

lemma vF_add_vF' (u : ℕ) : vF u + vF' u = Λ := by
  ext n
  simp only [ArithmeticFunction.add_apply, vF_apply, vF'_apply]
  by_cases h : n ≤ u
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mp h]

/-- The ring identity behind Vaughan's identity. -/
lemma vaughan_ring (u v : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      vF u - vF u * vG v * (ζ : ArithmeticFunction ℝ) + vG v * log
        + (vF' u - vF' u * ((ζ : ArithmeticFunction ℝ) * vG v)) := by
  have h1 : vF u - vF u * vG v * (ζ : ArithmeticFunction ℝ) + vG v * log
        + (vF' u - vF' u * ((ζ : ArithmeticFunction ℝ) * vG v))
      = (vF u + vF' u) - ((vF u + vF' u) * (ζ : ArithmeticFunction ℝ)) * vG v
        + vG v * log := by ring
  rw [h1, vF_add_vF', vonMangoldt_mul_zeta]
  ring

/-- `(ζ * G)(k)` as a sum over divisors. -/
lemma zeta_mul_vG_apply (v k : ℕ) :
    ((ζ : ArithmeticFunction ℝ) * vG v) k =
      ∑ d ∈ k.divisors, (if d ≤ v then (μ d : ℝ) else 0) := by
  rw [coe_zeta_mul_apply]
  rfl

/-- For `1 ≤ k ≤ v`, the truncated Möbius sum equals `[k = 1]`. -/
lemma trunc_moebius_sum_of_le (v k : ℕ) (hk : k ≤ v) :
    ∑ d ∈ k.divisors, (if d ≤ v then (μ d : ℝ) else 0) = if k = 1 then 1 else 0 := by
  have h : ∀ d ∈ k.divisors, (if d ≤ v then (μ d : ℝ) else 0) = (μ : ArithmeticFunction ℝ) d := by
    intro d hd
    have hdk : d ≤ k := Nat.divisor_le hd
    simp only [hdk.trans hk, ite_true, intCoe_apply]
  rw [Finset.sum_congr rfl h, ← coe_mul_zeta_apply, coe_moebius_mul_coe_zeta, one_apply]

/-- The easy bound on the truncated Möbius sum. -/
theorem abs_trunc_moebius_sum_le (v k : ℕ) :
    |∑ d ∈ k.divisors, (if d ≤ v then (μ d : ℝ) else 0)| ≤ k.divisors.card := by
  calc |∑ d ∈ k.divisors, (if d ≤ v then (μ d : ℝ) else 0)|
      ≤ ∑ d ∈ k.divisors, |(if d ≤ v then (μ d : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ k.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        split_ifs
        · have := abs_moebius_le_one (n := d)
          exact_mod_cast this
        · simp
    _ = k.divisors.card := by simp

theorem vaughan_identity (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n) :
    (Λ n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0) := by
  have hn0 : n ≠ 0 := by omega
  have key := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_ring u v)
  simp only [ArithmeticFunction.add_apply, af_sub_apply] at key
  -- second term
  have t2 : (vF u * vG v * (ζ : ArithmeticFunction ℝ)) n =
      ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal,
            (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0) := by
    rw [mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    have hx2 : x.2 ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hx |>.2) ∘ fun h => by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1; rw [h, mul_zero] at this; exact this.symm
    rw [natCoe_apply, zeta_apply_ne hx2, Nat.cast_one, mul_one, mul_apply]
    apply Finset.sum_congr rfl
    intro y _
    simp only [vF_apply, vG_apply]
    by_cases h1 : y.1 ≤ u <;> by_cases h2 : y.2 ≤ v <;> simp [h1, h2]
  -- third term
  have t3 : (vG v * log) n =
      ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0) := by
    rw [mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    simp only [vG_apply, log_apply]
    split_ifs <;> simp
  -- fourth term
  have t4 : (vF' u * ((ζ : ArithmeticFunction ℝ) * vG v)) n =
      vF' u n + ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0) := by
    rw [mul_apply]
    have hsplit : ∀ x ∈ n.divisorsAntidiagonal,
        vF' u x.1 * ((ζ : ArithmeticFunction ℝ) * vG v) x.2 =
          (if x.2 = 1 then vF' u x.1 else 0) +
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0) := by
      intro x _
      rw [zeta_mul_vG_apply, vF'_apply]
      by_cases h2 : x.2 ≤ v
      · rw [trunc_moebius_sum_of_le v x.2 h2]
        have : ¬ (u < x.1 ∧ v < x.2) := fun h => absurd h.2 (not_lt.mpr h2)
        rw [ite_eq_right this]
        split_ifs <;> simp
      · have h21 : x.2 ≠ 1 := by omega
        rw [ite_eq_right h21]
        by_cases h1 : u < x.1
        · simp [h1, not_le.mp h2]
        · simp [h1]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (n, 1)]
    · simp
    · intro x hx hne
      have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [ite_eq_right]
      intro h
      apply hne
      rw [h, mul_one] at hx'
      exact Prod.ext hx' h
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn0⟩) h
  rw [t2, t3, t4, vF_apply] at key
  linarith

end LeanLab.PNTPort.BV
