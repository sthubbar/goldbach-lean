module

public import Mathlib
public import LeanLab.VanDerCorput1939.Statements

/-!
P0067 van der Corput 1939: the constant K of (2) converges, and the global form of the
singular series, K P(N) = ∏_{p ∣ N} (1 − 1/(p−1)²) ∏_{p ∤ N} (1 + 1/(p−1)³) for every N ≥ 1.
For odd N every factor is positive, so K P(N) > 0; for even N the factor at p = 2 is 0, which is
why (1) is stated for odd N only.
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.VanDerCorput1939

open Real Finset

attribute [local instance] Classical.propDecidable

theorem summable_inv_sub_one_cube : Summable (fun n : ℕ => 1 / ((n : ℝ) - 1) ^ 3) := by
  rw [← summable_nat_add_iff 2]
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  refine this.congr fun n => ?_
  push_cast; ring_nf

/-- The Euler product (2) for `K` converges. -/
theorem K_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime} => 1 + 1 / ((p : ℝ) - 1) ^ 3) :=
  Real.multipliable_one_add_of_summable
    (summable_inv_sub_one_cube.subtype (fun p : ℕ => p.Prime))

/-- The local factor `(1 + 1/(p−1)³)(1 − 1/(p² − 3p + 3)) = 1 − 1/(p−1)²`, now for every prime,
`p = 2` included, where both sides are `0`. -/
theorem euler_factor_prime {p : ℕ} (hp : p.Prime) :
    (1 + 1 / ((p : ℝ) - 1) ^ 3) * (1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3)) =
      1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  rcases hp.eq_two_or_odd' with h | h
  · subst h; norm_num
  · have h3 : 3 ≤ p := by
      have := hp.two_le
      rcases h with ⟨k, hk⟩; omega
    exact euler_factor (p : ℝ) (by exact_mod_cast h3)

/-- The global factor at `p`. -/
def globalFactor (N : ℕ) (p : ℕ) : ℝ :=
  if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- **The global identity**: `K P(N) = ∏_p globalFactor N p` for every `N ≠ 0`. -/
theorem K_mul_P (N : ℕ) (hN : N ≠ 0) :
    K * P N = ∏' p : {p : ℕ // p.Prime}, globalFactor N p := by
  set g : {p : ℕ // p.Prime} → ℝ := fun p => 1 + 1 / ((p : ℝ) - 1) ^ 3
  set c : {p : ℕ // p.Prime} → ℝ := fun p =>
    if (p : ℕ) ∣ N then 1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3) else 1
  set s : Finset {p : ℕ // p.Prime} := N.primeFactors.subtype (fun p => p.Prime)
  have hc1 : ∀ p ∉ s, c p = 1 := by
    intro p hp
    simp only [s, mem_subtype, Nat.mem_primeFactors, not_and] at hp
    have : ¬ (p : ℕ) ∣ N := fun h => hp p.2 h hN
    simp only [c, if_neg this]
  have hcm : Multipliable c := multipliable_of_ne_finset_one hc1
  have hcP : ∏' p, c p = P N := by
    rw [tprod_eq_prod hc1]
    unfold P
    have key := prod_subtype_eq_prod_filter (s := N.primeFactors) (p := fun q => Nat.Prime q)
      (fun q : ℕ => if q ∣ N then 1 - 1 / ((q : ℝ) ^ 2 - 3 * q + 3) else (1 : ℝ))
    rw [filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)] at key
    refine (Eq.trans ?_ key).trans ?_
    · simp only [s, c]
    · apply prod_congr rfl
      intro p hp
      simp only [if_pos (Nat.dvd_of_mem_primeFactors hp)]
  have hgc : ∀ p : {p : ℕ // p.Prime}, g p * c p = globalFactor N p := by
    intro p
    simp only [g, c, globalFactor]
    split_ifs with h
    · exact euler_factor_prime p.2
    · ring
  unfold K
  rw [← hcP, ← K_multipliable.tprod_mul hcm]
  exact tprod_congr hgc

/-- Every global factor is positive for odd `N`. -/
theorem globalFactor_pos {N : ℕ} (hN : Odd N) (p : {p : ℕ // p.Prime}) :
    0 < globalFactor N p := by
  have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  unfold globalFactor
  split_ifs with h
  · have hp2 : (p : ℕ) ≠ 2 := by
      intro e; rw [e] at h; exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
    have h3 : (3 : ℝ) ≤ (p : ℕ) := by
      have := p.2.two_le; exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
    linarith
  · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
      apply div_nonneg zero_le_one; apply pow_nonneg; linarith
    linarith

/-- For even `N` the global factor at `2` is `0`, so `K P(N) = 0`: the main term of (1)
vanishes on even `N`, as it must. -/
theorem K_mul_P_even {N : ℕ} (hN : Even N) (hN0 : N ≠ 0) : K * P N = 0 := by
  have h2 : 2 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp hN, hN0⟩
  have : P N = 0 := Finset.prod_eq_zero h2 (by norm_num)
  rw [this, mul_zero]

end LeanLab.VanDerCorput1939
