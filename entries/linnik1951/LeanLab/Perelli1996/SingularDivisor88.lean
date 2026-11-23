module

public import LeanLab.Perelli1996.DivisorFactor
public import LeanLab.Perelli1996.Sing
public import LeanLab.Perelli1996.Triad22

/-!
P0083, page 488, the singular series divisor expansion before equation 33.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial
noncomputable section

/-- The singular series at two equals the constant singular series on page 479. -/
theorem sing_two_eq_constant : Sing 2 = singularConstant := by
  classical
  let two : {p : ℕ // p.Prime} := ⟨2, Nat.prime_two⟩
  let g := Triad22.twinC_factor
  have hfactor (p : {p : ℕ // p.Prime}) : singF 2 p = (if p = two then 2 else 1) * g p := by
    by_cases hp2 : p.1 = 2
    · have heq : p = two := Subtype.ext hp2
      subst p
      norm_num [g, Triad22.twinC_factor, singF, two]
    · have hne : p ≠ two := by intro h; apply hp2; exact congrArg Subtype.val h
      have hnd : ¬ p.1 ∣ 2 := by
        intro hd
        have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
        have := p.2.two_le
        omega
      simp [g, Triad22.twinC_factor, singF, hp2, hne, hnd]
  have hprod : Sing 2 = 2 * ∏' p, g p := by
    have hh := (hasProd_ite_eq two (2 : ℝ)).mul Triad22.twinC_multipliable.hasProd
    rw [sing_eq]
    have hfun : singF 2 = fun p => (if p = two then 2 else 1) * g p := funext hfactor
    rw [hfun]
    exact hh.tprod_eq
  rw [hprod]
  unfold singularConstant LeanLab.ChenExplicit.twinC
  apply congrArg (fun x : ℝ => 2 * x)
  let embed (p : {p : ℕ // p.Prime ∧ 2 < p}) : {p : ℕ // p.Prime} := ⟨p.1, p.2.1⟩
  have hinj : Function.Injective embed := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun p : {p : ℕ // p.Prime} => p.1) h
  have hs : Function.mulSupport g ⊆ Set.range embed := by
    intro p hp
    have hp2 : 2 < p.1 := by
      have hpge := p.2.two_le
      have hpne : p.1 ≠ 2 := by
        intro h
        apply hp
        simp [g, Triad22.twinC_factor, h]
      omega
    exact ⟨⟨p.1, p.2, hp2⟩, rfl⟩
  rw [← hinj.tprod_eq hs]
  apply tprod_congr
  intro p
  have hp2 : p.1 ≠ 2 := by have := p.2.2; omega
  simp [g, Triad22.twinC_factor, embed, hp2]

/-- The finite divisor expansion of the singular series for positive even integers. -/
theorem sing_even_divisor_sum (n : ℕ) (hn : n ≠ 0) (heven : Even n) :
    Sing n = singularConstant * ∑ d ∈ n.divisors, arithmeticFactor d := by
  classical
  let g (p : {p : ℕ // p.Prime}) : ℝ := if p.1 ∣ n then 1 + arithmeticFactor p.1 else 1
  let S : Finset {p : ℕ // p.Prime} := n.primeFactors.subtype Nat.Prime
  have hgout (p : {p : ℕ // p.Prime}) (hp : p ∉ S) : g p = 1 := by
    have hnd : ¬ p.1 ∣ n := by
      intro hd
      apply hp
      apply Finset.mem_subtype.mpr
      exact Nat.mem_primeFactors.mpr ⟨p.2, hd, hn⟩
    simp [g, hnd]
  have hg : HasProd g (∏ p ∈ S, g p) := hasProd_prod_of_ne_finset_one hgout
  have hfactor (p : {p : ℕ // p.Prime}) : singF n p = singF 2 p * g p := by
    by_cases hp2 : p.1 = 2
    · have h2 : 2 ∣ n := heven.two_dvd
      simp [singF, hp2, h2, g, arithmeticFactor_even (by norm_num : 2 ∣ 2)]
    · have hpgt : 2 < p.1 := by have := p.2.two_le; omega
      have hnd : ¬ p.1 ∣ 2 := by
        intro hd
        have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
        omega
      have hpR : (2 : ℝ) < p.1 := by exact_mod_cast hpgt
      have hp1 : (p.1 : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p.1 : ℝ) - 2 ≠ 0 := by linarith
      simp only [singF, g, if_neg hnd]
      by_cases hd : p.1 ∣ n
      · rw [if_pos hd, if_pos hd, arithmeticFactor_prime p.2 hpgt]
        field_simp
        ring
      · simp [hd]
  have hprod : (∏ p ∈ S, g p) = ∏ p ∈ n.primeFactors, (1 + arithmeticFactor p) := by
    calc
      (∏ p ∈ S, g p) = (∏ p ∈ S, (1 + arithmeticFactor p.1)) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hmem : p.1 ∈ n.primeFactors := Finset.mem_subtype.mp hp
        simp [g, Nat.dvd_of_mem_primeFactors hmem]
      _ = _ := by
        exact Finset.prod_subtype_of_mem (s := n.primeFactors) (fun p : ℕ => 1 + arithmeticFactor p)
          (fun p hp => Nat.prime_of_mem_primeFactors hp)
  calc Sing n = ∏' p, singF 2 p * g p := by rw [sing_eq]; exact tprod_congr hfactor
    _ = (∏' p, singF 2 p) * ∏' p, g p :=
      (sing_multipliable (n := 2) (by norm_num)).tprod_mul hg.multipliable
    _ = Sing 2 * ∏ p ∈ S, g p := by rw [hg.tprod_eq]; rfl
    _ = singularConstant * ∑ d ∈ n.divisors, arithmeticFactor d := by
      rw [sing_two_eq_constant, hprod, sum_arithmeticFactor n hn]

end
end LeanLab.Perelli1996.Section3
