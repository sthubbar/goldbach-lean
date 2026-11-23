module

public import Mathlib
public import LeanLab.Perelli1996.Statements
public import LeanLab.Perelli1996.Sing

@[expose] public section

namespace LeanLab.Perelli1996.Triad22
open Finset Real Filter Topology

/-- The factor `(1 if p=2 else 1 - 1/(p-1)²)` inside the twin prime constant `C_2`. -/
noncomputable def twinC_factor (p : {p : ℕ // p.Prime}) : ℝ :=
  if p.1 = 2 then 1 else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

theorem twinC_multipliable : Multipliable twinC_factor := by
  have hf : twinC_factor = fun p => 1 + (if p.1 = 2 then 0 else -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    funext p; unfold twinC_factor; split_ifs <;> ring
  rw [hf]
  apply Real.multipliable_one_add_of_summable
  have hg : Summable (fun p : {p : ℕ // p.Prime} => 4 / ((p.1 : ℝ)) ^ 2) := by
    have : Summable (fun m : ℕ => 4 / ((m : ℝ)) ^ 2) := by
      simpa [div_eq_mul_inv] using
        (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2)).mul_left 4
    exact this.subtype _
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [] with p
  have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
  split_ifs with hp
  · norm_num; positivity
  · rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_sub_one_sq_le h2

theorem partial_twinC_ge_half (S : Finset {p : ℕ // p.Prime}) : (1 : ℝ) / 2 ≤ ∏ p ∈ S, twinC_factor p := by
  set S' := S.erase ⟨2, Nat.prime_two⟩
  have h1 : ∏ p ∈ S, twinC_factor p = ∏ p ∈ S', twinC_factor p := by
    by_cases h2 : (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ S
    · rw [← Finset.mul_prod_erase S _ h2]
      have hf2 : twinC_factor ⟨2, Nat.prime_two⟩ = 1 := by
        unfold twinC_factor; rw [ite_eq_left_iff.2 (by intro h; contradiction)]
      rw [hf2, one_mul]
    · have h_eq : S = S' := by
        ext a
        rw [Finset.mem_erase]
        constructor
        · intro h
          exact ⟨by rintro rfl; exact h2 h, h⟩
        · rintro ⟨_, h⟩; exact h
      rw [h_eq]
  rw [h1]
  have hS' : ∀ p ∈ S', 3 ≤ p.1 := by
    intro p hp
    have hne : p ≠ ⟨2, Nat.prime_two⟩ := Finset.ne_of_mem_erase hp
    have h2le := p.2.two_le
    by_contra h
    apply hne
    apply Subtype.ext
    show p.1 = 2
    omega
  have h_eq_map : ∏ p ∈ S', twinC_factor p = ∏ p ∈ S'.map (Function.Embedding.subtype _), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro p hp
    unfold twinC_factor
    have hp_ne : p.1 ≠ 2 := by
      have h3 := hS' p hp
      omega
    rw [ite_eq_right_iff.2 (by intro h; contradiction)]
    rfl
  rw [h_eq_map]
  apply prod_ge_half (S'.map (Function.Embedding.subtype _))
  intro p hp
  rw [Finset.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩
  exact hS' q hq

theorem twinC_pos : 0 < ∏' p, twinC_factor p := by
  have hprod := twinC_multipliable.hasProd
  have hge : (1 : ℝ) / 2 ≤ ∏' p, twinC_factor p := by
    apply ge_of_tendsto hprod
    filter_upwards [] with S
    exact partial_twinC_ge_half S
  linarith

theorem triad22_pos : 0 < ∏' p : {p : ℕ // p.Prime}, (if p.1 = 2 then (1 : ℝ) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := twinC_pos

theorem partial_main (n : ℕ) (hnEven : Even n) (S : Finset {p : ℕ // p.Prime}) (h2 : (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ S) :
  2 * ∏ p ∈ S, twinC_factor p ≤ ∏ p ∈ S, singF n p := by
  set two : {p : ℕ // p.Prime} := ⟨2, Nat.prime_two⟩
  have hf2 : singF n two = 2 := by
    unfold singF
    have ht_div : 2 ∣ n := even_iff_two_dvd.1 hnEven
    rw [ite_eq_left_iff.2 (by intro h; contradiction)]
    norm_num
  have ht2 : twinC_factor two = 1 := by
    unfold twinC_factor
    rw [ite_eq_left_iff.2 (by intro h; contradiction)]
  rw [← Finset.mul_prod_erase S _ h2, ← Finset.mul_prod_erase S _ h2]
  rw [hf2, ht2, one_mul]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod₀
    · intro p hp
      have hS' : 3 ≤ p.1 := by
        have hne : p ≠ two := Finset.ne_of_mem_erase hp
        have h2le := p.2.two_le
        by_contra h
        apply hne
        apply Subtype.ext
        show p.1 = 2
        omega
      have hp_ne : p.1 ≠ 2 := by omega
      unfold twinC_factor
      rw [ite_eq_right_iff.2 (by intro h; contradiction)]
      have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by
        have h4 : (0 : ℝ) < ((p.1 : ℝ) - 1) ^ 2 := by
          have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hS'
          nlinarith
        rw [div_le_one h4]
        have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hS'
        nlinarith
      have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hS'
      linarith
    · intro p hp
      have hS' : 3 ≤ p.1 := by
        have hne : p ≠ two := Finset.ne_of_mem_erase hp
        have h2le := p.2.two_le
        by_contra h
        apply hne
        apply Subtype.ext
        show p.1 = 2
        omega
      have hp_ne : p.1 ≠ 2 := by omega
      unfold twinC_factor singF
      rw [ite_eq_right_iff.2 (by intro h; contradiction)]
      split_ifs
      · have : (0 : ℝ) < 1 / ((p.1 : ℝ) - 1) := by
          have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hS'
          apply one_div_pos.2; linarith
        have : (0 : ℝ) < 1 / ((p.1 : ℝ) - 1) ^ 2 := by
          have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hS'
          apply one_div_pos.2; nlinarith
        linarith
      · exact le_rfl
  · norm_num

theorem triad22_main (n : ℕ) (hnEven : Even n) (hn0 : n ≠ 0) :
  2 * ∏' p : {p : ℕ // p.Prime}, (if p.1 = 2 then (1 : ℝ) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) ≤ LeanLab.Perelli1996.Sing n := by
  have hs1 : Sing n = ∏' p, singF n p := rfl
  rw [hs1]
  have ht_prod := twinC_multipliable.hasProd
  have hs_prod := (sing_multipliable hn0).hasProd
  have hle : ∀ S : Finset {p : ℕ // p.Prime}, (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ S →
    2 * ∏ p ∈ S, twinC_factor p ≤ ∏ p ∈ S, singF n p := fun S hS => partial_main n hnEven S hS
  have ht_prod2 : Tendsto (fun S => 2 * ∏ p ∈ S, twinC_factor p) atTop (𝓝 (2 * ∏' p, twinC_factor p)) := by
    apply Filter.Tendsto.const_mul
    exact ht_prod
  apply le_of_tendsto_of_tendsto ht_prod2 hs_prod
  filter_upwards [Filter.eventually_ge_atTop {(⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime})}] with S hS
  exact hle S (hS (Finset.mem_singleton_self _))

end LeanLab.Perelli1996.Triad22
