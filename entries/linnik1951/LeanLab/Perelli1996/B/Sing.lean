module

public import Mathlib
public import LeanLab.Perelli1996.B.Definitions

/-!
P0083 Perelli 1996, page 477: the singular series `𝔖(n)` of `Statements.lean` converges as a
product for every `n ≠ 0`, and `𝔖(n) ≥ 1` for every even `n ≠ 0`. The lower bound is the
classical one: the factor at `2` is `2`, and `∏_{p ≥ 3} (1 - 1/(p-1)²) ≥ ∏_{p=3}^{M} … =
M / (2(M-1)) > 1/2` by telescoping over all integers.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Perelli1996.B
open Finset Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- The factor of `𝔖(n)` at `p`. -/
noncomputable def singF (n : ℕ) (p : {p : ℕ // p.Prime}) : ℝ :=
  if p.1 ∣ n then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

theorem sing_eq (n : ℕ) : Sing n = ∏' p, singF n p := rfl

/-- `1/(p-1)² ≤ 4/p²` for `p ≥ 2`. -/
theorem inv_sub_one_sq_le {p : ℝ} (hp : 2 ≤ p) : 1 / (p - 1) ^ 2 ≤ 4 / p ^ 2 := by
  have h1 : 0 < p - 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The product `𝔖(n)` converges** for every `n ≠ 0`. -/
theorem sing_multipliable {n : ℕ} (hn : n ≠ 0) : Multipliable (singF n) := by
  have hf : singF n = fun p => 1 + (if p.1 ∣ n then 1 / ((p.1 : ℝ) - 1)
      else -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    funext p; unfold singF; split_ifs <;> ring
  rw [hf]
  apply Real.multipliable_one_add_of_summable
  have hg : Summable (fun p : {p : ℕ // p.Prime} => 4 / ((p.1 : ℝ)) ^ 2) := by
    have : Summable (fun m : ℕ => 4 / ((m : ℝ)) ^ 2) := by
      simpa [div_eq_mul_inv] using
        (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2)).mul_left 4
    exact this.subtype _
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : {p : {p : ℕ // p.Prime} | ¬ (n < p.1)}.Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val) _ Subtype.val_injective.injOn
    apply (Set.finite_Iic n).subset
    rintro _ ⟨p, hp, rfl⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hp
    exact hp
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hp
  have hnd : ¬ p.1 ∣ n := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h) (by omega)
  have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
  rw [if_neg hnd, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_sub_one_sq_le h2

/-- Telescoping: `∏_{p=3}^{M} (1 - 1/(p-1)²) = M / (2(M-1))` for `M ≥ 2`. -/
theorem tele (M : ℕ) (hM : 2 ≤ M) :
    ∏ p ∈ Icc 3 M, (1 - 1 / ((p : ℝ) - 1) ^ 2) = (M : ℝ) / (2 * ((M : ℝ) - 1)) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.prod_insert (by simp), ih]
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : (M : ℝ) - 1 ≠ 0 := by intro h; linarith
    have h2 : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
    rw [h2]
    have h3 : (M : ℝ) ≠ 0 := by intro h; linarith
    field_simp
    push_cast
    ring

/-- Over any finite set `T` of integers `≥ 3`, `∏ (1 - 1/(p-1)²) ≥ 1/2`. -/
theorem prod_ge_half (T : Finset ℕ) (hT : ∀ p ∈ T, 3 ≤ p) :
    (1 : ℝ) / 2 ≤ ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  set M := max 2 (T.sup id) with hMdef
  have hM : 2 ≤ M := le_max_left _ _
  have hsub : T ⊆ Icc 3 M := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨hT p hp, le_trans (Finset.le_sup (f := id) hp) (le_max_right _ _)⟩
  have hfac : ∀ p ∈ Icc 3 M, 0 ≤ 1 - 1 / ((p : ℝ) - 1) ^ 2 ∧ 1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.1
    have h4 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
    have h5 : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one h4]; nlinarith
    exact ⟨by linarith, by linarith [one_div_pos.2 h4]⟩
  have hsplit := Finset.prod_sdiff hsub (f := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2)
  have hle : ∏ p ∈ Icc 3 M \ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => (hfac p (Finset.sdiff_subset hp)).1)
      (fun p hp => (hfac p (Finset.sdiff_subset hp)).2)
  have hnn : 0 ≤ ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_nonneg (fun p hp => (hfac p (hsub hp)).1)
  have htele := tele M hM
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hhalf : (1 : ℝ) / 2 ≤ (M : ℝ) / (2 * ((M : ℝ) - 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  calc (1 : ℝ) / 2 ≤ ∏ p ∈ Icc 3 M, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by rw [htele]; exact hhalf
    _ = (∏ p ∈ Icc 3 M \ T, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
          ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) := hsplit.symm
    _ ≤ 1 * ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by gcongr
    _ = _ := one_mul _

/-- Every finite partial product of `𝔖(n)` for even `n` that contains the factor at `2` is
at least `1`. -/
theorem partial_ge_one {n : ℕ} (hn : Even n) (S : Finset {p : ℕ // p.Prime})
    (h2 : (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ S) : 1 ≤ ∏ p ∈ S, singF n p := by
  set two : {p : ℕ // p.Prime} := ⟨2, Nat.prime_two⟩
  rw [← Finset.mul_prod_erase S _ h2]
  have hf2 : singF n two = 2 := by
    unfold singF
    rw [if_pos (even_iff_two_dvd.1 hn)]; norm_num
  rw [hf2]
  set S' := S.erase two
  have hS' : ∀ p ∈ S', 3 ≤ p.1 := by
    intro p hp
    have hne : p ≠ two := Finset.ne_of_mem_erase hp
    have h2le := p.2.two_le
    by_contra h
    apply hne
    apply Subtype.ext
    show p.1 = 2
    omega
  have hlow : ∀ p ∈ S', 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ singF n p := by
    intro p hp
    unfold singF
    split_ifs
    · have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hS' p hp
      have : 0 < 1 / ((p.1 : ℝ) - 1) := one_div_pos.2 (by linarith)
      have : 0 < 1 / ((p.1 : ℝ) - 1) ^ 2 := one_div_pos.2 (by nlinarith)
      linarith
    · exact le_rfl
  have hnn : ∀ p ∈ S', 0 ≤ 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 := by
    intro p hp
    have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hS' p hp
    have h4 : (0 : ℝ) < ((p.1 : ℝ) - 1) ^ 2 := by nlinarith
    have h5 : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by rw [div_le_one h4]; nlinarith
    linarith
  have hmono := Finset.prod_le_prod₀ hnn hlow
  have hmap : ∏ p ∈ S', (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) =
      ∏ p ∈ S'.map (Function.Embedding.subtype _), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [Finset.prod_map]; rfl
  have hhalf := prod_ge_half (S'.map (Function.Embedding.subtype _)) (by
    intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hS' q hq)
  rw [← hmap] at hhalf
  linarith

/-- **`𝔖(n) ≥ 1` for every even `n ≠ 0`.** -/
theorem one_le_sing {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) : 1 ≤ Sing n := by
  rw [sing_eq]
  have hprod := (sing_multipliable hn0).hasProd
  apply ge_of_tendsto hprod
  filter_upwards [Filter.eventually_ge_atTop {(⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime})}] with S hS
  exact partial_ge_one hn S (hS (Finset.mem_singleton_self _))

end LeanLab.Perelli1996.B

