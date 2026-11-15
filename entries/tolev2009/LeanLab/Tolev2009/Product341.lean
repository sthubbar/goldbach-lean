module

public import LeanLab.Tolev2009.Decomp341a

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 84 to 85 displays 57 to 61.
Finite lcm fibers and product fibers supply the divisor coefficient.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Product341
open LeanLab.Tolev2009.Decomp310b

/-- The lcm fiber reduction in Tolev 1999 displays 57 and 59.
A nonnegative scalar function can be carried through the divisor majorant. -/
theorem lcm_sum_bound (K : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0≤F n) :
    ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, F (Nat.lcm k₁ k₂) ≤
      ∑ h ∈ Icc 1 (K*K), (h.divisors.card:ℝ)^4*F h := by
  have hm : ∀ p ∈ Icc 1 K ×ˢ Icc 1 K, Nat.lcm p.1 p.2 ∈ Icc 1 (K*K) := by
    intro p hp
    obtain ⟨hp₁,hp₂⟩ := mem_product.mp hp
    obtain ⟨h₁,h₁K⟩ := mem_Icc.mp hp₁
    obtain ⟨h₂,h₂K⟩ := mem_Icc.mp hp₂
    exact mem_Icc.mpr ⟨Nat.lcm_pos (by omega) (by omega),
      (Nat.lcm_le_mul h₁ h₂).trans (Nat.mul_le_mul h₁K h₂K)⟩
  calc
    _ ≤ ∑ p ∈ Icc 1 K ×ˢ Icc 1 K,
        (p.1.divisors.card:ℝ)*p.2.divisors.card*F (Nat.lcm p.1 p.2) := by
      rw [sum_product]
      apply sum_le_sum
      intro k₁ hk₁
      apply sum_le_sum
      intro k₂ hk₂
      have hc₁ : (1:ℝ)≤k₁.divisors.card := by
        exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp hk₁).1; omega))
      have hc₂ : (1:ℝ)≤k₂.divisors.card := by
        exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp hk₂).1; omega))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:ℝ)≤(k₁.divisors.card:ℝ)*k₂.divisors.card by nlinarith) (hF _)
    _ = ∑ h ∈ Icc 1 (K*K),
        (∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2=h),
          (p.1.divisors.card:ℝ)*p.2.divisors.card)*F h := by
      rw [← sum_fiberwise_of_maps_to hm]
      apply sum_congr rfl
      intro h hh
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ _ := sum_le_sum (fun h hh => mul_le_mul_of_nonneg_right (lcm_fiber_divisor_bound h K) (hF h))

/-- The product regrouping in Tolev 1999 page 85 between displays 60 and 61.
A fourth divisor weight on one factor produces a fifth divisor weight on the product. -/
theorem divisor_product_bound (U V : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0≤F n) :
    ∑ h ∈ Icc 1 V, (h.divisors.card:ℝ)^4*∑ r ∈ Icc 1 U, F (h*r) ≤
      ∑ n ∈ Icc 1 (U*V), (n.divisors.card:ℝ)^5*F n := by
  classical
  have hm : ∀ p ∈ Icc 1 V ×ˢ Icc 1 U, p.1*p.2 ∈ Icc 1 (U*V) := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    obtain ⟨h₁p,h₁V⟩ := mem_Icc.mp h₁
    obtain ⟨h₂p,h₂U⟩ := mem_Icc.mp h₂
    exact mem_Icc.mpr ⟨by nlinarith,by nlinarith⟩
  have hf (n : ℕ) (hn : n ∈ Icc 1 (U*V)) :
      (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n),
        (p.1.divisors.card:ℝ)^4) ≤ (n.divisors.card:ℝ)^5 := by
    let s := (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n)
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hi : Set.InjOn (fun p : ℕ × ℕ => p.1) (s : Set (ℕ × ℕ)) := by
      intro p hp q hq he
      have hp' := mem_filter.mp hp
      have hq' := mem_filter.mp hq
      have hp0 : 0<p.1 := (mem_Icc.mp (mem_product.mp hp'.1).1).1
      apply Prod.ext he
      apply Nat.eq_of_mul_eq_mul_left hp0
      simpa only [he] using hp'.2.trans hq'.2.symm
    have hs : s.image Prod.fst ⊆ n.divisors := by
      intro h hh
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hh
      have hp' := (mem_filter.mp hp).2
      exact Nat.mem_divisors.mpr ⟨hp' ▸ dvd_mul_right p.1 p.2,hn0⟩
    calc
      _ = ∑ h ∈ s.image Prod.fst, (h.divisors.card:ℝ)^4 := (sum_image hi).symm
      _ ≤ ∑ h ∈ n.divisors, (h.divisors.card:ℝ)^4 :=
        sum_le_sum_of_subset_of_nonneg hs (fun h hh hnot => by positivity)
      _ ≤ ∑ h ∈ n.divisors, (n.divisors.card:ℝ)^4 := by
        apply sum_le_sum
        intro h hh
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hn0 (Nat.dvd_of_mem_divisors hh))
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  simp_rw [mul_sum]
  rw [← sum_product',← sum_fiberwise_of_maps_to hm]
  apply sum_le_sum
  intro n hn
  have he : (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n),
      (p.1.divisors.card:ℝ)^4*F (p.1*p.2)) =
      (∑ p ∈ (Icc 1 V ×ˢ Icc 1 U).filter (fun p => p.1*p.2=n),
        (p.1.divisors.card:ℝ)^4)*F n := by
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [(mem_filter.mp hp).2]
  rw [he]
  exact mul_le_mul_of_nonneg_right (hf n hn) (hF n)

end LeanLab.Tolev2009.Product341
