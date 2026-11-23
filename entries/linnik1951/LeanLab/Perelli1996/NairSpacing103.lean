module

public import Mathlib

/-!
P0083 Perelli 1996, page 481 between equations 3 and 4.

This file contains the standard spacing argument for polynomial values, in the style of
van der Corput 1939 and Landreau 1989: by the Lagrange formula for the leading coefficient,
`k + 1` integers in one residue class mod `d₂` at which `d₁ ^ (k (k + 1))` divides `F` cannot all
lie in an interval shorter than `d₁ d₂ / |a_k|`. The consequence `count_class` bounds the number
of such integers in an interval. It replaces the sieve input cited from Nair 1992.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open Polynomial

namespace LeanLab.Perelli1996.Nair103

/-- Spacing: `k + 1` points in one class mod `d₂`, with `d₁ ^ (k (k + 1))` dividing `F` at each,
inside `[lo, hi]`, force `d₁ d₂ ≤ |a_k| (hi - lo)`. -/
theorem spacing (F : ℤ[X]) (k : ℕ) (hkeq : F.natDegree = k) (hk : 1 ≤ k) (d₁ d₂ : ℕ)
    (hcop : Nat.Coprime d₁ d₂) (b lo hi : ℕ) (T : Finset ℕ) (hT : T.card = k + 1)
    (hb : ∀ n ∈ T, n % d₂ = b)
    (hdiv : ∀ n ∈ T, ((d₁ ^ (k * (k + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ))
    (hr : ∀ n ∈ T, lo ≤ n ∧ n ≤ hi) :
    d₁ * d₂ ≤ F.leadingCoeff.natAbs * (hi - lo) := by
  classical
  have hF0 : F ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hkeq
    omega
  have hci : Function.Injective (Int.castRingHom ℚ) := fun a b h => by simpa using h
  have hinj : Set.InjOn (fun n : ℕ => (n : ℚ)) (T : Set ℕ) := fun a _ b _ h => by
    exact Nat.cast_injective (R := ℚ) h
  have hdeg : (T.card : WithBot ℕ) = (F.map (Int.castRingHom ℚ)).degree + 1 := by
    rw [degree_map_eq_of_injective hci, degree_eq_natDegree hF0, hkeq, hT]
    rfl
  have hL := Lagrange.leadingCoeff_eq_sum (s := T) (v := fun n : ℕ => (n : ℚ)) hinj
    (P := F.map (Int.castRingHom ℚ)) hdeg
  rw [leadingCoeff_map_of_injective hci] at hL
  have hev : ∀ n : ℕ, (F.map (Int.castRingHom ℚ)).eval (n : ℚ) = ((F.eval (n : ℤ) : ℤ) : ℚ) := by
    intro n
    have := eval_intCast_map (Int.castRingHom ℚ) F (n : ℤ)
    rw [Int.cast_natCast] at this
    exact this
  have hL' : (F.leadingCoeff : ℚ) =
      ∑ i ∈ T, ((F.eval (i : ℤ) : ℤ) : ℚ) / ∏ j ∈ T.erase i, ((i : ℚ) - (j : ℚ)) := by
    have h0 : (Int.castRingHom ℚ) F.leadingCoeff = (F.leadingCoeff : ℚ) := rfl
    rw [← h0, hL]
    exact Finset.sum_congr rfl fun i _ => by rw [hev i]
  -- the integer identity
  have key : F.leadingCoeff * ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ)) =
      ∑ i ∈ T, F.eval (i : ℤ) * ∏ i' ∈ T.erase i, ∏ j ∈ T.erase i', ((i' : ℤ) - (j : ℤ)) := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_sum, hL']
    simp only [Int.cast_mul, Int.cast_prod, Int.cast_sub, Int.cast_natCast]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : (∏ j ∈ T.erase i, ((i : ℚ) - (j : ℚ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (by
        have := (Finset.mem_erase.mp hj).1
        exact_mod_cast this.symm))
    rw [← Finset.mul_prod_erase T (fun i' => ∏ j ∈ T.erase i', ((i' : ℚ) - (j : ℚ))) hi]
    rw [← mul_assoc, div_mul_cancel₀ _ hne]
  have hc : ∀ i ∈ T, (T.erase i).card = k := fun i hi => by
    rw [Finset.card_erase_of_mem hi, hT]; rfl
  -- divisibility by d₁ ^ K
  have h1 : (d₁ : ℤ) ^ (k * (k + 1)) ∣
      F.leadingCoeff * ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ)) := by
    rw [key]
    refine Finset.dvd_sum fun i hi => Dvd.dvd.mul_right ?_ _
    have := hdiv i hi
    rwa [Nat.cast_pow] at this
  -- divisibility by d₂ ^ K
  have hd2ij : ∀ i ∈ T, ∀ j ∈ T, (d₂ : ℤ) ∣ (i : ℤ) - (j : ℤ) := by
    intro i hi j hj
    have hm : j ≡ i [MOD d₂] := (hb j hj).trans (hb i hi).symm
    exact (Int.natCast_modEq_iff.mpr hm).dvd
  have hW : ∀ i ∈ T, (d₂ : ℤ) ^ k ∣ ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ)) := by
    intro i hi
    have : ∏ _j ∈ T.erase i, (d₂ : ℤ) ∣ ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ)) :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun j hj => hd2ij i hi j (Finset.mem_of_mem_erase hj))
    rwa [Finset.prod_const, hc i hi] at this
  have h2 : (d₂ : ℤ) ^ (k * (k + 1)) ∣ ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ)) := by
    have : ∏ _i ∈ T, (d₂ : ℤ) ^ k ∣ ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ)) :=
      Finset.prod_dvd_prod_of_dvd _ _ hW
    rwa [Finset.prod_const, hT, ← pow_mul] at this
  have hcopZ : IsCoprime ((d₁ : ℤ) ^ (k * (k + 1))) ((d₂ : ℤ) ^ (k * (k + 1))) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow
  have hD : (d₁ : ℤ) ^ (k * (k + 1)) * (d₂ : ℤ) ^ (k * (k + 1)) ∣
      F.leadingCoeff * ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ)) :=
    hcopZ.mul_dvd h1 (Dvd.dvd.mul_left h2 _)
  -- nonvanishing
  have hV0 : (∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr (by
        have := (Finset.mem_erase.mp hj).1
        exact_mod_cast this.symm)
  have hlc0 : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  -- size
  have hWabs : ∀ i ∈ T, |∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ))| ≤ (((hi - lo : ℕ) : ℤ)) ^ k := by
    intro i hi'
    rw [Finset.abs_prod]
    calc ∏ j ∈ T.erase i, |(i : ℤ) - (j : ℤ)| ≤ ∏ _j ∈ T.erase i, ((hi - lo : ℕ) : ℤ) :=
          Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j hj => by
            have hi1 := hr i hi'
            have hj1 := hr j (Finset.mem_of_mem_erase hj)
            exact abs_le.mpr ⟨by omega, by omega⟩)
      _ = (((hi - lo : ℕ) : ℤ)) ^ k := by rw [Finset.prod_const, hc i hi']
  have hVabs : |∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ))| ≤
      (((hi - lo : ℕ) : ℤ)) ^ (k * (k + 1)) := by
    rw [Finset.abs_prod]
    calc ∏ i ∈ T, |∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ))|
          ≤ ∏ _i ∈ T, (((hi - lo : ℕ) : ℤ)) ^ k :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hWabs
      _ = (((hi - lo : ℕ) : ℤ)) ^ (k * (k + 1)) := by rw [Finset.prod_const, hT, ← pow_mul]
  have hpos : 0 < |F.leadingCoeff * ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ))| :=
    abs_pos.mpr (mul_ne_zero hlc0 hV0)
  have h3 : (d₁ : ℤ) ^ (k * (k + 1)) * (d₂ : ℤ) ^ (k * (k + 1)) ≤
      |F.leadingCoeff * ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ))| :=
    Int.le_of_dvd hpos ((dvd_abs _ _).mpr hD)
  have h4 : |F.leadingCoeff * ∏ i ∈ T, ∏ j ∈ T.erase i, ((i : ℤ) - (j : ℤ))| ≤
      (F.leadingCoeff.natAbs : ℤ) * (((hi - lo : ℕ) : ℤ)) ^ (k * (k + 1)) := by
    rw [abs_mul, Int.abs_eq_natAbs]
    exact mul_le_mul_of_nonneg_left hVabs (Int.natCast_nonneg _)
  have h5 : d₁ ^ (k * (k + 1)) * d₂ ^ (k * (k + 1)) ≤
      F.leadingCoeff.natAbs * (hi - lo) ^ (k * (k + 1)) := by
    exact_mod_cast h3.trans h4
  have hKpos : k * (k + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h6 : F.leadingCoeff.natAbs ≤ F.leadingCoeff.natAbs ^ (k * (k + 1)) :=
    Nat.le_self_pow hKpos _
  have h7 : (d₁ * d₂) ^ (k * (k + 1)) ≤ (F.leadingCoeff.natAbs * (hi - lo)) ^ (k * (k + 1)) := by
    rw [mul_pow, mul_pow]
    exact h5.trans (Nat.mul_le_mul_right _ h6)
  exact (Nat.pow_le_pow_iff_left hKpos).mp h7

theorem count_class (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcop : Nat.Coprime d₁ d₂) (b lo hi : ℕ) :
    ((Finset.Icc lo hi).filter (fun n : ℕ => n % d₂ = b ∧
        ((d₁ ^ (F.natDegree * (F.natDegree + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ))).card ≤
      F.natDegree * (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1) := by
  classical
  have hD : 0 < d₁ * d₂ := Nat.mul_pos hd₁ hd₂
  set S := (Finset.Icc lo hi).filter (fun n : ℕ => n % d₂ = b ∧
        ((d₁ ^ (F.natDegree * (F.natDegree + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ)) with hS
  have hSmem : ∀ n ∈ S, (lo ≤ n ∧ n ≤ hi) ∧ n % d₂ = b ∧
      ((d₁ ^ (F.natDegree * (F.natDegree + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn
  have hfib : ∀ a ∈ S.image (fun n : ℕ => (n - lo) * F.leadingCoeff.natAbs / (d₁ * d₂)),
      (S.filter (fun x : ℕ => (x - lo) * F.leadingCoeff.natAbs / (d₁ * d₂) = a)).card ≤
        F.natDegree := by
    intro a _
    by_contra hcon
    have hcon' : F.natDegree + 1 ≤
        (S.filter (fun x : ℕ => (x - lo) * F.leadingCoeff.natAbs / (d₁ * d₂) = a)).card := by
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcon'
    have hTne : T.Nonempty := Finset.card_pos.mp (by rw [hTcard]; exact Nat.succ_pos _)
    have hmem : ∀ n ∈ T, ((lo ≤ n ∧ n ≤ hi) ∧ n % d₂ = b ∧
        ((d₁ ^ (F.natDegree * (F.natDegree + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ)) ∧
        (n - lo) * F.leadingCoeff.natAbs / (d₁ * d₂) = a := by
      intro n hn
      have h1 := Finset.mem_filter.mp (hTsub hn)
      exact ⟨hSmem n h1.1, h1.2⟩
    have hsp := spacing F F.natDegree rfl hk d₁ d₂ hcop b (T.min' hTne) (T.max' hTne) T hTcard
      (fun n hn => (hmem n hn).1.2.1) (fun n hn => (hmem n hn).1.2.2)
      (fun n hn => ⟨Finset.min'_le T n hn, Finset.le_max' T n hn⟩)
    have hmin := hmem _ (Finset.min'_mem T hTne)
    have hmax := hmem _ (Finset.max'_mem T hTne)
    have hle : T.min' hTne ≤ T.max' hTne := Finset.min'_le T _ (Finset.max'_mem T hTne)
    obtain ⟨p, hp⟩ : ∃ p, p = T.min' hTne := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = T.max' hTne := ⟨_, rfl⟩
    rw [← hp] at hsp hmin hle
    rw [← hq] at hsp hmax hle
    have hlop : lo ≤ p := hmin.1.1.1
    have e : (q - lo) * F.leadingCoeff.natAbs =
        (p - lo) * F.leadingCoeff.natAbs + F.leadingCoeff.natAbs * (q - p) := by
      have h : q - lo = (p - lo) + (q - p) := by omega
      rw [h, add_mul, mul_comm (q - p)]
    have h8 : ((p - lo) * F.leadingCoeff.natAbs + d₁ * d₂) / (d₁ * d₂) ≤
        (q - lo) * F.leadingCoeff.natAbs / (d₁ * d₂) :=
      Nat.div_le_div_right (by rw [e]; exact Nat.add_le_add_left hsp _)
    rw [Nat.add_div_right _ hD, hmin.2, hmax.2] at h8
    omega
  have himg : S.image (fun n : ℕ => (n - lo) * F.leadingCoeff.natAbs / (d₁ * d₂)) ⊆
      Finset.range (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1) := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    have hn' := hSmem n hn
    rw [Finset.mem_range]
    refine Nat.lt_succ_of_le (Nat.div_le_div_right ?_)
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  calc S.card ≤ F.natDegree *
        (S.image (fun n : ℕ => (n - lo) * F.leadingCoeff.natAbs / (d₁ * d₂))).card :=
        Finset.card_le_mul_card_image S _ hfib
    _ ≤ F.natDegree * (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1) := by
        refine Nat.mul_le_mul_left _ ?_
        have := Finset.card_le_card himg
        rwa [Finset.card_range] at this

end LeanLab.Perelli1996.Nair103
