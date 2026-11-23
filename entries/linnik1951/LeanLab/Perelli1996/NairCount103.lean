module

public import LeanLab.Perelli1996.NairExtract103
public import LeanLab.Perelli1996.NairSpacing103
public import LeanLab.Perelli1996.NairRoots103
public import LeanLab.Perelli1996.NairDivSum103
public import LeanLab.Perelli1996.NairPrep103

/-!
P0083 Perelli 1996, page 481 between equations 3 and 4.

This file contains the standard counting argument of van der Corput 1939 and Landreau 1989 for
power moments of the divisor function over polynomial values in short intervals. `count_div`
counts the integers of an interval at which `d₁ ^ (k (k + 1)) * d₂` divides `F`, by splitting into
root classes mod the squarefree `d₂` and using the spacing bound in each class. `tau_pow_sum`
bounds the sum of `tau(F(n)) ^ e` over an interval by the interval length plus a cutoff `D`, times
a fixed power of `1 + log D`, through divisor extraction and the hyperbola double sum.
It replaces the sieve input cited from Nair 1992.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open Polynomial

namespace LeanLab.Perelli1996.Nair103

theorem count_div (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (hprim : F.IsPrimitive) (d₁ d₂ : ℕ)
    (hd₁ : 0 < d₁) (hcop : Nat.Coprime d₁ d₂) (hsq : Squarefree d₂) (lo hi : ℕ) :
    ((Finset.Icc lo hi).filter (fun n : ℕ =>
        ((d₁ ^ (F.natDegree * (F.natDegree + 1)) * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ))).card ≤
      F.natDegree ^ (d₂.primeFactors.card + 1) *
        (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1) := by
  classical
  have hd₂ : 0 < d₂ := Nat.pos_of_ne_zero hsq.ne_zero
  have hsub : (Finset.Icc lo hi).filter (fun n : ℕ =>
        ((d₁ ^ (F.natDegree * (F.natDegree + 1)) * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ)) ⊆
      ((Finset.range d₂).filter (fun b : ℕ => (d₂ : ℤ) ∣ F.eval (b : ℤ))).biUnion
        (fun b => (Finset.Icc lo hi).filter (fun n : ℕ => n % d₂ = b ∧
          ((d₁ ^ (F.natDegree * (F.natDegree + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ))) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have h1 : ((d₁ ^ (F.natDegree * (F.natDegree + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ) :=
      dvd_trans (by rw [Nat.cast_mul]; exact dvd_mul_right _ _) hn.2
    have h2 : (d₂ : ℤ) ∣ F.eval (n : ℤ) :=
      dvd_trans (by rw [Nat.cast_mul]; exact dvd_mul_left _ _) hn.2
    rw [Finset.mem_biUnion]
    refine ⟨n % d₂, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt _ hd₂, eval_mod_dvd F d₂ n h2⟩
    · rw [Finset.mem_filter]
      exact ⟨hn.1, rfl, h1⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ (Finset.range d₂).filter (fun b : ℕ => (d₂ : ℤ) ∣ F.eval (b : ℤ)),
          ((Finset.Icc lo hi).filter (fun n : ℕ => n % d₂ = b ∧
            ((d₁ ^ (F.natDegree * (F.natDegree + 1)) : ℕ) : ℤ) ∣ F.eval (n : ℤ))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ (Finset.range d₂).filter (fun b : ℕ => (d₂ : ℤ) ∣ F.eval (b : ℤ)),
          F.natDegree * (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1) :=
        Finset.sum_le_sum (fun b _ => count_class F hk d₁ d₂ hd₁ hd₂ hcop b lo hi)
    _ = ((Finset.range d₂).filter (fun b : ℕ => (d₂ : ℤ) ∣ F.eval (b : ℤ))).card *
          (F.natDegree * (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ F.natDegree ^ d₂.primeFactors.card *
          (F.natDegree * (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1)) :=
        Nat.mul_le_mul_right _ (roots_squarefree F hprim d₂ hsq)
    _ = _ := by rw [pow_succ, mul_assoc]

/-- A term of a nonnegative double sum is at most the double sum. -/
theorem single_le_double (s : Finset ℕ) (t : ℕ → Finset ℕ) (g : ℕ → ℕ → ℝ)
    (hg : ∀ a b, 0 ≤ g a b) (a b : ℕ) (ha : a ∈ s) (hb : b ∈ t a) :
    g a b ≤ ∑ x ∈ s, ∑ y ∈ t x, g x y :=
  (Finset.single_le_sum (f := fun y => g a y) (fun y _ => hg a y) hb).trans
    (Finset.single_le_sum (f := fun x => ∑ y ∈ t x, g x y)
      (fun x _ => Finset.sum_nonneg (fun y _ => hg x y)) ha)

/-- Divisor extraction applied to a positive polynomial value below `D ^ r`. -/
theorem extract_pair (F : ℤ[X]) (K r : ℕ) (hr : 2 ≤ r) (hKr : K ≤ r) (e D n : ℕ)
    (hn : F.eval (n : ℤ) ≤ (D : ℤ) ^ r) (hpos : 0 < (F.eval (n : ℤ)).toNat) :
    ∃ d₁ d₂ : ℕ, 1 ≤ d₁ ∧ 1 ≤ d₂ ∧ d₁ * d₂ ≤ D ∧ Nat.Coprime d₁ d₂ ∧ Squarefree d₂ ∧
      ((d₁ ^ K * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ) ∧
      (((F.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ e ≤ (r : ℝ) ^ (r * e) *
        ((d₁.divisors.card : ℝ) ^ (e * r ^ 2) * (d₂.divisors.card : ℝ) ^ (e * r ^ 2)) := by
  obtain ⟨d₁, d₂, hcop, hsq, hdvd, hle, htau⟩ := divisor_extract r hr _ hpos
  have hmF : (((F.eval (n : ℤ)).toNat : ℕ) : ℤ) = F.eval (n : ℤ) := by omega
  have hd0 : d₁ ^ r * d₂ ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact (Nat.pos_iff_ne_zero.mp hpos) (Nat.eq_zero_of_zero_dvd hdvd)
  have hd₁ : 1 ≤ d₁ := by
    rcases Nat.eq_zero_or_pos d₁ with h | h
    · exfalso
      apply hd0
      rw [h, zero_pow (by omega), zero_mul]
    · exact h
  have hd₂ : 1 ≤ d₂ := by
    rcases Nat.eq_zero_or_pos d₂ with h | h
    · exfalso
      apply hd0
      rw [h, mul_zero]
    · exact h
  have hmD : (F.eval (n : ℤ)).toNat ≤ D ^ r := by
    have h : (((F.eval (n : ℤ)).toNat : ℕ) : ℤ) ≤ ((D ^ r : ℕ) : ℤ) := by
      rw [hmF, Nat.cast_pow]
      exact hn
    exact Int.ofNat_le.mp h
  have hprod : d₁ * d₂ ≤ D := by
    by_contra h
    have h2 := Nat.pow_lt_pow_left (not_le.mp h) (show r ≠ 0 by omega)
    exact absurd (hle.trans hmD) (not_le.mpr h2)
  have hdvdZ : ((d₁ ^ K * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ) := by
    rw [← hmF]
    exact Int.natCast_dvd_natCast.mpr
      (dvd_trans (Nat.mul_dvd_mul_right (pow_dvd_pow d₁ hKr) d₂) hdvd)
  have hnat : (F.eval (n : ℤ)).toNat.divisors.card ^ e ≤ r ^ (r * e) *
      (d₁.divisors.card ^ (e * r ^ 2) * d₂.divisors.card ^ (e * r ^ 2)) := by
    calc (F.eval (n : ℤ)).toNat.divisors.card ^ e
        ≤ (r ^ r * (d₁ * d₂).divisors.card ^ (r ^ 2)) ^ e := Nat.pow_le_pow_left htau e
      _ ≤ (r ^ r * (d₁.divisors.card * d₂.divisors.card) ^ (r ^ 2)) ^ e :=
          Nat.pow_le_pow_left
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (tau_mul_le d₁ d₂) _)) e
      _ = r ^ (r * e) *
          (d₁.divisors.card ^ (e * r ^ 2) * d₂.divisors.card ^ (e * r ^ 2)) := by ring
  refine ⟨d₁, d₂, hd₁, hd₂, hprod, hcop, hsq, hdvdZ, ?_⟩
  exact_mod_cast hnat

/-- For a fixed pair, the weighted count over the interval. -/
theorem pair_count (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (hprim : F.IsPrimitive) (G d₁ d₂ : ℕ)
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (lo hi : ℕ) :
    ∑ n ∈ Finset.Icc lo hi,
      (if Nat.Coprime d₁ d₂ ∧ Squarefree d₂ ∧
          ((d₁ ^ (F.natDegree * (F.natDegree + 1)) * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ) then
        (d₁.divisors.card : ℝ) ^ G * (d₂.divisors.card : ℝ) ^ G else 0) ≤
    (F.natDegree : ℝ) * ((d₁.divisors.card : ℝ) ^ (G + F.natDegree) *
      (d₂.divisors.card : ℝ) ^ (G + F.natDegree) *
      ((F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) / ((d₁ : ℝ) * d₂) + 1)) := by
  have ht1 : (1 : ℝ) ≤ (d₁.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  have ht2 : (1 : ℝ) ≤ (d₂.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  have hY : (0 : ℝ) ≤
      (F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) / ((d₁ : ℝ) * d₂) + 1 := by positivity
  by_cases hc : Nat.Coprime d₁ d₂ ∧ Squarefree d₂
  · have hcnt := count_div F hk hprim d₁ d₂ hd₁ hc.1 hc.2 lo hi
    obtain ⟨c, hcdef⟩ : ∃ c : ℕ, c = ((Finset.Icc lo hi).filter (fun n : ℕ =>
        ((d₁ ^ (F.natDegree * (F.natDegree + 1)) * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ))).card :=
      ⟨_, rfl⟩
    rw [← hcdef] at hcnt
    have hsum : ∑ n ∈ Finset.Icc lo hi,
        (if Nat.Coprime d₁ d₂ ∧ Squarefree d₂ ∧
            ((d₁ ^ (F.natDegree * (F.natDegree + 1)) * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ) then
          (d₁.divisors.card : ℝ) ^ G * (d₂.divisors.card : ℝ) ^ G else 0) =
        (c : ℝ) * ((d₁.divisors.card : ℝ) ^ G * (d₂.divisors.card : ℝ) ^ G) := by
      rw [hcdef, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hP : ((d₁ ^ (F.natDegree * (F.natDegree + 1)) * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ)
      · rw [if_pos ⟨hc.1, hc.2, hP⟩, if_pos hP]
      · rw [if_neg (fun h => hP h.2.2), if_neg hP]
    have hpow : F.natDegree ^ (d₂.primeFactors.card + 1) ≤
        F.natDegree * d₂.divisors.card ^ F.natDegree := by
      rw [pow_succ, mul_comm]
      apply Nat.mul_le_mul_left
      calc F.natDegree ^ d₂.primeFactors.card
          ≤ (2 ^ F.natDegree) ^ d₂.primeFactors.card :=
            Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
        _ = (2 ^ d₂.primeFactors.card) ^ F.natDegree := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ d₂.divisors.card ^ F.natDegree :=
            Nat.pow_le_pow_left (two_pow_omega_le_tau d₂ (by omega)) _
    have hX : ((F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1 : ℕ) : ℝ) ≤
        (F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) / ((d₁ : ℝ) * d₂) + 1 := by
      have h := Nat.cast_div_le (α := ℝ) (m := F.leadingCoeff.natAbs * (hi - lo)) (n := d₁ * d₂)
      rw [Nat.cast_mul, Nat.cast_mul] at h
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    have hcR : (c : ℝ) ≤ (F.natDegree : ℝ) * (d₂.divisors.card : ℝ) ^ F.natDegree *
        ((F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) / ((d₁ : ℝ) * d₂) + 1) := by
      calc (c : ℝ) ≤ ((F.natDegree ^ (d₂.primeFactors.card + 1) *
              (F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1) : ℕ) : ℝ) :=
            Nat.cast_le.mpr hcnt
        _ = ((F.natDegree ^ (d₂.primeFactors.card + 1) : ℕ) : ℝ) *
              ((F.leadingCoeff.natAbs * (hi - lo) / (d₁ * d₂) + 1 : ℕ) : ℝ) := Nat.cast_mul _ _
        _ ≤ ((F.natDegree * d₂.divisors.card ^ F.natDegree : ℕ) : ℝ) *
              ((F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) / ((d₁ : ℝ) * d₂) + 1) :=
            mul_le_mul (Nat.cast_le.mpr hpow) hX (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = _ := by rw [Nat.cast_mul, Nat.cast_pow]
    rw [hsum]
    calc (c : ℝ) * ((d₁.divisors.card : ℝ) ^ G * (d₂.divisors.card : ℝ) ^ G)
        ≤ ((F.natDegree : ℝ) * (d₂.divisors.card : ℝ) ^ F.natDegree *
            ((F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) / ((d₁ : ℝ) * d₂) + 1)) *
            ((d₁.divisors.card : ℝ) ^ G * (d₂.divisors.card : ℝ) ^ G) :=
          mul_le_mul_of_nonneg_right hcR (by positivity)
      _ = (F.natDegree : ℝ) * ((d₁.divisors.card : ℝ) ^ G *
            (d₂.divisors.card : ℝ) ^ (G + F.natDegree) *
            ((F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) / ((d₁ : ℝ) * d₂) + 1)) := by
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_right _ hY
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_right₀ ht1 (Nat.le_add_right _ _)
  · refine le_of_eq_of_le
      (Finset.sum_eq_zero (fun n _ => if_neg (fun h => hc ⟨h.1, h.2.1⟩))) ?_
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) hY)

/-- The divisor power moment with a general cutoff exponent `r`. -/
theorem tau_pow_sum_core (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (hprim : F.IsPrimitive) (e : ℕ)
    (he : 1 ≤ e) (r : ℕ) (hr : 2 ≤ r) (hKr : F.natDegree * (F.natDegree + 1) ≤ r) :
    ∃ (M : ℕ) (C : ℝ), 0 < C ∧ ∀ lo hi D : ℕ, 1 ≤ D →
      (∀ n ∈ Finset.Icc lo hi, F.eval (n : ℤ) ≤ (D : ℤ) ^ r) →
      ∑ n ∈ Finset.Icc lo hi, (((F.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ e ≤
        C * (((hi - lo : ℕ) : ℝ) + D) * (1 + Real.log D) ^ M := by
  obtain ⟨M, hM⟩ := tau_pair_sum (e * r ^ 2 + F.natDegree)
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hk0 : (0 : ℝ) < (F.natDegree : ℝ) := by exact_mod_cast hk
  have ha0 : (0 : ℝ) ≤ (F.leadingCoeff.natAbs : ℝ) := Nat.cast_nonneg _
  have hrk : (0 : ℝ) ≤ (r : ℝ) ^ (r * e) * (F.natDegree : ℝ) :=
    mul_nonneg (pow_nonneg hr0.le _) hk0.le
  refine ⟨M, (r : ℝ) ^ (r * e) * (F.natDegree : ℝ) * ((F.leadingCoeff.natAbs : ℝ) + 1),
    mul_pos (mul_pos (pow_pos hr0 _) hk0) (by linarith), ?_⟩
  intro lo hi D _ hF
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (F.leadingCoeff.natAbs : ℝ) * ((hi - lo : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hh0 : (0 : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ A := by rw [hAdef]; exact mul_nonneg ha0 hh0
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ → ℕ → ℝ, g = fun (n : ℕ) (d₁ d₂ : ℕ) =>
      if Nat.Coprime d₁ d₂ ∧ Squarefree d₂ ∧
          ((d₁ ^ (F.natDegree * (F.natDegree + 1)) * d₂ : ℕ) : ℤ) ∣ F.eval (n : ℤ) then
        (d₁.divisors.card : ℝ) ^ (e * r ^ 2) * (d₂.divisors.card : ℝ) ^ (e * r ^ 2) else 0 :=
    ⟨_, rfl⟩
  have hgnn : ∀ n d₁ d₂, 0 ≤ g n d₁ d₂ := by
    intro n d₁ d₂
    rw [hg]
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  have hpc : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → 1 ≤ d₂ →
      ∑ n ∈ Finset.Icc lo hi, g n d₁ d₂ ≤
        (F.natDegree : ℝ) * ((d₁.divisors.card : ℝ) ^ (e * r ^ 2 + F.natDegree) *
          (d₂.divisors.card : ℝ) ^ (e * r ^ 2 + F.natDegree) * (A / ((d₁ : ℝ) * d₂) + 1)) := by
    intro d₁ d₂ h1 h2
    rw [hg, hAdef]
    exact pair_count F hk hprim (e * r ^ 2) d₁ d₂ h1 h2 lo hi
  have h1 : ∀ n ∈ Finset.Icc lo hi,
      (((F.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ e ≤ (r : ℝ) ^ (r * e) *
        ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
          g n d₁ d₂ := by
    intro n hn
    rcases Nat.eq_zero_or_pos (F.eval (n : ℤ)).toNat with h0 | hpos
    · rw [h0, Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, zero_pow (by omega)]
      exact mul_nonneg (pow_nonneg hr0.le _)
        (Finset.sum_nonneg (fun d₁ _ => Finset.sum_nonneg (fun d₂ _ => hgnn n d₁ d₂)))
    · obtain ⟨d₁, d₂, hd₁, hd₂, hprod, hcop, hsq, hdvd, hle⟩ :=
        extract_pair F (F.natDegree * (F.natDegree + 1)) r hr hKr e D n (hF n hn) hpos
      have hmem1 : d₁ ∈ Finset.Icc 1 D :=
        Finset.mem_Icc.mpr ⟨hd₁, le_trans (Nat.le_mul_of_pos_right d₁ hd₂) hprod⟩
      have hmem2 : d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D) :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hd₂, le_trans (Nat.le_mul_of_pos_left d₂ hd₁) hprod⟩, hprod⟩
      have hs := single_le_double (Finset.Icc 1 D)
        (fun d₁ => (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D)) (g n) (hgnn n)
        d₁ d₂ hmem1 hmem2
      have hgv : g n d₁ d₂ =
          (d₁.divisors.card : ℝ) ^ (e * r ^ 2) * (d₂.divisors.card : ℝ) ^ (e * r ^ 2) := by
        rw [hg]
        exact if_pos ⟨hcop, hsq, hdvd⟩
      exact hle.trans (mul_le_mul_of_nonneg_left (hgv.symm.le.trans hs) (pow_nonneg hr0.le _))
  have hL : (0 : ℝ) ≤ (1 + Real.log D) ^ M :=
    pow_nonneg (by have := Real.log_natCast_nonneg D; linarith) M
  have hAD : A + D ≤ ((F.leadingCoeff.natAbs : ℝ) + 1) * (((hi - lo : ℕ) : ℝ) + D) := by
    rw [hAdef]
    nlinarith [mul_nonneg ha0 hD0]
  calc ∑ n ∈ Finset.Icc lo hi, (((F.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ e
      ≤ ∑ n ∈ Finset.Icc lo hi, (r : ℝ) ^ (r * e) *
          ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
            g n d₁ d₂ := Finset.sum_le_sum h1
    _ = (r : ℝ) ^ (r * e) *
          ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
            ∑ n ∈ Finset.Icc lo hi, g n d₁ d₂ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl (fun d₁ _ => Finset.sum_comm)
    _ ≤ (r : ℝ) ^ (r * e) *
          ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
            (F.natDegree : ℝ) * ((d₁.divisors.card : ℝ) ^ (e * r ^ 2 + F.natDegree) *
              (d₂.divisors.card : ℝ) ^ (e * r ^ 2 + F.natDegree) *
              (A / ((d₁ : ℝ) * d₂) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0.le _)
        apply Finset.sum_le_sum
        intro d₁ hd₁
        apply Finset.sum_le_sum
        intro d₂ hd₂
        exact hpc d₁ d₂ (Finset.mem_Icc.mp hd₁).1
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₂).1).1
    _ = (r : ℝ) ^ (r * e) * (F.natDegree : ℝ) *
          ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
            ((d₁.divisors.card : ℝ) ^ (e * r ^ 2 + F.natDegree) *
              (d₂.divisors.card : ℝ) ^ (e * r ^ 2 + F.natDegree) *
              (A / ((d₁ : ℝ) * d₂) + 1)) := by
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d₁ _
        rw [Finset.mul_sum]
    _ ≤ (r : ℝ) ^ (r * e) * (F.natDegree : ℝ) * ((A + D) * (1 + Real.log D) ^ M) :=
        mul_le_mul_of_nonneg_left (hM D A hA) hrk
    _ ≤ (r : ℝ) ^ (r * e) * (F.natDegree : ℝ) *
          ((((F.leadingCoeff.natAbs : ℝ) + 1) * (((hi - lo : ℕ) : ℝ) + D)) *
            (1 + Real.log D) ^ M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAD hL) hrk
    _ = (r : ℝ) ^ (r * e) * (F.natDegree : ℝ) * ((F.leadingCoeff.natAbs : ℝ) + 1) *
          (((hi - lo : ℕ) : ℝ) + D) * (1 + Real.log D) ^ M := by ring

theorem tau_pow_sum (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (hprim : F.IsPrimitive) (e : ℕ) (he : 1 ≤ e) :
    ∃ (M : ℕ) (C : ℝ), 0 < C ∧ ∀ lo hi D : ℕ, 1 ≤ D →
      (∀ n ∈ Finset.Icc lo hi, F.eval (n : ℤ) ≤ (D : ℤ) ^ (4 * (F.natDegree * (F.natDegree + 1)))) →
      ∑ n ∈ Finset.Icc lo hi, (((F.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ e ≤
        C * (((hi - lo : ℕ) : ℝ) + D) * (1 + Real.log D) ^ M := by
  have hK1 : 1 ≤ F.natDegree * (F.natDegree + 1) := Nat.mul_pos hk (Nat.succ_pos _)
  exact tau_pow_sum_core F hk hprim e he (4 * (F.natDegree * (F.natDegree + 1)))
    (le_trans (by norm_num) (Nat.mul_le_mul_left 4 hK1))
    (Nat.le_mul_of_pos_left _ (by norm_num))

end LeanLab.Perelli1996.Nair103
