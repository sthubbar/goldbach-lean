module

public import LeanLab.DensityGoldbach.AlsetriShaoModulus
public import LeanLab.DensityGoldbach.PrimesAP

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5907, paper P0047.

# Alsetri-Shao, arXiv 2405.18576, Theorem 1.1: density 1 - ε is not enough for binary Goldbach

Paper, Theorem 1.1: for any ε > 0 there exists a subset A of the primes with relative lower density
greater than 1 - ε such that a positive proportion of the even positive integers cannot be written as
a sum of two primes in A.

Proof here, the construction behind the paper's sharpness remarks: take an odd squarefree m with
∏_{p ∣ m} (p-2) ≤ (ε/2) φ(m), `AlsetriShaoModulus.exists_modulus`, and the set S of units x mod m
such that 1 - x is not a unit, or is a unit with val x < val (1 - x). Then S + S misses 1 mod m, and S
loses at most the ∏ (p-2) units of `Xset m 1`, `card_X_one_le`. A is the primes in the classes of S;
its relative density is at least |S|/φ(m) times 1 - η by the prime number theorem in progressions,
`PrimesAP.pi_ap_lower`, from the lab's Siegel-Walfisz; and no even n ≡ m + 1 mod 2m is in A + A.
No cited input. Binary Goldbach is OPEN; this shows that density alone, without control in every
residue class, cannot give it.
-/

@[expose] public section

namespace LeanLab.DensityGoldbach.AlsetriShaoThm11

open Finset LeanLab.DensityGoldbach.AlsetriShaoLocal

/-- Units `x` with `1 - x` not a unit, or with `val x < val (1 - x)`: one of each pair `x, 1 - x`. -/
def Sset (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  univ.filter (fun x => IsUnit x ∧ (¬ IsUnit (1 - x) ∨ x.val < (1 - x).val))

lemma S_no_sum (m : ℕ) [NeZero m] {x y : ZMod m} (hx : x ∈ Sset m) (hy : y ∈ Sset m) :
    x + y ≠ 1 := by
  intro h
  simp only [Sset, mem_filter, mem_univ, true_and] at hx hy
  have hy' : y = 1 - x := by rw [← h]; ring
  have hx' : x = 1 - y := by rw [← h]; ring
  have h1 : x.val < y.val := by
    rcases hx.2 with h2 | h2
    · exact absurd (hy' ▸ hy.1) h2
    · rwa [← hy'] at h2
  have h2 : y.val < x.val := by
    rcases hy.2 with h3 | h3
    · exact absurd (hx' ▸ hx.1) h3
    · rwa [← hx'] at h3
  omega

lemma card_U_le (m : ℕ) [NeZero m] : (U m).card ≤ (Sset m).card + (Xset m 1).card := by
  refine le_trans (card_le_card fun x hx => ?_) (card_union_le _ _)
  simp only [U, mem_filter, mem_univ, true_and] at hx
  rw [mem_union]
  by_cases h : IsUnit (1 - x)
  · by_cases hlt : x.val < (1 - x).val
    · left; simp [Sset, hx, hlt]
    · right; simp [Xset, hx, h]
  · left; simp [Sset, hx, h]

open Classical in
/-- **Alsetri-Shao, Theorem 1.1.** For every `ε > 0` there is a set `A` of primes whose relative
lower density in the primes exceeds `1 - ε`, written as a lower bound `δ π(N) ≤ |A ∩ [0, N]|` for
all large `N` with `δ > 1 - ε`, while a positive proportion of even numbers, at least `c N` of those up
to `N`, are not `p + q` with `p, q ∈ A`. -/
theorem theorem1_1 : ∀ ε : ℝ, 0 < ε → ∃ A : Set ℕ, (∀ p ∈ A, p.Prime) ∧
    (∃ δ : ℝ, 1 - ε < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      δ * (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤
        (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.range (N + 1)).filter
        (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q)).card : ℝ)) := by
  intro ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨m, hm0, hmodd, hsq, hdecay⟩ := exists_modulus (ε' / 2) (by positivity)
  haveI : NeZero m := ⟨hm0.ne'⟩
  set S := Sset m with hSdef
  set A : Set ℕ := {p | p.Prime ∧ ((p : ZMod m) ∈ S)} with hAdef
  have hφ : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm0
  -- |S| ≥ (1 - ε'/2) φ(m)
  have hS : (1 - ε' / 2) * (Nat.totient m : ℝ) ≤ (S.card : ℝ) := by
    have h1 := card_U_le m
    rw [card_U] at h1
    have h2 := card_X_one_le m hm0 hsq
    have h3 : (Nat.totient m : ℝ) ≤ (S.card : ℝ) + ((Xset m 1).card : ℝ) := by exact_mod_cast h1
    have h4 : ((Xset m 1).card : ℝ) ≤ ((∏ p ∈ m.primeFactors, (p - 2) : ℕ) : ℝ) := by
      exact_mod_cast h2
    nlinarith
  refine ⟨A, fun p hp => hp.1, ?_, ?_⟩
  · -- density
    set η := ε' / 4 with hη
    have hη0 : 0 < η := by positivity
    have hev : ∀ x ∈ S, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (1 - η) / (Nat.totient m : ℝ) * (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤
          (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % m = x.val % m)).card : ℝ) := by
      intro x hx
      simp only [hSdef, Sset, mem_filter, mem_univ, true_and] at hx
      have hcop : Nat.Coprime x.val m := by
        have := hx.1
        rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at this
        exact this
      exact LeanLab.DensityGoldbach.pi_ap_lower m x.val hm0 hcop η hη0
    choose! Nf hNf using hev
    refine ⟨(1 - η) * S.card / Nat.totient m, ?_, S.sup Nf, fun N hN => ?_⟩
    · have : (1 - ε' / 2) * (1 - η) ≤ (1 - η) * S.card / Nat.totient m := by
        rw [le_div_iff₀ hφ]
        have h5 : 0 ≤ 1 - η := by rw [hη]; linarith
        nlinarith
      have : 1 - ε' < (1 - ε' / 2) * (1 - η) := by rw [hη]; nlinarith
      linarith
    · -- the count of A splits over the classes of S
      have hsplit : (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) =
          ∑ x ∈ S, (((Finset.range (N + 1)).filter
            (fun p => p.Prime ∧ p % m = x.val % m)).card : ℝ) := by
        rw [card_eq_sum_card_fiberwise (f := fun p : ℕ => (p : ZMod m)) (t := S)]
        · push_cast
          refine sum_congr rfl fun x _ => ?_
          congr 2
          ext p
          simp only [mem_filter, mem_range, hAdef, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨⟨hp, hpp, -⟩, rfl⟩
            exact ⟨hp, hpp, by rw [ZMod.val_natCast, Nat.mod_mod]⟩
          · rintro ⟨hp, hpp, hmod⟩
            have hx : (p : ZMod m) = x := by
              rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_natCast_iff']
              exact hmod
            exact ⟨⟨hp, hpp, by rw [hx]; assumption⟩, hx⟩
        · intro p hp
          rw [Finset.mem_coe, mem_filter] at hp
          exact hp.2.2
      calc (1 - η) * S.card / Nat.totient m * (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ)
          = ∑ x ∈ S, (1 - η) / (Nat.totient m : ℝ) *
              (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) := by
            rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ x ∈ S, (((Finset.range (N + 1)).filter
              (fun p => p.Prime ∧ p % m = x.val % m)).card : ℝ) :=
            sum_le_sum fun x hx => hNf x hx N (le_trans (le_sup hx) hN)
        _ = _ := by convert hsplit.symm
  · -- exceptions: n ≡ m + 1 mod 2m
    refine ⟨1 / (4 * m), by positivity, 6 * m + 2, fun N hN => ?_⟩
    set K := (N - (m + 1)) / (2 * m) with hK
    have himg : ((Finset.range K).image (fun k => 2 * m * k + (m + 1))) ⊆
        (Finset.range (N + 1)).filter (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q) := by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
      rw [mem_range] at hk
      rw [mem_filter, mem_range]
      refine ⟨?_, ?_, ?_⟩
      · have : 2 * m * k ≤ N - (m + 1) := by
          have := Nat.mul_le_of_le_div _ _ _ (show k ≤ (N - (m + 1)) / (2 * m) by omega)
          linarith [this]
        omega
      · obtain ⟨j, hj⟩ := hmodd
        exact ⟨m * k + j + 1, by rw [hj]; ring⟩
      · rintro ⟨p, hp, q, hq, hpq⟩
        simp only [hAdef, Set.mem_ofPred_eq] at hp hq
        apply S_no_sum m hp.2 hq.2
        have : ((2 * m * k + (m + 1) : ℕ) : ZMod m) = 1 := by
          push_cast; rw [ZMod.natCast_self]; ring
        rw [← this, hpq]; push_cast; ring
    have hcard : (K : ℝ) ≤ (((Finset.range (N + 1)).filter
        (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q)).card : ℝ) := by
      have := card_le_card himg
      rw [card_image_of_injective _ (fun a b h => by
        have hm' : 0 < 2 * m := by omega
        exact Nat.eq_of_mul_eq_mul_left hm' (by omega)), card_range] at this
      exact_mod_cast this
    refine le_trans ?_ hcard
    -- K ≥ (N - m - 1)/(2m) - 1 ≥ N/(4m)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hKr : ((N - (m + 1) : ℕ) : ℝ) / (2 * m) - 1 ≤ (K : ℝ) := by
      have h := Nat.lt_div_mul_add (show 0 < 2 * m by omega) (a := N - (m + 1))
      have : ((N - (m + 1) : ℕ) : ℝ) < (K : ℝ) * (2 * m) + 2 * m := by exact_mod_cast h
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      linarith
    have hNm : ((N - (m + 1) : ℕ) : ℝ) = (N : ℝ) - m - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hNm] at hKr
    have hN' : (6 * (m : ℝ) + 2) ≤ N := by exact_mod_cast hN
    refine le_trans ?_ hKr
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div,
      mul_div_assoc]
    rw [show 4 * (m : ℝ) / (2 * m) = 2 by field_simp; ring]
    nlinarith

end LeanLab.DensityGoldbach.AlsetriShaoThm11

