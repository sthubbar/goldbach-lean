module

public import LeanLab.KumchevLiu2007.Statements

/-!
Kumchev and Liu 2007, Sums of primes and squares of primes in short intervals, arXiv 0801.0130.
Unit U-1534, run 20261026T0004Z-24325, DECOMPOSE. File b: the local conditions behind the sets
H2 and H3 and the singular series facts of Section 3.3, properties iii and iv, split into LEAF
lemmas, plus the Theorem 3 exponent check.

`LocSol2 p n`: `n ≡ x + y² (mod p)` with `x, y` nonzero mod `p`, the local problem of `p₁ + p₂²`.
`LocSol3 p n`: `n ≡ x² + y² + z² (mod p)` with `x, y, z` nonzero mod `p`, that of three prime
squares. Both are trust surface; `locSol2_nonempty` and `locSol3_nonempty` show they can hold.

Assemblies, no gap of their own, CONDITIONAL ON the leaves below:
* `locSol3_of_InH3`: every `n ∈ ℋ₃` is locally a sum of three prime squares at every prime.
* `locSol2_of_InH2`: every `n ∈ ℋ₂` is locally a prime plus a prime square at every prime.
* `InH2_iff_locSol2`: `ℋ₂` is exactly the set where the local problems at 2 and 3 are solvable.
* `not_dvd_five_of_locSol3`: local solvability at 5 forces `5 ∤ n`, the reason for `5 ∤ n` in `ℋ₃`.

AI-written Lean code, Claude, unit U-1534. Checked only by the Lean kernel.
Binary Goldbach is OPEN; these are Hua type problems.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.U1534

open LeanLab.KumchevLiu2007
open scoped Pointwise

/-- `n` is congruent mod `p` to `x + y²` with `x, y` nonzero mod `p`. -/
def LocSol2 (p n : ℕ) : Prop := ∃ x y : ZMod p, x ≠ 0 ∧ y ≠ 0 ∧ x + y ^ 2 = (n : ZMod p)

/-- `n` is congruent mod `p` to `x² + y² + z²` with `x, y, z` nonzero mod `p`. -/
def LocSol3 (p n : ℕ) : Prop :=
  ∃ x y z : ZMod p, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ 2 + y ^ 2 + z ^ 2 = (n : ZMod p)

/-- Vacuity check: `LocSol2` can hold, `12 ≡ 1 + 1² (mod 5)`. -/
theorem locSol2_nonempty : LocSol2 5 12 := ⟨1, 1, by decide, by decide, by decide⟩

/-- Vacuity check: `LocSol3` can hold, `3 ≡ 1² + 1² + 1² (mod 5)`. -/
theorem locSol3_nonempty : LocSol3 5 3 := ⟨1, 1, 1, by decide, by decide, by decide, by decide⟩

/-- LEAF. Unit U-1534. Every odd `n` is locally a sum of three nonzero squares mod 2;
Section 3.3, property iv, the prime 2. -/
theorem locSol3_two {n : ℕ} (hn : n % 2 = 1) : LocSol3 2 n := by
  use 1, 1, 1
  refine ⟨by decide, by decide, by decide, ?_⟩
  have : (n : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod n 2]
    rw [hn]
    rfl
  rw [this]
  rfl

/-- LEAF. Unit U-1534. A sum of three odd squares is `3 mod 8`, so odd prime squares can only
reach `n ≡ 3 (mod 8)`; Section 1, the definition of `ℋ₃`, and Section 3.3, property iv. -/
lemma odd_sq_mod_eight {x : ℕ} (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases this with h | h | h | h
  · calc x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
    _ = 1 ^ 2 % 8 := by rw [h]
    _ = 1 := by norm_num
  · calc x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
    _ = 3 ^ 2 % 8 := by rw [h]
    _ = 1 := by norm_num
  · calc x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
    _ = 5 ^ 2 % 8 := by rw [h]
    _ = 1 := by norm_num
  · calc x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
    _ = 7 ^ 2 % 8 := by rw [h]
    _ = 1 := by norm_num

theorem three_odd_sq_mod_eight {x y z : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 1) (hz : z % 2 = 1) :
    (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 3 := by
  have hx2 := odd_sq_mod_eight hx
  have hy2 := odd_sq_mod_eight hy
  have hz2 := odd_sq_mod_eight hz
  omega

/-- LEAF. Unit U-1534. Every `n` divisible by 3 is locally a sum of three nonzero squares mod 3;
Section 3.3, property iv, the prime 3. -/
theorem locSol3_three {n : ℕ} (hn : n % 3 = 0) : LocSol3 3 n := by
  use 1, 1, 1
  refine ⟨by decide, by decide, by decide, ?_⟩
  have : (n : ZMod 3) = 0 := by
    rw [← ZMod.natCast_mod n 3]
    rw [hn]
    rfl
  rw [this]
  rfl

/-- LEAF. Unit U-1534. Every `n` prime to 5 is locally a sum of three nonzero squares mod 5;
Section 3.3, property iv, the prime 5. -/
theorem locSol3_five {n : ℕ} (hn : ¬ 5 ∣ n) : LocSol3 5 n := by
  have h_mod : n % 5 ≠ 0 := by
    intro h_eq
    apply hn
    exact Nat.dvd_of_mod_eq_zero h_eq
  have h1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases h1 with h | h | h | h
  · use 2, 1, 1
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 5) = 1 := by rw [← ZMod.natCast_mod n 5, h]; rfl
    rw [this]; rfl
  · use 3, 3, 3
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 5) = 2 := by rw [← ZMod.natCast_mod n 5, h]; rfl
    rw [this]; rfl
  · use 1, 1, 1
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 5) = 3 := by rw [← ZMod.natCast_mod n 5, h]; rfl
    rw [this]; rfl
  · use 2, 2, 1
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 5) = 4 := by rw [← ZMod.natCast_mod n 5, h]; rfl
    rw [this]; rfl

/-- LEAF. Unit U-1534. No `n` divisible by 5 is a sum of three nonzero squares mod 5, since the
nonzero squares mod 5 are 1 and 4; the condition `5 ∤ n` in `ℋ₃`, Section 1. -/
theorem not_locSol3_five {n : ℕ} (hn : 5 ∣ n) : ¬ LocSol3 5 n := by
  intro h
  rcases h with ⟨x, y, z, hx, hy, hz, heq⟩
  have : (n : ZMod 5) = 0 := by
    rw [← ZMod.natCast_mod n 5]
    have h_mod : n % 5 = 0 := Nat.mod_eq_zero_of_dvd hn
    rw [h_mod]
    rfl
  rw [this] at heq
  revert heq hz hy hx x y z
  decide

/-- LEAF. Unit U-1534. Every residue mod 7 is a sum of three nonzero squares mod 7;
Section 3.3, property iv, the prime 7. -/
theorem locSol3_seven (n : ℕ) : LocSol3 7 n := by
  have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
  rcases h1 with h | h | h | h | h | h | h
  · use 1, 2, 3
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 7) = 0 := by rw [← ZMod.natCast_mod n 7, h]; rfl
    rw [this]; rfl
  · use 3, 3, 2
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 7) = 1 := by rw [← ZMod.natCast_mod n 7, h]; rfl
    rw [this]; rfl
  · use 2, 2, 1
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 7) = 2 := by rw [← ZMod.natCast_mod n 7, h]; rfl
    rw [this]; rfl
  · use 1, 1, 1
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 7) = 3 := by rw [← ZMod.natCast_mod n 7, h]; rfl
    rw [this]; rfl
  · use 3, 1, 1
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 7) = 4 := by rw [← ZMod.natCast_mod n 7, h]; rfl
    rw [this]; rfl
  · use 3, 3, 1
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 7) = 5 := by rw [← ZMod.natCast_mod n 7, h]; rfl
    rw [this]; rfl
  · use 1, 1, 2
    refine ⟨by decide, by decide, by decide, ?_⟩
    have : (n : ZMod 7) = 6 := by rw [← ZMod.natCast_mod n 7, h]; rfl
    rw [this]; rfl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- LEAF. Unit U-1534. For every prime `p ≥ 7`, every residue mod `p` is a sum of three nonzero
squares mod `p`; Section 3.3, property iv, `A₃(n, p) > -1` for `p ≥ 7`. -/
theorem locSol3_large {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (n : ℕ) : LocSol3 p n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let s : Finset (ZMod p) := Finset.univ.erase 0
  let a := s.image (fun x => x ^ 2)
  have ha : a.Nonempty := by
    refine ⟨1, Finset.mem_image.mpr ⟨1, ?_, by simp⟩⟩
    simp [s]
  have hcard : p - 1 ≤ 2 * a.card := by
    have hf : s.card ≤ ∑ y ∈ a, 2 := by
      rw [Finset.card_eq_sum_card_image (fun x : ZMod p => x ^ 2) s]
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hsub : s.filter (fun z => z ^ 2 = x ^ 2) ⊆ {x, -x} := by
        intro z hz
        have heq := (Finset.mem_filter.mp hz).2
        simpa only [Finset.mem_insert, Finset.mem_singleton] using
          sq_eq_sq_iff_eq_or_eq_neg.mp heq
      exact (Finset.card_le_card hsub).trans (by simpa using (Finset.card_insert_le x ({-x} : Finset (ZMod p))))
    simpa [s, a, ZMod.card, Nat.mul_comm] using hf
  have hdouble := ZMod.cauchy_davenport hp ha ha
  have hsum := ZMod.cauchy_davenport hp (ha.add ha) ha
  have hlarge : p ≤ ((a + a) + a).card := by
    have hapos := ha.card_pos
    omega
  have heq : (a + a) + a = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, ZMod.card] using hlarge
  have hn : (n : ZMod p) ∈ (a + a) + a := by rw [heq]; simp
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hn
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hu
  obtain ⟨r, hr, hrx⟩ := Finset.mem_image.mp hx
  obtain ⟨t, ht, hty⟩ := Finset.mem_image.mp hy
  obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hv
  refine ⟨r, t, z, ?_, ?_, ?_, ?_⟩
  · exact (Finset.mem_erase.mp hr).1
  · exact (Finset.mem_erase.mp ht).1
  · exact (Finset.mem_erase.mp hz).1
  · rw [hrx, hty, hzv, hxy, huv]

/-- LEAF. Unit U-1534. Every even `n` is locally a prime plus a prime square mod 2;
Section 3.3, property iii, the prime 2. -/
theorem locSol2_two {n : ℕ} (hn : n % 2 = 0) : LocSol2 2 n := by
  use 1, 1
  refine ⟨by decide, by decide, ?_⟩
  have : (n : ZMod 2) = 0 := by
    rw [← ZMod.natCast_mod n 2]
    rw [hn]
    rfl
  rw [this]
  rfl

/-- LEAF. Unit U-1534. No odd `n` is `x + y²` mod 2 with `x, y` nonzero, so `2 ∣ n` in `ℋ₂`;
Section 1, the definition of `ℋ₂`. -/
theorem not_locSol2_two {n : ℕ} (hn : n % 2 = 1) : ¬ LocSol2 2 n := by
  intro h
  rcases h with ⟨x, y, hx, hy, heq⟩
  have : (n : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod n 2]
    rw [hn]
    rfl
  rw [this] at heq
  revert heq hy hx x y
  decide

/-- LEAF. Unit U-1534. Every `n ≢ 1 (mod 3)` is `x + y²` mod 3 with `x, y` nonzero;
Section 3.3, property iii, the prime 3. -/
theorem locSol2_three {n : ℕ} (hn : n % 3 ≠ 1) : LocSol2 3 n := by
  have h1 : n % 3 = 0 ∨ n % 3 = 2 := by omega
  rcases h1 with h_zero | h_two
  · use 2, 1
    refine ⟨by decide, by decide, ?_⟩
    have : (n : ZMod 3) = 0 := by
      rw [← ZMod.natCast_mod n 3]
      rw [h_zero]
      rfl
    rw [this]
    rfl
  · use 1, 1
    refine ⟨by decide, by decide, ?_⟩
    have : (n : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod n 3]
      rw [h_two]
      rfl
    rw [this]
    rfl

/-- LEAF. Unit U-1534. No `n ≡ 1 (mod 3)` is `x + y²` mod 3 with `x, y` nonzero, the reason for
`n ≢ 1 (mod 3)` in `ℋ₂`; Section 1, the definition of `ℋ₂`. -/
theorem not_locSol2_three {n : ℕ} (hn : n % 3 = 1) : ¬ LocSol2 3 n := by
  intro h
  rcases h with ⟨x, y, hx, hy, heq⟩
  have : (n : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod n 3]
    rw [hn]
    rfl
  rw [this] at heq
  revert heq hy hx x y
  decide

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- LEAF. Unit U-1534. For every prime `p ≥ 5`, every residue mod `p` is `x + y²` with `x, y`
nonzero mod `p`; Section 3.3, property iii, `A₂(n, p) > -1` for `p ≥ 5`. -/
theorem locSol2_large {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (n : ℕ) : LocSol2 p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by norm_num : 0 < 2) this
    omega
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have := Nat.le_of_dvd (by norm_num : 0 < 3) this
    omega
  by_cases hn : (n : ZMod p) = 1
  · refine ⟨-3, 2, neg_ne_zero.mpr hthree, htwo, ?_⟩
    rw [hn]
    ring
  · refine ⟨(n : ZMod p) - 1, 1, sub_ne_zero.mpr hn, one_ne_zero, ?_⟩
    ring

/-- LEAF. Unit U-1534. With `θ₁ = 7/12 + ε` and `θ₂ = 3/5 - 2ε`, `ε > 0`, the exponent
`θ₁ θ₂` is below `7/20`, the range of Theorem 3; Section 6.1, last paragraph. -/
theorem theta_thm3_lt {ε : ℝ} (hε : 0 < ε) : (7 / 12 + ε) * (3 / 5 - 2 * ε) < 7 / 20 := by
  have : (7 / 12 + ε) * (3 / 5 - 2 * ε) = 7 / 20 - (17 / 30) * ε - 2 * ε ^ 2 := by ring
  rw [this]
  have h1 : 0 < (17 / 30 : ℝ) * ε := mul_pos (by norm_num) hε
  have h2 : 0 < 2 * ε ^ 2 := mul_pos (by norm_num) (pow_pos hε 2)
  linarith

/-! ### Assemblies -/

/-- A prime other than 2, 3 and 5 is at least 7. -/
lemma seven_le_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) :
    7 ≤ p := by
  have := hp.two_le
  by_contra h
  push Not at h
  interval_cases p <;> simp_all <;> exact absurd hp (by decide)

/-- A prime other than 2 and 3 is at least 5. -/
lemma five_le_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  have := hp.two_le
  by_contra h
  push Not at h
  interval_cases p <;> simp_all <;> exact absurd hp (by decide)

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `locSol3_two`, `locSol3_three`,
`locSol3_five` and `locSol3_large`. Every `n ∈ ℋ₃` is locally a sum of three squares of units
at every prime `p`. -/
theorem locSol3_of_InH3 {n : ℕ} (hn : InH3 n) {p : ℕ} (hp : p.Prime) : LocSol3 p n := by
  obtain ⟨h24, h5⟩ := hn
  by_cases e2 : p = 2
  · subst e2; exact locSol3_two (by omega)
  by_cases e3 : p = 3
  · subst e3; exact locSol3_three (by omega)
  by_cases e5 : p = 5
  · subst e5; exact locSol3_five h5
  exact locSol3_large hp (seven_le_of_prime hp e2 e3 e5) n

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `locSol2_two`, `locSol2_three` and
`locSol2_large`. Every `n ∈ ℋ₂` is locally a prime plus a prime square at every prime `p`. -/
theorem locSol2_of_InH2 {n : ℕ} (hn : InH2 n) {p : ℕ} (hp : p.Prime) : LocSol2 p n := by
  obtain ⟨h3, h2⟩ := hn
  by_cases e2 : p = 2
  · subst e2; exact locSol2_two (by omega)
  by_cases e3 : p = 3
  · subst e3; exact locSol2_three h3
  exact locSol2_large hp (five_le_of_prime hp e2 e3) n

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `locSol2_two`, `not_locSol2_two`,
`locSol2_three` and `not_locSol2_three`. `ℋ₂` is exactly the set of `n` that are locally
`p₁ + p₂²` at both 2 and 3. -/
theorem InH2_iff_locSol2 (n : ℕ) : InH2 n ↔ LocSol2 2 n ∧ LocSol2 3 n := by
  constructor
  · intro ⟨h3, h2⟩
    exact ⟨locSol2_two (by omega), locSol2_three h3⟩
  · intro ⟨l2, l3⟩
    refine ⟨fun h => not_locSol2_three h l3, ?_⟩
    by_contra h
    exact not_locSol2_two (by omega) l2

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `not_locSol3_five`. Local solvability of
three squares of units at 5 forces `5 ∤ n`. -/
theorem not_dvd_five_of_locSol3 {n : ℕ} (h : LocSol3 5 n) : ¬ 5 ∣ n :=
  fun hd => not_locSol3_five hd h

end LeanLab.KumchevLiu2007.U1534
