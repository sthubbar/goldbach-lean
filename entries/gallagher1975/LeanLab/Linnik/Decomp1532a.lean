module

public import Mathlib
public import LeanLab.Linnik.Gallagher1975Lemma3
public import LeanLab.Linnik.Task37Fourier
public import LeanLab.Linnik.U1434Lemma21
public import LeanLab.Linnik.Task37Display19
public import LeanLab.Linnik.U1474R0
public import LeanLab.Romanov.Decomp134b
public import LeanLab.Romanov.Residues134

/-!
Unit U-1532, run 20261026T0004Z-24325, DECOMPOSE.
Gallagher 1975, Primes and powers of 2, Invent. Math. 29, 125-142, base g = 2.

File a: the powers of 2 modulo q, Section 2 of the paper, pp. 133-136.
* `ordTwo q`, the order `e(q)` of 2 modulo an odd `q`, p. 133.
* `pairs k L`, pairs of exponent tuples `ν, μ ∈ [1, L]^k`, written with `Fin L` and the shift
  `ν i + 1` of `sv`; `dif x = 2^{ν₁} + ... + 2^{ν_k} - (2^{μ₁} + ... + 2^{μ_k})`, so that
  `r_{k,k}(n)` of display (3), p. 134, is the number of `x` with `dif x = n`.
* `Mprod x = ∏_{e ≤ x} (2^e - 1)`, the modulus `M` in the proof of Lemma 4, p. 133.
Leaves: Lemma 3 inputs on `e(q)`, Lemma 4 split into four steps, Lemma 5, Lemma 7, Lemma 8.
Assembly: `lemma4`, Lemma 4 of p. 133, from the four Lemma 4 leaves.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp1532a

open Finset
open LeanLab.Linnik.U1434Lemma21 (sv)

/-- `e(q)`, the order of 2 modulo `q`, p. 133; for odd `q` it is the least `e ≥ 1` with
`2^e ≡ 1 mod q`. -/
noncomputable def ordTwo (q : ℕ) : ℕ := orderOf (2 : ZMod q)

/-- Pairs of exponent tuples `(ν, μ)`, `ν i + 1, μ i + 1 ∈ [1, L]`. -/
abbrev pairs (k L : ℕ) : Type := (Fin k → Fin L) × (Fin k → Fin L)

/-- `dif (ν, μ) = Σ 2^{ν_i + 1} - Σ 2^{μ_i + 1}`, the integer `n` of display (3), p. 134. -/
def dif {k L : ℕ} (x : pairs k L) : ℤ := (sv x.1 : ℤ) - sv x.2

/-- `M = ∏_{e=1}^{x} (2^e - 1)`, proof of Lemma 4, p. 133. -/
def Mprod (x : ℕ) : ℕ := ∏ e ∈ Icc 1 x, (2 ^ e - 1)

/-- LEAF. Unit U-1532. For odd `q` the order `e(q)` of 2 modulo `q` is positive,
p. 133, definition before Lemma 3. -/
theorem ordTwo_pos {q : ℕ} (hq : Odd q) : 0 < ordTwo q := by
  have h_unit : IsUnit (2 : ZMod q) := by
    apply ZMod.isUnit_prime_of_not_dvd
    · exact Nat.prime_two
    · exact hq.not_two_dvd_nat
  rcases q with _ | q'
  · exfalso; revert hq; decide
  · have h_pos := orderOf_pos h_unit.unit
    have h_eq : orderOf (2 : ZMod (q' + 1)) = orderOf h_unit.unit := by
      exact @orderOf_units _ _ h_unit.unit
    rwa [← h_eq] at h_pos

/-- LEAF. Unit U-1532. For odd `q`, `q` divides `2^{e(q)} - 1`, p. 133, definition of
`e(q)`. -/
theorem dvd_two_pow_ordTwo_sub_one {q : ℕ} (hq : Odd q) : q ∣ 2 ^ ordTwo q - 1 := by
  have h1 : (2 : ZMod q) ^ ordTwo q = 1 := pow_orderOf_eq_one (2 : ZMod q)
  have h2 : ((2 ^ ordTwo q : ℕ) : ZMod q) = 1 := by exact_mod_cast h1
  have h3 : (2 ^ ordTwo q : ℕ) ≡ 1 [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have h4 : (1 : ZMod q) = ((1 : ℕ) : ZMod q) := by simp
    rw [← h4]
    exact h2
  have h3' : 1 ≡ 2 ^ ordTwo q [MOD q] := h3.symm
  have h4 : (q : ℤ) ∣ (2 ^ ordTwo q : ℕ) - (1 : ℤ) := Nat.ModEq.dvd h3'
  apply Int.ofNat_dvd.mp
  have h5 : ((2 ^ ordTwo q - 1 : ℕ) : ℤ) = (2 ^ ordTwo q : ℕ) - (1 : ℤ) := by
    apply Nat.cast_sub
    exact Nat.one_le_pow _ _ (by norm_num)
  rw [h5]
  exact h4

/-- LEAF. Unit U-1532. For odd `q ≥ 1`, `log q ≤ e(q) log 2`, the bound `e(f) ≫ log f` used in
the proof of Lemma 10, p. 137. -/
theorem log_le_ordTwo_mul_log_two {q : ℕ} (hq : Odd q) :
    Real.log q ≤ ordTwo q * Real.log 2 := by
  have h_dvd : q ∣ 2 ^ ordTwo q - 1 := dvd_two_pow_ordTwo_sub_one hq
  have h_pos : 0 < 2 ^ ordTwo q - 1 := by
    have h1 : 2 ^ 1 ≤ 2 ^ ordTwo q := by
      apply Nat.pow_le_pow_right (by norm_num) (ordTwo_pos hq)
    have h_pow : 2 ^ 1 = 2 := by rfl
    rw [h_pow] at h1
    omega
  have h_le : q ≤ 2 ^ ordTwo q - 1 := by
    apply Nat.le_of_dvd h_pos h_dvd
  have h_le2 : q ≤ 2 ^ ordTwo q := by omega
  have h_le3 : (q : ℝ) ≤ ((2 ^ ordTwo q : ℕ) : ℝ) := by exact_mod_cast h_le2
  have h_log : Real.log (q : ℝ) ≤ Real.log ((2 ^ ordTwo q : ℕ) : ℝ) := by
    have hq_pos : 0 < q := by
      rcases q with _ | q'
      · exfalso; revert hq; decide
      · exact Nat.zero_lt_succ _
    apply Real.log_le_log
    · exact_mod_cast hq_pos
    · exact h_le3
  have h_log2 : Real.log ((2 ^ ordTwo q : ℕ) : ℝ) = (ordTwo q : ℝ) * Real.log 2 := by
    have h_pow : ((2 ^ ordTwo q : ℕ) : ℝ) = (2 : ℝ) ^ (ordTwo q : ℕ) := by push_cast; rfl
    rw [h_pow]
    exact Real.log_pow (2 : ℝ) (ordTwo q)
  rwa [h_log2] at h_log

/-- LEAF. Unit U-1532. For odd `q`, `2^a ≡ 2^b mod q` exactly when `a ≡ b mod e(q)`; this is the
periodicity used in the proofs of Lemmas 3 and 5, pp. 133-134. -/
theorem two_pow_modEq_iff {q : ℕ} (hq : Odd q) (a b : ℕ) :
    2 ^ a ≡ 2 ^ b [MOD q] ↔ a ≡ b [MOD ordTwo q] := by
  have h_unit : IsUnit (2 : ZMod q) := by
    apply ZMod.isUnit_prime_of_not_dvd
    · exact Nat.prime_two
    · exact hq.not_two_dvd_nat
  constructor
  · intro h
    have h1 : ((2 ^ a : ℕ) : ZMod q) = ((2 ^ b : ℕ) : ZMod q) := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    have h2 : (2 : ZMod q) ^ a = (2 : ZMod q) ^ b := by
      push_cast at h1
      exact h1
    have h4 : h_unit.unit ^ a = h_unit.unit ^ b := by
      apply Units.ext
      exact h2
    have h5 : a ≡ b [MOD orderOf h_unit.unit] := by
      exact pow_eq_pow_iff_modEq.mp h4
    have h6 : orderOf (2 : ZMod q) = orderOf h_unit.unit := by
      exact @orderOf_units _ _ h_unit.unit
    rwa [← h6] at h5
  · intro h
    have h1 : a ≡ b [MOD orderOf h_unit.unit] := by
      have h6 : orderOf (2 : ZMod q) = orderOf h_unit.unit := by
        exact @orderOf_units _ _ h_unit.unit
      have h7 : ordTwo q = orderOf (2 : ZMod q) := rfl
      rwa [h7, h6] at h
    have h2 : h_unit.unit ^ a = h_unit.unit ^ b := by
      exact pow_eq_pow_iff_modEq.mpr h1
    have h3 : (2 : ZMod q) ^ a = (2 : ZMod q) ^ b := by
      exact congr_arg Units.val h2
    have h4 : ((2 ^ a : ℕ) : ZMod q) = ((2 ^ b : ℕ) : ZMod q) := by
      push_cast
      exact h3
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h4

/-- LEAF. Unit U-1532. For odd `q`, every residue class `c` contains at most `L / e(q) + 1` of
the powers `2^μ`, `1 ≤ μ ≤ L`; the last step of the proof of Lemma 5, p. 134. -/
theorem card_pow_residue_le {q : ℕ} (hq : Odd q) (c L : ℕ) :
    (#{μ ∈ Icc 1 L | 2 ^ μ % q = c} : ℝ) ≤ L / ordTwo q + 1 := by
  exact LeanLab.Romanov.Residues134.pow_residue_count_le hq c L

/-- LEAF. Unit U-1532. Every `n` has at most two ordered representations `n = 2^a + 2^b`, the
uniqueness of `n = g^μ (1 + g^δ)` in the proof of Lemma 5, p. 134. -/
theorem card_two_pow_pairs_le (n : ℕ) :
    #{x ∈ range n ×ˢ range n | 2 ^ x.1 + 2 ^ x.2 = n} ≤ 2 := by
  classical
  let S := (range n ×ˢ range n).filter (fun x => 2 ^ x.1 + 2 ^ x.2 = n)
  change S.card ≤ 2
  by_cases hs : S.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hsub : S ⊆ {x, (x.2, x.1)} := by
      intro y hy
      have he := (mem_filter.mp hy).2.trans (mem_filter.mp hx).2.symm
      rcases LeanLab.Linnik.U1447Display30.pow_pair _ _ _ _ he with h | h
      · simp [Prod.ext h.1 h.2]
      · simp [show y = (x.2, x.1) from Prod.ext h.1 h.2]
    exact (card_le_card hsub).trans card_le_two
  · simp [not_nonempty_iff_eq_empty.mp hs]

/-- LEAF. Unit U-1532. Lemma 5, display (4), p. 134, with constant 2: for `k ≥ 2` the number
`r_{k,k}(0)` of pairs with `2^{ν₁} + ... + 2^{ν_k} = 2^{μ₁} + ... + 2^{μ_k}` is at most
`2 L^{2k-2}`. -/
theorem rkk_zero_le {k : ℕ} (hk : 2 ≤ k) (L : ℕ) :
    #{x : pairs k L | dif x = 0} ≤ 2 * L ^ (2 * k - 2) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h := LeanLab.Linnik.Task37Display19.Dc_two_left j (j + 2) L
  have he : (#{x : pairs (j + 2) L | dif x = 0} : ℝ) =
      LeanLab.Linnik.U1447Display30.Dc (j + 2) (j + 2) L := by
    rw [LeanLab.Linnik.U1447Display30.Dc, ← Fintype.sum_prod_type', sum_boole]
    congr 2
    ext x
    simp only [mem_filter, mem_univ, true_and, dif, sub_eq_zero, Nat.cast_inj]
  rw [← he] at h
  have hex : 2 * (j + 2) - 2 = j + (j + 2) := by omega
  rw [hex]
  exact_mod_cast h

/-- LEAF. Unit U-1532. Lemma 5, display (5), p. 134: for odd `q` and `k ≥ 1`, the number of
pairs with `q ∣ n` is at most `L^{2k} / e(q) + L^{2k-1}`. -/
theorem card_dvd_dif_le {q : ℕ} (hq : Odd q) {k : ℕ} (hk : 1 ≤ k) (L : ℕ) :
    (#{x : pairs k L | (q : ℤ) ∣ dif x} : ℝ) ≤
      (L : ℝ) ^ (2 * k) / ordTwo q + (L : ℝ) ^ (2 * k - 1) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have he (ν μ : Fin (j + 1) → Fin L) :
      (q : ℤ) ∣ dif (ν, μ) ↔ sv ν % q = sv μ % q := by
    rw [dif, ← Int.modEq_iff_dvd, Int.natCast_modEq_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [← sum_boole, Fintype.sum_prod_type, sum_comm]
  simp_rw [he]
  calc
    _ = ∑ μ : Fin (j + 1) → Fin L,
        (#{ν : Fin (j + 1) → Fin L | sv ν % q = sv μ % q} : ℝ) := by
          simp only [sum_boole]
    _ ≤ ∑ _μ : Fin (j + 1) → Fin L,
        ((L : ℝ) ^ (j + 1) / ordTwo q + (L : ℝ) ^ j) := by
          apply sum_le_sum
          intro μ hμ
          exact LeanLab.Romanov.Residues134.tuple_residue_count_le hq j L (sv μ % q)
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have h1 : 2 * (j + 1) = (j + 1) + (j + 1) := by omega
      have h2 : 2 * (j + 1) - 1 = (j + 1) + j := by omega
      rw [h2, h1, pow_add, pow_add]
      ring

/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133: an odd `q` with `e(q) ≤ x` divides
`M = ∏_{e ≤ x} (2^e - 1)`. -/
theorem dvd_Mprod {q x : ℕ} (hq : Odd q) (hx : ordTwo q ≤ x) : q ∣ Mprod x := by
  have h_dvd : q ∣ 2 ^ ordTwo q - 1 := dvd_two_pow_ordTwo_sub_one hq
  apply dvd_trans h_dvd
  have h_pos : 1 ≤ ordTwo q := ordTwo_pos hq
  have h_mem : ordTwo q ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨h_pos, hx⟩
  exact Finset.dvd_prod_of_mem (fun e => 2 ^ e - 1) h_mem

/-- LEAF. Unit U-1532. For `x ≥ 2`, `M = ∏_{e ≤ x} (2^e - 1) ≥ 3`, so `log log M` is
positive in the proof of Lemma 4, p. 133. -/
theorem three_le_Mprod {x : ℕ} (hx : 2 ≤ x) : 3 ≤ Mprod x := by
  have h_split : Finset.Icc 1 x = Finset.Icc 1 2 ∪ Finset.Icc 3 x := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [Mprod, h_split]
  have h_disj : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 x) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_Icc] at ha hb
    omega
  rw [Finset.prod_union h_disj]
  have h_prod1 : ∏ e ∈ Finset.Icc 1 2, (2 ^ e - 1) = 3 := by rfl
  rw [h_prod1]
  have h_prod2 : 1 ≤ ∏ e ∈ Finset.Icc 3 x, (2 ^ e - 1) := by
    apply Finset.one_le_prod
    intro i hi
    have h_le : 3 ≤ i := (Finset.mem_Icc.mp hi).1
    have h_pow : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h_le
    omega
  omega

/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133: `log M ≤ x² log 2`, the printed
`M ≤ g^{x²}`. -/
theorem log_Mprod_le (x : ℕ) : Real.log (Mprod x) ≤ (x : ℝ) ^ 2 * Real.log 2 := by
  have h0 : 0 < Mprod x := Nat.pos_of_ne_zero (LeanLab.Linnik.U1474R0.Q_ne_zero x)
  have hb : (Mprod x : ℝ) ≤ (2 : ℝ) ^ (x * x) := by
    exact_mod_cast LeanLab.Linnik.U1474R0.Q_le x
  calc
    Real.log (Mprod x) ≤ Real.log ((2 : ℝ) ^ (x * x)) :=
      Real.log_le_log (by exact_mod_cast h0) hb
    _ = _ := by rw [Real.log_pow]; push_cast; ring

/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133, the Euler product identity
`Σ_{q ∣ m} μ(q)² q / φ(q)² = ∏_{p ∣ m} (1 + p/(p-1)²)` for `m ≥ 1`. -/
theorem sum_divisors_eq_prod {m : ℕ} (hm : 0 < m) :
    ∑ q ∈ m.divisors, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 =
      ∏ p ∈ m.primeFactors, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
  classical
  have he (q : ℕ) : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q /
      (q.totient : ℝ) ^ 2 = ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 *
        ((q : ℝ) / (q.totient : ℝ) ^ 2) := by ring
  simp_rw [he]
  rw [LeanLab.Romanov.Decomp134b.squarefree_divisor_expansion m hm.ne', prod_one_add]
  apply sum_congr rfl
  intro S hS
  have hpr : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp hS hp)
  have hphi := LeanLab.Romanov.Decomp134b.inverse_totient_prime_product S hpr
  calc
    ((∏ p ∈ S, p : ℕ) : ℝ) / ((∏ p ∈ S, p : ℕ).totient : ℝ) ^ 2 =
        (∏ p ∈ S, (p : ℝ)) * ((1 : ℝ) / ((∏ p ∈ S, p : ℕ).totient : ℝ)) ^ 2 := by
          rw [Nat.cast_prod]; ring
    _ = _ := by
      rw [hphi, ← prod_pow, ← prod_mul_distrib]
      apply prod_congr rfl
      intro p hp
      rw [div_pow, one_pow, mul_one_div]

/-- Gallagher 1975 p.133. Auxiliary rational bound for the odd correction tail. -/
theorem odd_correction_partial (n : ℕ) :
    (∏ i ∈ range n, (1 + 1 / (((2 * i + 11 : ℕ) : ℝ) * (2 * i + 10)))) *
      (1 + 1 / (4 * (n : ℝ) + 18)) ≤ 19 / 18 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [prod_range_succ]
    have hlocal : (1 + 1 / (((2 * n + 11 : ℕ) : ℝ) * (2 * n + 10))) *
        (1 + 1 / (4 * ((n + 1 : ℕ) : ℝ) + 18)) ≤ 1 + 1 / (4 * (n : ℝ) + 18) := by
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      field_simp
      nlinarith
    have hp : 0 ≤ ∏ i ∈ range n, (1 + 1 / (((2 * i + 11 : ℕ) : ℝ) * (2 * i + 10))) := by positivity
    calc
      _ = (∏ i ∈ range n, (1 + 1 / (((2 * i + 11 : ℕ) : ℝ) * (2 * i + 10)))) *
          ((1 + 1 / (((2 * n + 11 : ℕ) : ℝ) * (2 * n + 10))) *
            (1 + 1 / (4 * ((n + 1 : ℕ) : ℝ) + 18))) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hlocal hp).trans ih



/-- Gallagher 1975 p.133. Auxiliary correction product over a finite set of primes. -/
theorem prime_correction_prod_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 2 := by
  classical
  let f : ℕ → ℝ := fun p => 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))
  let M := S.sup id + 1
  let A : Finset ℕ := {2, 3, 5, 7}
  let T : Finset ℕ := (range M).image (fun i => 2 * i + 11)
  have hsub : S ⊆ A ∪ T := by
    intro p hp
    by_cases hsmall : p < 11
    · have hpr := hS p hp
      have hmem : p ∈ A := by
        dsimp [A]
        interval_cases p <;> norm_num at *
      exact mem_union_left _ hmem
    · have hodd : Odd p := (hS p hp).odd_of_ne_two (by omega)
      obtain ⟨j, hj⟩ := hodd
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨j - 5, mem_range.mpr ?_, by omega⟩
      have hle : p ≤ S.sup id := le_sup (f := id) hp
      dsimp [M]
      omega
  have hpos (p : ℕ) (hp : p ∈ A ∪ T) : 1 ≤ f p := by
    have hp2 : 2 ≤ p := by
      rcases mem_union.mp hp with ha | ht
      · simp only [A, mem_insert, mem_singleton] at ha
        omega
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
        omega
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    dsimp [f]
    have hpred : 0 < (p : ℝ) - 1 := by linarith
    have hx : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
    linarith
  have hdis : Disjoint A T := by
    rw [disjoint_left]
    intro p hp ht
    simp only [A, mem_insert, mem_singleton] at hp
    obtain ⟨i, hi, he⟩ := mem_image.mp ht
    omega
  have htail : ∏ p ∈ T, f p ≤ 19 / 18 := by
    have hi : Set.InjOn (fun i : ℕ => 2 * i + 11) (range M) := by
      intro a ha b hb he
      dsimp at he
      omega
    dsimp only [T]
    rw [prod_image hi]
    have h := odd_correction_partial M
    have h0 : 0 ≤ ∏ i ∈ range M, (1 + 1 / (((2 * i + 11 : ℕ) : ℝ) * (2 * i + 10))) := by positivity
    have hx : 0 ≤ 1 / (4 * (M : ℝ) + 18) := by positivity
    have he : (∏ p ∈ range M, f (2 * p + 11)) =
        ∏ i ∈ range M, (1 + 1 / (((2 * i + 11 : ℕ) : ℝ) * (2 * i + 10))) := by
      apply prod_congr rfl
      intro i hi
      dsimp [f]
      push_cast
      ring
    rw [he]
    nlinarith
  have hsmall : ∏ p ∈ A, f p = 301 / 160 := by norm_num [A, f]
  change ∏ p ∈ S, f p ≤ 2
  calc
    _ ≤ ∏ p ∈ A ∪ T, f p := prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p hp => (hpos p (hsub hp)).trans' zero_le_one)
      (fun p hp _ => hpos p hp)
    _ = (301 / 160) * ∏ p ∈ T, f p := by rw [prod_union hdis, hsmall]
    _ ≤ (301 / 160) * (19 / 18) := mul_le_mul_of_nonneg_left htail (by norm_num)
    _ ≤ 2 := by norm_num


/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133: `∏_{p ∣ m} (1 + p/(p-1)²) ≤ 2 m/φ(m)`, since
the factor over `p/(p-1)` is `1 + 1/(p(p-1))` and the product of these over all primes is below
2. -/
theorem prod_le_two_mul_div_totient {m : ℕ} (hm : 0 < m) :
    ∏ p ∈ m.primeFactors, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ 2 * ((m : ℝ) / m.totient) := by
  classical
  rw [LeanLab.Romanov.Decomp134b.totient_ratio_eq_prod m hm]
  have hlocal (p : ℕ) (hp : p ∈ m.primeFactors) :
      1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2 =
        (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) * ((p : ℝ) / ((p : ℝ) - 1)) := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
    ring
  calc
    _ = (∏ p ∈ m.primeFactors, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) *
        (∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl hlocal
    _ ≤ 2 * (∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right
        (prime_correction_prod_le m.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp))
        (prod_nonneg (fun p hp => by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          exact div_nonneg (by positivity) (by linarith)))

/-- LEAF. Unit U-1532. The bound `m/φ(m) ≪ log log m` for `m ≥ 3`, the last step of the proof of
Lemma 4, p. 133. -/
theorem div_totient_le_loglog :
    ∃ C : ℝ, ∀ m : ℕ, 3 ≤ m → (m : ℝ) / m.totient ≤ C * Real.log (Real.log m) := by
  classical
  let B : ℝ := Real.log (Real.log 3)
  have hB : 0 < B := LeanLab.Romanov.Decomp134b.loglog_pos 3 (by omega)
  refine ⟨6 * Real.exp 24 * Real.exp 2 * (1 + Real.log 3 / B), fun m hm => ?_⟩
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : 1 < Real.log (m : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  let L : ℕ := ⌊Real.log (m : ℝ)⌋₊ + 2
  have hL2 : 2 ≤ L := by omega
  have hLlo : Real.log (m : ℝ) ≤ L := by
    have h := Nat.lt_floor_add_one (Real.log (m : ℝ))
    dsimp [L]
    push_cast
    linarith
  have hLhi : (L : ℝ) ≤ 3 * Real.log m := by
    have h := Nat.floor_le (show 0 ≤ Real.log (m : ℝ) by linarith)
    dsimp [L]
    push_cast
    linarith
  have hc := LeanLab.PNTPort.BV.card_primeFactors_mul_log_two_le (q := m) (by omega)
  have hcard : m.primeFactors.card ≤ 2 * L ^ 2 := by
    have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    have hh : (m.primeFactors.card : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by
      have h2 := Real.log_two_gt_d9
      nlinarith [sq_nonneg ((L : ℝ) - 1), (Nat.cast_nonneg m.primeFactors.card : (0 : ℝ) ≤ m.primeFactors.card)]
    exact_mod_cast hh
  have hp := LeanLab.Linnik.U1466Display17.prod_bound
    LeanLab.Linnik.U1469Mertens.oddPrimes_prod_le hL2 hcard
  rw [max_eq_left (Real.exp_pos 24).le] at hp
  have hfac : m.primeFactors.erase 2 = m.primeFactors.filter (fun p => 2 < p) := by
    ext p
    simp only [mem_erase, mem_filter]
    constructor
    · rintro ⟨hne, hmem⟩
      have h2 := (Nat.prime_of_mem_primeFactors hmem).two_le
      exact ⟨hmem, by omega⟩
    · rintro ⟨hmem, h2⟩
      exact ⟨by omega, hmem⟩
  have hmass : LeanLab.Romanov.Decomp134b.oddMass m ≤
      ∏ p ∈ m.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [LeanLab.Romanov.Decomp134b.oddMass_eq_prod m (by omega), hfac]
    apply prod_le_prod₀
    · intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
      have hp1 : 0 < (p : ℝ) - 1 := by linarith
      positivity
    · intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
      have hp1 : 0 < (p : ℝ) - 1 := by linarith
      have he : 1 + 1 / ((p : ℝ) - 1) = (p : ℝ) / ((p : ℝ) - 1) := by
        field_simp
        ring
      rw [he]
      apply (div_le_div_iff₀ hp1 (by linarith : 0 < (p : ℝ) - 2)).mpr
      nlinarith
  have hll : B ≤ Real.log (Real.log (m : ℝ)) := by
    apply Real.log_le_log
    · have : (0 : ℝ) < Real.log 3 := by positivity
      exact this
    · exact Real.log_le_log (by norm_num) hmR
  have hlogL : Real.log L ≤ (1 + Real.log 3 / B) * Real.log (Real.log m) := by
    calc
      Real.log L ≤ Real.log (3 * Real.log m) := Real.log_le_log (by exact_mod_cast (show 0 < L by omega)) hLhi
      _ = Real.log 3 + Real.log (Real.log m) := Real.log_mul (by norm_num) (by linarith)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hll (show 0 ≤ Real.log 3 / B by positivity)
        have he : Real.log 3 / B * B = Real.log 3 := div_mul_cancel₀ _ hB.ne'
        nlinarith
  calc
    (m : ℝ) / m.totient ≤ 2 * LeanLab.Romanov.Decomp134b.oddMass m :=
      LeanLab.Romanov.Decomp134b.odd_mass_totient_le m hm
    _ ≤ 2 * (Real.exp 24 * 3 * Real.exp 2 * Real.log L) :=
      mul_le_mul_of_nonneg_left (hmass.trans hp) (by norm_num)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hlogL (show 0 ≤ 6 * Real.exp 24 * Real.exp 2 by positivity)
      nlinarith

/-- LEAF. Unit U-1532. Lemma 7, p. 135, for g = 2: there are `d` and `C` with
`n/φ(n) ≤ C Σ μ(q)²/φ(q)` over odd `q ∣ n`, `q ≤ log^d n`, for every `n ≥ 3`. -/
theorem lemma7 : ∃ d : ℕ, ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
    (n : ℝ) / n.totient ≤
      C * ∑ q ∈ n.divisors.filter (fun q : ℕ => Odd q ∧ (q : ℝ) ≤ Real.log n ^ d),
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient := by
  exact LeanLab.Romanov.Decomp134b.lemma7

open LeanLab.Linnik.U1464Display20
open LeanLab.Linnik.U1466Display17

/-- Gallagher 1975 p.136 proof of Lemma 8. The totient ratio is bounded by twice
the odd squarefree divisor weight, with both sides zero at the zero integer. -/
theorem totient_ratio_le_weight (h : ℤ) :
    (h.natAbs : ℝ) / h.natAbs.totient ≤ 2 * FD 0 h := by
  classical
  by_cases hh : h = 0
  · simp [hh, FD]
  have hn : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have he : h.natAbs.divisors.filter (fun d => 0 < d) = h.natAbs.divisors := by
    apply filter_eq_self.mpr
    intro d hd
    exact Nat.pos_of_mem_divisors hd
  rw [FD, if_neg hh, he, ← prod_expand hn]
  rw [LeanLab.Romanov.Decomp134b.totient_ratio_eq_prod _ (Nat.pos_of_ne_zero hn)]
  let P := h.natAbs.primeFactors
  have htwo : (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1)) ≤
      2 * ∏ p ∈ P.erase 2, (p : ℝ) / ((p : ℝ) - 1) := by
    by_cases h2 : 2 ∈ P
    · nth_rw 1 [← insert_erase h2]
      rw [prod_insert (notMem_erase _ _)]
      norm_num
    · rw [erase_eq_of_notMem h2]
      have h0 : 0 ≤ ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1) := by
        apply prod_nonneg
        intro p hp
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        exact div_nonneg (by positivity) (by linarith)
      linarith
  have heP : P.erase 2 = P.filter (fun p => 2 < p) := by
    ext p
    simp only [mem_erase, mem_filter]
    constructor
    · rintro ⟨hp2, hp⟩
      have hpr := (Nat.prime_of_mem_primeFactors hp).two_le
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hp2⟩
      exact ⟨by omega, hp⟩
  rw [heP] at htwo
  refine htwo.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  apply prod_le_prod₀
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
    apply (div_le_div_iff₀ (by linarith : 0 < (p : ℝ) - 1) (by linarith : 0 < (p : ℝ) - 2)).mpr
    nlinarith


/-- Gallagher 1975 p.136 proof of Lemma 8. The weight of one free exponent is linear
when the fixed integer has at most twice the exponent length in binary digits. -/
theorem one_coordinate_weight {L : ℕ} (hL : 1 ≤ L) (m : ℤ)
    (hm : m.natAbs ≤ 2 ^ (2 * L + 2)) :
    ∑ x : Fin L, FD 0 (hval m x) ≤
      (R0tail 0 + 18 * Real.exp 24 * Real.exp 2) * L := by
  let B := 2 ^ (2 * L + 4)
  have hB : ∀ x : Fin L, (hval m x).natAbs ≤ B := by
    intro x
    have hpow : 2 ^ ((x : ℕ) + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow' : 2 ^ L ≤ 2 ^ (2 * L + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hab := Int.natAbs_sub_le (2 ^ ((x : ℕ) + 1)) m
    have hab' : (hval m x).natAbs ≤ 2 ^ ((x : ℕ) + 1) + m.natAbs := by simpa [hval] using hab
    dsimp [B]
    rw [show 2 * L + 4 = (2 * L + 2) + 2 by omega, pow_add]
    omega
  have hmain := sum_FD_le 0 L B m hB
  have htail := sum_tail_le LeanLab.Linnik.U1474R0.r0Summable 0 B
  have hdiv := sum_dvd_le 0 B (Pm_ne_zero L m)
  have hprod : Pm L m ≤ B ^ L := by
    unfold Pm
    calc
      _ ≤ B ^ #((univ : Finset (Fin L)).filter (fun x : Fin L => hval m x ≠ 0)) :=
        prod_le_pow_card _ _ _ (fun x hx => hB x)
      _ ≤ B ^ L := Nat.pow_le_pow_right (by dsimp [B]; positivity)
        ((card_filter_le _ _).trans_eq (by simp))
  have hcard : (Pm L m).primeFactors.card ≤ 2 * (2 * L + 4) ^ 2 := by
    apply card_pf_le (Pm_ne_zero L m)
    calc
      _ ≤ B ^ L := hprod
      _ = 2 ^ ((2 * L + 4) * L) := by dsimp [B]; rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hp := prod_bound LeanLab.Linnik.U1469Mertens.oddPrimes_prod_le
    (show 2 ≤ 2 * L + 4 by omega) hcard
  rw [max_eq_left (Real.exp_pos 24).le] at hp
  have hlog : Real.log ((2 * L + 4 : ℕ) : ℝ) ≤ 6 * L := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((2 * L + 4 : ℕ) : ℝ) by positivity)
    push_cast at h ⊢
    have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have h1 := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have h2 := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ Real.exp 24 * 3 * Real.exp 2 by positivity)
  nlinarith


/-- LEAF. Unit U-1532. Lemma 8, p. 136, A. I. Vinogradov's bound: for `1 ≤ k ≤ N`, `N ≥ 2`,
`L = [log₂ N]`, `Σ_{n ≠ 0} r_{k,k}(n) |n|/φ(|n|) ≤ C L^{2k}` with an absolute `C`. -/
theorem lemma8 : ∃ C : ℝ, ∀ k N : ℕ, 1 ≤ k → k ≤ N → 2 ≤ N →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) ≤ C * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  let A : ℝ := R0tail 0 + 18 * Real.exp 24 * Real.exp 2
  refine ⟨2 * A, fun k N hk hkN hN => ?_⟩
  let L := Nat.log 2 N
  have hL : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have hNpow : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkey (ν : Fin j → Fin L) (μ : Fin (j + 1) → Fin L) :
      ∑ x : Fin L, ((dif (Fin.cons x ν, μ)).natAbs : ℝ) /
        (dif (Fin.cons x ν, μ)).natAbs.totient ≤ (2 * A) * L := by
    let m : ℤ := (sv μ : ℤ) - sv ν
    have he (x : Fin L) : dif (Fin.cons x ν, μ) = hval m x := by
      rw [dif, sv_cons]
      dsimp [hval, m]
      push_cast
      ring
    have hm : m.natAbs ≤ 2 ^ (2 * L + 2) := by
      have hμ := LeanLab.Linnik.U1434Lemma21.sv_le μ
      have hν := LeanLab.Linnik.U1434Lemma21.sv_le ν
      have hμ' : sv μ ≤ N * 2 ^ L := hμ.trans (Nat.mul_le_mul_right _ hkN)
      have hν' : sv ν ≤ N * 2 ^ L := hν.trans (Nat.mul_le_mul_right _ (by omega))
      have hnat : m.natAbs ≤ N * 2 ^ L := by dsimp [m]; omega
      calc
        _ ≤ N * 2 ^ L := hnat
        _ ≤ 2 ^ (L + 1) * 2 ^ L := Nat.mul_le_mul_right _ hNpow.le
        _ ≤ 2 ^ (2 * L + 2) := by rw [← pow_add]; apply Nat.pow_le_pow_right (by norm_num); omega
    calc
      _ ≤ 2 * ∑ x : Fin L, FD 0 (hval m x) := by
        rw [mul_sum]
        exact sum_le_sum (fun x _ => by rw [he]; exact totient_ratio_le_weight _)
      _ ≤ 2 * (A * L) := mul_le_mul_of_nonneg_left (one_coordinate_weight hL m hm) (by norm_num)
      _ = _ := by ring
  have heq : (∑ x : pairs (j + 1) L with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / (dif x).natAbs.totient) =
      ∑ x : pairs (j + 1) L, ((dif x).natAbs : ℝ) / (dif x).natAbs.totient := by
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    by_cases hh : dif x = 0 <;> simp [hh]
  change (∑ x : pairs (j + 1) L with dif x ≠ 0, _) ≤ _
  rw [heq, Fintype.sum_prod_type, sum_cons]
  calc
    _ = ∑ ν : Fin j → Fin L, ∑ μ : Fin (j + 1) → Fin L, ∑ x : Fin L,
        ((dif (Fin.cons x ν, μ)).natAbs : ℝ) / (dif (Fin.cons x ν, μ)).natAbs.totient := by
      exact sum_congr rfl (fun _ _ => sum_comm)
    _ ≤ ∑ _ν : Fin j → Fin L, ∑ _μ : Fin (j + 1) → Fin L, (2 * A) * L :=
      sum_le_sum (fun ν _ => sum_le_sum (fun μ _ => hkey ν μ))
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have he : 2 * (j + 1) = j + (j + 1) + 1 := by omega
      rw [he, pow_add, pow_add]
      ring

/-- ASSEMBLY, CONDITIONAL ON the leaves `dvd_Mprod`, `three_le_Mprod`, `log_Mprod_le`,
`sum_divisors_eq_prod`, `prod_le_two_mul_div_totient` and `div_totient_le_loglog`.
Lemma 4, p. 133, for g = 2: `Σ μ(q)² q / φ(q)² ≪ log x` over odd `q` with `e(q) ≤ x`, here over
any finite range `1 ≤ q ≤ Q`, uniformly in `Q`. -/
theorem lemma4 : ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → ∀ Q : ℕ,
    ∑ q ∈ Icc 1 Q with Odd q ∧ ordTwo q ≤ x,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 ≤
        C * Real.log x := by
  obtain ⟨C, hC⟩ := div_totient_le_loglog
  refine ⟨4 * C, fun x hx Q => ?_⟩
  set M := Mprod x with hMdef
  have hM3 : 3 ≤ M := three_le_Mprod hx
  have hM0 : 0 < M := by omega
  have hsub : (Icc 1 Q).filter (fun q => Odd q ∧ ordTwo q ≤ x) ⊆ M.divisors := by
    intro q hq
    rw [mem_filter] at hq
    exact Nat.mem_divisors.mpr ⟨dvd_Mprod hq.2.1 hq.2.2, hM0.ne'⟩
  have h1 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2)
    (fun q _ _ => by positivity)
  rw [sum_divisors_eq_prod hM0] at h1
  have h2 := prod_le_two_mul_div_totient hM0
  have h3 := hC M hM3
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hlogM1 : 1 < Real.log M := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hll0 : 0 < Real.log (Real.log M) := Real.log_pos hlogM1
  have htot : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM0
  have hratio : 0 < (M : ℝ) / M.totient := div_pos (by linarith) htot
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have : C * Real.log (Real.log M) < 0 := mul_neg_of_neg_of_pos hneg hll0
    linarith
  have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogMle := log_Mprod_le x
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll : Real.log (Real.log M) ≤ 2 * Real.log x := by
    have hle : Real.log M ≤ (x : ℝ) ^ 2 := by
      calc Real.log M ≤ (x : ℝ) ^ 2 * Real.log 2 := hlogMle
        _ ≤ (x : ℝ) ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (x : ℝ) ^ 2 := by ring
    calc Real.log (Real.log M) ≤ Real.log ((x : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) hle
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  calc ∑ q ∈ Icc 1 Q with Odd q ∧ ordTwo q ≤ x,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2
      ≤ ∏ p ∈ M.primeFactors, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := h1
    _ ≤ 2 * ((M : ℝ) / M.totient) := h2
    _ ≤ 2 * (C * Real.log (Real.log M)) := by linarith
    _ ≤ 2 * (C * (2 * Real.log x)) := by
        have := mul_le_mul_of_nonneg_left hll hC0
        linarith
    _ = 4 * C * Real.log x := by ring

/-- Gallagher 1975 pp.133 and 135. The reciprocal totient square weight is bounded
by the existing odd squarefree Romanov weight. -/
theorem moebius_totient_le_weight {q : ℕ} (hq : Odd q) :
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 ≤ wt q := by
  classical
  by_cases hs : Squarefree q
  · have hmu : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
    rw [hmu, one_mul, wt, if_pos ⟨hq, hs⟩]
    have he := LeanLab.Romanov.Decomp134b.inverse_totient_prime_product q.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hs] at he
    have hprod : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hs]
      push_cast
      rfl
    calc
      (q : ℝ) / (q.totient : ℝ) ^ 2 = (q : ℝ) * ((1 : ℝ) / q.totient) ^ 2 := by ring
      _ = ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        rw [hprod, he, ← prod_pow, ← prod_mul_distrib]
        apply prod_congr rfl
        intro p hp
        rw [div_pow, one_pow, mul_one_div]
      _ ≤ _ := by
        apply prod_le_prod₀
        · intro p hp
          positivity
        · intro p hp
          have hpr := Nat.prime_of_mem_primeFactors hp
          have hne : p ≠ 2 := by
            intro heq
            exact hq.not_two_dvd_nat (heq ▸ Nat.dvd_of_mem_primeFactors hp)
          have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hpr.two_le; omega)
          apply (div_le_div_iff₀ (by nlinarith : 0 < ((p : ℝ) - 1) ^ 2)
            (by linarith : 0 < (p : ℝ) - 2)).mpr
          nlinarith
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, wt, hs]



/-- Gallagher 1975 p.135 after the second split. Explicit dyadic reciprocal order tail. -/
theorem order_weight_tail (S : Finset ℕ) (J : ℕ) :
    ∑ q ∈ S with Odd q ∧ 2 ^ J ≤ ordTwo q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q /
        (q.totient : ℝ) ^ 2 / ordTwo q ≤
      (Real.exp 24 * 3 * Real.exp 2 * Real.log 2) *
        (2 * (J : ℝ) + 4) / (2 : ℝ) ^ J := by
  classical
  let T := S.filter (fun q => Odd q ∧ 2 ^ J ≤ ordTwo q)
  let K : ℝ := Real.exp 24 * 3 * Real.exp 2 * Real.log 2
  have hfirst : (∑ q ∈ T, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q /
      (q.totient : ℝ) ^ 2 / ordTwo q) ≤ ∑ q ∈ T, wt q / (eps q : ℝ) := by
    apply sum_le_sum
    intro q hq
    exact div_le_div_of_nonneg_right (moebius_totient_le_weight (mem_filter.mp hq).2.1)
      (Nat.cast_nonneg _)
  have hindex : ∀ j ∈ T.image LeanLab.Linnik.U1474R0.jd, J ≤ j := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hj
    apply Nat.le_log_of_pow_le (by norm_num)
    exact (mem_filter.mp hq).2.2
  have hfib := Finset.sum_fiberwise_of_maps_to (s := T)
    (t := T.image LeanLab.Linnik.U1474R0.jd) (g := LeanLab.Linnik.U1474R0.jd)
    (fun q hq => mem_image_of_mem _ hq) (fun q => wt q / (eps q : ℝ))
  have hgroups : (∑ q ∈ T, wt q / (eps q : ℝ)) ≤
      ∑ j ∈ T.image LeanLab.Linnik.U1474R0.jd, LeanLab.Linnik.U1474R0.g j := by
    rw [← hfib]
    apply sum_le_sum
    intro j hj
    apply le_trans ?_ (LeanLab.Linnik.U1474R0.dyadic_le S j)
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨hqT, hqj⟩ := mem_filter.mp hq
      exact mem_filter.mpr ⟨(mem_filter.mp hqT).1, (mem_filter.mp hqT).2.1, hqj⟩
    · intro q hq hqT
      exact div_nonneg (wt_nonneg _) (Nat.cast_nonneg _)
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlinear : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := (1 / 2 : ℝ)) 1 (by norm_num)
  have heq (n : ℕ) : LeanLab.Linnik.U1474R0.g (J + n) =
      K * (1 / 2 : ℝ) ^ J * ((n : ℝ) * (1 / 2 : ℝ) ^ n +
        ((J : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    simp only [LeanLab.Linnik.U1474R0.g, Nat.cast_add, pow_add, K]
    ring
  have hshift : Summable (fun n : ℕ => LeanLab.Linnik.U1474R0.g (J + n)) := by
    simp_rw [heq]
    exact (hlinear.add (hgeom.mul_left _)).mul_left _
  have hsum : (∑' n : ℕ, LeanLab.Linnik.U1474R0.g (J + n)) =
      K * (2 * (J : ℝ) + 4) / (2 : ℝ) ^ J := by
    simp_rw [heq]
    rw [tsum_mul_left, hlinear.tsum_add (hgeom.mul_left _), tsum_mul_left,
      tsum_coe_mul_geometric_of_norm_lt_one (by norm_num),
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    rw [div_pow]
    ring
  let U := T.image LeanLab.Linnik.U1474R0.jd
  have hsub : U ⊆ Ico J (U.sup id + 1) := by
    intro j hj
    exact mem_Ico.mpr ⟨hindex j hj, Nat.lt_succ_of_le (le_sup (f := id) hj)⟩
  have htail : (∑ j ∈ U, LeanLab.Linnik.U1474R0.g j) ≤
      ∑' n : ℕ, LeanLab.Linnik.U1474R0.g (J + n) := by
    calc
      _ ≤ ∑ j ∈ Ico J (U.sup id + 1), LeanLab.Linnik.U1474R0.g j :=
        sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => LeanLab.Linnik.U1474R0.g_nonneg j)
      _ = ∑ n ∈ range (U.sup id + 1 - J), LeanLab.Linnik.U1474R0.g (J + n) := by
        rw [sum_Ico_eq_sum_range]
      _ ≤ _ := hshift.sum_le_tsum _ (fun n _ => LeanLab.Linnik.U1474R0.g_nonneg _)
  exact (hfirst.trans (hgroups.trans htail)).trans_eq hsum



/-- Gallagher 1975 p.135. The reciprocal order tail is bounded by log E divided by E. -/
theorem order_weight_tail_log : ∃ C : ℝ, ∀ E : ℕ, 2 ≤ E → ∀ S : Finset ℕ,
    ∑ q ∈ S with Odd q ∧ E < ordTwo q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q /
        (q.totient : ℝ) ^ 2 / ordTwo q ≤ C * Real.log E / E := by
  classical
  let B : ℝ := Real.exp 24 * 3 * Real.exp 2
  refine ⟨12 * B, fun E hE S => ?_⟩
  let J := Nat.log 2 E
  have hJ : 1 ≤ J := Nat.le_log_of_pow_le (by norm_num) (by simpa using hE)
  have hpow : 2 ^ J ≤ E := Nat.pow_log_le_self 2 (by omega)
  have hup : E < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) E
  have hER : (0 : ℝ) < E := by exact_mod_cast (show 0 < E by omega)
  have hPR : (0 : ℝ) < 2 ^ J := by positivity
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (J : ℝ) * Real.log 2 ≤ Real.log E := by
    have hpR : (2 : ℝ) ^ J ≤ E := by exact_mod_cast hpow
    have hh := Real.log_le_log hPR hpR
    rwa [Real.log_pow] at hh
  have hupper : (E : ℝ) ≤ 2 * (2 : ℝ) ^ J := by
    have hh : (E : ℝ) < (2 : ℝ) ^ (J + 1) := by exact_mod_cast hup
    rw [pow_succ] at hh
    linarith
  have hnum : Real.log 2 * (2 * (J : ℝ) + 4) ≤ 6 * Real.log E := by
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hratio : Real.log 2 * (2 * (J : ℝ) + 4) / (2 : ℝ) ^ J ≤
      12 * Real.log E / E := by
    apply (div_le_div_iff₀ hPR hER).mpr
    calc
      _ ≤ (6 * Real.log E) * E := mul_le_mul_of_nonneg_right hnum hER.le
      _ ≤ (6 * Real.log E) * (2 * (2 : ℝ) ^ J) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by ring
  have hsub : S.filter (fun q => Odd q ∧ E < ordTwo q) ⊆
      S.filter (fun q => Odd q ∧ 2 ^ J ≤ ordTwo q) := by
    intro q hq
    obtain ⟨hqS, hqo, hqE⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hqS, hqo, by omega⟩
  calc
    _ ≤ ∑ q ∈ S with Odd q ∧ 2 ^ J ≤ ordTwo q,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q /
          (q.totient : ℝ) ^ 2 / ordTwo q :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ (B * Real.log 2) * (2 * (J : ℝ) + 4) / (2 : ℝ) ^ J := order_weight_tail S J
    _ = B * (Real.log 2 * (2 * (J : ℝ) + 4) / (2 : ℝ) ^ J) := by ring
    _ ≤ B * (12 * Real.log E / E) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring


/-- Gallagher 1975 pp.135 and 136. The nonnegative reciprocal order series converges. -/
theorem order_weight_summable : Summable (fun q : ℕ => if Odd q then
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q /
      (q.totient : ℝ) ^ 2 / ordTwo q else 0) := by
  apply Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity) ?_
    LeanLab.Linnik.U1474R0.r0Summable
  intro q
  by_cases hq : Odd q
  · rw [if_pos hq]
    exact div_le_div_of_nonneg_right (moebius_totient_le_weight hq) (Nat.cast_nonneg _)
  · simp [hq, wt]


/-- Gallagher 1975 p.135. The second coefficient sum after the order split is logarithmic. -/
theorem totient_square_sum_le_log {R : ℕ} (hR : 2 ≤ R) :
    ∑ q ∈ Icc 1 R with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 ≤
      Real.exp 24 * Real.log R := by
  classical
  let P := oddPrimesUpTo R
  let M := ∏ p ∈ P, p
  let T := (Icc 1 R).filter Odd
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (mem_filter.mp hp).2.1
  have hM : M ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hprime p hp).ne_zero)
  have hpf : M.primeFactors = P := Nat.primeFactors_prod hprime
  have hodd : P.filter (fun p => 2 < p) = P := by
    apply filter_eq_self.mpr
    intro p hp
    exact (mem_filter.mp hp).2.2
  have hsf : (∑ q ∈ T, wt q) = ∑ q ∈ T.filter Squarefree, wt q := by
    symm
    apply sum_filter_of_ne
    intro q hq hw
    by_contra hs
    exact hw (by simp [wt, hs])
  have hsub : T.filter Squarefree ⊆ M.divisors := by
    intro q hq
    obtain ⟨hqT, hqs⟩ := mem_filter.mp hq
    obtain ⟨hqI, hqo⟩ := mem_filter.mp hqT
    have hqpos : 0 < q := (mem_Icc.mp hqI).1
    have hqp : q.primeFactors ⊆ P := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hpq : p ≤ q := Nat.le_of_dvd hqpos hpd
      have hp2 : p ≠ 2 := by
        intro he
        exact hqo.not_two_dvd_nat (he ▸ hpd)
      have hp3 : 2 < p := by have := hpr.two_le; omega
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (by have := (mem_Icc.mp hqI).2; omega), hpr, hp3⟩
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hM⟩
    rw [← Nat.prod_primeFactors_of_squarefree hqs]
    exact prod_dvd_prod_of_subset q.primeFactors P id hqp
  calc
    _ ≤ ∑ q ∈ T, wt q := by
      apply sum_le_sum
      intro q hq
      exact moebius_totient_le_weight (mem_filter.mp hq).2
    _ = ∑ q ∈ T.filter Squarefree, wt q := hsf
    _ ≤ ∑ q ∈ M.divisors, wt q :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => wt_nonneg q)
    _ = ∏ p ∈ P, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
      rw [← prod_expand hM, hpf, hodd]
    _ ≤ _ := LeanLab.Linnik.U1469Mertens.oddPrimes_prod_le R hR


open LeanLab.Linnik.Task37Fourier

/-- Gallagher 1975 p.135. The exponential sum at a rational point is its finite character sum. -/
theorem rational_Gs_eq_character_sum {q : ℕ} [NeZero q] (L : ℕ) (a : ZMod q) :
    LeanLab.Linnik.U1426ChainWire.Gs L ((a.val : ℝ) / q) =
      ∑ μ : Fin L, ZMod.stdAddChar (a * 2 ^ ((μ : ℕ) + 1)) := by
  rw [LeanLab.Linnik.U1434Lemma21.Gs_fin]
  apply sum_congr rfl
  intro μ hμ
  have he : a * (2 : ZMod q) ^ ((μ : ℕ) + 1) =
      ((a.val * 2 ^ ((μ : ℕ) + 1) : ℕ) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [he, char_nat_exp]
  congr 1
  push_cast
  ring


/-- Gallagher 1975 p.135. Complete rational grid moments count divisible tuple differences. -/
theorem Gs_grid_moment_eq {q : ℕ} [NeZero q] (k L : ℕ) :
    ∑ a : ZMod q, ‖LeanLab.Linnik.U1426ChainWire.Gs L ((a.val : ℝ) / q)‖ ^ (2 * k) =
      q * (#{x : pairs k L | (q : ℤ) ∣ dif x} : ℝ) := by
  classical
  have hpow (a : ZMod q) : (∑ μ : Fin L, ZMod.stdAddChar (a * 2 ^ ((μ : ℕ) + 1))) ^ k =
      ∑ ν : Fin k → Fin L, ZMod.stdAddChar (a * (sv ν : ZMod q)) := by
    rw [Fintype.sum_pow]
    apply sum_congr rfl
    intro ν hν
    rw [char_prod]
    congr 1
    simp only [sv, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, mul_sum]
  have hn (a : ZMod q) :
      ((‖∑ μ : Fin L, ZMod.stdAddChar (a * 2 ^ ((μ : ℕ) + 1))‖ ^ (2 * k) : ℝ) : ℂ) =
        (∑ μ : Fin L, ZMod.stdAddChar (a * 2 ^ ((μ : ℕ) + 1))) ^ k *
          (starRingEnd ℂ) ((∑ μ : Fin L, ZMod.stdAddChar (a * 2 ^ ((μ : ℕ) + 1))) ^ k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  have hh (a : ZMod q) :
      (∑ μ : Fin L, ZMod.stdAddChar (a * 2 ^ ((μ : ℕ) + 1))) ^ k *
        (starRingEnd ℂ) ((∑ μ : Fin L, ZMod.stdAddChar (a * 2 ^ ((μ : ℕ) + 1))) ^ k) =
      ∑ ν : Fin k → Fin L, ∑ μ : Fin k → Fin L,
        ZMod.stdAddChar (a * ((sv ν : ZMod q) - (sv μ : ZMod q))) := by
    rw [hpow, map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro ν hν
    apply sum_congr rfl
    intro μ hμ
    rw [char_star, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hc : cntAll k k L q = (#{x : pairs k L | (q : ℤ) ∣ dif x} : ℝ) := by
    rw [cntAll, ← Fintype.sum_prod_type', sum_boole]
    rfl
  have hcomplex : ((∑ a : ZMod q,
      ‖LeanLab.Linnik.U1426ChainWire.Gs L ((a.val : ℝ) / q)‖ ^ (2 * k) : ℝ) : ℂ) =
        (q : ℂ) * (cntAll k k L q : ℂ) := by
    simp_rw [rational_Gs_eq_character_sum, Complex.ofReal_sum, hn, hh]
    exact tuple_orthogonality k k L
  rw [hc] at hcomplex
  exact_mod_cast hcomplex


/-- Gallagher 1975 p.135. Lemma 5 gives the complete grid upper moment bound. -/
theorem Gs_grid_moment_le {q : ℕ} [NeZero q] (hq : Odd q) {k : ℕ} (hk : 1 ≤ k) (L : ℕ) :
    ∑ a : ZMod q, ‖LeanLab.Linnik.U1426ChainWire.Gs L ((a.val : ℝ) / q)‖ ^ (2 * k) ≤
      q * ((L : ℝ) ^ (2 * k) / ordTwo q + (L : ℝ) ^ (2 * k - 1)) := by
  rw [Gs_grid_moment_eq]
  exact mul_le_mul_of_nonneg_left (card_dvd_dif_le hq hk L) (Nat.cast_nonneg _)


/-- Gallagher 1975 p.133 Lemma 3. Its modular form at a reduced rational point. -/
theorem rational_power_gap {q : ℕ} [NeZero q] (hq : Odd q) (a : (ZMod q)ˣ)
    {L : ℕ} (he : 2 ≤ ordTwo q) (heL : ordTwo q ≤ L) :
    ‖LeanLab.Linnik.U1426ChainWire.Gs L (((a : ZMod q).val : ℝ) / q)‖ <
      (1 - 1 / (16 * (ordTwo q : ℝ))) * L := by
  have hq1 : 1 < q := by
    by_contra hn
    have hqeq : q = 1 := by have := NeZero.ne q; omega
    subst q
    simp [ordTwo, Subsingleton.orderOf_eq] at he
  have : Fact (1 < q) := ⟨hq1⟩
  have ha0 : (a : ZMod q) ≠ 0 := a.isUnit.ne_zero
  have hav : 0 < (a : ZMod q).val := ZMod.val_pos.mpr ha0
  have haV : (a : ZMod q).val < q := ZMod.val_lt _
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have haR : (0 : ℝ) < (a : ZMod q).val := by exact_mod_cast hav
  have haQ : ((a : ZMod q).val : ℝ) < q := by exact_mod_cast haV
  have hα : ¬ ∃ z : ℤ, (((a : ZMod q).val : ℝ) / q) = z := by
    rintro ⟨z, hz⟩
    have hz0 : (0 : ℝ) < z := by rw [← hz]; positivity
    have hz1 : (z : ℝ) < 1 := by rw [← hz]; exact (div_lt_one hqR).mpr haQ
    have h0 : (0 : ℤ) < z := by exact_mod_cast hz0
    have h1 : z < (1 : ℤ) := by exact_mod_cast hz1
    omega
  have hper : ∃ z : ℤ, ((2 : ℝ) ^ ordTwo q - 1) *
      (((a : ZMod q).val : ℝ) / q) = z := by
    obtain ⟨t, ht⟩ := dvd_two_pow_ordTwo_sub_one hq
    have htR : (2 : ℝ) ^ ordTwo q - 1 = q * (t : ℝ) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) ht
      rw [Nat.cast_sub Nat.one_le_two_pow] at h
      push_cast at h
      exact h
    refine ⟨(t * (a : ZMod q).val : ℕ), ?_⟩
    rw [htR]
    push_cast
    field_simp
  have hG : LeanLab.Linnik.Gallagher1975Lemma1.G L (((a : ZMod q).val : ℝ) / q) =
      LeanLab.Linnik.U1426ChainWire.Gs L (((a : ZMod q).val : ℝ) / q) := by
    unfold LeanLab.Linnik.Gallagher1975Lemma1.G LeanLab.Linnik.U1426ChainWire.Gs
    apply sum_congr rfl
    intro ν hν
    unfold LeanLab.Linnik.Gallagher1975Lemma1.e LeanLab.Linnik.U1412Display53.eC
    congr 1
    push_cast
    ring
  rw [← hG]
  exact LeanLab.Linnik.Gallagher1975Lemma1.lemma3 hα hper he heL


/-- Gallagher 1975 pp.133 and 135. Primitive rational grid moments inherit the order gap. -/
theorem primitive_grid_moment_le {q : ℕ} [NeZero q] (hq : Odd q) {L : ℕ}
    (he : 2 ≤ ordTwo q) (heL : ordTwo q ≤ L) (k : ℕ) :
    (∑ a : (ZMod q)ˣ,
      ‖LeanLab.Linnik.U1426ChainWire.Gs L (((a : ZMod q).val : ℝ) / q)‖ ^ (2 * k)) ≤
      (q.totient : ℝ) * (((1 - 1 / (16 * (ordTwo q : ℝ))) * L) ^ (2 * k)) := by
  calc
    _ ≤ ∑ _a : (ZMod q)ˣ, (((1 - 1 / (16 * (ordTwo q : ℝ))) * L) ^ (2 * k)) := by
      apply sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ (norm_nonneg _) (rational_power_gap hq a he heL).le _
    _ = _ := by simp


end LeanLab.Linnik.Decomp1532a
