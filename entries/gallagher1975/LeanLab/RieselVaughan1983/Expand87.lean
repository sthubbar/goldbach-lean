module

public import LeanLab.RieselVaughan1983.Lemma10Xi
public import LeanLab.RieselVaughan1983.Lemma11Char

/-!
P0032 Riesel-Vaughan 1983, (8.7), page 62: the character expansion of (8.3).
Unit U-1216, PC run 20261020T1103Z-23466. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Page 62: when d ≤ y/2 every prime p in I_k satisfies p ∤ d; hence, by (8.3),
  (8.7)  Σ_{d∣n} R_k(n) = (1/φ(d)) Σ_{χ mod d} χ(−1) |S_k(χ)|²,  (8.8) S_k(χ) = Σ_{p ∈ I_k} χ(p).

What is here, all PROVED unconditional:
* `T_eq_card_pairs`: (8.3), Σ_{d∣n, n ≤ x} R_k(n) = #{(p, p') primes in I_k : d ∣ p + p'} once
  ky + 2y ≤ x.
* `char_sum_pairs`: orthogonality, Σ_χ χ(−1) |Σ_{p∈P} χ(p)|² = φ(d) #{(p, p') ∈ P² : p + p' ≡ 0}
  for P prime to d.
* `isUnit_of_mem_Pset`: primes of I_k are prime to d when d ≤ y/2 < ky/2.
* `expansion_87`: (8.7), φ(d) Σ_{d∣n} R_k(n) = Σ_χ χ(−1)|S_k(χ)|² for 1 ≤ d ≤ y/2, k ≥ 1,
  ky + 2y ≤ x.
* `charSum`, `rest_expansion`: Rest_k = Σ_{d ≤ y/2, 2∤d} μ(d)/φ(d)² Σ_χ χ(−1)|S_k(χ)|².
KNOWN mathematics.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Expand87

open LeanLab.RieselVaughan1983.Xi

/-- (8.3) as a pair count: `Σ_{d∣n, n ≤ x} R_k(n) = #{(p, p') ∈ I_k² primes : d ∣ p + p'}`. -/
theorem T_eq_card_pairs {x y : ℝ} {k d : ℕ} (hy : 0 ≤ y) (hx : (k : ℝ) * y + 2 * y ≤ x) :
    T x y k d = (#((Xi.Pset y k ×ˢ Xi.Pset y k).filter (fun q : ℕ × ℕ => d ∣ q.1 + q.2)) : ℝ) := by
  unfold T Rk
  rw [← Nat.cast_sum]
  congr 1
  rw [← card_sigma]
  apply card_nbij' (fun np => (np.2, np.1 - np.2)) (fun q => ⟨q.1 + q.2, q.1⟩)
  · rintro ⟨n, p⟩ hnp
    simp only [mem_coe, mem_sigma, mem_filter, mem_range] at hnp
    obtain ⟨⟨-, hdn, hn0⟩, hpn, hp, hq, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hnp
    simp only [mem_coe, mem_filter, mem_product, Xi.Pset, mem_range]
    refine ⟨⟨⟨Nat.lt_succ_of_le (Nat.le_floor h2), hp, h1, h2⟩,
      ⟨Nat.lt_succ_of_le (Nat.le_floor h4), hq, h3, h4⟩⟩, ?_⟩
    have : p + (n - p) = n := by omega
    rw [this]; exact hdn
  · rintro ⟨p, q⟩ hpq
    simp only [mem_coe, mem_filter, mem_product, Xi.Pset, mem_range] at hpq
    obtain ⟨⟨⟨-, hp, h1, h2⟩, ⟨-, hq, h3, h4⟩⟩, hd⟩ := hpq
    simp only [mem_coe, mem_sigma, mem_filter, mem_range]
    have hsub : p + q - p = q := by omega
    have hpos : 0 < p + q := by have := hp.two_le; omega
    refine ⟨⟨?_, hd, hpos.ne'⟩, by omega, hp, by rw [hsub]; exact hq, ⟨h1, h2⟩, ?_⟩
    · -- p + q ≤ ⌊x⌋
      apply Nat.lt_succ_of_le
      apply Nat.le_floor
      push_cast
      linarith
    · rw [hsub]; exact ⟨h3, h4⟩
  · rintro ⟨n, p⟩ hnp
    simp only [mem_coe, mem_sigma, mem_filter, mem_range] at hnp
    obtain ⟨-, hpn, -⟩ := hnp
    simp only [Sigma.mk.injEq]
    refine ⟨by omega, HEq.rfl⟩
  · rintro ⟨p, q⟩ _
    simp

variable {d : ℕ} [NeZero d]

/-- Orthogonality with the twist `χ(−1)`:
`Σ_χ χ(−1) |Σ_{p∈P} χ(p)|² = φ(d) #{(p, p') ∈ P² : p + p' ≡ 0 mod d}`. -/
theorem char_sum_pairs (P : Finset ℕ) (hP : ∀ p ∈ P, IsUnit (p : ZMod d)) :
    ∑ χ : DirichletCharacter ℂ d, χ (-1) * ((‖∑ p ∈ P, χ p‖ ^ 2 : ℝ) : ℂ) =
      (d.totient : ℂ) * (#((P ×ˢ P).filter (fun q : ℕ × ℕ => d ∣ q.1 + q.2)) : ℂ) := by
  have key : ∀ χ : DirichletCharacter ℂ d, χ (-1) * ((‖∑ p ∈ P, χ p‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ P ×ˢ P, χ (q.2 : ZMod d)⁻¹ * χ (-(q.1 : ZMod d)) := by
    intro χ
    have hz : ((‖∑ p ∈ P, χ p‖ ^ 2 : ℝ) : ℂ) =
        (∑ p ∈ P, χ p) * starRingEnd ℂ (∑ p ∈ P, χ p) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hz, map_sum, Finset.sum_mul_sum, ← Finset.sum_product', mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [L11.conj_apply_unit χ (hP q.2 (Finset.mem_product.1 hq).2)]
    have : χ (-(q.1 : ZMod d)) = χ (-1) * χ (q.1 : ZMod d) := by
      rw [← map_mul, neg_one_mul]
    rw [this]; ring
  simp_rw [key]
  rw [Finset.sum_comm]
  have h2 : ∀ q ∈ P ×ˢ P, ∑ χ : DirichletCharacter ℂ d, χ (q.2 : ZMod d)⁻¹ * χ (-(q.1 : ZMod d)) =
      if d ∣ q.1 + q.2 then (d.totient : ℂ) else 0 := by
    intro q hq
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (hP q.2 (Finset.mem_product.1 hq).2)]
    have hiff : ((q.2 : ZMod d) = -(q.1 : ZMod d)) ↔ d ∣ q.1 + q.2 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, eq_neg_iff_add_eq_zero, add_comm]
    by_cases h : d ∣ q.1 + q.2
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun e => h (hiff.mp e)), if_neg h]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Page 62: when `d ≤ y/2`, `k ≥ 1`, every prime of `I_k` exceeds `d`, so is prime to `d`. -/
theorem isUnit_of_mem_Pset {y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 0 ≤ y) (hd : (d : ℝ) ≤ y / 2)
    {p : ℕ} (hp : p ∈ Xi.Pset y k) : IsUnit (p : ZMod d) := by
  rw [Xi.Pset, mem_filter] at hp
  obtain ⟨-, hpr, h1, -⟩ := hp
  rw [ZMod.isUnit_iff_coprime, hpr.coprime_iff_not_dvd]
  intro hdvd
  have hle : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne d)) hdvd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : (p : ℝ) ≤ d := by exact_mod_cast hle
  nlinarith

/-- **(8.7)**: for `1 ≤ d ≤ y/2`, `k ≥ 1` and `ky + 2y ≤ x`,
`φ(d) Σ_{d∣n} R_k(n) = Σ_{χ mod d} χ(−1) |S_k(χ)|²`. -/
theorem expansion_87 {x y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 0 ≤ y)
    (hx : (k : ℝ) * y + 2 * y ≤ x) (hd : (d : ℝ) ≤ y / 2) :
    (d.totient : ℂ) * (T x y k d : ℂ) =
      ∑ χ : DirichletCharacter ℂ d, χ (-1) * ((‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 : ℝ) : ℂ) := by
  rw [char_sum_pairs (Xi.Pset y k) (fun p hp => isUnit_of_mem_Pset hk hy hd hp),
    T_eq_card_pairs hy hx]
  push_cast
  rfl

/-- With `K = 200`, `y = x/202` and `1 ≤ k ≤ 200`, the cut `ky + 2y ≤ x` holds. -/
theorem cut_ok {x : ℝ} {k : ℕ} (hx : 0 ≤ x) (hk : k ≤ 200) :
    (k : ℝ) * (x / 202) + 2 * (x / 202) ≤ x := by
  have : (k : ℝ) ≤ 200 := by exact_mod_cast hk
  nlinarith

/-- Vacuity: `d = 3`, `y = 10`, `k = 1` meet the hypotheses of `expansion_87` with `x = 30`;
the prime `7` lies in `I_1 = (5, 15]`. -/
theorem expansion_vacuity : (3 : ℝ) ≤ 10 / 2 ∧ (1 : ℝ) * 10 + 2 * 10 ≤ 30 ∧ 7 ∈ Xi.Pset 10 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [Xi.Pset, mem_filter, mem_range]
  refine ⟨?_, by norm_num, by norm_num, by norm_num⟩
  have : ⌊(1 : ℕ) * (10 : ℝ) / 2 + 10⌋₊ = 15 := by norm_num
  rw [this]; norm_num


/-- `Σ_{χ mod d} χ(−1)|S_k(χ)|²`, zero at `d = 0`. -/
def charSum (y : ℝ) (k d : ℕ) : ℂ :=
  if h : d ≠ 0 then
    haveI : NeZero d := ⟨h⟩
    ∑ χ : DirichletCharacter ℂ d, χ (-1) * ((‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 : ℝ) : ℂ)
  else 0

/-- (8.7) inserted in the `d ≤ y/2` part of (8.5):
`Rest_k = Σ_{d ≤ y/2, 2∤d} μ(d)/φ(d)² Σ_{χ mod d} χ(−1)|S_k(χ)|²`. -/
theorem rest_expansion {x y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 0 ≤ y)
    (hx : (k : ℝ) * y + 2 * y ≤ x) :
    (RestK x y k : ℂ) = ∑ d ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd,
      (((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charSum y k d := by
  unfold RestK
  push_cast
  apply sum_congr rfl
  intro d hd
  rw [mem_filter, mem_Icc] at hd
  have hd0 : d ≠ 0 := by omega
  haveI : NeZero d := ⟨hd0⟩
  have hdy : (d : ℝ) ≤ y / 2 := by
    have : (d : ℝ) ≤ (⌊y / 2⌋₊ : ℝ) := by exact_mod_cast hd.1.2
    linarith [Nat.floor_le (show 0 ≤ y / 2 by linarith)]
  have hE := expansion_87 (x := x) (k := k) hk hy hx hdy
  have hφ : (d.totient : ℂ) ≠ 0 := by
    have : 0 < d.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)
    exact_mod_cast this.ne'
  unfold charSum
  rw [dif_pos hd0, ← hE, coef]
  push_cast
  field_simp

end LeanLab.RieselVaughan1983.Expand87
