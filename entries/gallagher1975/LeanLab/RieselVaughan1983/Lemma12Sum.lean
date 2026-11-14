module

public import Mathlib
public import LeanLab.RieselVaughan1983.Lemma11Char

/-!
P0032 Riesel-Vaughan 1983, Lemma 12, page 64: the elementary core.
PC run 20261020T0503Z-11094, unit U-1176. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

* `gfun`: the paper's multiplicative `g`, `g(2) = 0`, `g(p) = (2p - 1)/(p - 1)²` for `p > 2`,
  `g(p^k) = 0` for `k > 1`, written as `μ(n)² ∏_{p ∣ n} (2p - 1)/(p - 1)²` on odd `n`, `0` on even.
* `inv_totient_sq_eq`: for odd `d ≥ 1`, `1/φ(d)² = (1/d²) Σ_{r ∣ d} g(r)`; the paper states it for
  odd squarefree `d`, and it holds for every odd `d`.
* `lemma12_tail`: the page 64 display, `Σ_{a < d ≤ D, d odd} μ(d)²/φ(d)² ≤ (2/a) Σ_{r ≤ D} g(r)/r`;
  at `a = y/2` this is `(4/y) Σ_r g(r)/r`, the paper's bound before (2.24).
KNOWN mathematics.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section
namespace LeanLab.RieselVaughan1983.L12

/-- The local factor `(2p - 1)/(p - 1)²`. -/
def gp (p : ℕ) : ℝ := (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2

/-- The paper's `g`. -/
def gfun (n : ℕ) : ℝ := if Odd n then ((μ n : ℝ)) ^ 2 * ∏ p ∈ n.primeFactors, gp p else 0

/-- `g` as a real arithmetic function. -/
def G : ArithmeticFunction ℝ := ⟨gfun, by simp [gfun]⟩

lemma G_apply (n : ℕ) : G n = gfun n := rfl

lemma G_mult : G.IsMultiplicative := by
  refine ⟨by simp [G_apply, gfun], fun {m n} hmn => ?_⟩
  simp only [G_apply, gfun]
  by_cases hm : Odd m <;> by_cases hn : Odd n
  · rw [if_pos (Nat.odd_mul.2 ⟨hm, hn⟩), if_pos hm, if_pos hn,
      isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.Coprime.primeFactors_mul hmn,
      Finset.prod_union hmn.disjoint_primeFactors]
    push_cast; ring
  · rw [if_neg (fun h => hn (Nat.odd_mul.1 h).2), if_neg hn]; ring
  · rw [if_neg (fun h => hm (Nat.odd_mul.1 h).1), if_neg hm]; ring
  · rw [if_neg (fun h => hm (Nat.odd_mul.1 h).1), if_neg hm]; ring

/-- `h(n) = ∏_{p ∣ n, p > 2} (p/(p - 1))²`, equal to `n²/φ(n)²` on odd `n`. -/
def hfun (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2

def H : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else hfun n, by simp⟩

lemma H_apply {n : ℕ} (hn : n ≠ 0) : H n = hfun n := by
  show (if n = 0 then 0 else hfun n) = hfun n
  rw [if_neg hn]

lemma H_mult : H.IsMultiplicative := by
  refine ⟨by rw [H_apply one_ne_zero]; simp [hfun], fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [H]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [H]
  rw [H_apply (by positivity), H_apply hm.ne', H_apply hn.ne']
  unfold hfun
  rw [Nat.Coprime.primeFactors_mul hmn, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter hmn.disjoint_primeFactors)]

/-- `n²/φ(n)² = h(n)` for odd `n`. -/
lemma hfun_odd {n : ℕ} (hn : Odd n) : hfun n = (n : ℝ) ^ 2 / (n.totient : ℝ) ^ 2 := by
  have hn0 : n ≠ 0 := by have := hn.pos; omega
  have hfil : n.primeFactors.filter (· ≠ 2) = n.primeFactors := by
    apply Finset.filter_true_of_mem
    intro p hp h2
    rw [h2] at hp
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  unfold hfun
  rw [hfil, Finset.prod_pow, Finset.prod_div_distrib]
  have key := Nat.totient_mul_prod_primeFactors n
  have keyR : (n.totient : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) key
    push_cast at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  have hprod : (0 : ℝ) < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_pos; intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hphi : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have h : (∏ p ∈ n.primeFactors, (p : ℝ)) / ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) =
      (n : ℝ) / n.totient := by
    rw [div_eq_div_iff hprod.ne' hphi.ne']; linarith [keyR]
  rw [h, div_pow]

lemma GZ_mult : (G * (ζ : ArithmeticFunction ℝ)).IsMultiplicative :=
  G_mult.mul isMultiplicative_zeta.natCast

lemma on_prime_pow (p k : ℕ) (hp : p.Prime) :
    (G * (ζ : ArithmeticFunction ℝ)) (p ^ k) = H (p ^ k) := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, H_apply (pow_ne_zero _ hp.ne_zero)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [G_apply, gfun, hfun]
  unfold hfun
  rw [Nat.primeFactors_prime_pow hk.ne' hp]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [Finset.sum_range_succ']
    have hz : ∑ j ∈ range k, G (2 ^ (j + 1)) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      rw [G_apply, gfun, if_neg (by
        rw [Nat.not_odd_iff_even]; exact (Nat.even_pow' (by omega)).2 even_two)]
    rw [hz, Finset.filter_singleton, if_neg (by simp)]; simp [G_apply, gfun]
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.2 even_two) hodd
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : ∑ j ∈ range k', G (p ^ (j + 1 + 1)) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      rw [G_apply, gfun, if_pos hodd.pow, moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
      simp
    rw [hz, zero_add]
    simp only [pow_zero, zero_add, pow_one, G_apply, gfun]
    rw [if_pos hodd, if_pos odd_one, moebius_apply_prime hp, hp.primeFactors]
    simp only [Nat.primeFactors_one, Finset.prod_empty, Finset.prod_singleton, moebius_apply_one]
    rw [Finset.filter_singleton, if_pos hp2, Finset.prod_singleton]
    unfold gp
    field_simp
    ring

/-- `Σ_{r ∣ d} g(r) = d²/φ(d)²` for odd `d`. -/
theorem sum_divisors_g (d : ℕ) (hd : Odd d) :
    ∑ r ∈ d.divisors, gfun r = (d : ℝ) ^ 2 / (d.totient : ℝ) ^ 2 := by
  have hEq : G * (ζ : ArithmeticFunction ℝ) = H :=
    (IsMultiplicative.eq_iff_eq_on_prime_powers _ GZ_mult _ H_mult).2
      (fun p i hp => on_prime_pow p i hp)
  have h1 : (G * (ζ : ArithmeticFunction ℝ)) d = H d := by rw [hEq]
  rw [coe_mul_zeta_apply, H_apply (by have := hd.pos; omega), hfun_odd hd] at h1
  simpa [G_apply] using h1

/-- The paper's identity, page 64: `1/φ(d)² = (1/d²) Σ_{r ∣ d} g(r)` for odd `d`. -/
theorem inv_totient_sq_eq (d : ℕ) (hd : Odd d) :
    1 / (d.totient : ℝ) ^ 2 = (1 / (d : ℝ) ^ 2) * ∑ r ∈ d.divisors, gfun r := by
  rw [sum_divisors_g d hd]
  have : (d : ℝ) ≠ 0 := by have := hd.pos; positivity
  field_simp

lemma gfun_nonneg (n : ℕ) : 0 ≤ gfun n := by
  unfold gfun
  split_ifs with h
  · apply mul_nonneg (sq_nonneg _)
    apply Finset.prod_nonneg
    intro p hp
    unfold gp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    apply div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

/-- **Lemma 12's tail**, page 64: `Σ_{a < d ≤ D, d odd} μ(d)²/φ(d)² ≤ (2/a) Σ_{r ≤ D, r odd} g(r)/r`. -/
theorem lemma12_tail {a D : ℝ} (ha : 0 < a) :
    ∑ d ∈ (Icc (⌊a⌋₊ + 1) ⌊D⌋₊).filter Odd, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 ≤
      (2 / a) * ∑ r ∈ (Icc 1 ⌊D⌋₊).filter Odd, gfun r / r := by
  set Dset := (Icc (⌊a⌋₊ + 1) ⌊D⌋₊).filter Odd with hD
  set R := (Icc 1 ⌊D⌋₊).filter Odd with hR
  have step1 : ∑ d ∈ Dset, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 ≤
      ∑ d ∈ Dset, ∑ r ∈ d.divisors, gfun r * (1 / ((d : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro d hd
    have hodd : Odd d := (Finset.mem_filter.1 hd).2
    have hmu : ((μ d : ℝ)) ^ 2 ≤ 1 := by
      have h := (abs_moebius_le_one (n := d))
      have h' : |((μ d : ℝ))| ≤ 1 := by exact_mod_cast h
      nlinarith [abs_nonneg ((μ d : ℝ)), sq_abs ((μ d : ℝ))]
    calc ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 ≤ 1 / (d.totient : ℝ) ^ 2 := by gcongr
      _ = (1 / (d : ℝ) ^ 2) * ∑ r ∈ d.divisors, gfun r := inv_totient_sq_eq d hodd
      _ = ∑ r ∈ d.divisors, gfun r * (1 / ((d : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
  have step2 : ∑ d ∈ Dset, ∑ r ∈ d.divisors, gfun r * (1 / ((d : ℝ) ^ 2)) =
      ∑ r ∈ R, ∑ d ∈ Dset.filter (fun d => r ∣ d), gfun r * (1 / ((d : ℝ) ^ 2)) := by
    apply Finset.sum_comm'
    intro d r
    simp only [hD, hR, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hodd⟩, hrd, hd0⟩
      have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrd (by omega)
      exact ⟨⟨⟨⟨h1, h2⟩, hodd⟩, hrd⟩, ⟨⟨hr0, le_trans (Nat.le_of_dvd (by omega) hrd) h2⟩,
        Odd.of_dvd_nat hodd hrd⟩⟩
    · rintro ⟨⟨⟨⟨h1, h2⟩, hodd⟩, hrd⟩, _⟩
      exact ⟨⟨⟨h1, h2⟩, hodd⟩, hrd, by omega⟩
  have step3 : ∀ r ∈ R, ∑ d ∈ Dset.filter (fun d => r ∣ d), gfun r * (1 / ((d : ℝ) ^ 2)) ≤
      gfun r / r * (2 / a) := by
    intro r hr
    have hr1 : 1 ≤ r := by simp only [hR, mem_filter, mem_Icc] at hr; omega
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    set M := Icc (⌊a / r⌋₊ + 1) ⌊D⌋₊ with hM
    have hsub : Dset.filter (fun d => r ∣ d) ⊆ M.image (fun m => r * m) := by
      intro d hd
      simp only [hD, mem_filter, mem_Icc] at hd
      obtain ⟨⟨⟨h1, h2⟩, _⟩, ⟨m, rfl⟩⟩ := hd
      refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
      have hda : a < ((r * m : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one a
        have h1' : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ ((r * m : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h1' this ⊢; linarith
      push_cast at hda
      simp only [hM, mem_Icc]
      constructor
      · have : a / r < m := by rw [div_lt_iff₀ hrpos]; linarith
        have h3 := (Nat.floor_lt (div_nonneg ha.le hrpos.le)).2 this
        omega
      · have : m ≤ r * m := Nat.le_mul_of_pos_left m (by omega)
        omega
    have hinj : Set.InjOn (fun m => r * m) (M : Set ℕ) := by
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
    calc ∑ d ∈ Dset.filter (fun d => r ∣ d), gfun r * (1 / ((d : ℝ) ^ 2))
        ≤ ∑ d ∈ M.image (fun m => r * m), gfun r * (1 / ((d : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro d _ _; exact mul_nonneg (gfun_nonneg r) (by positivity)
      _ = ∑ m ∈ M, gfun r * (1 / (((r * m : ℕ) : ℝ) ^ 2)) :=
          Finset.sum_image (fun x hx y hy h => hinj hx hy h)
      _ = gfun r / r ^ 2 * ∑ m ∈ M, 1 / ((m : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          have hm1 : (0 : ℝ) < m := by
            simp only [hM, mem_Icc] at hm; exact_mod_cast (by omega : 0 < m)
          push_cast
          field_simp
      _ ≤ gfun r / r ^ 2 * (2 / (a / r)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (gfun_nonneg r) (by positivity))
          exact L11.sum_inv_sq_window (a / r) (div_pos ha hrpos) _
      _ = gfun r / r * (2 / a) := by field_simp
  calc ∑ d ∈ Dset, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2
      ≤ ∑ r ∈ R, gfun r / r * (2 / a) := step1.trans (step2 ▸ Finset.sum_le_sum step3)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Lemma 12 at the paper's cut `a = y/2`: the tail is at most `(4/y) Σ_r g(r)/r`. -/
theorem lemma12_half {y D : ℝ} (hy : 0 < y) :
    ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊D⌋₊).filter Odd, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 ≤
      (4 / y) * ∑ r ∈ (Icc 1 ⌊D⌋₊).filter Odd, gfun r / r := by
  have h := lemma12_tail (a := y / 2) (D := D) (by positivity)
  have e : 2 / (y / 2) = 4 / y := by field_simp; ring
  rwa [e] at h

/-- Sanity: `g(3) = 5/4`, so `1/φ(3)² = 1/4 = (1/9)(1 + 5/4)`. -/
theorem g_three : gfun 3 = 5 / 4 := by
  unfold gfun gp
  rw [if_pos (by decide), moebius_apply_prime Nat.prime_three, Nat.prime_three.primeFactors]
  norm_num

end LeanLab.RieselVaughan1983.L12
