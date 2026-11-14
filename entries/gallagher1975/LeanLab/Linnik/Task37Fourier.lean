module

public import LeanLab.Linnik.Task37Display19

/-!
Li and Liu, https://arxiv.org/pdf/2610.15784, page 6, Section 3.
Identify the residue count P_d with the printed finite Fourier average.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Task37Fourier
open Finset
open LeanLab.Linnik.U1434Lemma21 (sv)
open LeanLab.Linnik.U1464Display20

noncomputable def zq (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (1 / (eps q : ℂ)) * ∑ t : Fin (eps q), ZMod.stdAddChar (a * 2 ^ ((t : ℕ) + 1))

lemma char_star {q : ℕ} [NeZero q] (x : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma char_prod {q n : ℕ} [NeZero q] (f : Fin n → ZMod q) :
    (∏ i, ZMod.stdAddChar (f i)) = ZMod.stdAddChar (∑ i, f i) := by
  have key (s : Finset (Fin n)) :
      (∏ i ∈ s, ZMod.stdAddChar (f i)) = ZMod.stdAddChar (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha, AddChar.map_add_eq_mul, ih]
  exact key univ

lemma zq_pow {q : ℕ} [NeZero q] (a : ZMod q) (I : ℕ) :
    zq q a ^ I = (1 / (eps q : ℂ)) ^ I *
      ∑ ν : Fin I → Fin (eps q), ZMod.stdAddChar (a * (sv ν : ZMod q)) := by
  unfold zq
  rw [mul_pow, Fintype.sum_pow]
  congr 1
  refine sum_congr rfl fun ν _ => ?_
  rw [char_prod]
  congr 1
  simp only [sv, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, mul_sum]

lemma zq_star_pow {q : ℕ} [NeZero q] (a : ZMod q) (J : ℕ) :
    (starRingEnd ℂ) (zq q a ^ J) = (1 / (eps q : ℂ)) ^ J *
      ∑ μ : Fin J → Fin (eps q), ZMod.stdAddChar (-(a * (sv μ : ZMod q))) := by
  rw [zq_pow, map_mul, map_pow, map_sum]
  simp only [map_div₀, map_one, map_natCast]
  congr 1
  exact sum_congr rfl fun μ _ => char_star _

lemma zq_mixed {q : ℕ} [NeZero q] (a : ZMod q) (I J : ℕ) :
    zq q a ^ I * (starRingEnd ℂ) (zq q a ^ J) =
      (1 / (eps q : ℂ)) ^ (I + J) *
        ∑ ν : Fin I → Fin (eps q), ∑ μ : Fin J → Fin (eps q),
          ZMod.stdAddChar (a * ((sv ν : ZMod q) - (sv μ : ZMod q))) := by
  rw [zq_pow, zq_star_pow, pow_add]
  rw [show ((1 / (eps q : ℂ)) ^ I * ∑ ν : Fin I → Fin (eps q),
      ZMod.stdAddChar (a * (sv ν : ZMod q))) *
      ((1 / (eps q : ℂ)) ^ J * ∑ μ : Fin J → Fin (eps q),
      ZMod.stdAddChar (-(a * (sv μ : ZMod q)))) =
      ((1 / (eps q : ℂ)) ^ I * (1 / (eps q : ℂ)) ^ J) *
        ((∑ ν : Fin I → Fin (eps q), ZMod.stdAddChar (a * (sv ν : ZMod q))) *
        (∑ μ : Fin J → Fin (eps q), ZMod.stdAddChar (-(a * (sv μ : ZMod q))))) by ring]
  congr 1
  rw [sum_mul_sum]
  refine sum_congr rfl fun ν _ => sum_congr rfl fun μ _ => ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

lemma tuple_orthogonality {q : ℕ} [NeZero q] (I J L : ℕ) :
    (∑ a : ZMod q, ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L,
      ZMod.stdAddChar (a * ((sv ν : ZMod q) - (sv μ : ZMod q)))) = (q : ℂ) * (cntAll I J L q : ℂ) := by
  rw [sum_comm]
  unfold cntAll
  simp only [Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun ν _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun μ _ => ?_
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  have hz := ZMod.intCast_zmod_eq_zero_iff_dvd ((sv ν : ℤ) - sv μ) q
  push_cast at hz
  by_cases h : (q : ℤ) ∣ ((sv ν : ℤ) - sv μ)
  · simp [h, hz.mpr h]
  · have hn : (sv ν : ZMod q) - (sv μ : ZMod q) ≠ 0 := fun h0 => h (hz.mp h0)
    simp [h, hn]

lemma residue_period {q c : ℕ} (hq : Odd q) (hc : c < eps q) :
    cntRes (eps q) (eps q) c = 1 := by
  rw [cntRes_eq (eps_pos hq) hc]
  simp [(eps_pos hq).ne']

lemma Pd_eq_period_count {q : ℕ} (hq : Odd q) (I J : ℕ) :
    Pd q I J = cntAll I J (eps q) q / (eps q : ℝ) ^ (I + J) := by
  rw [cntAll_eq I J (eps q) q (eps_pos hq)]
  unfold Pd
  rw [sum_div]
  refine sum_congr rfl fun t ht => ?_
  rw [sum_div]
  refine sum_congr rfl fun s hs => ?_
  have ht1 : (∏ a, cntRes (eps q) (eps q) (t a)) = 1 :=
    prod_eq_one fun a _ => residue_period hq (mem_range.mp (Fintype.mem_piFinset.mp ht a))
  have hs1 : (∏ b, cntRes (eps q) (eps q) (s b)) = 1 :=
    prod_eq_one fun b _ => residue_period hq (mem_range.mp (Fintype.mem_piFinset.mp hs b))
  rw [ht1, hs1]
  simp only [prod_const, card_univ, Fintype.card_fin, mul_one]
  rw [one_div_pow, one_div_pow, pow_add]
  ring

/-- The finite Fourier identity defining P_d in the paper. -/
theorem Pd_fourier {q : ℕ} [NeZero q] (hq : Odd q) (I J : ℕ) :
    (Pd q I J : ℂ) = (1 / (q : ℂ)) *
      ∑ a : ZMod q, zq q a ^ I * (starRingEnd ℂ) (zq q a ^ J) := by
  simp_rw [zq_mixed]
  rw [← mul_sum, tuple_orthogonality, Pd_eq_period_count hq]
  push_cast
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [one_div_pow]
  field_simp

/-- The standard additive character is the paper's exponential. -/
lemma char_nat_exp {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) =
      U1412Display53.eC ((n : ℝ) / q) := by
  have hn : (n : ZMod q) = ((n : ℤ) : ZMod q) := by simp
  rw [hn, ZMod.stdAddChar_coe]
  unfold U1412Display53.eC
  congr 1
  push_cast
  ring

/-- The period average has exactly the exponential normalization printed in Section 3. -/
lemma zq_exp {q : ℕ} [NeZero q] (a : ZMod q) :
    zq q a = (1 / (eps q : ℂ)) * ∑ t : Fin (eps q),
      U1412Display53.eC (((a.val * 2 ^ ((t : ℕ) + 1) : ℕ) : ℝ) / q) := by
  unfold zq
  congr 1
  refine sum_congr rfl fun t _ => ?_
  have he : a * (2 : ZMod q) ^ ((t : ℕ) + 1) =
      ((a.val * 2 ^ ((t : ℕ) + 1) : ℕ) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [he, char_nat_exp]

/-- Modulus one gives the constant Fourier average. -/
theorem zq_one (a : ZMod 1) : zq 1 a = 1 := by
  have he : eps 1 = 1 := Subsingleton.orderOf_eq (2 : ZMod 1)
  simp [zq, he, Subsingleton.elim a 0]

end LeanLab.Linnik.Task37Fourier


