module

public import LeanLab.KumchevLiu2007.Decomp1534c
public import LeanLab.PNTSieve.MertensUpper

/-!
Kumchev and Liu, arXiv 0801.0130, paper P0088. Route burst session 9, 2026-11-12.
Upstream helper file for `Decomp129`: the lower half of page 13 display 48 for
j equal to 2. The prime factor lemmas `A2_prime_root_count`,
`nonzero_square_roots_le_two`, `A2_prime_norm_bound` and
`A2_prime_norm_le_inv_add` are copies of the proved lemmas of the same names in
`Decomp129b`, which imports `Decomp129` and so cannot be used there. They are
copied, not moved, so that no existing file changes.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task129a

open Real Complex LeanLab.KumchevLiu2007
open U1534
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Page 13 display 45 and page 14 display 46, computed by additive
character orthogonality. The nonzero square root count determines A2 at a prime. -/
theorem A2_prime_root_count (p : ℕ) [Fact p.Prime] (n : ℕ) :
    A2 n p = ((p : ℂ) - 1 - (p : ℂ) *
      (((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card : ℂ)) /
      ((p : ℂ) - 1) ^ 2 := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have std_int (a : ℤ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    rw [ZMod.stdAddChar_coe]
    unfold ee
    congr 1
    push_cast
    ring
  have std_nat (a : ℕ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    simpa using std_int (a : ℤ)
  have sum_range (f : ZMod p → ℂ) :
      ∑ a ∈ Finset.range p, f (a : ZMod p) = ∑ a : ZMod p, f a := by
    apply Finset.sum_bij (s := Finset.range p) (t := (Finset.univ : Finset (ZMod p))) (fun a _ => (a : ZMod p))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have coprime_iff (a : ℕ) : Nat.Coprime a p ↔ (a : ZMod p) ≠ 0 := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, ne_eq, ZMod.natCast_eq_zero_iff]
  have filtered (f : ZMod p → ℂ) :
      ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p), f (a : ZMod p) =
      ∑ a ∈ (Finset.univ.erase (0 : ZMod p)), f a := by
    rw [Finset.sum_filter]
    simp_rw [coprime_iff]
    rw [sum_range (fun a => if a ≠ 0 then f a else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  have std_neg (a : ℕ) : ee (-((a * n : ℕ) : ℝ) / p) =
      ZMod.stdAddChar (-((a : ZMod p) * (n : ZMod p))) := by
    have heq : -((a * n : ℕ) : ℝ) / p = ((-((a * n : ℕ) : ℤ) : ℤ) : ℝ) / p := by
      push_cast; ring
    rw [heq, std_int]
    push_cast
    rfl
  have gauss_eq (a : ℕ) : gaussS p a * ee (-((a*n : ℕ) : ℝ)/p) =
      ∑ x ∈ Finset.univ.erase (0 : ZMod p),
        ZMod.stdAddChar ((a : ZMod p) * (x ^ 2 - (n : ZMod p))) := by
    rw [std_neg]
    unfold gaussS
    simp_rw [std_nat, Nat.cast_mul, Nat.cast_pow]
    rw [filtered (fun x => ZMod.stdAddChar ((a : ZMod p) * x ^ 2)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hchar (t : ZMod p) :
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * t) =
        if t = 0 then (p : ℂ) - 1 else -1 := by
    have ht := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) t
      (ZMod.isPrimitive_stdAddChar p)
    have hs := Finset.sum_erase_add (s := Finset.univ)
      (f := fun a : ZMod p => ZMod.stdAddChar (a * t)) (Finset.mem_univ 0)
    simp only [zero_mul, AddChar.map_zero_eq_one] at hs
    rw [ht, ZMod.card] at hs
    by_cases ht0 : t = 0
    · simp only [ht0, ite_true] at hs ⊢
      linear_combination hs
    · simp only [ht0, ite_false, Nat.cast_zero] at hs ⊢
      linear_combination hs
  let s := Finset.univ.erase (0 : ZMod p)
  let R := s.filter (fun x => x ^ 2 = (n : ZMod p))
  have hg : ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
      gaussS p a * ee (-((a*n : ℕ) : ℝ)/p) =
      (p : ℂ) * (R.card : ℂ) - ((p : ℂ) - 1) := by
    simp_rw [gauss_eq]
    rw [filtered (fun a => ∑ x ∈ Finset.univ.erase (0 : ZMod p),
      ZMod.stdAddChar (a * (x ^ 2 - (n : ZMod p)))), Finset.sum_comm]
    simp_rw [hchar, sub_eq_zero]
    have heq (x : ZMod p) : (if x ^ 2 = (n : ZMod p) then (p : ℂ) - 1 else -1) =
        (p : ℂ) * (if x ^ 2 = (n : ZMod p) then 1 else 0) - 1 := by
      split_ifs <;> ring
    simp_rw [heq, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hR : (∑ x ∈ s, if x ^ 2 = (n : ZMod p) then (1 : ℂ) else 0) = R.card := by
      simp [R]
    change (p : ℂ) * (∑ x ∈ s, if x ^ 2 = (n : ZMod p) then (1 : ℂ) else 0) -
      (∑ x ∈ s, (1 : ℂ)) = _
    rw [hR]
    simp [s, ZMod.card, Nat.cast_sub hp.one_le]
  unfold A2
  rw [hg, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  norm_num only [Int.cast_neg, Int.cast_one, Nat.cast_sub hp.one_le, Nat.cast_one]
  change -1 / ((p : ℂ) - 1)^2 * ((p : ℂ) * (R.card : ℂ) - ((p : ℂ) - 1)) =
    ((p : ℂ) - 1 - (p : ℂ) * (R.card : ℂ)) / ((p : ℂ) - 1)^2
  ring

/-- Page 14 display 46. The root count used in the prime factor formula
is at most two, by the degree of X squared minus n. -/
theorem nonzero_square_roots_le_two (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card ≤ 2 := by
  let f : Polynomial (ZMod p) := Polynomial.X ^ 2 - Polynomial.C (n : ZMod p)
  have hf : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) _
  have hsub : ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).val ⊆ f.roots := by
    intro x hx
    apply (Polynomial.mem_roots hf).mpr
    have heq := (Finset.mem_filter.mp hx).2
    simpa [f] using sub_eq_zero.mpr heq
  have hc := Polynomial.card_le_degree_of_subset_roots hsub
  simpa only [f, Polynomial.natDegree_X_pow_sub_C] using hc

/-- Page 14 display 47 at a prime, with an explicit rational upper bound
from the root count formula. -/
theorem A2_prime_norm_bound (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖A2 n p‖ ≤ ((p : ℝ) + 1) / ((p : ℝ) - 1)^2 := by
  let R := (Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))
  have hp : p.Prime := Fact.out
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hR : (R.card : ℝ) ≤ 2 := by exact_mod_cast nonzero_square_roots_le_two p n
  have heq : A2 n p =
      ((((p : ℝ) - 1 - (p : ℝ) * (R.card : ℝ)) / ((p : ℝ) - 1)^2 : ℝ) : ℂ) := by
    rw [A2_prime_root_count]
    push_cast
    rfl
  have hd : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  have hm : (p : ℝ) * (R.card : ℝ) ≤ (p : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  have hn : 0 ≤ (p : ℝ) * (R.card : ℝ) := by positivity
  have habs : |(p : ℝ) - 1 - (p : ℝ) * (R.card : ℝ)| ≤ (p : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right habs hd.le

/-- Page 14 display 47 at a prime, with an explicit error constant. -/
theorem A2_prime_norm_le_inv_add (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖A2 n p‖ ≤ 1 / (p : ℝ) + 6 / (p : ℝ)^2 := by
  have hp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst p
    by_cases hn : n % 2 = 0
    · rw [A2_two_even hn]; norm_num
    · rw [A2_two_odd (by omega)]; norm_num
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  apply (A2_prime_norm_bound p n).trans
  have heq : 1 / (p : ℝ) + 6 / (p : ℝ)^2 = ((p : ℝ) + 6) / (p : ℝ)^2 := by
    field_simp
  rw [heq, div_le_div_iff₀ hd (by positivity : 0 < (p : ℝ)^2)]
  have hh : 0 ≤ ((p : ℝ) - 3) * (3 * (p : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-! ### Display 48, lower half, for j equal to 2. -/

/-- Real analysis: log of 1 minus x is at least minus x minus 2 x squared for x
in 0, 1/2, from Mathlib's Taylor bound for the logarithm. -/
theorem log_one_sub_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_nonneg h0] at h
  have hden : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  have := (abs_le.mp (h.trans hden)).1
  linarith

/-- The same in exponential form: 1 minus x is at least exp of minus x minus 2 x squared. -/
theorem exp_le_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  calc Real.exp (-x - 2 * x ^ 2) ≤ Real.exp (Real.log (1 - x)) :=
        Real.exp_le_exp.mpr (log_one_sub_ge h0 h1)
    _ = 1 - x := Real.exp_log (by linarith)

/-- Arithmetic for primes p at least 5 with x equal to 1/p plus 6/p squared,
the bound of page 14 display 47 at a prime in `A2_prime_norm_le_inv_add`. -/
theorem xp_facts {p : ℝ} (hp : 5 ≤ p) :
    0 ≤ 1 / p + 6 / p ^ 2 ∧ 1 / p + 6 / p ^ 2 ≤ 1 / 2 ∧
      (1 / p + 6 / p ^ 2) + 2 * (1 / p + 6 / p ^ 2) ^ 2 ≤ 1 / p + 16 * (p ^ 2)⁻¹ := by
  have hp0 : 0 < p := by linarith
  set u := 1 / p with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hu : u ≤ 1 / 5 := by
    rw [hu_def]; exact one_div_le_one_div_of_le (by norm_num) hp
  have e1 : 6 / p ^ 2 = 6 * u ^ 2 := by rw [hu_def]; field_simp
  have e2 : (p ^ 2)⁻¹ = u ^ 2 := by rw [hu_def]; field_simp
  rw [e1, e2]
  have h5 : (1 + 6 * u) ^ 2 ≤ 5 := by nlinarith
  have hsq : (u + 6 * u ^ 2) ^ 2 = u ^ 2 * (1 + 6 * u) ^ 2 := by ring
  refine ⟨by positivity, by nlinarith, ?_⟩
  rw [hsq]
  nlinarith [mul_le_mul_of_nonneg_left h5 (sq_nonneg u)]

/-- Route burst session 9. The split leaf `eq48_P2_lower` of `Decomp129`,
with the product written out, page 13 display 48 lower half for j equal to 2, proved with
c equal to exp of minus 44 and P0 equal to 2. The local factors at 2 and 3 are
2 and 3/2 on H2; for p at least 5 the factor is at least 1 minus 1/p minus 6/p
squared by display 47; the product is bounded below through the logarithm and
the lab Mertens bound, sum of 1/p up to N at most log log N plus 12. -/
theorem P2_lower_explicit :
    ∃ c P0 : ℝ, 0 < c ∧ 2 ≤ P0 ∧ ∀ P : ℝ, P0 ≤ P → ∀ n : ℕ, InH2 n →
      c / Real.log P ≤ ‖∏ p ∈ (Finset.range (⌊P⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)‖ := by
  refine ⟨Real.exp (-44), 2, Real.exp_pos _, le_rfl, ?_⟩
  intro P hP n hn
  set N := ⌊P⌋₊ with hN_def
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hP)
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNP : (N : ℝ) ≤ P := Nat.floor_le (by linarith)
  set S := (Finset.range (N + 1)).filter Nat.Prime with hS_def
  set x : ℕ → ℝ := fun p => if 5 ≤ p then 1 / (p : ℝ) + 6 / (p : ℝ) ^ 2 else 0 with hx_def
  have hx0 : ∀ p, 0 ≤ x p := by
    intro p; simp only [hx_def]; split_ifs with h
    · exact (xp_facts (by exact_mod_cast h)).1
    · exact le_rfl
  have hx1 : ∀ p, x p ≤ 1 / 2 := by
    intro p; simp only [hx_def]; split_ifs with h
    · exact (xp_facts (by exact_mod_cast h)).2.1
    · norm_num
  -- local factors
  have hloc : ∀ p ∈ S, 1 - x p ≤ ‖1 + U1534.A2 n p‖ := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    simp only [hx_def]
    split_ifs with h5
    · have : Fact p.Prime := ⟨hpp⟩
      have hb := A2_prime_norm_le_inv_add p n
      have ht : ‖(1 : ℂ)‖ ≤ ‖1 + U1534.A2 n p‖ + ‖U1534.A2 n p‖ := by
        have := norm_sub_le (1 + U1534.A2 n p) (U1534.A2 n p)
        simpa only [add_sub_cancel_right] using this
      rw [norm_one] at ht
      linarith
    · have hp23 : p = 2 ∨ p = 3 := by
        have := hpp.two_le
        interval_cases p <;> simp_all <;> norm_num at hpp
      rcases hp23 with rfl | rfl
      · rw [U1534.A2_two_even (by have := hn.2; omega)]
        norm_num
      · rw [U1534.A2_three_ne_one hn.1]
        have : (1 : ℂ) + 1 / 2 = ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        norm_num
  have hnorm : ‖∏ p ∈ (Finset.range (⌊P⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)‖ =
      ∏ p ∈ S, ‖1 + U1534.A2 n p‖ := by
    simp only [hS_def, hN_def]
    exact Complex.norm_prod _ _
  have hprod1 : ∏ p ∈ S, (1 - x p) ≤ ‖∏ p ∈ (Finset.range (⌊P⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)‖ := by
    rw [hnorm]
    exact Finset.prod_le_prod₀ (fun p _ => by linarith [hx1 p]) hloc
  have hprod2 : Real.exp (-∑ p ∈ S, (x p + 2 * x p ^ 2)) ≤ ∏ p ∈ S, (1 - x p) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le)
    intro p _
    have := exp_le_one_sub (hx0 p) (hx1 p)
    rwa [show -(x p + 2 * x p ^ 2) = -x p - 2 * x p ^ 2 by ring]
  -- the sum
  have hper : ∀ p ∈ S, x p + 2 * x p ^ 2 ≤ 1 / (p : ℝ) + 16 * ((p : ℝ) ^ 2)⁻¹ := by
    intro p _
    simp only [hx_def]
    split_ifs with h5
    · exact (xp_facts (by exact_mod_cast h5)).2.2
    · norm_num; positivity
  have hsum1 : ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log N) + 12 := by
    refine le_trans ?_ (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN2)
    apply le_of_eq
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [hS_def, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_lt.le, by omega⟩, h2⟩
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by omega, h2⟩
  have hsum2 : ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have hsub : S ⊆ Finset.Ioo 0 (N + 1) := by
      intro p hp
      simp only [hS_def, Finset.mem_filter, Finset.mem_range] at hp
      simp only [Finset.mem_Ioo]
      exact ⟨hp.2.pos, hp.1⟩
    calc ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo 0 (N + 1), ((i : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 / ((0 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 0 (N + 1)
      _ = 2 := by norm_num
  have hsum : ∑ p ∈ S, (x p + 2 * x p ^ 2) ≤ Real.log (Real.log N) + 44 := by
    calc ∑ p ∈ S, (x p + 2 * x p ^ 2)
        ≤ ∑ p ∈ S, (1 / (p : ℝ) + 16 * ((p : ℝ) ^ 2)⁻¹) := Finset.sum_le_sum hper
      _ = ∑ p ∈ S, (1 : ℝ) / p + 16 * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ Real.log (Real.log N) + 44 := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hexp : Real.exp (-44) / Real.log N ≤ ‖∏ p ∈ (Finset.range (⌊P⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)‖ := by
    refine le_trans ?_ (hprod2.trans hprod1)
    have : Real.exp (-44) / Real.log N = Real.exp (-(Real.log (Real.log N) + 44)) := by
      rw [show -(Real.log (Real.log N) + 44) = -44 + -Real.log (Real.log N) by ring,
        Real.exp_add, Real.exp_neg (Real.log (Real.log N)), Real.exp_log hlogN, div_eq_mul_inv]
    rw [this]
    exact Real.exp_le_exp.mpr (by linarith)
  refine le_trans ?_ hexp
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le hlogN
  exact Real.log_le_log (by linarith) hNP

end LeanLab.KumchevLiu2007.Task129a

