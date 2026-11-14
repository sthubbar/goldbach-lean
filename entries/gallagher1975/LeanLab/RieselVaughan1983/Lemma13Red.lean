module

public import LeanLab.RieselVaughan1983.Eq816

/-!
P0032 Riesel-Vaughan 1983, Lemma 13, pages 64 to 66, reduced to the single cited display (8.18).
Unit U-1242, PC run 20261020T1503Z-30533. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Page 66: by (8.16), Φ_k = ½ C Σ_{q ≤ w} μ(q) f(q) Σ*_{χ mod q} χ(−1)|S_k(χ)|². The term q = 1
is S_k²; the one primitive character mod 3 is odd, so the q = 3 term is ≥ 0; every other term
is ≥ −f(q) Σ*_{χ mod q}|S_k(χ)|². With F = max_{5 ≤ q ≤ w} f(q)/(0.361 + log(z/q)), attained at
q = 5 by `Lemma13Max.lemma13_max`, and (8.18),
  Σ_{5 ≤ r ≤ w} (0.361 + log(z/r)) Σ*_{χ mod r}|S_k(χ)|² ≤ S_k N_k − S_k²(0.361 + log z),
which the paper derives from Montgomery-Vaughan's weighted large sieve (2.6) and their Lemmas
3 and 8, one gets Φ_k ≥ ½ C (S_k² − F S_k N_k + F S_k²(0.361 + log z)), which is Lemma 13 with
z = (2N_k/3)^{1/2}, the z of (8.6), w = z/100.

What is here, PROVED unconditional unless marked:
* `card_Pset_eq`: #(primes in I_k) = S_k exactly, sharpening the lab's `card_Pset_le`.
* `Pq_one`: the q = 1 term is S_k².
* `odd_of_primitive_three`: the primitive characters mod 3 have χ(−1) = −1.
* `re_term_ge`: Re μ(q) f(q) P(q) ≥ −f(q) Σ*|S_k(χ)|².
* `Eq818`: (8.18), a cited Prop, NOT proved.
* `lemma13_of_818`: Lemma13P CONDITIONAL ON `Eq818`.
* `theorem_of_lemma5_818`: the 18-prime Theorem CONDITIONAL ON Lemma 5 at five rows, Lemma 6,
  (2.30), (2.31), (3.3) and `Eq818`.
KNOWN mathematics, the paper's route.
-/

@[expose] public section

open Finset Real ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Lemma13Red

open LeanLab.RieselVaughan1983.Delta LeanLab.RieselVaughan1983.Euler23
  LeanLab.RieselVaughan1983.Eq816 LeanLab.RieselVaughan1983.Xi

/-- `#(primes in I_k) = S_k`. -/
theorem card_Pset_eq (y : ℝ) (k : ℕ) (hy : 0 ≤ y) : (#(Xi.Pset y k) : ℝ) = Sk y k := by
  unfold Sk
  set a := (k : ℝ) * y / 2
  have ha : 0 ≤ a := by positivity
  have hdisj : Disjoint (Xi.Pset y k) ((range (⌊a⌋₊ + 1)).filter Nat.Prime) := by
    rw [disjoint_left]
    intro p hp hp'
    rw [Xi.Pset, mem_filter] at hp
    rw [mem_filter, mem_range] at hp'
    have : (p : ℝ) ≤ a := by
      have h1 : (p : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast (show p ≤ ⌊a⌋₊ by omega)
      linarith [Nat.floor_le ha]
    have h' : a < (p : ℝ) := hp.2.2.1
    linarith
  have heq : Xi.Pset y k ∪ (range (⌊a⌋₊ + 1)).filter Nat.Prime =
      (range (⌊a + y⌋₊ + 1)).filter Nat.Prime := by
    ext p
    rw [mem_union, mem_filter, mem_range, mem_filter, mem_range, Xi.Pset, mem_filter, mem_range]
    constructor
    · rintro (hp | hp)
      · exact ⟨hp.1, hp.2.1⟩
      · have : ⌊a⌋₊ ≤ ⌊a + y⌋₊ := Nat.floor_le_floor (by linarith)
        exact ⟨by omega, hp.2⟩
    · rintro ⟨h1, h2⟩
      by_cases h : p ≤ ⌊a⌋₊
      · exact Or.inr ⟨by omega, h2⟩
      · left
        refine ⟨h1, h2, ?_, ?_⟩
        · have : ⌊a⌋₊ < p := by omega
          exact (Nat.floor_lt ha).mp this
        · have hp : p ≤ ⌊a + y⌋₊ := by omega
          have := Nat.floor_le (show 0 ≤ a + y by linarith)
          have : (p : ℝ) ≤ (⌊a + y⌋₊ : ℝ) := by exact_mod_cast hp
          show (p : ℝ) ≤ a + y
          linarith
  rw [primeCounting_eq_card, primeCounting_eq_card, ← heq, card_union_of_disjoint hdisj]
  push_cast; ring

/-- Every value of a character mod `1` is `1`. -/
lemma char_one_apply (ψ : DirichletCharacter ℂ 1) (a : ZMod 1) : ψ a = 1 := by
  have : a = 1 := Subsingleton.elim _ _
  rw [this, map_one]

/-- The term `q = 1` of (8.16): `P(1) = S_k²`, with `S_k` the number of primes in `I_k`. -/
theorem Pq_one (y : ℝ) (k : ℕ) : Pq y k 1 = (((#(Xi.Pset y k) : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [Pq_eq_plain y k one_ne_zero]
  have hfil : (univ : Finset (DirichletCharacter ℂ 1)).filter (fun ψ => ψ.conductor = 1) =
      {1} := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    have hψ : ψ = 1 := MulChar.ext' fun a => by rw [char_one_apply, char_one_apply]
    subst hψ
    simp [DirichletCharacter.conductor_one]
  rw [hfil, sum_singleton]
  have hS : Spsi y k (1 : DirichletCharacter ℂ 1) = (#(Xi.Pset y k) : ℂ) := by
    unfold Spsi
    simp [char_one_apply]
  rw [hS, char_one_apply, one_mul]
  push_cast
  rw [Complex.norm_natCast]
  norm_cast

/-- The primitive characters mod `3` are odd: `χ(−1) = −1`. -/
theorem odd_of_primitive_three (ψ : DirichletCharacter ℂ 3) (hψ : ψ.conductor = 3) :
    ψ (-1) = -1 := by
  have hsq : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul, show ((-1 : ZMod 3) * -1) = 1 by decide, map_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exfalso
    have h1 : ψ = 1 := by
      apply MulChar.ext'
      intro a
      fin_cases a
      · show ψ 0 = (1 : DirichletCharacter ℂ 3) 0
        rw [MulChar.map_zero, MulChar.map_zero]
      · show ψ 1 = (1 : DirichletCharacter ℂ 3) 1
        rw [map_one, map_one]
      · have : (2 : ZMod 3) = -1 := by decide
        simp only [Fin.reduceFinMk, Fin.isValue]
        show ψ 2 = (1 : DirichletCharacter ℂ 3) 2
        rw [this, h]
        have hu : IsUnit (-1 : ZMod 3) := isUnit_one.neg
        rw [MulChar.one_apply hu]
    rw [h1, DirichletCharacter.conductor_one] at hψ
    norm_num at hψ
  · exact h

/-- `Σ*_{χ mod r}|S_k(χ)|²` over the primitive characters mod `r`, zero at `r = 0`. -/
def Qr (y : ℝ) (k : ℕ) (r : ℕ) : ℝ :=
  if h : r ≠ 0 then
    haveI : NeZero r := ⟨h⟩
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
      ‖Spsi y k ψ‖ ^ 2
  else 0

lemma Qr_nonneg (y : ℝ) (k r : ℕ) : 0 ≤ Qr y k r := by
  unfold Qr; split_ifs
  · exact sum_nonneg fun _ _ => sq_nonneg _
  · exact le_rfl

/-- `z = (2N_k/3)^{1/2}` of (8.6), so that `w_k = z/100`. -/
def zk (y : ℝ) (k : ℕ) : ℝ := Real.sqrt (2 / 3 * Nk y k)

lemma wk_eq (y : ℝ) (k : ℕ) : wk y k = zk y k / 100 := rfl

/-- **(8.18)**, page 66, cited: from Montgomery-Vaughan's weighted large sieve (2.6) and their
Lemmas 3 and 8, `Σ_{5 ≤ r ≤ w} (0.361 + log(z/r)) Σ*_{χ mod r}|S_k(χ)|² ≤ S_k N_k − S_k²(0.361 + log z)`,
in the range of Lemma 13. NOT proved here. -/
def Eq818 : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    ∑ r ∈ Icc 5 ⌊wk (x / 202) k⌋₊,
        (0.361 + Real.log (zk (x / 202) k / r)) * Qr (x / 202) k r ≤
      Sk (x / 202) k * Nk (x / 202) k -
        Sk (x / 202) k ^ 2 * (0.361 + Real.log (zk (x / 202) k))

/-- The real part of `P(q)`. -/
lemma re_Pq (y : ℝ) (k : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (Pq y k q).re = haveI : NeZero q := ⟨hq⟩
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun ψ => ψ.conductor = q),
        (ψ (-1)).re * ‖Spsi y k ψ‖ ^ 2 := by
  haveI : NeZero q := ⟨hq⟩
  rw [Pq_eq_plain y k hq, Complex.re_sum]
  apply sum_congr rfl
  intro ψ _
  rw [Complex.re_mul_ofReal]

/-- `|Re P(q)| ≤ Σ*_{χ mod q}|S_k(χ)|²`. -/
lemma abs_re_Pq_le (y : ℝ) (k : ℕ) {q : ℕ} (hq : q ≠ 0) : |(Pq y k q).re| ≤ Qr y k q := by
  haveI : NeZero q := ⟨hq⟩
  rw [re_Pq y k hq]
  unfold Qr; rw [dif_pos hq]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ψ _ => ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖Spsi y k ψ‖)]
  have h1 : |(ψ (-1)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one ψ _)
  nlinarith [sq_nonneg ‖Spsi y k ψ‖]

/-- Each term of (8.16) is at least `−½ C f(q) Σ*|S_k(χ)|²`. -/
lemma term_ge (y : ℝ) (k : ℕ) {q : ℕ} (hq : q ≠ 0) :
    -(1 / 2 * LeanLab.RieselVaughan1983.Ctw * LeanLab.RieselVaughan1983.Lemma13Max.fq q *
        Qr y k q) ≤
      ((((1 / 2) * LeanLab.RieselVaughan1983.Ctw * ((μ q : ℤ) : ℝ) *
        LeanLab.RieselVaughan1983.Lemma13Max.fq q : ℝ) : ℂ) * Pq y k q).re := by
  rw [Complex.re_ofReal_mul]
  have hC := LeanLab.RieselVaughan1983.Ctw_pos
  have hf := LeanLab.RieselVaughan1983.Lemma13Max.fq_nonneg q
  have hmu : |((μ q : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  have hP := abs_re_Pq_le y k hq
  have hQ := Qr_nonneg y k q
  have h1 : |((μ q : ℤ) : ℝ) * (Pq y k q).re| ≤ Qr y k q := by
    rw [abs_mul]; nlinarith [abs_nonneg ((Pq y k q).re), abs_nonneg ((μ q : ℤ) : ℝ)]
  have h2 := neg_abs_le (((μ q : ℤ) : ℝ) * (Pq y k q).re)
  have h3 : 0 ≤ 1 / 2 * LeanLab.RieselVaughan1983.Ctw * LeanLab.RieselVaughan1983.Lemma13Max.fq q :=
    by positivity
  nlinarith

lemma fq_one : LeanLab.RieselVaughan1983.Lemma13Max.fq 1 = 1 := by
  unfold LeanLab.RieselVaughan1983.Lemma13Max.fq
  rw [if_pos ⟨odd_one, squarefree_one⟩]; simp

lemma fq_even {q : ℕ} (h : Even q) : LeanLab.RieselVaughan1983.Lemma13Max.fq q = 0 := by
  unfold LeanLab.RieselVaughan1983.Lemma13Max.fq
  rw [if_neg (fun h' => (Nat.not_even_iff_odd.mpr h'.1) h)]

/-- The term `q = 3` of (8.16) is `≥ 0`. -/
lemma term_three_nonneg (y : ℝ) (k : ℕ) :
    0 ≤ ((((1 / 2) * LeanLab.RieselVaughan1983.Ctw * ((μ 3 : ℤ) : ℝ) *
        LeanLab.RieselVaughan1983.Lemma13Max.fq 3 : ℝ) : ℂ) * Pq y k 3).re := by
  rw [Complex.re_ofReal_mul, re_Pq y k (by norm_num)]
  have h3 : Nat.Prime 3 := by norm_num
  rw [moebius_apply_prime h3]
  have hsum : (∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ 3)).filter (fun ψ => ψ.conductor = 3),
      (ψ (-1)).re * ‖Spsi y k ψ‖ ^ 2) = -(Qr y k 3) := by
    unfold Qr; rw [dif_pos (by norm_num), ← sum_neg_distrib]
    apply sum_congr rfl
    intro ψ hψ
    rw [mem_filter] at hψ
    rw [odd_of_primitive_three ψ hψ.2]; simp
  erw [hsum]
  have hC := LeanLab.RieselVaughan1983.Ctw_pos
  have hf := LeanLab.RieselVaughan1983.Lemma13Max.fq_nonneg 3
  have hQ := Qr_nonneg y k 3
  push_cast
  nlinarith [mul_nonneg (mul_nonneg hC.le hf) hQ]

/-- At most `N_k/2 + 1` primes lie in `I_k` once `ky/2 ≥ 2`: all of them are odd. -/
theorem card_Pset_le_half {y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 4 ≤ y) :
    (#(Xi.Pset y k) : ℝ) ≤ Nk y k / 2 + 1 := by
  set a := (k : ℝ) * y / 2 with ha_def
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 2 ≤ a := by rw [ha_def]; nlinarith
  set A := ⌊a⌋₊
  set B := ⌊a + y⌋₊
  have hAB : A ≤ B := Nat.floor_le_floor (by linarith)
  have hmaps : ∀ p ∈ Xi.Pset y k, p / 2 ∈ Icc ((A + 1) / 2) (B / 2) := by
    intro p hp
    rw [Xi.Pset, mem_filter, mem_range] at hp
    have h1 : A < p := (Nat.floor_lt (by linarith)).mpr hp.2.2.1
    have h2 : p ≤ B := by
      have := hp.1
      show p ≤ ⌊(k : ℝ) * y / 2 + y⌋₊
      omega
    rw [mem_Icc]; constructor <;> omega
  have hinj : Set.InjOn (fun p => p / 2) (Xi.Pset y k : Set ℕ) := by
    intro p hp p' hp' h
    simp only at h
    rw [mem_coe, Xi.Pset, mem_filter] at hp hp'
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (2 : ℝ) < 2 := lt_of_le_of_lt ha hp.2.2.1
      linarith
    have hp2' : p' ≠ 2 := by
      rintro rfl
      have : (2 : ℝ) < 2 := lt_of_le_of_lt ha hp'.2.2.1
      linarith
    have ho := Nat.odd_iff.mp (hp.2.1.odd_of_ne_two hp2)
    have ho' := Nat.odd_iff.mp (hp'.2.1.odd_of_ne_two hp2')
    omega
  have hc := card_le_card_of_injOn (fun p => p / 2) hmaps hinj
  rw [Nat.card_Icc] at hc
  have h2 : 2 * #(Xi.Pset y k) ≤ B - A + 2 := by omega
  have h2r : (2 : ℝ) * #(Xi.Pset y k) ≤ (B : ℝ) - A + 2 := by
    have : ((B - A + 2 : ℕ) : ℝ) = (B : ℝ) - A + 2 := by
      rw [Nat.cast_add, Nat.cast_sub hAB]; norm_num
    rw [← this]; exact_mod_cast h2
  have hN : Nk y k = (B : ℝ) - A := rfl
  rw [hN]; linarith

lemma log5_lt : Real.log 5 < 1.609438 := by
  have he := Real.exp_one_gt_d9
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hs : Real.exp 1.609438 = Real.exp 1 * Real.exp 0.609438 := by
    rw [← Real.exp_add]; norm_num
  have h06' : (1.83939736 : ℝ) < Real.exp 0.609438 := by
    have := Real.sum_le_exp_of_nonneg (x := (0.609438 : ℝ)) (by norm_num) 13
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  rw [hs]
  nlinarith

lemma log32_lt : Real.log (3 / 2) < 0.40547 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.sum_le_exp_of_nonneg (x := (0.40547 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

lemma y_big {y : ℝ} (hy0 : 0 < y) (hy : 350 < Real.log y) : 10 ^ 7 ≤ y := by
  have h1 : Real.exp 350 < y := by
    rw [← Real.exp_log hy0]; exact Real.exp_lt_exp.mpr hy
  have h2 : (2 : ℝ) ^ 350 ≤ Real.exp 350 := by
    have : Real.exp 350 = Real.exp 1 ^ 350 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 350
  have h3 : (10 : ℝ) ^ 7 ≤ 2 ^ 350 := by
    have h4 : (10 : ℝ) ^ 7 ≤ 2 ^ 24 := by norm_num
    exact h4.trans (pow_le_pow_right₀ (by norm_num) (by norm_num))
  exact (h3.trans h2).trans h1.le

/-- The value of (8.16) is at least `½ C (S_k² − Σ_{5 ≤ q ≤ W} f(q) Σ*|S_k(χ)|²)`, for `W ≥ 4`. -/
theorem re_limit_ge (y : ℝ) (k : ℕ) (hy : 0 ≤ y) {W : ℕ} (hW : 4 ≤ W) :
    1 / 2 * LeanLab.RieselVaughan1983.Ctw * (Sk y k ^ 2 -
        ∑ q ∈ Icc 5 W, LeanLab.RieselVaughan1983.Lemma13Max.fq q * Qr y k q) ≤
      (∑ q ∈ Icc 1 W, ((((1 / 2) * LeanLab.RieselVaughan1983.Ctw * ((μ q : ℤ) : ℝ) *
        LeanLab.RieselVaughan1983.Lemma13Max.fq q : ℝ) : ℂ) * Pq y k q)).re := by
  set G : ℕ → ℂ := fun q => (((1 / 2) * LeanLab.RieselVaughan1983.Ctw * ((μ q : ℤ) : ℝ) *
        LeanLab.RieselVaughan1983.Lemma13Max.fq q : ℝ) : ℂ) * Pq y k q with hG
  have hsplit : Icc 1 W = Icc 1 4 ∪ Icc 5 W := by
    ext q; simp only [mem_union, mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 4) (Icc 5 W) := by
    rw [disjoint_left]; intro q h1 h2; rw [mem_Icc] at h1 h2; omega
  rw [hsplit, sum_union hdisj, Complex.add_re, Complex.re_sum, Complex.re_sum]
  have h14 : Icc 1 4 = {1, 2, 3, 4} := by decide
  have hlow : 1 / 2 * LeanLab.RieselVaughan1983.Ctw * Sk y k ^ 2 ≤ ∑ q ∈ Icc 1 4, (G q).re := by
    rw [h14, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
      sum_singleton]
    have h1 : (G 1).re = 1 / 2 * LeanLab.RieselVaughan1983.Ctw * Sk y k ^ 2 := by
      simp only [hG]
      rw [Complex.re_ofReal_mul, Pq_one, Complex.ofReal_re, ← card_Pset_eq y k hy, fq_one]
      simp
    have h2 : (G 2).re = 0 := by
      simp only [hG]; rw [fq_even (by decide)]; simp
    have h4 : (G 4).re = 0 := by
      simp only [hG]; rw [fq_even (by decide)]; simp
    have h3 := term_three_nonneg y k
    rw [h1, h2, h4]
    simp only [hG] at h3 ⊢
    linarith
  have hhigh : -(1 / 2 * LeanLab.RieselVaughan1983.Ctw *
      ∑ q ∈ Icc 5 W, LeanLab.RieselVaughan1983.Lemma13Max.fq q * Qr y k q) ≤
      ∑ q ∈ Icc 5 W, (G q).re := by
    rw [mul_sum, ← sum_neg_distrib]
    apply sum_le_sum
    intro q hq
    rw [mem_Icc] at hq
    have := term_ge y k (q := q) (by omega)
    simp only [hG]
    linarith
  linarith

/-- **Lemma 13**, page 64, CONDITIONAL ON (8.18): `Lemma13P`. -/
theorem lemma13_of_818 (h818 : Eq818) : Lemma13P := by
  intro x hx hL k hk ε hε
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hy0 : 0 < y := by positivity
  have hy7 : 10 ^ 7 ≤ y := y_big hy0 hL
  obtain ⟨hN1, hN2⟩ := Nk_bounds y k hy0.le
  set N := Nk y k with hNdef
  set S := Sk y k with hSdef
  have hN0 : 0 < N := by linarith
  -- log N ≥ 349
  have hlogN : 349 ≤ Real.log N := by
    have h1 : y / 2 ≤ N := by linarith
    have h2 : Real.log (y / 2) ≤ Real.log N := Real.log_le_log (by positivity) h1
    rw [Real.log_div hy0.ne' (by norm_num)] at h2
    have h3 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  -- z and its logarithm
  set z := zk y k with hzdef
  have hlogz : Real.log z = (Real.log (2 / 3) + Real.log N) / 2 := by
    rw [hzdef, zk, Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hN0.ne']
  have hl23 : Real.log (2 / 3) = -Real.log (3 / 2) := by
    rw [show (2 : ℝ) / 3 = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  have hl32 := log32_lt
  have hl32' : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hl5 := log5_lt
  have hl5' : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hz3 : 3 ≤ Real.log z := by rw [hlogz, hl23]; linarith
  have hz0 : 0 < z := by
    rw [hzdef, zk]; apply Real.sqrt_pos.mpr; positivity
  -- W
  set W := ⌊wk y k⌋₊ with hWdef
  have hw0 : 0 ≤ wk y k := by unfold wk; positivity
  have hW : 4 ≤ W := by
    have h : (5 : ℝ) ≤ wk y k := by
      unfold wk
      have : (500 : ℝ) ≤ Real.sqrt (2 / 3 * N) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
      linarith
    have := Nat.le_floor (show ((5 : ℕ) : ℝ) ≤ wk y k by exact_mod_cast h)
    omega
  -- the lower bound on the limit
  have hlim := eq816 y k hw0
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hval := re_limit_ge y k hy0.le hW
  -- F
  set F := LeanLab.RieselVaughan1983.Lemma13Max.fq 5 / (0.361 + Real.log (z / 5)) with hFdef
  have hlz5 : Real.log (z / 5) = Real.log z - Real.log 5 := Real.log_div hz0.ne' (by norm_num)
  have hden5 : 0 < 0.361 + Real.log (z / 5) := by rw [hlz5]; linarith
  have hF0 : 0 ≤ F := div_nonneg (LeanLab.RieselVaughan1983.Lemma13Max.fq_nonneg 5) hden5.le
  have hfq : ∀ q ∈ Icc 5 W, LeanLab.RieselVaughan1983.Lemma13Max.fq q * Qr y k q ≤
      F * ((0.361 + Real.log (z / q)) * Qr y k q) := by
    intro q hq
    rw [mem_Icc] at hq
    have hqz : (q : ℝ) ≤ z / 100 := by
      have h1 : (q : ℝ) ≤ (W : ℝ) := by exact_mod_cast hq.2
      have h2 : (W : ℝ) ≤ wk y k := Nat.floor_le hw0
      rw [wk_eq] at h2; linarith
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hden : 0 < 0.361 + Real.log (z / q) := by
      have : (100 : ℝ) ≤ z / q := by rw [le_div_iff₀ hq0]; linarith
      have : 0 < Real.log (z / q) := Real.log_pos (by linarith)
      linarith
    have hm := LeanLab.RieselVaughan1983.Lemma13Max.lemma13_max hz3 hq.1 hqz
    rw [div_le_iff₀ hden] at hm
    have hQ := Qr_nonneg y k q
    calc LeanLab.RieselVaughan1983.Lemma13Max.fq q * Qr y k q
        ≤ (F * (0.361 + Real.log (z / q))) * Qr y k q := mul_le_mul_of_nonneg_right hm hQ
      _ = F * ((0.361 + Real.log (z / q)) * Qr y k q) := by ring
  have h818' := h818 x hx hL k hk
  simp only [← hydef] at h818'
  have hsum : ∑ q ∈ Icc 5 W, LeanLab.RieselVaughan1983.Lemma13Max.fq q * Qr y k q ≤
      F * (S * N - S ^ 2 * (0.361 + Real.log z)) := by
    calc _ ≤ ∑ q ∈ Icc 5 W, F * ((0.361 + Real.log (z / q)) * Qr y k q) := sum_le_sum hfq
      _ = F * ∑ q ∈ Icc 5 W, (0.361 + Real.log (z / q)) * Qr y k q := by rw [mul_sum]
      _ ≤ F * (S * N - S ^ 2 * (0.361 + Real.log z)) := mul_le_mul_of_nonneg_left h818' hF0
  -- S ≥ 0, S log 5 ≤ N
  have hS0 : 0 ≤ S := Sk_nonneg y k hy0.le
  have hSN : S ≤ N / 2 + 1 := by
    rw [hSdef, ← card_Pset_eq y k hy0.le]; exact card_Pset_le_half hk1 (by linarith)
  have hX : 0 ≤ S * (N - S * Real.log 5) := by
    apply mul_nonneg hS0; nlinarith
  -- the algebra
  set A := 0.361 + Real.log z with hAdef
  have hAL : 0 < A - Real.log 5 := by rw [hAdef]; linarith
  have hfq5 : LeanLab.RieselVaughan1983.Lemma13Max.fq 5 = 1 / 15 :=
    LeanLab.RieselVaughan1983.Lemma13Max.fq_five
  have hFv : F = 1 / (15 * (A - Real.log 5)) := by
    rw [hFdef, hfq5, hlz5, hAdef]; field_simp; ring
  have hD : 0 < -(29024 / 10000) + Real.log N := by linarith
  have hDle : -(29024 / 10000) + Real.log N ≤ 2 * (A - Real.log 5) := by
    rw [hAdef, hlogz, hl23]; linarith
  have key : S ^ 2 - F * (S * N - S ^ 2 * A) =
      16 / 15 * S ^ 2 - S * (N - S * Real.log 5) / (15 * (A - Real.log 5)) := by
    rw [hFv]; field_simp; ring
  have hcmp : S * (N - S * Real.log 5) / (15 * (A - Real.log 5)) ≤
      2 * S * (N - S * Real.log 5) / (15 * (-(29024 / 10000) + Real.log N)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hB : 1 / 2 * LeanLab.RieselVaughan1983.Ctw * (16 / 15 * S ^ 2 -
      2 * S * (N - S * Real.log 5) / (15 * (-(29024 / 10000) + Real.log N))) ≤
      1 / 2 * LeanLab.RieselVaughan1983.Ctw * (S ^ 2 -
        ∑ q ∈ Icc 5 W, LeanLab.RieselVaughan1983.Lemma13Max.fq q * Qr y k q) := by
    have hC := LeanLab.RieselVaughan1983.Ctw_pos
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : S ^ 2 - F * (S * N - S ^ 2 * A) ≤
        S ^ 2 - ∑ q ∈ Icc 5 W, LeanLab.RieselVaughan1983.Lemma13Max.fq q * Qr y k q := by
      linarith
    linarith
  have hfin := (tendsto_order.1 hre).1 _ (show 1 / 2 * LeanLab.RieselVaughan1983.Ctw *
      (16 / 15 * S ^ 2 - 2 * S * (N - S * Real.log 5) /
        (15 * (-(29024 / 10000) + Real.log N))) - ε < _ by linarith)
  obtain ⟨D0, hD0⟩ := eventually_atTop.mp hfin
  exact ⟨D0, fun D hD => (hD0 D hD).le⟩

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at five rows, Lemma 6 (i) and (ii), (2.30) and (2.31), Rosser-Schoenfeld (3.3) and
(8.18). In Section 8 only (8.18), the Montgomery-Vaughan large sieve step, is cited now. -/
theorem theorem_of_lemma5_818 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33)
    (h : Eq818) : Theorem :=
  theorem_of_lemma5_13 h24 h42 h278 h396 h5 h6 h6' hTab hRS (lemma13_of_818 h)

end LeanLab.RieselVaughan1983.Lemma13Red
