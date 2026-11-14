module

public import LeanLab.RieselVaughan1983.Lemma11Theta

/-!
P0032 Riesel-Vaughan 1983, (8.10), (8.11) and Lemma 12 for the paper's Δ_k, page 64, with
primitive characters, and the reduction of Section 8 to Lemma 13 alone.
Unit U-1223, PC run 20261020T1103Z-23466. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

(8.10) Φ_k = Σ_{2∤d} μ(d)/φ(d)² Σ_{χ mod d, d* ≤ w} χ*(−1)|S_k(χ*)|², an absolutely convergent
series over all odd d; (8.11) Δ_k is its part d > y/2. Lemma 12, page 64: |Δ_k| ≤ 8 A₁₁ w S_k,
from Σ_{χ mod d, d* ≤ w}|S_k(χ*)|² ≤ Σ_{r ≤ w} φ(r) S_k (y/r + 1) ≤ 2wy S_k and the tail
Σ_{d > y/2} μ(d)²/φ(d)² ≤ 4A₁₁/y. Here Φ_k is handled through its partial sums Φ_k^{(D)} over
d ≤ D, so no infinite sum is needed: Lemma 13, Φ_k ≥ its bound, is used in the form that
Φ_k^{(D)} comes within any ε > 0 of that bound for all large D, which the convergence of (8.10)
gives.

What is here, all PROVED unconditional unless marked:
* `Spsi`, `charSmallP`: S_k(ψ) for a character of any level, and Σ_{χ mod d, d* ≤ w}
  χ*(−1)|S_k(χ*)|² with Mathlib's primitive character χ*.
* `charSmallP_eq`: for 1 ≤ d ≤ y/2 it equals the lab's `Theta.charSmall`, so D_k is built from it.
* `changeLevel_heq`, `conductor_prim_injOn`: χ ↦ (d*, χ*) is injective.
* `sum_small_le`: Σ_{χ mod d, d* ≤ w}|S_k(χ*)|² ≤ 2wy S_k for w ≤ y/2.
* `DeltaD`, `lemma12`: **Lemma 12**, ‖Δ_k^{(D)}‖ ≤ 8A₁₁ w S_k for every truncation D.
* `PhiD`, `phi_split`: Φ_k^{(D)} = D_k + Δ_k^{(D)} for D ≥ y/2.
* `Lemma13P`: Lemma 13 for the partial sums, a Prop, NOT proved: it cites Montgomery-Vaughan's
  large sieve (2.6) and their Lemmas 3 and 8, and (2.3).
* `lemma12and13_of`: `Theta.Lemma12and13P` from `Lemma13P`.
* `theorem_of_lemma5_13`: the 18-prime Theorem CONDITIONAL ON Lemma 5 at five rows, Lemma 6,
  (2.30), (2.31), (3.3) and `Lemma13P`.
KNOWN mathematics, the paper's route.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Delta

open LeanLab.RieselVaughan1983.Xi LeanLab.RieselVaughan1983.Expand87
  LeanLab.RieselVaughan1983.Theta

/-- `S_k(ψ) = Σ_{p ∈ I_k} ψ(p)` for a character `ψ` of any level `r`. -/
def Spsi (y : ℝ) (k : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) : ℂ :=
  ∑ p ∈ Xi.Pset y k, ψ (p : ZMod r)

/-- `Σ_{χ mod d, d* ≤ w} χ*(−1)|S_k(χ*)|²`, zero at `d = 0`. -/
def charSmallP (y : ℝ) (k : ℕ) (w : ℝ) (d : ℕ) : ℂ :=
  if h : d ≠ 0 then
    haveI : NeZero d := ⟨h⟩
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => ¬ w < (χ.conductor : ℝ)),
      χ.primitiveCharacter (-1) * ((‖Spsi y k χ.primitiveCharacter‖ ^ 2 : ℝ) : ℂ)
  else 0

lemma prim_neg_one {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) :
    χ.primitiveCharacter (-1) = χ (-1) := by
  have h := χ.primitiveCharacter_apply_of_isCoprime (a := -1) isCoprime_one_left.neg_left
  simpa using h

/-- For `1 ≤ d ≤ y/2` the primitive form equals the lab's `charSmall`. -/
theorem charSmallP_eq {y w : ℝ} {k d : ℕ} (hk : 1 ≤ k) (hy : 0 ≤ y) (hd : d ≠ 0)
    (hdy : (d : ℝ) ≤ y / 2) : charSmallP y k w d = charSmall y k w d := by
  unfold charSmallP charSmall
  rw [dif_pos hd, dif_pos hd]
  haveI : NeZero d := ⟨hd⟩
  apply sum_congr rfl
  intro χ _
  have hS : Spsi y k χ.primitiveCharacter = ∑ p ∈ Xi.Pset y k, χ (p : ZMod d) := by
    unfold Spsi
    exact S_primitive χ _ (fun p hp =>
      (ZMod.isUnit_iff_coprime p d).mp (isUnit_of_mem_Pset hk hy hdy hp))
  rw [prim_neg_one, hS]

/-- Two characters of level `d` with the same conductor and primitive character are equal. -/
lemma changeLevel_heq {d c1 c2 : ℕ} (hc : c1 = c2) (ψ1 : DirichletCharacter ℂ c1)
    (ψ2 : DirichletCharacter ℂ c2) (hψ : HEq ψ1 ψ2) (h1 : c1 ∣ d) (h2 : c2 ∣ d) :
    DirichletCharacter.changeLevel h1 ψ1 = DirichletCharacter.changeLevel h2 ψ2 := by
  subst hc
  obtain rfl := eq_of_heq hψ
  rfl

/-- `χ ↦ (d*, χ*)` is injective. -/
theorem conductor_prim_injOn {d : ℕ} [NeZero d] (s : Finset (DirichletCharacter ℂ d)) :
    Set.InjOn (fun χ : DirichletCharacter ℂ d =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ r : ℕ, DirichletCharacter ℂ r)) s := by
  intro χ1 _ χ2 _ h
  simp only [Sigma.mk.inj_iff] at h
  rw [← χ1.changeLevel_primitiveCharacter, ← χ2.changeLevel_primitiveCharacter]
  exact changeLevel_heq h.1 _ _ h.2 _ _

/-- The characters of level `r`, empty at `r = 0`. -/
def fib (r : ℕ) : Finset (DirichletCharacter ℂ r) :=
  if h : r ≠ 0 then
    haveI : NeZero r := ⟨h⟩
    univ
  else ∅

lemma mem_fib {r : ℕ} (hr : r ≠ 0) (ψ : DirichletCharacter ℂ r) : ψ ∈ fib r := by
  unfold fib; rw [dif_pos hr]; exact mem_univ _

/-- Page 64: for `1 ≤ r ≤ y/2`, `Σ_{ψ mod r}|S_k(ψ)|² ≤ 2y S_k`. -/
theorem sum_level_le {y : ℝ} {k r : ℕ} (hk : 1 ≤ k) (hy : 0 < y) (hr : r ≠ 0)
    (hry : (r : ℝ) ≤ y / 2) :
    ∑ ψ ∈ fib r, ‖Spsi y k ψ‖ ^ 2 ≤ 2 * y * Sk y k := by
  haveI : NeZero r := ⟨hr⟩
  have hfib : fib r = univ := by unfold fib; rw [dif_pos hr]
  rw [hfib]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have h1 := L11.lemma11_char_real (d := r) (Xi.Pset y k) ((k : ℝ) * y / 2) y hy.le
    (fun p hp => by rw [Xi.Pset, mem_filter] at hp; exact ⟨hp.2.2.1, hp.2.2.2⟩)
    (fun p hp => isUnit_of_mem_Pset hk hy.le hry hp)
  have hφ : (r.totient : ℝ) ≤ r := by exact_mod_cast Nat.totient_le r
  have hS := card_Pset_le y k hy.le
  have hS0 : (0 : ℝ) ≤ #(Xi.Pset y k) := Nat.cast_nonneg _
  have h2 : (r.totient : ℝ) * (y / r + 1) ≤ 2 * y := by
    have : (r : ℝ) * (y / r + 1) = y + r := by field_simp
    have h3 : (r.totient : ℝ) * (y / r + 1) ≤ r * (y / r + 1) :=
      mul_le_mul_of_nonneg_right hφ (by positivity)
    linarith
  unfold Spsi
  calc ∑ ψ : DirichletCharacter ℂ r, ‖∑ p ∈ Xi.Pset y k, ψ (p : ZMod r)‖ ^ 2
      ≤ (r.totient : ℝ) * ((#(Xi.Pset y k) : ℝ) * (y / r + 1)) := h1
    _ = (#(Xi.Pset y k) : ℝ) * ((r.totient : ℝ) * (y / r + 1)) := by ring
    _ ≤ Sk y k * (2 * y) := by
        apply mul_le_mul hS h2 (by positivity) (Sk_nonneg y k hy.le)
    _ = 2 * y * Sk y k := by ring

/-- Page 64: `Σ_{χ mod d, d* ≤ w}|S_k(χ*)|² ≤ 2wy S_k` for `0 ≤ w ≤ y/2`. -/
theorem sum_small_le {y w : ℝ} {k d : ℕ} [NeZero d] (hk : 1 ≤ k) (hy : 0 < y) (hw : 0 ≤ w)
    (hwy : w ≤ y / 2) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => ¬ w < (χ.conductor : ℝ)),
      ‖Spsi y k χ.primitiveCharacter‖ ^ 2 ≤ 2 * w * y * Sk y k := by
  classical
  set s := (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => ¬ w < (χ.conductor : ℝ))
  set g := fun χ : DirichletCharacter ℂ d =>
    (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ r : ℕ, DirichletCharacter ℂ r)
  set f := fun z : (Σ r : ℕ, DirichletCharacter ℂ r) => ‖Spsi y k z.2‖ ^ 2
  have hS := Sk_nonneg y k hy.le
  have e1 : ∑ χ ∈ s, ‖Spsi y k χ.primitiveCharacter‖ ^ 2 = ∑ z ∈ s.image g, f z := by
    rw [sum_image (conductor_prim_injOn s)]
  have hsub : s.image g ⊆ (Icc 1 ⌊w⌋₊).sigma fib := by
    intro z hz
    rw [mem_image] at hz
    obtain ⟨χ, hχ, rfl⟩ := hz
    rw [mem_filter] at hχ
    rw [mem_sigma, mem_Icc]
    have hc0 : χ.conductor ≠ 0 := χ.conductor_ne_zero
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hc0, Nat.le_floor (not_lt.mp hχ.2)⟩, mem_fib hc0 _⟩
  have e2 : ∑ z ∈ (Icc 1 ⌊w⌋₊).sigma fib, f z = ∑ r ∈ Icc 1 ⌊w⌋₊, ∑ ψ ∈ fib r, f ⟨r, ψ⟩ :=
    sum_sigma _ _ _
  have hle : ∀ r ∈ Icc 1 ⌊w⌋₊, ∑ ψ ∈ fib r, f ⟨r, ψ⟩ ≤ 2 * y * Sk y k := by
    intro r hr
    rw [mem_Icc] at hr
    have hr0 : r ≠ 0 := by omega
    have hrw : (r : ℝ) ≤ w := by
      have : (r : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hr.2
      linarith [Nat.floor_le hw]
    exact sum_level_le hk hy hr0 (by linarith)
  rw [e1]
  calc ∑ z ∈ s.image g, f z ≤ ∑ z ∈ (Icc 1 ⌊w⌋₊).sigma fib, f z :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ r ∈ Icc 1 ⌊w⌋₊, ∑ ψ ∈ fib r, f ⟨r, ψ⟩ := e2
    _ ≤ ∑ r ∈ Icc 1 ⌊w⌋₊, 2 * y * Sk y k := sum_le_sum hle
    _ = (⌊w⌋₊ : ℝ) * (2 * y * Sk y k) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ w * (2 * y * Sk y k) := mul_le_mul_of_nonneg_right (Nat.floor_le hw) (by positivity)
    _ = 2 * w * y * Sk y k := by ring

theorem norm_charSmallP_le {y w : ℝ} {k d : ℕ} (hk : 1 ≤ k) (hy : 0 < y) (hw : 0 ≤ w)
    (hwy : w ≤ y / 2) : ‖charSmallP y k w d‖ ≤ 2 * w * y * Sk y k := by
  have hS := Sk_nonneg y k hy.le
  unfold charSmallP
  by_cases hd : d ≠ 0
  · rw [dif_pos hd]
    haveI : NeZero d := ⟨hd⟩
    refine le_trans (norm_sum_le _ _) (le_trans ?_ (sum_small_le (d := d) hk hy hw hwy))
    apply sum_le_sum
    intro χ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ‖χ.primitiveCharacter (-1)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h0 : 0 ≤ ‖Spsi y k χ.primitiveCharacter‖ ^ 2 := by positivity
    nlinarith
  · rw [dif_neg hd, norm_zero]; positivity

lemma abs_mu_div_sq (d : ℕ) :
    |(μ d : ℝ) / (d.totient : ℝ) ^ 2| = ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg ((d.totient : ℝ)))]
  congr 1
  have h1 : |(μ d : ℝ)| = ((|μ d| : ℤ) : ℝ) := by push_cast; rfl
  have h2 : ((μ d : ℝ)) ^ 2 = ((μ d ^ 2 : ℤ) : ℝ) := by push_cast; rfl
  rw [h1, h2, abs_moebius, moebius_sq]

/-- (8.11) truncated at `D`: `Δ_k^{(D)} = Σ_{y/2 < d ≤ D, 2∤d} μ(d)/φ(d)² Σ_{d* ≤ w} ...`. -/
def DeltaD (y : ℝ) (k : ℕ) (w : ℝ) (D : ℕ) : ℂ :=
  ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) D).filter Odd,
    (((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charSmallP y k w d

/-- **Lemma 12**, page 64: `‖Δ_k^{(D)}‖ ≤ 8 A₁₁ w S_k` for every `D`. -/
theorem lemma12 {y w : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 0 < y) (hw : 0 ≤ w) (hwy : w ≤ y / 2)
    (D : ℕ) : ‖DeltaD y k w D‖ ≤ 8 * OddSums.A11 * w * Sk y k := by
  have hS := Sk_nonneg y k hy.le
  have hB : 0 ≤ 2 * w * y * Sk y k := by positivity
  unfold DeltaD
  calc ‖∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) D).filter Odd,
          (((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charSmallP y k w d‖
      ≤ ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) D).filter Odd,
          ‖(((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charSmallP y k w d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) D).filter Odd,
          ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 * (2 * w * y * Sk y k) := by
        apply sum_le_sum
        intro d _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mu_div_sq]
        exact mul_le_mul_of_nonneg_left (norm_charSmallP_le hk hy hw hwy) (by positivity)
    _ = (∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) D).filter Odd, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2) *
          (2 * w * y * Sk y k) := by rw [sum_mul]
    _ ≤ (4 * OddSums.A11 / y) * (2 * w * y * Sk y k) := by
        apply mul_le_mul_of_nonneg_right _ hB
        have h := OddSumsApply.lemma12_half_A11 (y := y) (D := (D : ℝ)) hy
        rwa [Nat.floor_natCast] at h
    _ = 8 * OddSums.A11 * w * Sk y k := by field_simp; ring

/-- (8.10) truncated at `D`: `Φ_k^{(D)} = Σ_{d ≤ D, 2∤d} μ(d)/φ(d)² Σ_{d* ≤ w} χ*(−1)|S_k(χ*)|²`. -/
def PhiD (y : ℝ) (k : ℕ) (w : ℝ) (D : ℕ) : ℂ :=
  ∑ d ∈ (Icc 1 D).filter Odd, (((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charSmallP y k w d

/-- `Φ_k^{(D)} = D_k + Δ_k^{(D)}` once `D ≥ y/2`. -/
theorem phi_split {y w : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 0 ≤ y) {D : ℕ} (hD : ⌊y / 2⌋₊ ≤ D) :
    PhiD y k w D = DK y k w + DeltaD y k w D := by
  unfold PhiD DK DeltaD
  have hsplit : (Icc 1 D).filter Odd =
      (Icc 1 ⌊y / 2⌋₊).filter Odd ∪ (Icc (⌊y / 2⌋₊ + 1) D).filter Odd := by
    ext d
    simp only [mem_union, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h : d ≤ ⌊y / 2⌋₊
      · exact Or.inl ⟨⟨h1, h⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  rw [hsplit, sum_union]
  · congr 1
    apply sum_congr rfl
    intro d hd
    rw [mem_filter, mem_Icc] at hd
    have hd0 : d ≠ 0 := by omega
    have hdy : (d : ℝ) ≤ y / 2 := by
      have : (d : ℝ) ≤ (⌊y / 2⌋₊ : ℝ) := by exact_mod_cast hd.1.2
      linarith [Nat.floor_le (show 0 ≤ y / 2 by linarith)]
    rw [charSmallP_eq hk hy hd0 hdy]
  · rw [disjoint_left]
    intro d h1 h2
    rw [mem_filter, mem_Icc] at h1 h2
    omega

/-- **Lemma 13**, page 64, for the partial sums of (8.10): `Φ_k^{(D)}` comes within any `ε > 0`
of Lemma 13's lower bound for all large `D`; with `K = 200`, `y = x/202`, `w` of (8.6). This is
what `Φ_k ≥` the bound gives, since (8.10) converges. NOT proved here. -/
def Lemma13P : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200, ∀ ε : ℝ, 0 < ε →
    ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      1 / 2 * Ctw * (16 / 15 * Sk (x / 202) k ^ 2 -
        2 * Sk (x / 202) k * (Nk (x / 202) k - Sk (x / 202) k * Real.log 5) /
          (15 * (-(29024 / 10000) + Real.log (Nk (x / 202) k)))) - ε ≤
        (PhiD (x / 202) k (wk (x / 202) k) D).re

/-- `Theta.Lemma12and13P` from `Lemma13P`: Lemma 12 is discharged. -/
theorem lemma12and13_of (h : Lemma13P) : Lemma12and13P := by
  intro x hx hL k hk
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hy0 : 0 < y := by positivity
  have hy4 : 4 < y := by
    by_contra hc
    push_neg at hc
    have : Real.log y ≤ Real.log 4 := Real.log_le_log hy0 hc
    have : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  obtain ⟨hN1, hN2⟩ := Nk_bounds y k hy0.le
  have hw0 : 0 ≤ wk y k := by unfold wk; positivity
  have hwy : wk y k ≤ y / 2 := by
    obtain ⟨-, h2⟩ := Lemma14.w_bounds (by linarith : (2 : ℝ) ≤ y) hN1 hN2
    have hs : Real.sqrt y ≤ y / 2 := by
      have h0 := Real.sqrt_nonneg y
      have hsq := Real.sq_sqrt hy0.le
      have h2s : 2 ≤ Real.sqrt y := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      nlinarith
    unfold wk; linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨D0, hD0⟩ := h x hx hL k hk ε hε
  set D := max D0 ⌊y / 2⌋₊
  have hΦ := hD0 D (le_max_left _ _)
  simp only [← hydef] at hΦ
  have hsp := phi_split (w := wk y k) hk1 hy0.le (le_max_right D0 ⌊y / 2⌋₊)
  have hre : (PhiD y k (wk y k) D).re = (DK y k (wk y k)).re + (DeltaD y k (wk y k) D).re := by
    rw [hsp, Complex.add_re]
  have hΔ := lemma12 hk1 hy0 hw0 hwy D
  have hΔre : (DeltaD y k (wk y k) D).re ≤ 8 * OddSums.A11 * wk y k * Sk y k := by
    have := Complex.re_le_norm (DeltaD y k (wk y k) D)
    linarith
  linarith

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at five rows, Lemma 6 (i) and (ii), (2.30) and (2.31), Rosser-Schoenfeld (3.3) and
`Lemma13P`. In Section 8 only Lemma 13 is cited now. -/
theorem theorem_of_lemma5_13 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33)
    (h : Lemma13P) : Theorem :=
  theorem_of_lemma5_12and13 h24 h42 h278 h396 h5 h6 h6' hTab hRS (lemma12and13_of h)

end LeanLab.RieselVaughan1983.Delta
