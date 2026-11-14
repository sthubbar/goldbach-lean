module

public import LeanLab.RieselVaughan1983.Expand87

/-!
P0032 Riesel-Vaughan 1983, the conductor split (8.9) to (8.12) of Rest_k and Lemma 11 for the
paper's Θ_k, pages 62 to 64.
Unit U-1217, PC run 20261020T1103Z-23466. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Page 62: each term of (8.7) is unaltered if χ is replaced by the primitive χ* inducing it,
since every prime of I_k is prime to d. (8.12): Θ_k = Σ_{d ≤ y/2, 2∤d} μ(d)/φ(d)² Σ_{χ mod d,
d* > w} χ(−1)|S_k(χ)|²; the d* ≤ w part is Φ_k − Δ_k by (8.10) and (8.11).
Lemma 11, page 63: |Θ_k| ≤ 3 A₁₀ (y/w) S_k.

What is here, all PROVED unconditional unless marked:
* `prim_apply`, `S_primitive`: χ*(p) = χ(p) for p prime to d, so S_k(χ*) = S_k(χ), from
  Mathlib's `primitiveCharacter_apply_of_isCoprime`.
* `charBig`, `charSmall`, `charSum_split`: Σ_χ = Σ_{d* ≤ w} + Σ_{d* > w}.
* `ThetaK`, `DK`, `rest_split`: Rest_k = D_k + Θ_k over ℂ, D_k the d* ≤ w part, which is the
  paper's Φ_k − Δ_k.
* `charBig_eq_zero`: no character mod d ≤ w has conductor above w.
* `norm_charBig_le`: ‖Σ_{d* > w} χ(−1)|S_k(χ)|²‖ ≤ φ(d) S_k (3y/(2d)) for d ≤ y/2.
* `lemma11`: **Lemma 11**, ‖Θ_k‖ ≤ 3 A₁₀ (y/w) S_k.
* `Lemma12and13P`: the d* ≤ w part, Re D_k ≥ Lemma 13's bound − 8A₁₁ w S_k, a Prop, NOT proved:
  it needs Φ_k as an infinite sum over d, (2.3), Lemma 12 and Lemma 13, which cites
  Montgomery-Vaughan.
* `lemma11to13_of`: `Xi.Lemma11to13P` from `Lemma12and13P`, so Lemma 11 is discharged.
* `theorem_of_lemma5_12and13`: the 18-prime Theorem CONDITIONAL ON Lemma 5 at five rows,
  Lemma 6, (2.30), (2.31), (3.3) and `Lemma12and13P`.
KNOWN mathematics, the paper's route.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Theta

open LeanLab.RieselVaughan1983.Xi LeanLab.RieselVaughan1983.Expand87

/-- `χ*(p) = χ(p)` for `p` prime to the level. -/
theorem prim_apply {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {p : ℕ} (hp : Nat.Coprime p d) :
    χ.primitiveCharacter (p : ZMod χ.conductor) = χ (p : ZMod d) := by
  have h := χ.primitiveCharacter_apply_of_isCoprime (a := (p : ℤ))
    (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hp))
  simpa using h

/-- `S_k(χ*) = S_k(χ)` when every prime of `I_k` is prime to `d`. -/
theorem S_primitive {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Coprime p d) :
    ∑ p ∈ P, χ.primitiveCharacter (p : ZMod χ.conductor) = ∑ p ∈ P, χ (p : ZMod d) :=
  sum_congr rfl (fun p hp => prim_apply χ (hP p hp))

/-- `Σ_{χ mod d, d* > w} χ(−1)|S_k(χ)|²`, zero at `d = 0`. -/
def charBig (y : ℝ) (k : ℕ) (w : ℝ) (d : ℕ) : ℂ :=
  if h : d ≠ 0 then
    haveI : NeZero d := ⟨h⟩
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => w < (χ.conductor : ℝ)),
      χ (-1) * ((‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 : ℝ) : ℂ)
  else 0

/-- `Σ_{χ mod d, d* ≤ w} χ(−1)|S_k(χ)|²`, zero at `d = 0`. -/
def charSmall (y : ℝ) (k : ℕ) (w : ℝ) (d : ℕ) : ℂ :=
  if h : d ≠ 0 then
    haveI : NeZero d := ⟨h⟩
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => ¬ w < (χ.conductor : ℝ)),
      χ (-1) * ((‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 : ℝ) : ℂ)
  else 0

theorem charSum_split (y : ℝ) (k : ℕ) (w : ℝ) (d : ℕ) :
    charSum y k d = charSmall y k w d + charBig y k w d := by
  unfold charSum charSmall charBig
  by_cases h : d ≠ 0
  · rw [dif_pos h, dif_pos h, dif_pos h, add_comm]
    exact (sum_filter_add_sum_filter_not _ _ _).symm
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

/-- (8.12): `Θ_k`. -/
def ThetaK (y : ℝ) (k : ℕ) (w : ℝ) : ℂ :=
  ∑ d ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd, (((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charBig y k w d

/-- The `d* ≤ w` part, `Φ_k − Δ_k` by (8.10) and (8.11). -/
def DK (y : ℝ) (k : ℕ) (w : ℝ) : ℂ :=
  ∑ d ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd, (((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charSmall y k w d

/-- (8.9) for the `d ≤ y/2` part: `Rest_k = D_k + Θ_k`. -/
theorem rest_split {x y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 0 ≤ y) (hx : (k : ℝ) * y + 2 * y ≤ x)
    (w : ℝ) : (RestK x y k : ℂ) = DK y k w + ThetaK y k w := by
  rw [rest_expansion hk hy hx, DK, ThetaK, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [charSum_split y k w d, mul_add]

/-- No character mod `d ≤ w` has conductor above `w`. -/
theorem charBig_eq_zero {y w : ℝ} {k d : ℕ} (hd : d ≠ 0) (hdw : (d : ℝ) ≤ w) :
    charBig y k w d = 0 := by
  unfold charBig
  rw [dif_pos hd]
  apply sum_eq_zero
  intro χ hχ
  exfalso
  rw [mem_filter] at hχ
  haveI : NeZero d := ⟨hd⟩
  have h1 : χ.conductor ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) χ.conductor_dvd_level
  have h2 : (χ.conductor : ℝ) ≤ d := by exact_mod_cast h1
  linarith [hχ.2]

/-- Page 63: for `1 ≤ d ≤ y/2`, `‖Σ_{d* > w} χ(−1)|S_k(χ)|²‖ ≤ φ(d) S_k (3y/(2d))`. -/
theorem norm_charBig_le {y w : ℝ} {k d : ℕ} (hk : 1 ≤ k) (hy : 0 < y) (hd : d ≠ 0)
    (hdy : (d : ℝ) ≤ y / 2) :
    ‖charBig y k w d‖ ≤ (d.totient : ℝ) * (Sk y k * (3 * y / (2 * d))) := by
  haveI : NeZero d := ⟨hd⟩
  unfold charBig
  rw [dif_pos hd]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  calc ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => w < (χ.conductor : ℝ)),
          χ (-1) * ((‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => w < (χ.conductor : ℝ)),
          ‖χ (-1) * ((‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => w < (χ.conductor : ℝ)),
          ‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 := by
        apply sum_le_sum
        intro χ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have : ‖χ (-1)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have h0 : 0 ≤ ‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 := by positivity
        nlinarith
    _ ≤ ∑ χ : DirichletCharacter ℂ d, ‖∑ p ∈ Xi.Pset y k, χ p‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ (d.totient : ℝ) * ((#(Xi.Pset y k) : ℝ) * (y / d + 1)) := by
        apply L11.lemma11_char_real (Xi.Pset y k) ((k : ℝ) * y / 2) y hy.le
        · intro p hp
          rw [Xi.Pset, mem_filter] at hp
          exact ⟨hp.2.2.1, hp.2.2.2⟩
        · intro p hp
          exact isUnit_of_mem_Pset hk hy.le hdy hp
    _ ≤ (d.totient : ℝ) * (Sk y k * (3 * y / (2 * d))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have h1 : y / d + 1 ≤ 3 * y / (2 * d) := by
          rw [div_add_one hd0.ne', div_le_div_iff₀ hd0 (by positivity)]
          nlinarith
        have h2 := card_Pset_le y k hy.le
        have h3 : 0 ≤ y / d + 1 := by positivity
        calc (#(Xi.Pset y k) : ℝ) * (y / d + 1) ≤ Sk y k * (y / d + 1) :=
              mul_le_mul_of_nonneg_right h2 h3
          _ ≤ Sk y k * (3 * y / (2 * d)) :=
              mul_le_mul_of_nonneg_left h1 (Sk_nonneg y k hy.le)

/-- **Lemma 11**, page 63, for the paper's `Θ_k`: `‖Θ_k‖ ≤ 3 A₁₀ (y/w) S_k`. -/
theorem lemma11 {y w : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 0 < y) (hw : 0 < w) :
    ‖ThetaK y k w‖ ≤ 3 * OddSums.A10 * (y / w) * Sk y k := by
  have hS := Sk_nonneg y k hy.le
  set g : ℕ → ℝ := fun d => ((μ d : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ)) with hg
  have hg0 : ∀ d, 0 ≤ g d := fun d => by simp only [hg]; positivity
  -- each term
  have hterm : ∀ d ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd,
      ‖(((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charBig y k w d‖ ≤
        (if ⌊w⌋₊ < d then (3 / 2 * y * Sk y k) * g d else 0) := by
    intro d hd
    rw [mem_filter, mem_Icc] at hd
    have hd0 : d ≠ 0 := by omega
    have hdy : (d : ℝ) ≤ y / 2 := by
      have : (d : ℝ) ≤ (⌊y / 2⌋₊ : ℝ) := by exact_mod_cast hd.1.2
      linarith [Nat.floor_le (show 0 ≤ y / 2 by linarith)]
    by_cases hdw : ⌊w⌋₊ < d
    · rw [if_pos hdw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hφ : (0 : ℝ) < d.totient := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)
      have hdr : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
      have habs : |(μ d : ℝ) / (d.totient : ℝ) ^ 2| = ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 := by
        rw [abs_div, abs_of_nonneg (sq_nonneg ((d.totient : ℝ)))]
        congr 1
        have h1 : |(μ d : ℝ)| = ((|μ d| : ℤ) : ℝ) := by push_cast; rfl
        have h2 : ((μ d : ℝ)) ^ 2 = ((μ d ^ 2 : ℤ) : ℝ) := by push_cast; rfl
        rw [h1, h2, abs_moebius, moebius_sq]
      rw [habs]
      calc ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 * ‖charBig y k w d‖
          ≤ ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 *
              ((d.totient : ℝ) * (Sk y k * (3 * y / (2 * d)))) :=
            mul_le_mul_of_nonneg_left (norm_charBig_le hk hy hd0 hdy) (by positivity)
        _ = 3 / 2 * y * Sk y k * g d := by
            simp only [hg]; field_simp
    · rw [if_neg hdw]
      have hdw' : (d : ℝ) ≤ w := by
        have : d ≤ ⌊w⌋₊ := by omega
        have h1 : (d : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast this
        linarith [Nat.floor_le hw.le]
      rw [charBig_eq_zero hd0 hdw', mul_zero, norm_zero]
  calc ‖ThetaK y k w‖
      ≤ ∑ d ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd,
          ‖(((μ d : ℝ) / (d.totient : ℝ) ^ 2 : ℝ) : ℂ) * charBig y k w d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd,
          (if ⌊w⌋₊ < d then (3 / 2 * y * Sk y k) * g d else 0) := sum_le_sum hterm
    _ = ∑ d ∈ (Icc (⌊w⌋₊ + 1) ⌊y / 2⌋₊).filter Odd, (3 / 2 * y * Sk y k) * g d := by
        rw [← sum_filter]
        apply sum_congr _ (fun _ _ => rfl)
        ext d
        simp only [mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
          exact ⟨⟨by omega, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨⟨by omega, h2⟩, h3⟩, by omega⟩
    _ = (3 / 2 * y * Sk y k) * ∑ d ∈ (Icc (⌊w⌋₊ + 1) ⌊y / 2⌋₊).filter Odd, g d := by
        rw [mul_sum]
    _ ≤ (3 / 2 * y * Sk y k) * ((2 / w) * OddSums.A10) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 := L11.lemma11_tail (w := w) (D := y / 2) hw
        have h2 := OddSums.odd_sum_A10 ⌊y / 2⌋₊
        have h3 : 0 ≤ 2 / w := by positivity
        calc ∑ d ∈ (Icc (⌊w⌋₊ + 1) ⌊y / 2⌋₊).filter Odd, g d
            ≤ (2 / w) * ∑ r ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd,
                ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ)) := h1
          _ ≤ (2 / w) * OddSums.A10 := mul_le_mul_of_nonneg_left h2 h3
    _ = 3 * OddSums.A10 * (y / w) * Sk y k := by field_simp

/-- Lemma 12 and Lemma 13 with (8.10), (8.11) on the `d* ≤ w` part: `Re D_k ≥` Lemma 13's
bound `− 8A₁₁ w S_k`, with `K = 200`, `y = x/202` and `w` of (8.6). NOT proved here. -/
def Lemma12and13P : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    1 / 2 * Ctw * (16 / 15 * Sk (x / 202) k ^ 2 -
        2 * Sk (x / 202) k * (Nk (x / 202) k - Sk (x / 202) k * Real.log 5) /
          (15 * (-(29024 / 10000) + Real.log (Nk (x / 202) k)))) -
      8 * OddSums.A11 * wk (x / 202) k * Sk (x / 202) k ≤
        (DK (x / 202) k (wk (x / 202) k)).re

/-- Lemma 11 discharged: `Xi.Lemma11to13P` from `Lemma12and13P`. -/
theorem lemma11to13_of (h : Lemma12and13P) : Lemma11to13P := by
  intro x hx hL k hk
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ 200 := (mem_Icc.mp hk).2
  have hy0 : 0 < y := by positivity
  have hy1 : 1 < y := by
    by_contra hc
    push_neg at hc
    have : Real.log y ≤ 0 := Real.log_nonpos hy0.le hc
    linarith
  obtain ⟨hN1, -⟩ := Nk_bounds y k hy0.le
  have hw : 0 < wk y k := by
    unfold wk
    apply div_pos _ (by norm_num)
    apply Real.sqrt_pos.mpr
    linarith
  have hsplit := rest_split (x := x) (y := y) (k := k) hk1 hy0.le (cut_ok hx.le hk2) (wk y k)
  have hre : RestK x y k = (DK y k (wk y k)).re + (ThetaK y k (wk y k)).re := by
    have := congrArg Complex.re hsplit
    simpa using this
  have hT := lemma11 (w := wk y k) hk1 hy0 hw
  have hTre : -(3 * OddSums.A10 * (y / wk y k) * Sk y k) ≤ (ThetaK y k (wk y k)).re := by
    have := Complex.abs_re_le_norm (ThetaK y k (wk y k))
    have := neg_abs_le (ThetaK y k (wk y k)).re
    linarith
  have hD := h x hx hL k hk
  rw [hre]
  linarith

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at five rows, Lemma 6 (i) and (ii), (2.30) and (2.31), Rosser-Schoenfeld (3.3) and
`Lemma12and13P`, the `d* ≤ w` part of Section 8. -/
theorem theorem_of_lemma5_12and13 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33)
    (h : Lemma12and13P) : Theorem :=
  theorem_of_lemma5_11to13 h24 h42 h278 h396 h5 h6 h6' hTab hRS (lemma11to13_of h)

end LeanLab.RieselVaughan1983.Theta
