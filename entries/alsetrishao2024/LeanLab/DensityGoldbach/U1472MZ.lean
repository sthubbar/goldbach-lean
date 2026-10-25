module

public import Mathlib

/-!
Unit U-1472, run 20261022T0804Z-19316. P0047 Alsetri and Shao 2024, cited input `GreenThm21Disc3`.

Green 2005, Roth's theorem in the primes, arXiv math/0302311v3, Section 6, Lemma 6.5
(Marcinkiewicz-Zygmund): for `f : [N] → ℂ` and real `p > 1`,
`Σ_{r ∈ Z_N} |f~(r)|^p = Σ_{r=0}^{N-1} |f^(r/N)|^p ≤ C(p) N ∫ |f^(θ)|^p dθ`.
Here it is PROVED at `p = 3` with `C = 27/4`, for real coefficients on frequencies
`n_x ∈ {1, …, N}`, by Green's own route: a kernel built from two Dirichlet kernels whose Fourier
coefficients are `1` on `{0, …, N}`, a pointwise Young inequality in place of Jensen, and the exact
evaluation of the kernel sums over `r` by orthogonality on `Z_N`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Real

noncomputable section
namespace LeanLab.DensityGoldbach.U1472

/-- `e(t) = exp(2πit)`. -/
def eC (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

@[fun_prop] lemma continuous_eC : Continuous eC := by unfold eC; fun_prop

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show 2 * (π : ℂ) * Complex.I * t = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma conj_eC (t : ℝ) : (starRingEnd ℂ) (eC t) = eC (-t) := by
  unfold eC; rw [← Complex.exp_conj]; congr 1; simp only [map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]; push_cast; ring

lemma eC_intCast_div (N : ℕ) [NeZero N] (j : ℤ) :
    ZMod.stdAddChar (j : ZMod N) = eC (j / N) := by
  rw [ZMod.stdAddChar_coe]; unfold eC; congr 1; push_cast; ring

/-- `∫_0^1 e(c + mθ) dθ = e(c)` if `m = 0`, else `0`. -/
lemma integral_eC (c : ℝ) (m : ℤ) :
    ∫ θ in (0 : ℝ)..1, eC (c + m * θ) = if m = 0 then eC c else 0 := by
  have hs : ∀ θ : ℝ, eC (c + m * θ) = eC c * Complex.exp ((2 * π * Complex.I * m) * θ) := by
    intro θ; rw [eC_add]; unfold eC; congr 1; congr 1; push_cast; ring
  simp_rw [hs]
  rw [intervalIntegral.integral_const_mul]
  split_ifs with hm
  · subst hm; simp
  · have hc : (2 * π * Complex.I * m) ≠ 0 := by
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp_all
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * m * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show 2 * π * Complex.I * m * ((1 : ℝ) : ℂ) = m * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h1]; simp

lemma integral_sum_eC {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ι → ℝ) (m : ι → ℤ) :
    ∫ θ in (0 : ℝ)..1, ∑ i ∈ s, a i * eC (c i + m i * θ) =
      ∑ i ∈ s, a i * (if m i = 0 then eC (c i) else 0) := by
  rw [intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_eC]
  · intro i _; exact (by fun_prop : Continuous fun θ : ℝ => a i * eC (c i + m i * θ)).intervalIntegrable _ _

/-! ### Dirichlet kernels and the reproducing kernel -/

/-- `D_L(φ) = Σ_{j<L} e(jφ)`. -/
def D (L : ℕ) (φ : ℝ) : ℂ := ∑ j ∈ range L, eC (j * φ)

@[fun_prop] lemma continuous_D (L : ℕ) : Continuous (D L) := by unfold D; fun_prop

lemma normD_neg (L : ℕ) (φ : ℝ) : ‖D L (-φ)‖ = ‖D L φ‖ := by
  have : D L (-φ) = (starRingEnd ℂ) (D L φ) := by
    unfold D; rw [map_sum]; refine sum_congr rfl fun j _ => ?_
    rw [conj_eC]; congr 1; ring
  rw [this, Complex.norm_conj]

lemma normsq_D (L : ℕ) (φ : ℝ) : ((‖D L φ‖ ^ 2 : ℝ) : ℂ) =
    ∑ j ∈ range L, ∑ j' ∈ range L, eC (((j : ℝ) - j') * φ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold D; rw [map_sum, sum_mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
  rw [conj_eC, ← eC_add]; congr 1; ring

/-- The kernel `K(φ) = N⁻¹ D_N(φ) D_{2N}(-φ)`, whose coefficients are `1` on `-N, …, 0`. -/
def K (N : ℕ) (φ : ℝ) : ℂ := (1 / (N : ℂ)) * (D N φ * D (2 * N) (-φ))

/-- The positive majorant `w(φ) = |D_{2N}(φ)|²/(4N) + |D_N(φ)|²/N` of `|K|`. -/
def w (N : ℕ) (φ : ℝ) : ℝ := ‖D (2 * N) φ‖ ^ 2 / (4 * N) + ‖D N φ‖ ^ 2 / N

@[fun_prop] lemma continuous_w (N : ℕ) : Continuous (w N) := by unfold w; fun_prop

lemma w_nonneg (N : ℕ) (φ : ℝ) : 0 ≤ w N φ := by unfold w; positivity

lemma normK_le (N : ℕ) [NeZero N] (φ : ℝ) : ‖K N φ‖ ≤ w N φ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold K w
  rw [norm_mul, norm_mul, normD_neg, norm_div, norm_one]
  simp only [Complex.norm_natCast]
  set x := ‖D (2 * N) φ‖
  set y := ‖D N φ‖
  have : x * y ≤ x ^ 2 / 4 + y ^ 2 := by nlinarith [sq_nonneg (x / 2 - y)]
  calc 1 / (N : ℝ) * (y * x) = (x * y) / N := by ring
    _ ≤ (x ^ 2 / 4 + y ^ 2) / N := div_le_div_of_nonneg_right this hN.le
    _ = _ := by ring

@[fun_prop] lemma continuous_K (N : ℕ) : Continuous (K N) := by unfold K; fun_prop

/-! ### The trigonometric polynomial and the reproducing formula -/

/-- `F(θ) = Σ_x a(x) e(-n_x θ)`, Green's `f^` for `f = a` placed at the frequencies `n_x`. -/
def Fc {ι : Type*} [Fintype ι] (n : ι → ℕ) (a : ι → ℝ) (θ : ℝ) : ℂ :=
  ∑ x, (a x : ℂ) * eC (-(n x : ℝ) * θ)

@[fun_prop] lemma continuous_Fc {ι : Type*} [Fintype ι] (n : ι → ℕ) (a : ι → ℝ) :
    Continuous (Fc n a) := by unfold Fc; fun_prop

lemma Kexp (N : ℕ) (φ : ℝ) : K N φ =
    ∑ p ∈ range N ×ˢ range (2 * N), (1 / (N : ℂ)) * eC ((((p.1 : ℤ) - p.2 : ℤ) : ℝ) * φ) := by
  unfold K D
  rw [sum_product, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j' _ => ?_
  rw [← eC_add]; congr 2; push_cast; ring

lemma integral_eC_K (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m ∧ m ≤ N) (t : ℝ) :
    ∫ θ in (0 : ℝ)..1, eC (-(m : ℝ) * θ) * K N (t - θ) = eC (-(m : ℝ) * t) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h : ∀ θ : ℝ, eC (-(m : ℝ) * θ) * K N (t - θ) =
      ∑ p ∈ range N ×ˢ range (2 * N), (1 / (N : ℂ)) *
        eC ((((p.1 : ℤ) - p.2 : ℤ) : ℝ) * t + ((-(m : ℤ) - p.1 + p.2 : ℤ) : ℝ) * θ) := by
    intro θ
    rw [Kexp, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_left_comm, ← eC_add]; congr 2; push_cast; ring
  simp_rw [h]
  rw [integral_sum_eC, sum_product]
  have hinner : ∀ j ∈ range N, (∑ j' ∈ range (2 * N), (1 / (N : ℂ)) *
      (if (-(m : ℤ) - ((j, j').1 : ℤ) + ((j, j').2 : ℤ) : ℤ) = 0 then
        eC (((((j, j').1 : ℤ) - (j, j').2 : ℤ) : ℝ) * t) else 0)) =
      (1 / (N : ℂ)) * eC (-(m : ℝ) * t) := by
    intro j hj
    rw [sum_eq_single (j + m)]
    · rw [if_pos (by push_cast; ring)]; congr 2; push_cast; ring
    · intro j' _ hj'
      rw [if_neg (show ¬((-(m : ℤ) - (j : ℤ) + (j' : ℤ) : ℤ) = 0) by omega), mul_zero]
    · intro h; exfalso; apply h; rw [mem_range] at hj ⊢; omega
  rw [sum_congr rfl hinner, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- Reproducing formula: `F(t) = ∫_0^1 F(θ) K(t - θ) dθ` when every `n_x ∈ {1, …, N}`. -/
lemma reproduce {ι : Type*} [Fintype ι] (N : ℕ) [NeZero N] (n : ι → ℕ)
    (hn : ∀ x, 1 ≤ n x ∧ n x ≤ N) (a : ι → ℝ) (t : ℝ) :
    ∫ θ in (0 : ℝ)..1, Fc n a θ * K N (t - θ) = Fc n a t := by
  have h : ∀ θ : ℝ, Fc n a θ * K N (t - θ) =
      ∑ x, (a x : ℂ) * (eC (-(n x : ℝ) * θ) * K N (t - θ)) := by
    intro θ; unfold Fc; rw [sum_mul]; refine sum_congr rfl fun x _ => ?_; ring
  simp_rw [h]
  rw [intervalIntegral.integral_finsetSum]
  · unfold Fc
    refine sum_congr rfl fun x _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_eC_K N (n x) (hn x)]
  · intro x _
    exact (by fun_prop : Continuous fun θ : ℝ =>
      (a x : ℂ) * (eC (-(n x : ℝ) * θ) * K N (t - θ))).intervalIntegrable _ _

/-! ### Integrals of the majorant -/

lemma integral_normsq_D (L : ℕ) (t : ℝ) :
    ∫ θ in (0 : ℝ)..1, ((‖D L (t - θ)‖ ^ 2 : ℝ) : ℂ) = L := by
  have hexp : ∀ θ, ((‖D L (t - θ)‖ ^ 2 : ℝ) : ℂ) = ∑ i ∈ range L ×ˢ range L,
      (1 : ℂ) * eC ((((i.1 : ℤ) - i.2 : ℤ) : ℝ) * t + ((-((i.1 : ℤ) - i.2) : ℤ) : ℝ) * θ) := by
    intro θ; rw [normsq_D, sum_product]
    refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
    rw [one_mul]; congr 1; push_cast; ring
  simp_rw [hexp]
  rw [integral_sum_eC, sum_product]
  have : ∀ j ∈ range L, (∑ j' ∈ range L, (1 : ℂ) *
      (if (-((j : ℤ) - j') : ℤ) = 0 then eC ((((j : ℤ) - j' : ℤ) : ℝ) * t) else 0)) = 1 := by
    intro j _
    rw [sum_eq_single j]
    · simp [eC]
    · intro j' _ hj'; rw [if_neg (by omega), mul_zero]
    · intro h; exact absurd ‹j ∈ range L› h
  rw [sum_congr rfl this]; simp

lemma integral_w (N : ℕ) [NeZero N] (t : ℝ) : ∫ θ in (0 : ℝ)..1, w N (t - θ) = 3 / 2 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  unfold w
  push_cast
  have i1 := integral_normsq_D (2 * N) t
  have i2 := integral_normsq_D N t
  push_cast at i1 i2
  rw [intervalIntegral.integral_add, intervalIntegral.integral_div, intervalIntegral.integral_div,
    i1, i2]
  · first | (field_simp; ring) | field_simp | norm_num
  · exact (by fun_prop : Continuous fun θ : ℝ =>
      ((‖D (2 * N) (t - θ)‖ : ℂ)) ^ 2 / (4 * N)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun θ : ℝ =>
      ((‖D N (t - θ)‖ : ℂ)) ^ 2 / N).intervalIntegrable _ _

/-! ### The sums over `r` of the majorant -/

lemma orth' (N : ℕ) [NeZero N] (x : ZMod N) :
    ∑ r : ZMod N, ZMod.stdAddChar (r * x) = if x = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)]
  simp [ZMod.card]

lemma card_fiber_le (N : ℕ) [NeZero N] (L : ℕ) (hL : L ≤ 2 * N) (j : ℕ) :
    ((range L).filter (fun j' : ℕ => ((j' : ℤ) : ZMod N) = ((j : ℤ) : ZMod N))).card ≤ 2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  calc _ ≤ ({j % N, j % N + N} : Finset ℕ).card := by
        apply card_le_card
        intro j' hj'
        simp only [mem_filter, mem_range] at hj'
        obtain ⟨hj'L, hc⟩ := hj'
        have hc' : j' % N = j % N := by
          have := (ZMod.intCast_eq_intCast_iff' (j' : ℤ) (j : ℤ) N).1 hc
          exact_mod_cast this
        have h1 := Nat.div_add_mod j' N
        have h2 : j' / N < 2 := by
          rw [Nat.div_lt_iff_lt_mul hN]; omega
        simp only [mem_insert, mem_singleton]
        generalize hq : j' / N = q at h1 h2
        generalize hr : j' % N = m at h1 hc'
        obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
        · left; simp at h1; omega
        · right; simp at h1; omega
    _ ≤ 2 := card_le_two

lemma sum_r_normsq_D (N : ℕ) [NeZero N] (L : ℕ) (hL : L ≤ 2 * N) (θ : ℝ) :
    ∑ r : ZMod N, ‖D L ((r.val : ℝ) / N - θ)‖ ^ 2 ≤ N * (2 * L) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  -- expand and use orthogonality
  have hc : ((∑ r : ZMod N, ‖D L ((r.val : ℝ) / N - θ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ range L, ∑ j' ∈ range L, eC (-(((j : ℝ) - j') * θ)) *
        (if (((j : ℤ) - j' : ℤ) : ZMod N) = 0 then (N : ℂ) else 0) := by
    rw [Complex.ofReal_sum]
    simp_rw [normsq_D]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j' _ => ?_
    have horth := LeanLab.DensityGoldbach.U1472.orth' N (((j : ℤ) - j' : ℤ) : ZMod N)
    rw [← horth, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [show (((j : ℝ) - j') * ((r.val : ℝ) / N - θ)) =
      (-(((j : ℝ) - j') * θ)) + ((((j : ℤ) - j') * r.val : ℤ) : ℝ) / N by push_cast; ring, eC_add,
      ← eC_intCast_div]
    congr 2; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]; ring
  have hle : ‖((∑ r : ZMod N, ‖D L ((r.val : ℝ) / N - θ)‖ ^ 2 : ℝ) : ℂ)‖ ≤ N * (2 * L) := by
    rw [hc]
    refine le_trans (norm_sum_le _ _) ?_
    calc _ ≤ ∑ j ∈ range L, ∑ j' ∈ range L,
          (if ((j' : ℤ) : ZMod N) = ((j : ℤ) : ZMod N) then (N : ℝ) else 0) := by
          refine sum_le_sum fun j _ => le_trans (norm_sum_le _ _) (sum_le_sum fun j' _ => ?_)
          rw [norm_mul, norm_eC, one_mul]
          by_cases h : ((j' : ℤ) : ZMod N) = ((j : ℤ) : ZMod N)
          · rw [if_pos (by push_cast at h ⊢; rw [h, sub_self]), if_pos h]; simp
          · rw [if_neg (by push_cast at h ⊢; intro h'; exact h (sub_eq_zero.1 h').symm), if_neg h]
            simp
      _ ≤ ∑ j ∈ range L, (2 * N : ℝ) := by
          refine sum_le_sum fun j _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          have := card_fiber_le N L hL j
          have h2 : (((range L).filter (fun j' : ℕ => ((j' : ℤ) : ZMod N) =
              ((j : ℤ) : ZMod N))).card : ℝ) ≤ 2 := by exact_mod_cast this
          nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      _ = N * (2 * L) := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  rw [Complex.norm_real, Real.norm_eq_abs] at hle
  exact le_trans (le_abs_self _) hle

lemma sum_r_w (N : ℕ) [NeZero N] (θ : ℝ) : ∑ r : ZMod N, w N ((r.val : ℝ) / N - θ) ≤ 3 * N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold w
  rw [sum_add_distrib, ← sum_div, ← sum_div]
  have h1 := sum_r_normsq_D N (2 * N) le_rfl θ
  have h2 := sum_r_normsq_D N N (by omega) θ
  push_cast at h1 h2
  calc _ ≤ ((N : ℝ) * (2 * (2 * N))) / (4 * N) + ((N : ℝ) * (2 * N)) / N := by gcongr
    _ = 3 * N := by first | (field_simp; ring) | field_simp | ring

/-! ### Young's inequality step -/

lemma young_cube (X A B : ℝ) (hX : 0 ≤ X) (hB : 0 < B) (hA : 0 ≤ A)
    (H : ∀ s : ℝ, 0 < s → X ≤ s ^ 2 / 3 * A + 2 / (3 * s) * B) : X ^ 3 ≤ B ^ 2 * A := by
  rcases hX.eq_or_lt with h | h
  · rw [← h]; simp; positivity
  · have h1 := H (B / X) (by positivity)
    have e : 2 / (3 * (B / X)) * B = 2 * X / 3 := by field_simp
    rw [e, div_pow] at h1
    have h2 : X / 3 ≤ B ^ 2 / X ^ 2 / 3 * A := by linarith
    have h3 : X ^ 3 = X ^ 2 * X := by ring
    have h4 : X ^ 2 * (X / 3) ≤ X ^ 2 * (B ^ 2 / X ^ 2 / 3 * A) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : X ^ 2 * (B ^ 2 / X ^ 2 / 3 * A) = B ^ 2 * A / 3 := by field_simp
    nlinarith

lemma young_pt (y v s : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) (hs : 0 < s) :
    y * v ≤ s ^ 2 / 3 * (y ^ 3 * v) + 2 / (3 * s) * v := by
  have key : 0 ≤ (s * y - 1) ^ 2 * (s * y + 2) := by positivity
  have h1 : y ≤ s ^ 2 / 3 * y ^ 3 + 2 / (3 * s) := by
    rw [show s ^ 2 / 3 * y ^ 3 + 2 / (3 * s) = ((s * y) ^ 3 + 2) / (3 * s) by first | (field_simp; ring) | field_simp,
      le_div_iff₀ (by positivity)]
    nlinarith [key]
  nlinarith [mul_le_mul_of_nonneg_right h1 hv]

/-! ### Lemma 6.5 at `p = 3` -/

/-- **Green 2005, Lemma 6.5 at `p = 3`**, PROVED: `Σ_r |F(r/N)|³ ≤ (27/4) N ∫_0^1 |F|³`. -/
theorem mz3 {ι : Type*} [Fintype ι] (N : ℕ) [NeZero N] (n : ι → ℕ)
    (hn : ∀ x, 1 ≤ n x ∧ n x ≤ N) (a : ι → ℝ) :
    ∑ r : ZMod N, ‖Fc n a ((r.val : ℝ) / N)‖ ^ 3 ≤
      27 / 4 * N * ∫ θ in (0 : ℝ)..1, ‖Fc n a θ‖ ^ 3 := by
  have hpt : ∀ t : ℝ, ‖Fc n a t‖ ^ 3 ≤
      (3 / 2) ^ 2 * ∫ θ in (0 : ℝ)..1, ‖Fc n a θ‖ ^ 3 * w N (t - θ) := by
    intro t
    have hX : ‖Fc n a t‖ ≤ ∫ θ in (0 : ℝ)..1, ‖Fc n a θ‖ * w N (t - θ) := by
      rw [← reproduce N n hn a t]
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm zero_le_one) ?_
      refine intervalIntegral.integral_mono_on zero_le_one
        ((by fun_prop : Continuous fun θ => ‖Fc n a θ * K N (t - θ)‖).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun θ => ‖Fc n a θ‖ * w N (t - θ)).intervalIntegrable _ _)
        fun θ _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (normK_le N _) (norm_nonneg _)
    refine young_cube _ _ _ (norm_nonneg _) (by norm_num)
      (intervalIntegral.integral_nonneg zero_le_one fun θ _ =>
        mul_nonneg (by positivity) (w_nonneg _ _)) fun s hs => ?_
    refine le_trans hX ?_
    rw [← integral_w N t, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_mono_on zero_le_one
        ((by fun_prop : Continuous fun θ => ‖Fc n a θ‖ * w N (t - θ)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun θ => s ^ 2 / 3 * (‖Fc n a θ‖ ^ 3 * w N (t - θ)) +
          2 / (3 * s) * w N (t - θ)).intervalIntegrable _ _) fun θ _ => ?_
      exact young_pt _ _ _ (norm_nonneg _) (w_nonneg _ _) hs
    · exact (by fun_prop : Continuous fun θ =>
        s ^ 2 / 3 * (‖Fc n a θ‖ ^ 3 * w N (t - θ))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ => 2 / (3 * s) * w N (t - θ)).intervalIntegrable _ _
  calc _ ≤ ∑ r : ZMod N, (3 / 2) ^ 2 *
        ∫ θ in (0 : ℝ)..1, ‖Fc n a θ‖ ^ 3 * w N ((r.val : ℝ) / N - θ) :=
        sum_le_sum fun r _ => hpt _
    _ = (3 / 2) ^ 2 * ∫ θ in (0 : ℝ)..1,
          ‖Fc n a θ‖ ^ 3 * ∑ r : ZMod N, w N ((r.val : ℝ) / N - θ) := by
        rw [← mul_sum]; congr 1
        rw [← intervalIntegral.integral_finsetSum]
        · congr 1; funext θ; rw [mul_sum]
        · intro r _
          exact (by fun_prop : Continuous fun θ =>
            ‖Fc n a θ‖ ^ 3 * w N ((r.val : ℝ) / N - θ)).intervalIntegrable _ _
    _ ≤ (3 / 2) ^ 2 * ∫ θ in (0 : ℝ)..1, ‖Fc n a θ‖ ^ 3 * (3 * N) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun θ _ =>
          mul_le_mul_of_nonneg_left (sum_r_w N θ) (by positivity)
        · exact (by fun_prop : Continuous fun θ =>
            ‖Fc n a θ‖ ^ 3 * ∑ r : ZMod N, w N ((r.val : ℝ) / N - θ)).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun θ => ‖Fc n a θ‖ ^ 3 * (3 * N)).intervalIntegrable _ _
    _ = 27 / 4 * N * ∫ θ in (0 : ℝ)..1, ‖Fc n a θ‖ ^ 3 := by
        rw [intervalIntegral.integral_mul_const]; ring

end LeanLab.DensityGoldbach.U1472
