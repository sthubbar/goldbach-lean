module

public import LeanLab.DensityGoldbach.U1467Bohr

/-!
Unit U-1471, run 20261022T0403Z-7595. P0047 Alsetri and Shao 2024, the cited input `Green66`.

`Green66` of U1446Thm12.lean is Green's Lemma 6.6 at `p = 3`, extended from `a = Aμ` to every
`0 ≤ f ≤ ν_b`, in the lab's indexing `n ∈ {0, …, N-1}` with weight `ν_b`. Here it is reduced to
`GreenThm21Disc3`, the restriction estimate Green's Lemma 6.6 rests on, in Green's own objects:

B. Green, Roth's theorem in the primes, arXiv math/0302311v3, read 2026-10-22 by WebFetch of the PDF.
Section 2: `Λ_{b,m,N} = {n ≤ N | nm + b prime}`, `λ_{b,m,N}(n) = φ(m) log(nm+b)/(mN)` on `Λ`,
Theorem 2.1 (Bourgain): for real `p > 2` there is `C(p)` with `‖Tf‖_p ≤ C(p) N^{-1/p} ‖f‖_2`,
display (2.2), `Tf = (f λ)^`, the `L²` norm taken with respect to `λ_{b,m,N}`, for `m ≤ log N`.
Section 6: `μ = λ_{b,m,N}` on `Z_N` through `Z_N ↪ [N]`, `f~(r) = Σ_x f(x) e(-rx/N)`, and
Lemma 6.5 (Marcinkiewicz-Zygmund) `Σ_r |f~(r)|^p ≤ C(p) N ∫ |f^(θ)|^p dθ`.
Theorem 2.1 followed by Lemma 6.5 is exactly `GreenThm21Disc3` at `p = 3`, for real `f`.
Printed page numbers are not in the text extraction; locations are by section and display.

The reduction, PROVED here: `green66_of_thm21 : GreenThm21Disc3 → Green66`, writing
`f = f·1_{x≠0} + f(0)δ_0`, `g = f/ν_b` off `0`, so `‖g‖²_{L²(μ)} ≤ E ν_b ≤ 2` by the lab's PNT
`nu_avg_close`, and the `δ_0` term, Green's `n = N` against the lab's `n = 0`, is `O(N^{-2/3})`,
joined by Minkowski in `ℓ³`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1471
open LeanLab.DensityGoldbach.U1446

/-- Green's index of `x ∈ Z_N` under `Z_N ↪ [N] = {1, …, N}`: `x.val`, and `N` for `x = 0`. -/
def gIdx (N : ℕ) [NeZero N] (x : ZMod N) : ℕ := if x = 0 then N else x.val

/-- Green's weight `μ = λ_{b,m,N}` on `Z_N`, Section 2 and Section 6, with `m = W`. -/
def lamG (W b N : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  if (gIdx N x * W + b).Prime then
    (Nat.totient W : ℝ) * Real.log (gIdx N x * W + b) / (W * N) else 0

/-- Green's discrete transform `f~(r) = Σ_x f(x) e(-rx/N)`, Section 6. -/
def tildeG (N : ℕ) [NeZero N] (a : ZMod N → ℝ) (r : ZMod N) : ℂ :=
  ∑ x : ZMod N, (a x : ℂ) * ZMod.stdAddChar (-(r * x))

/-- **Green 2005, Theorem 2.1, display (2.2), discretised by Lemma 6.5, at `p = 3`**, for real
coefficients, `m = W = z#` with `z` large and `N` a large prime, so that `m ≤ log N`:
`Σ_r |(gμ)~(r)|³ ≤ C (Σ_x g(x)² μ(x))^{3/2}` with `C` depending on nothing. -/
def GreenThm21Disc3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z → ∀ b : ℕ, b < primorial z →
    Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ g : ZMod N → ℝ,
        ∑ r : ZMod N, ‖tildeG N (fun x => g x * lamG (primorial z) b N x) r‖ ^ (3 : ℝ) ≤
          C * (∑ x : ZMod N, g x ^ 2 * lamG (primorial z) b N x) ^ ((3 : ℝ) / 2)

/-! ### Elementary pieces -/

lemma lamG_ne_zero_pt (W b N : ℕ) [NeZero N] (x : ZMod N) (hx : x ≠ 0) :
    lamG W b N x = nuW W b N x / N := by
  unfold lamG nuW gIdx
  rw [if_neg hx, show x.val * W + b = W * x.val + b by ring]
  split_ifs
  · push_cast; ring
  · simp

lemma lamG_nonneg (W b N : ℕ) [NeZero N] (x : ZMod N) : 0 ≤ lamG W b N x := by
  unfold lamG
  split_ifs
  · have := Real.log_natCast_nonneg (gIdx N x * W + b)
    push_cast at this
    exact div_nonneg (mul_nonneg (by positivity) this) (by positivity)
  · exact le_rfl

lemma hatE_add (N : ℕ) [NeZero N] (f g : ZMod N → ℝ) (r : ZMod N) :
    hatE N (f + g) r = hatE N f r + hatE N g r := by
  unfold hatE
  simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add]

lemma hatE_eq_tilde (N : ℕ) [NeZero N] (f a : ZMod N → ℝ) (h : ∀ x, a x = f x / N)
    (r : ZMod N) : hatE N f r = tildeG N a r := by
  unfold hatE tildeG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x]; push_cast; ring

lemma hatE_delta (N : ℕ) [NeZero N] (c : ℝ) (r : ZMod N) :
    hatE N (fun x => if x = 0 then c else 0) r = ((c / N : ℝ) : ℂ) := by
  unfold hatE
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp; ring
  · intro x _ hx; simp [hx]
  · simp

lemma rpow3 (x : ℝ) : x ^ (3 : ℝ) = x ^ 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The `δ_0` piece has `ℓ³` mass at most `1` once `N ≥ B³` with `f(0) ≤ B`. -/
lemma delta_mass (N : ℕ) [NeZero N] (c B : ℝ) (hc : 0 ≤ c) (hcB : c ≤ B) (hN : B ^ 3 ≤ N) :
    ∑ r : ZMod N, ‖hatE N (fun x => if x = 0 then c else 0) r‖ ^ (3 : ℝ) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  simp only [hatE_delta, Complex.norm_real, Real.norm_eq_abs, rpow3, sum_const, card_univ,
    ZMod.card, nsmul_eq_mul]
  rw [abs_of_nonneg (div_nonneg hc hN0.le), div_pow]
  have hc3 : c ^ 3 ≤ N := le_trans (pow_le_pow_left₀ hc hcB 3) hN
  rw [mul_div_assoc', div_le_one (by positivity)]
  have h1 : (N : ℝ) * c ^ 3 ≤ N * N := mul_le_mul_of_nonneg_left hc3 hN0.le
  have h2 : (N : ℝ) * N ≤ N ^ 3 := by
    have : (N : ℝ) * N * 1 ≤ N * N * N := mul_le_mul_of_nonneg_left hN1 (by positivity)
    nlinarith
  linarith

/-! ### The reduction -/

theorem green66_of_thm21 (H : GreenThm21Disc3) : Green66 := by
  obtain ⟨C, hC, z₁, hG⟩ := H
  refine ⟨(C * 2 ^ ((3 : ℝ) / 2)) ^ (1 / (3 : ℝ)) + 1, by positivity, z₁,
    fun z hz b hb hcop => ?_⟩
  set W := primorial z
  obtain ⟨N₁, hN₁⟩ := hG z hz b hb hcop
  obtain ⟨N₂, hN₂⟩ := nu_avg_close W b hb hcop 1 one_pos
  set B : ℝ := if b.Prime then (Nat.totient W : ℝ) / W * Real.log b else 0
  refine ⟨max N₁ (max N₂ ⌈B ^ 3⌉₊), fun N _ hNp hN f hf => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  -- split `f = f₁ + f₀`
  set f₁ : ZMod N → ℝ := fun x => if x = 0 then 0 else f x
  set f₀ : ZMod N → ℝ := fun x => if x = 0 then f 0 else 0
  have hsplit : f = f₁ + f₀ := by
    funext x; by_cases hx : x = 0
    · subst hx; simp [f₁, f₀]
    · simp [f₁, f₀, hx]
  -- the coefficient `g = f / ν` off `0`
  set g : ZMod N → ℝ := fun x => if x = 0 then 0 else f x / nuW W b N x
  have hga : ∀ x, g x * lamG W b N x = f₁ x / N := by
    intro x
    by_cases hx : x = 0
    · simp [g, f₁, hx]
    · simp only [g, f₁, if_neg hx]
      rw [lamG_ne_zero_pt W b N x hx]
      by_cases hν : nuW W b N x = 0
      · have : f x = 0 := le_antisymm (hν ▸ (hf x).2) (hf x).1
        simp [hν, this]
      · field_simp
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
    intro x
    by_cases hx : x = 0
    · simp [g, hx]
    · simp only [g, if_neg hx]
      exact ⟨div_nonneg (hf x).1 (nuW_nonneg _ _ _ _), div_le_one_of_le₀ (hf x).2
        (nuW_nonneg _ _ _ _)⟩
  -- `‖g‖²_{L²(μ)} ≤ E ν ≤ 2`
  have hL2 : ∑ x : ZMod N, g x ^ 2 * lamG W b N x ≤ 2 := by
    have hav := hN₂ N (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
    have hav2 : avg N (nuW W b N) ≤ 2 := by linarith [(abs_le.1 hav).2]
    have hpt : ∀ x, g x ^ 2 * lamG W b N x ≤ nuW W b N x / N := by
      intro x
      by_cases hx : x = 0
      · simp only [g, if_pos hx]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact div_nonneg (nuW_nonneg _ _ _ _) hNr.le
      · rw [lamG_ne_zero_pt W b N x hx]
        have hl : 0 ≤ nuW W b N x / N := div_nonneg (nuW_nonneg _ _ _ _) hNr.le
        have : g x ^ 2 ≤ 1 := by nlinarith [hg01 x]
        nlinarith
    calc _ ≤ ∑ x : ZMod N, nuW W b N x / N := sum_le_sum fun x _ => hpt x
      _ = avg N (nuW W b N) := by
          unfold avg; rw [Finset.mul_sum]; exact sum_congr rfl fun x _ => by ring
      _ ≤ 2 := hav2
  -- the main piece
  have hT1 : ∑ r : ZMod N, ‖hatE N f₁ r‖ ^ (3 : ℝ) ≤ C * 2 ^ ((3 : ℝ) / 2) := by
    have e : ∀ r, hatE N f₁ r = tildeG N (fun x => g x * lamG W b N x) r :=
      fun r => hatE_eq_tilde N f₁ _ hga r
    simp only [e]
    refine le_trans (hN₁ N hNp (le_trans (le_max_left _ _) hN) g) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    exact Real.rpow_le_rpow (sum_nonneg fun x _ => mul_nonneg (sq_nonneg _)
      (lamG_nonneg _ _ _ _)) hL2 (by norm_num)
  -- the `δ_0` piece, Green's `n = N` against the lab's `n = 0`
  have hT0 : ∑ r : ZMod N, ‖hatE N f₀ r‖ ^ (3 : ℝ) ≤ 1 := by
    have hB : f 0 ≤ B := by
      have := (hf 0).2
      simpa [nuW, B] using this
    have hBN : B ^ 3 ≤ N := by
      have h1 := Nat.le_ceil (B ^ 3)
      have h2 : ((⌈B ^ 3⌉₊ : ℕ) : ℝ) ≤ N := by
        exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
      linarith
    exact delta_mass N (f 0) B (hf 0).1 hB hBN
  -- Minkowski in `ℓ³`
  have hp : (1 : ℝ) ≤ 3 := by norm_num
  have hadd : ∀ r, ‖hatE N f r‖ ≤ ‖hatE N f₁ r‖ + ‖hatE N f₀ r‖ := by
    intro r; rw [hsplit, hatE_add]; exact norm_add_le _ _
  have hmono : lpHat N 3 f ≤
      (∑ r : ZMod N, (‖hatE N f₁ r‖ + ‖hatE N f₀ r‖) ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) := by
    unfold lpHat
    exact Real.rpow_le_rpow (sum_nonneg fun r _ => by positivity)
      (sum_le_sum fun r _ => Real.rpow_le_rpow (norm_nonneg _) (hadd r) (by norm_num))
      (by norm_num)
  have hmink := Real.Lp_add_le_of_nonneg (s := (univ : Finset (ZMod N)))
    (f := fun r => ‖hatE N f₁ r‖) (g := fun r => ‖hatE N f₀ r‖) hp
    (fun r _ => norm_nonneg _) (fun r _ => norm_nonneg _)
  have h1 : (∑ r : ZMod N, ‖hatE N f₁ r‖ ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) ≤
      (C * 2 ^ ((3 : ℝ) / 2)) ^ (1 / (3 : ℝ)) :=
    Real.rpow_le_rpow (sum_nonneg fun r _ => by positivity) hT1 (by norm_num)
  have h0 : (∑ r : ZMod N, ‖hatE N f₀ r‖ ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one (sum_nonneg fun r _ => by positivity) hT0 (by norm_num)
  linarith

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `GreenThm21Disc3` and `Green62`. -/
theorem alsetriShao_1_2_U1471 (H21 : GreenThm21Disc3) (H62 : Green62) : AlsetriShao12 :=
  LeanLab.DensityGoldbach.U1467.alsetriShao_1_2_U1467 H62 (green66_of_thm21 H21)

/-- Vacuity: the hypotheses of `GreenThm21Disc3` can hold, `g = 0` with any prime `N`, and the
weight `lamG` is a genuine nonnegative majorant, positive at `x = 1` when `W + b` is prime. -/
theorem vacuity_Thm21 : lamG 2 1 3 1 > 0 := by
  unfold lamG gIdx
  have h0 : ((1 : ZMod 3) = 0) = False := by simp
  have hv : (1 : ZMod 3).val = 1 := rfl
  simp only [h0, if_false, hv]
  rw [if_pos (by norm_num)]
  have : (0 : ℝ) < Real.log ((1 * 2 + 1 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  push_cast at this ⊢
  positivity

end LeanLab.DensityGoldbach.U1471
