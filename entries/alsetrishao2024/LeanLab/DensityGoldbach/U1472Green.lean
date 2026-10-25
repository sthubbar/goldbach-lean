module

public import LeanLab.DensityGoldbach.U1471Green66
public import LeanLab.DensityGoldbach.U1472MZ

/-!
Unit U-1472, run 20261022T0804Z-19316. P0047 Alsetri and Shao 2024, Theorem 1.2.

Before: `alsetriShao_1_2_U1471 : GreenThm21Disc3 → Green62 → AlsetriShao12`.
`GreenThm21Disc3` is Green 2005 Theorem 2.1 at `p = 3` composed with Lemma 6.5. Lemma 6.5 is
elementary and is PROVED in U1472MZ.lean, `mz3`. What remains of `GreenThm21Disc3` is exactly
Green's printed Theorem 2.1 at `p = 3`, on the circle, `GreenThm21Circle3` below.

B. Green, Roth's theorem in the primes, arXiv math/0302311v3, read 2026-10-22 by WebFetch.
Section 2: `m ≤ log N`, `0 ≤ b ≤ m - 1` coprime to `m`, `Λ_{b,m,N} = {n ≤ N | nm + b prime}`,
`λ_{b,m,N}(n) = φ(m) log(nm + b)/(mN)` on `Λ`. Theorem 2.1: for real `p > 2` there is `C(p)` with
`‖Tf‖_p ≤ C(p) N^{-1/p} ‖f‖_2` for all `f : Λ → ℂ`, `Tf = (fλ)^`, the `L²` norm with respect to
`λ`. Section 6: `f~(r) = Σ_x f(x) e(-rx/N)` and `f~(r) = f^(r/N)` under `Z_N ↪ [N]`, so Green's
`f^(θ) = Σ_n f(n) e(-nθ)`, which is `Fc` of U1472MZ.lean at `n_x = gIdx x`.

Result: `thm21Disc3_of_circle : GreenThm21Circle3 → GreenThm21Disc3` PROVED, and the headline
`alsetriShao_1_2_U1472 : GreenThm21Circle3 → Green62 → AlsetriShao12`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1472
open LeanLab.DensityGoldbach.U1446 LeanLab.DensityGoldbach.U1471

/-- **Green 2005, Theorem 2.1 at `p = 3`**, printed form on the circle, for real `f = g`,
`m = W = z#` with `z` large and `N` a large prime, so that `m ≤ log N`:
`∫_0^1 |(gλ)^(θ)|³ dθ ≤ C N⁻¹ (Σ_n g(n)² λ(n))^{3/2}`, which is `‖Tg‖_3 ≤ C^{1/3} N^{-1/3} ‖g‖_2`. -/
def GreenThm21Circle3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z → ∀ b : ℕ, b < primorial z →
    Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ g : ZMod N → ℝ,
        ∫ θ in (0 : ℝ)..1, ‖Fc (gIdx N) (fun x => g x * lamG (primorial z) b N x) θ‖ ^ (3 : ℝ) ≤
          C * (N : ℝ)⁻¹ * (∑ x : ZMod N, g x ^ 2 * lamG (primorial z) b N x) ^ ((3 : ℝ) / 2)

lemma gIdx_cast (N : ℕ) [NeZero N] (x : ZMod N) : ((gIdx N x : ℕ) : ZMod N) = x := by
  unfold gIdx; split_ifs with h
  · rw [h, ZMod.natCast_self]
  · exact ZMod.natCast_zmod_val x

lemma gIdx_range (N : ℕ) [NeZero N] (x : ZMod N) : 1 ≤ gIdx N x ∧ gIdx N x ≤ N := by
  have hN := Nat.pos_of_ne_zero (NeZero.ne N)
  unfold gIdx; split_ifs with h
  · exact ⟨hN, le_rfl⟩
  · refine ⟨Nat.pos_of_ne_zero fun h0 => h ?_, (ZMod.val_lt x).le⟩
    rw [← ZMod.natCast_zmod_val x, h0, Nat.cast_zero]

/-- Green's identity `f~(r) = f^(r/N)`, Section 6. -/
lemma tilde_eq_Fc (N : ℕ) [NeZero N] (a : ZMod N → ℝ) (r : ZMod N) :
    tildeG N a r = Fc (gIdx N) a ((r.val : ℝ) / N) := by
  unfold tildeG Fc
  refine sum_congr rfl fun x _ => ?_
  congr 1
  have : -(r * x) = (((-((gIdx N x : ℤ) * r.val)) : ℤ) : ZMod N) := by
    push_cast; rw [gIdx_cast, ZMod.natCast_zmod_val]; ring
  rw [this, eC_intCast_div]; congr 1; push_cast; ring

/-- Lemma 6.5 in the objects of `GreenThm21Disc3`. -/
theorem mz3_tilde (N : ℕ) [NeZero N] (a : ZMod N → ℝ) :
    ∑ r : ZMod N, ‖tildeG N a r‖ ^ (3 : ℝ) ≤
      27 / 4 * N * ∫ θ in (0 : ℝ)..1, ‖Fc (gIdx N) a θ‖ ^ (3 : ℝ) := by
  simp only [rpow3, tilde_eq_Fc]
  exact mz3 N (gIdx N) (gIdx_range N) a

/-- `GreenThm21Disc3` from Green's printed Theorem 2.1 at `p = 3`, PROVED via `mz3`. -/
theorem thm21Disc3_of_circle (H : GreenThm21Circle3) : GreenThm21Disc3 := by
  obtain ⟨C, hC, z₁, hG⟩ := H
  refine ⟨27 / 4 * C, by positivity, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hG z hz b hb hcop
  refine ⟨N₀, fun N _ hNp hN g => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  refine le_trans (mz3_tilde N _) ?_
  have h := hN₀ N hNp hN g
  calc 27 / 4 * (N : ℝ) * ∫ θ in (0 : ℝ)..1,
        ‖Fc (gIdx N) (fun x => g x * lamG (primorial z) b N x) θ‖ ^ (3 : ℝ)
      ≤ 27 / 4 * N * (C * (N : ℝ)⁻¹ *
          (∑ x : ZMod N, g x ^ 2 * lamG (primorial z) b N x) ^ ((3 : ℝ) / 2)) := by gcongr
    _ = _ := by field_simp

/-- `Green66` from Green's printed Theorem 2.1 at `p = 3`. -/
theorem green66_of_circle (H : GreenThm21Circle3) : Green66 :=
  green66_of_thm21 (thm21Disc3_of_circle H)

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `GreenThm21Circle3` and `Green62`. -/
theorem alsetriShao_1_2_U1472 (H21 : GreenThm21Circle3) (H62 : Green62) : AlsetriShao12 :=
  alsetriShao_1_2_U1471 (thm21Disc3_of_circle H21) H62

/-! ### Faithfulness tests -/

/-- Vacuity of `GreenThm21Circle3`: for `g = 0` both sides vanish, so the inequality holds with
any `C`, the hypotheses on `z, b, N` are satisfiable, `vacuity_Green`, and the weight is a genuine
nonnegative weight, `vacuity_Thm21`. -/
theorem vacuity_Circle3 (z b N : ℕ) [NeZero N] (C : ℝ) (hC : 0 ≤ C) :
    ∫ θ in (0 : ℝ)..1, ‖Fc (gIdx N) (fun x => (0 : ℝ) * lamG (primorial z) b N x) θ‖ ^ (3 : ℝ) ≤
      C * (N : ℝ)⁻¹ * (∑ x : ZMod N, (0 : ℝ) ^ 2 * lamG (primorial z) b N x) ^ ((3 : ℝ) / 2) := by
  simp [Fc]

/-- Non-triviality of `GreenThm21Circle3`: the left side is a genuine `L³` mass. At `g = 1` and a
point `t`, the integrand is `|Σ_x λ(x) e(-n_x t)|³`, and at `t = 0` it equals `(Σ λ)³`. -/
theorem nontrivial_Circle3 (N W b : ℕ) [NeZero N] :
    ‖Fc (gIdx N) (fun x => (1 : ℝ) * lamG W b N x) 0‖ = ∑ x : ZMod N, lamG W b N x := by
  unfold Fc
  simp only [mul_zero, one_mul]
  have : ∀ x : ZMod N, (lamG W b N x : ℂ) * eC 0 = ((lamG W b N x : ℝ) : ℂ) := by
    intro x; simp [eC]
  simp_rw [this]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg fun x _ => lamG_nonneg _ _ _ _)]

end LeanLab.DensityGoldbach.U1472

