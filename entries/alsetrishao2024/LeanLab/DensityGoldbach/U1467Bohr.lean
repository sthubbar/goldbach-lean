module

public import LeanLab.DensityGoldbach.U1467Lemma32

/-!
U-1467, run 20261022T0403Z-7595: the Bohr set size bound `BohrLower`, Tao and Vu, Additive
Combinatorics, Lemma 4.20, by pigeonhole. With `K ≥ 2π/ε` buckets per frequency, the map
`x ↦ (⌊K (rx mod N)/N⌋)_{r ∈ R}` takes at most `K^{|R|}` values, so a fibre `F` has
`|F| ≥ N/K^{|R|}`; for `x, x₀ ∈ F`, `|e_N(r(x - x₀)) - 1| ≤ 2π/K ≤ ε`, so `F - x₀` lies in the
Bohr set. Hence `κ = K^{-k}`.

With this, Alsetri-Shao Proposition 3.1 is PROVED, `as_prop31_proved`, and Theorem 1.2 is
CONDITIONAL ON `Green62` and `Green66` only, `alsetriShao_1_2_U1467`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1467
open LeanLab.DensityGoldbach.U1446 LeanLab.DensityGoldbach.U1448

/-- The bucket of `a ∈ [0, N)` among `K` equal arcs. -/
def bucket (N K : ℕ) (a : ℕ) : ℕ := a * K / N

/-- Two residues in the same bucket give `|e_N(r x - r x₀) - 1| ≤ 2π/K`. -/
lemma close_of_bucket {N : ℕ} [NeZero N] (K : ℕ) (hK : 0 < K) (u v : ZMod N)
    (h : bucket N K u.val = bucket N K v.val) :
    ‖(ZMod.stdAddChar (u - v) : ℂ) - 1‖ ≤ 2 * Real.pi / K := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set a := u.val
  set b := v.val
  have huv : u - v = (((a : ℤ) - (b : ℤ) : ℤ) : ZMod N) := by
    push_cast; simp [a, b]
  rw [huv, ZMod.stdAddChar_coe]
  have e : 2 * (Real.pi : ℂ) * Complex.I * (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) / N =
      Complex.I * ((2 * Real.pi * ((a : ℝ) - b) / N : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs]
  -- `|a K - b K| < N` from equal buckets
  have ha1 := Nat.div_mul_le_self (a * K) N
  have ha2 := Nat.lt_div_mul_add (a := a * K) (Nat.pos_of_ne_zero (NeZero.ne N))
  have hb1 := Nat.div_mul_le_self (b * K) N
  have hb2 := Nat.lt_div_mul_add (a := b * K) (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold bucket at h
  rw [h] at ha1 ha2
  have r1 : ((b * K / N * N : ℕ) : ℝ) ≤ (a : ℝ) * K := by exact_mod_cast ha1
  have r2 : (a : ℝ) * K < ((b * K / N * N : ℕ) : ℝ) + N := by exact_mod_cast ha2
  have r3 : ((b * K / N * N : ℕ) : ℝ) ≤ (b : ℝ) * K := by exact_mod_cast hb1
  have r4 : (b : ℝ) * K < ((b * K / N * N : ℕ) : ℝ) + N := by exact_mod_cast hb2
  have hab : |((a : ℝ) - b)| * K ≤ N := by
    rw [show |((a : ℝ) - b)| * K = |((a : ℝ) - b) * K| by rw [abs_mul, abs_of_pos hK0], abs_le]
    constructor <;> nlinarith
  have hpi := Real.pi_pos
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hN0,
    div_le_div_iff₀ hN0 hK0]
  have := mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  nlinarith

/-- **Bohr set size bound, PROVED.** -/
theorem bohrLower_proved : BohrLower := by
  intro ε hε k
  set K := ⌈2 * Real.pi / ε⌉₊ + 1 with hKdef
  have hK : 0 < K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKε : 2 * Real.pi / K ≤ ε := by
    rw [div_le_iff₀ hK0]
    have h1 := Nat.le_ceil (2 * Real.pi / ε)
    have h2 : (⌈2 * Real.pi / ε⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    rw [div_le_iff₀ hε] at h1
    nlinarith
  refine ⟨1 / (K : ℝ) ^ k, by positivity, fun N _ R hR => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- the colouring
  let φ : ZMod N → (↥R → Fin K) := fun x r =>
    ⟨bucket N K (r.1 * x).val, by
      unfold bucket
      rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne N))]
      exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt _) hK |>.trans_le (by rw [mul_comm])⟩
  have hcardt : ((univ : Finset (↥R → Fin K)).card : ℝ) = (K : ℝ) ^ R.card := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]; push_cast; rfl
  have hpow : (K : ℝ) ^ R.card ≤ (K : ℝ) ^ k :=
    pow_le_pow_right₀ (by exact_mod_cast hK) hR
  have hpos : (0 : ℝ) < (K : ℝ) ^ R.card := by positivity
  obtain ⟨y, -, hy⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := (univ : Finset (ZMod N))) (t := univ) (f := φ) (b := (N : ℝ) / (K : ℝ) ^ R.card)
    (fun _ _ => mem_univ _) univ_nonempty (by
      rw [nsmul_eq_mul, hcardt, card_univ, ZMod.card]; field_simp; rfl)
  set F := univ.filter (fun x => φ x = y) with hF
  have hFpos : 0 < F.card := by
    have : (0 : ℝ) < F.card := lt_of_lt_of_le (by positivity) hy
    exact_mod_cast this
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 hFpos
  have hsub : F.image (fun x => x - x₀) ⊆
      univ.filter (fun x : ZMod N => ∀ r ∈ R, ‖(ZMod.stdAddChar (r * x) : ℂ) - 1‖ ≤ ε) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
    refine mem_filter.2 ⟨mem_univ _, fun r hr => ?_⟩
    have hxy : φ x = y := (mem_filter.1 hx).2
    have hx0y : φ x₀ = y := (mem_filter.1 hx₀).2
    have hb := congrArg (fun g => (g ⟨r, hr⟩ : ℕ)) (hxy.trans hx0y.symm)
    simp only [φ] at hb
    rw [mul_sub]
    exact (close_of_bucket K hK _ _ hb).trans hKε
  have hinj : (F.image (fun x => x - x₀)).card = F.card :=
    card_image_of_injective _ (sub_left_injective)
  have := card_le_card hsub
  rw [hinj] at this
  have hF' : (N : ℝ) / (K : ℝ) ^ k ≤ F.card :=
    (div_le_div_of_nonneg_left hN0.le hpos hpow).trans hy
  calc 1 / (K : ℝ) ^ k * N = (N : ℝ) / (K : ℝ) ^ k := by ring
    _ ≤ F.card := hF'
    _ ≤ _ := by exact_mod_cast this

/-- **Alsetri-Shao Proposition 3.1, PROVED** in the U1446 form `> δ³/1000` off `η N` points. -/
theorem as_prop31_proved : AS_Prop31 := as_prop31_of_bohr bohrLower_proved

/-- **Alsetri-Shao Proposition 3.1, printed form, PROVED.** -/
theorem as_prop31Printed_proved : AS_Prop31Printed := printed_of_U1446 as_prop31_proved

/-- **Alsetri-Shao 2024, Theorem 1.2, CONDITIONAL ON `Green62`, `Green66` only.** -/
theorem alsetriShao_1_2_U1467 (H62 : Green62) (H66 : Green66) : AlsetriShao12 :=
  alsetriShao_1_2_of_printed as_prop31Printed_proved H62 H66

end LeanLab.DensityGoldbach.U1467

