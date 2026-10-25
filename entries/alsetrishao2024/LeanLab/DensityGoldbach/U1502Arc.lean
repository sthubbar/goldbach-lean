module

public import LeanLab.DensityGoldbach.U1484Final
public import LeanLab.DensityGoldbach.U1502Core
public import LeanLab.VanDerCorput1939.Totient

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

The major arc profile of `ν̂_b`, pointwise: a refinement of `U1484.twS_explicit` that keeps the
size `1/φ(m)` of the main term and the decay of the geometric sum `V(β)`, instead of bounding the
main term by `X/z`.

* `coefSum_split`: `|coefSum(ρ)| ≤ W/φ(W) |μ(m)/φ(m)|`, `m` the denominator of the part `ρ₂` of `ρ`
  prime to `W`, and `Wρ ≡ Wρ₂ mod 1` whenever `coefSum(ρ) ≠ 0`.
* `twS_cases`: either all `k/W - r/(WN)` are minor, or there are `ρ₂, β, t` with
  `-r/N = Wρ₂ + t + Wβ`, `|β| ≤ 1/(Q+1)` and `|twS| ≤ W/φ(W) |μ(m)/φ(m)| |V(β)| + W E`.
* `V_div_le_psi`: `|V_X(β)|/(WN) ≤ ψ_N(y)` whenever `‖y‖ ≤ W|β|`, `X ≤ WN`, `|β| < 1/2`.
* `farey_point`: the point `a'/m` with `a' ≡ -W num(ρ₂) mod m`, reduced, and `‖r/N - a'/m‖ ≤ W|β|`.
* `gmu_psi_le`: `|μ(m)/φ(m)| ψ ≤ 2/√T + Φ_T(s)` for `ψ = ψ_N(s/N - a'/m)`, `a'` reduced mod `m`.

Known mathematics, no cited input. AI-written Lean code, Claude, 2026-10-23. Checked only by
the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.DensityGoldbach.U1502

open LeanLab.DensityGoldbach.U1478 LeanLab.DensityGoldbach.U1481 LeanLab.DensityGoldbach.U1484
open LeanLab.PNTPort.LargeSieve

local notation "SV" => LeanLab.PNTPort.Vinogradov.S
local notation "eL" => LeanLab.PNTPort.LargeSieve.e
local notation "VV" => LeanLab.PNTPort.Vinogradov.V

/-! ### The coefficient sum, split -/

theorem coefSum_split {W b : ℕ} (hW : Squarefree W) (hb : Nat.Coprime b W) (ρ : ℚ) :
    ∃ ρ2 : ℚ, Nat.Coprime ρ2.den W ∧
      ‖coefSum W b ρ‖ ≤ (W : ℝ) / Nat.totient W * ‖gμ ρ2.den‖ ∧
      (coefSum W b ρ ≠ 0 → ∃ t : ℤ, (W : ℚ) * ρ = W * ρ2 + t) := by
  have hW0 : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  set d := ρ.den
  set d1 := smPart W d
  set d2 := cpPart W d
  have hd : d1 * d2 = d := sm_mul_cp W d ρ.den_nz
  have hd1 : d1 ≠ 0 := fun h => by rw [h, zero_mul] at hd; exact ρ.den_nz hd.symm
  have hd2 : d2 ≠ 0 := fun h => by rw [h, mul_zero] at hd; exact ρ.den_nz hd.symm
  have hc12 : Nat.Coprime d1 d2 := coprime_of_smooth (smooth_smPart W d) (cpPart_coprime W d)
  set A := Nat.gcdA d1 d2
  set B := Nat.gcdB d1 d2
  have hbez : ((Nat.gcd d1 d2 : ℕ) : ℤ) = d1 * A + d2 * B := Nat.gcd_eq_gcd_ab d1 d2
  rw [hc12] at hbez
  set ρ1 : ℚ := ((ρ.num * B : ℤ) : ℚ) / d1
  set ρ2 : ℚ := ((ρ.num * A : ℤ) : ℚ) / d2
  have hsplit : ρ = ρ1 + ρ2 := by
    have hbq : (1 : ℚ) = d1 * A + d2 * B := by exact_mod_cast hbez
    have hdq : (d : ℚ) = d1 * d2 := by exact_mod_cast hd.symm
    have hd1q : (d1 : ℚ) ≠ 0 := by exact_mod_cast hd1
    have hd2q : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
    conv_lhs => rw [← Rat.num_div_den ρ]
    simp only [ρ1, ρ2]
    rw [show (ρ.den : ℚ) = d from rfl, hdq]
    push_cast
    field_simp
    linear_combination (ρ.num : ℚ) * hbq
  have hρ1 : ρ1.den ∣ d1 := den_divq_dvd _ _
  have hρ2 : ρ2.den ∣ d2 := den_divq_dvd _ _
  have hsm1 : Smooth W ρ1.den := fun p hp h => smooth_smPart W d p hp (h.trans hρ1)
  have hcp2 : Nat.Coprime ρ2.den W := (cpPart_coprime W d).coprime_dvd_left hρ2
  have hfac : coefSum W b ρ = coefSum W b ρ1 * gμ ρ2.den := by
    unfold coefSum
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    have hsmk : Smooth W (((k : ℚ) / W + ρ1).den) := by
      intro p hp hpk
      rcases (Nat.Prime.dvd_mul hp).1 (hpk.trans (Rat.add_den_dvd _ _)) with h | h
      · exact h.trans (den_kW_dvd k W hW0)
      · exact hsm1 p hp h
    have hcop := coprime_of_smooth hsmk hcp2
    rw [hsplit, ← add_assoc, den_add_coprime hcop, gμ_mul hcop, mul_assoc]
  have hc1 : ‖coefSum W b ρ1‖ ≤ (W : ℝ) / Nat.totient W := by
    by_cases h1 : ρ1.den ∣ W
    · exact (norm_coefSum_dvd hW hb h1).le
    · rw [coefSum_smooth_zero hW0 hsm1 h1, norm_zero]; positivity
  refine ⟨ρ2, hcp2, ?_, ?_⟩
  · rw [hfac, norm_mul]
    exact mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
  · intro hne
    by_cases h1 : ρ1.den ∣ W
    · refine ⟨ρ1.num * (W / ρ1.den : ℕ), ?_⟩
      have hd0 : (ρ1.den : ℚ) ≠ 0 := by exact_mod_cast ρ1.den_nz
      have hW1 : (W : ℚ) * ρ1 = ((ρ1.num * (W / ρ1.den : ℕ) : ℤ) : ℚ) := by
        rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div h1 hd0]
        conv_lhs => rw [← Rat.num_div_den ρ1]
        field_simp
      rw [hsplit, mul_add, hW1]; ring
    · exfalso
      apply hne
      rw [hfac, coefSum_smooth_zero hW0 hsm1 h1, zero_mul]

/-! ### The twisted sum, two cases -/

/-- **Two cases for `twS`**: all minor, or one major point with the split main term. -/
theorem twS_cases {z b N r P Q : ℕ} (hz1 : 1 ≤ z) (hb : Nat.Coprime b (primorial z))
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hQX : Q ≤ Xc (primorial z) b N) {E : ℝ}
    (hmaj : ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ primorial z * P → IsCoprime a (q : ℤ) →
      ∀ β : ℝ, |β| ≤ 1 / ((Q : ℝ) + 1) →
        ‖SV (Xc (primorial z) b N) (a / q + β) - gμ q * VV (Xc (primorial z) b N) β‖ ≤ E)
    (hE0 : 0 ≤ E) :
    ‖twS (primorial z) b N r‖ ≤ primorial z * Mb (Xc (primorial z) b N) P Q +
        primorial z * E ∨
      ∃ ρ2 : ℚ, ∃ β : ℝ, ∃ t : ℤ, Nat.Coprime ρ2.den (primorial z) ∧
        |β| ≤ 1 / ((Q : ℝ) + 1) ∧
        (primorial z : ℝ) * (-((r : ℝ) / (primorial z * N))) =
          (primorial z : ℝ) * (ρ2 : ℝ) + t + primorial z * β ∧
        ‖twS (primorial z) b N r‖ ≤ (primorial z : ℝ) / Nat.totient (primorial z) *
          ‖gμ ρ2.den‖ * ‖VV (Xc (primorial z) b N) β‖ + primorial z * E := by
  set W := primorial z with hWdef
  set X := Xc W b N with hXdef
  have hW : 0 < W := primorial_pos z
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hMb := Mb_nonneg X P Q
  set θ : ℝ := -((r : ℝ) / (W * N)) with hθdef
  rcases minor_or_major W P Q θ with hmin | ⟨k, hk, a, q, hq1, hqP, hclose⟩
  · left
    have hmin' : ∀ k < W,
        LeanLab.PNTPort.Vinogradov.MinorAt P Q ((k : ℝ) / W - (r : ℝ) / (W * N)) := by
      intro k hk; have := hmin k hk; rwa [hθdef, ← sub_eq_add_neg] at this
    have h := twS_minor (b := b) (N := N) hP hQ hQX hmin'
    have : ‖twS W b N r‖ ≤ W * Mb X P Q := h
    have : 0 ≤ (W : ℝ) * E := by positivity
    linarith
  · set ρ : ℚ := (a : ℚ) / q - (k : ℚ) / W with hρdef
    set β : ℝ := θ - ρ with hβdef
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hρr : (ρ : ℝ) = (a : ℝ) / q - (k : ℝ) / W := by rw [hρdef]; push_cast; ring
    have hβ : |β| ≤ 1 / ((Q : ℝ) + 1) := by
      have e : β = (k : ℝ) / W + θ - a / q := by rw [hβdef, hρr]; ring
      rw [e]
      refine hclose.trans ?_
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hθ : θ = (ρ : ℝ) + β := by rw [hβdef]; ring
    have hE : ∀ k' < W, ‖SV X ((((k' : ℚ) / W + ρ : ℚ) : ℝ) + β) -
        gμ (((k' : ℚ) / W + ρ).den) * VV X β‖ ≤ E := by
      intro k' _
      set x : ℚ := (k' : ℚ) / W + ρ
      have hx : ((x : ℚ) : ℝ) = (x.num : ℝ) / (x.den : ℕ) := by rw [Rat.cast_def]
      rw [hx]
      exact hmaj x.num x.den x.pos (den_shift_le hW k k' a hq1 hqP) (isCoprime_num_den x) β hβ
    have hmajor := twS_major (b := b) ρ β hθ hE
    obtain ⟨ρ2, hcp, hcs, hne⟩ := coefSum_split (squarefree_primorial z) hb ρ
    by_cases h0 : coefSum W b ρ = 0
    · left
      rw [h0, norm_zero, zero_mul, zero_add] at hmajor
      have : 0 ≤ (W : ℝ) * Mb X P Q := by positivity
      linarith
    · right
      obtain ⟨t, ht⟩ := hne h0
      refine ⟨ρ2, β, t, hcp, hβ, ?_, ?_⟩
      · have htr : (W : ℝ) * (ρ : ℝ) = (W : ℝ) * (ρ2 : ℝ) + t := by exact_mod_cast ht
        show (W : ℝ) * θ = _
        rw [hθ, mul_add, htr]
      · refine hmajor.trans ?_
        have := mul_le_mul_of_nonneg_right hcs (norm_nonneg (VV X β))
        linarith

/-! ### The geometric sum against `ψ_N` -/

lemma norm_V_le_geom (X : ℕ) {β : ℝ} (h : 0 < dist0 β) : ‖VV X β‖ ≤ 1 / (2 * dist0 β) := by
  unfold LeanLab.PNTPort.Vinogradov.V
  have hI : Icc 1 X = Ico 1 (X + 1) := by ext n; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, show X + 1 - 1 = X by omega]
  have : ∀ k ∈ range X, eL (((1 + k : ℕ) : ℝ) * β) = eL β * eL (k * β) := by
    intro k _; rw [← e_add]; congr 1; push_cast; ring
  rw [sum_congr rfl this, ← mul_sum, norm_mul, norm_e, one_mul]
  exact norm_geom_le X h

lemma dist0_of_small {β : ℝ} (h : |β| < 1 / 2) : dist0 β = |β| := by
  unfold dist0
  have : round β = 0 := by
    rw [round_eq_zero_iff]
    rw [abs_lt] at h
    exact ⟨by linarith [h.1], h.2⟩
  rw [this]; simp

/-- **`V` against `ψ_N`**: `|V_X(β)|/(WN) ≤ ψ_N(y)` whenever `‖y‖ ≤ W|β|`. -/
theorem V_div_le_psi (X W N : ℕ) (hW : 0 < W) (hN : 0 < N) (hXW : (X : ℝ) ≤ W * N) (β y : ℝ)
    (hβ : |β| < 1 / 2) (hy : dist0 y ≤ W * |β|) :
    ‖VV X β‖ / (W * N) ≤ psiN N y := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hWN : (0 : ℝ) < W * N := by positivity
  by_cases h1 : (N : ℝ) * dist0 y ≤ 1
  · unfold psiN; rw [if_pos h1]
    rw [div_le_one hWN]
    exact (norm_V_le X β).trans hXW
  · push Not at h1
    have hd0 : 0 < dist0 y := by
      by_contra h; push Not at h
      have : (N : ℝ) * dist0 y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNr.le h
      linarith
    have hb0 : 0 < |β| := by
      by_contra h; push Not at h
      have : (W : ℝ) * |β| ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hWr.le h
      linarith
    have hdb : dist0 β = |β| := dist0_of_small hβ
    have hV := norm_V_le_geom X (β := β) (by rw [hdb]; exact hb0)
    rw [hdb] at hV
    unfold psiN; rw [if_neg (not_le.2 h1)]
    calc ‖VV X β‖ / (W * N) ≤ 1 / (2 * |β|) / (W * N) :=
          div_le_div_of_nonneg_right hV hWN.le
      _ = 1 / (2 * (N * (W * |β|))) := by field_simp
      _ ≤ 1 / (N * dist0 y) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (N : ℝ) * dist0 y ≤ N * (W * |β|) := mul_le_mul_of_nonneg_left hy hNr.le
          nlinarith

/-- **The Farey point**: from `-y = Wρ₂ + t + Wβ` with `(den ρ₂, W) = 1`, a reduced residue
`a'` mod `m = den ρ₂` with `‖y - a'/m‖ ≤ W|β|`. -/
theorem farey_point (ρ2 : ℚ) (W : ℕ) (hcp : Nat.Coprime ρ2.den W) (y β : ℝ) (t : ℤ)
    (hrel : -y = (W : ℝ) * (ρ2 : ℝ) + t + W * β) :
    ∃ a : ℕ, a ∈ Us ρ2.den ∧ dist0 (y - (a : ℝ) / ρ2.den) ≤ W * |β| := by
  set m := ρ2.den with hm
  have hm0 : (0 : ℤ) < m := by exact_mod_cast ρ2.pos
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast ρ2.den_nz
  set u : ℤ := -((W : ℤ) * ρ2.num) with hu
  have hnn : 0 ≤ u % m := Int.emod_nonneg u hm0.ne'
  set a : ℕ := (u % m).toNat with ha
  have hac : ((a : ℕ) : ℤ) = u % m := Int.toNat_of_nonneg hnn
  refine ⟨a, ?_, ?_⟩
  · unfold Us
    rw [mem_filter, mem_range]
    constructor
    · have := Int.emod_lt_of_pos u hm0
      omega
    · rw [← Nat.isCoprime_iff_coprime, hac]
      have h1 : IsCoprime (m : ℤ) ρ2.num := (isCoprime_num_den ρ2).symm
      have h2 : IsCoprime (m : ℤ) (W : ℤ) := Nat.isCoprime_iff_coprime.2 hcp
      have h3 : IsCoprime (m : ℤ) u := by rw [hu]; exact (h2.mul_right h1).neg_right
      rw [Int.emod_def, sub_eq_add_neg, ← mul_neg]
      exact h3.add_mul_left_right _
  · -- `y - a/m = (u/m) - t - Wβ`, an integer minus `Wβ`
    have hρ : (ρ2 : ℝ) = (ρ2.num : ℝ) / m := by rw [Rat.cast_def]
    have har : (a : ℝ) = (u : ℝ) - m * ((u / m : ℤ) : ℝ) := by
      have : ((a : ℤ) : ℝ) = ((u % m : ℤ) : ℝ) := by rw [hac]
      push_cast at this
      rw [this, Int.emod_def]; push_cast; ring
    have key : y - (a : ℝ) / m = (((u / m : ℤ) - t : ℤ) : ℝ) - W * β := by
      have hy : y = -((W : ℝ) * (ρ2 : ℝ) + t + W * β) := by linarith
      rw [hy, har, hρ, hu]
      push_cast
      field_simp
      ring
    rw [key]
    have := dist0_le_abs_sub_int ((((u / m : ℤ) - t : ℤ) : ℝ) - W * β) ((u / m : ℤ) - t)
    rw [show (((u / m : ℤ) - t : ℤ) : ℝ) - W * β - (((u / m : ℤ) - t : ℤ) : ℝ) = -(W * β) by ring,
      abs_neg, abs_mul, Nat.abs_cast] at this
    exact this

/-- **One Farey point against the profile**: `|μ(m)/φ(m)| ψ ≤ 2/√T + Φ_T(s)`. -/
theorem gmu_psi_le {N : ℕ} [NeZero N] (T : ℕ) (hT : 1 ≤ T) (s : ZMod N) (m a : ℕ)
    (hm : 1 ≤ m) (ha : a ∈ Us m) :
    ‖gμ m‖ * psiN N (thetaN N s - (a : ℝ) / m) ≤ 2 / Real.sqrt T + PhiT N T s := by
  have hψ0 := psiN_nonneg N (thetaN N s - (a : ℝ) / m)
  have hψ1 := psiN_le_one N (thetaN N s - (a : ℝ) / m)
  have hP0 := PhiT_nonneg (N := N) T s
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hsq0 : 0 < Real.sqrt T := Real.sqrt_pos.2 hTr
  have h2T : 0 ≤ 2 / Real.sqrt T := by positivity
  have hφ : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.2 hm
  by_cases hsq : Squarefree m
  · have hg : ‖gμ m‖ = 1 / (Nat.totient m : ℝ) := by
      unfold gμ
      rw [norm_div, Complex.norm_intCast, Complex.norm_natCast]
      have : |((μ m : ℤ) : ℝ)| = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
        push_cast; rw [abs_pow, abs_neg, abs_one, one_pow]
      rw [this]
    rw [hg]
    by_cases hmT : m ≤ T
    · have hmem : (⟨m, a⟩ : Σ _ : ℕ, ℕ) ∈ Fs T := by
        unfold Fs; rw [mem_sigma]
        exact ⟨mem_Qs.2 ⟨⟨hm, hmT⟩, hsq⟩, ha⟩
      have h := single_le_sum (f := fun j : Σ _ : ℕ, ℕ => wF j * psiN N (thetaN N s - bF j))
        (fun j _ => mul_nonneg (wF_nonneg j) (psiN_nonneg _ _)) hmem
      have h2 : wF (⟨m, a⟩ : Σ _ : ℕ, ℕ) * psiN N (thetaN N s - bF ⟨m, a⟩) =
          1 / (Nat.totient m : ℝ) * psiN N (thetaN N s - (a : ℝ) / m) := rfl
      unfold PhiT
      linarith
    · push Not at hmT
      -- `1/φ(m) ≤ 2 m^{-3/4} ≤ 2/√m ≤ 2/√T`
      have htg := LeanLab.VanDerCorput1939.totient_ge m (by omega)
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm34 : Real.sqrt m ≤ (m : ℝ) ^ ((3 : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hmr (by norm_num)
      have hTm : Real.sqrt T ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast hmT.le)
      have h1 : 1 / (Nat.totient m : ℝ) ≤ 2 / Real.sqrt T := by
        rw [div_le_div_iff₀ hφ hsq0]
        nlinarith
      have : 1 / (Nat.totient m : ℝ) * psiN N (thetaN N s - (a : ℝ) / m) ≤ 1 / (Nat.totient m : ℝ) :=
        mul_le_of_le_one_right (by positivity) hψ1
      linarith
  · unfold gμ
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp only [Int.cast_zero, zero_div, norm_zero, zero_mul]
    linarith

end LeanLab.DensityGoldbach.U1502
