module

public import LeanLab.PNTPort.Vinogradov.MajorArc
public import Mathlib.NumberTheory.Primorial

/-!
Unit U-1481, run 20261022T1302Z-31860. P0047 Alsetri and Shao 2024, Theorem 1.2, major arc
coefficient sum of Green 2005 Lemma 6.2.

For `k < W` let `q_k` be the reduced denominator of `k/W + ρ`, `ρ ∈ ℚ`. The coefficient sum is
`coefSum W b ρ = Σ_{k<W} e(-kb/W) μ(q_k)/φ(q_k)`.

* `ram_group`: `Σ_{m<W} e(-mb/W) μ(W/(m,W))/φ(W/(m,W)) = W/φ(W)`, `W` squarefree, `(b, W) = 1`.
* `coefSum_dvd`: if `den ρ ∣ W` then `coefSum = e(jb/W) W/φ(W)`, `j = ρW`.
* `coefSum_not_dvd`: if every prime `p ≤ z` divides the squarefree `W` and `den ρ ∤ W` then
  `‖coefSum‖ ≤ W/(φ(W) z)`, by splitting `ρ = ρ₁ + ρ₂` with `den ρ₁` `W`-smooth and `den ρ₂`
  prime to `W`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.DensityGoldbach.U1481

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- `g(n) = μ(n)/φ(n)`. -/
def gμ (n : ℕ) : ℂ := (μ n : ℂ) / (Nat.totient n : ℂ)

/-- `Σ_{d | W} μ(d)²/φ(d) = W/φ(W)` for squarefree `W`. -/
theorem sum_mu_sq_totient {W : ℕ} (hW : Squarefree W) :
    ∑ d ∈ W.divisors, (μ d : ℂ) * gμ d = (W : ℂ) / (Nat.totient W : ℂ) := by
  have hW0 : W ≠ 0 := hW.ne_zero
  have hφW : (Nat.totient W : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero hW0)).ne'
  have key : ∀ d ∈ W.divisors, (μ d : ℂ) * gμ d =
      (Nat.totient (W / d) : ℂ) / (Nat.totient W : ℂ) := by
    intro d hd
    have hdW : d ∣ W := Nat.dvd_of_mem_divisors hd
    have hsq : Squarefree d := hW.squarefree_of_dvd hdW
    have hmul : d * (W / d) = W := Nat.mul_div_cancel' hdW
    have hcop : Nat.Coprime d (W / d) := Nat.coprime_of_squarefree_mul (by rw [hmul]; exact hW)
    have htot : Nat.totient W = Nat.totient d * Nat.totient (W / d) := by
      rw [← Nat.totient_mul hcop, hmul]
    have hμ2 : (μ d : ℂ) * μ d = 1 := by
      have := moebius_sq_eq_one_of_squarefree hsq
      rw [← Int.cast_mul, ← sq, this]; simp
    have hφd : (Nat.totient d : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero hsq.ne_zero)).ne'
    have hφe : (Nat.totient (W / d) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (fun h => by
        rw [h, mul_zero] at hmul; exact hW0 hmul.symm))).ne'
    unfold gμ
    rw [htot]; push_cast
    rw [mul_div_assoc', hμ2]
    field_simp
  rw [sum_congr rfl key, ← sum_div]
  congr 1
  have := Nat.sum_div_divisors W (fun e => (Nat.totient e : ℂ))
  rw [this]
  exact_mod_cast Nat.sum_totient W


/-- **Ramanujan grouping**: for squarefree `W` and `(b, W) = 1`,
`Σ_{m < W} e(-mb/W) μ(W/(m,W))/φ(W/(m,W)) = W/φ(W)`. -/
theorem ram_group {W b : ℕ} (hW : Squarefree W) (hb : Nat.Coprime b W) :
    ∑ m ∈ range W, eL (-((m : ℝ) * b / W)) * gμ (W / Nat.gcd m W) =
      (W : ℂ) / (Nat.totient W : ℂ) := by
  have hW0 : W ≠ 0 := hW.ne_zero
  have hmaps : ∀ m ∈ range W, W / Nat.gcd m W ∈ W.divisors := by
    intro m _
    exact Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m W), hW0⟩
  rw [← sum_fiberwise_of_maps_to hmaps, ← sum_mu_sq_totient hW]
  refine sum_congr rfl fun d hd => ?_
  have hdW : d ∣ W := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  set c := W / d with hc
  have hcd : c * d = W := Nat.div_mul_cancel hdW
  have hc0 : 0 < c := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hcd; exact hW0 hcd.symm)
  have hcopd : Nat.Coprime b d := Nat.Coprime.coprime_dvd_right hdW hb
  have hram := LeanLab.PNTPort.Vinogradov.ramanujan_coprime (q := d) hd0 (a := -(b : ℤ))
    (by rw [IsCoprime.neg_left_iff, Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcopd)
  rw [← hram, sum_mul]
  have hgcd : ∀ m, W / Nat.gcd m W = d → Nat.gcd m W = c := by
    intro m h
    rw [hc, ← h, Nat.div_div_self (Nat.gcd_dvd_right m W) hW0]
  refine sum_nbij' (fun m => m / c) (fun u => c * u) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [mem_filter, mem_range] at hm ⊢
    have hg := hgcd m hm.2
    have hcm : c ∣ m := hg ▸ Nat.gcd_dvd_left m W
    obtain ⟨u, rfl⟩ := hcm
    rw [Nat.mul_div_cancel_left u hc0]
    refine ⟨?_, ?_⟩
    · have : c * u < c * d := by rw [hcd]; exact hm.1
      exact Nat.lt_of_mul_lt_mul_left this
    · rw [← hcd, Nat.gcd_mul_left] at hg
      have : Nat.gcd u d = 1 := by
        have h2 : c * Nat.gcd u d = c * 1 := by rw [hg, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hc0 h2
      exact this
  · intro u hu
    simp only [mem_filter, mem_range] at hu ⊢
    refine ⟨?_, ?_⟩
    · rw [← hcd]; exact Nat.mul_lt_mul_of_pos_left hu.1 hc0
    · rw [← hcd, Nat.gcd_mul_left, hu.2, mul_one, Nat.mul_div_cancel_left d hc0]
  · intro m hm
    simp only [mem_filter, mem_range] at hm
    have hg := hgcd m hm.2
    exact Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_left m W)
  · intro u _; exact Nat.mul_div_cancel_left u hc0
  · intro m hm
    simp only [mem_filter, mem_range] at hm
    have hg := hgcd m hm.2
    have hcm : c ∣ m := hg ▸ Nat.gcd_dvd_left m W
    obtain ⟨u, rfl⟩ := hcm
    rw [hm.2, Nat.mul_div_cancel_left u hc0]
    congr 1
    congr 1
    have hWr : (W : ℝ) = c * d := by exact_mod_cast hcd.symm
    have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
    have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [hWr]; push_cast; field_simp


/-! ### Reduced denominators -/

/-- Coprime denominators multiply. -/
theorem den_add_coprime {x y : ℚ} (h : Nat.Coprime x.den y.den) :
    (x + y).den = x.den * y.den := by
  apply Nat.dvd_antisymm (Rat.add_den_dvd x y)
  have hx : x.den ∣ (x + y).den * y.den := by
    have h1 : x.den ∣ ((x + y) + (-y)).den.lcm 0 ∨ True := Or.inr trivial
    have h2 := Rat.add_den_dvd (x + y) (-y)
    rw [add_neg_cancel_right, Rat.neg_den] at h2
    exact h2
  have hy : y.den ∣ (x + y).den * x.den := by
    have h2 := Rat.add_den_dvd (x + y) (-x)
    rw [add_comm x y, add_neg_cancel_right, Rat.neg_den] at h2
    rw [add_comm x y]; exact h2
  have hx' : x.den ∣ (x + y).den := h.dvd_of_dvd_mul_right hx
  have hy' : y.den ∣ (x + y).den := h.symm.dvd_of_dvd_mul_right hy
  exact h.mul_dvd_of_dvd_of_dvd hx' hy'

/-- `den(m/W) = W/(m, W)`. -/
theorem den_natdiv (m W : ℕ) (hW : 0 < W) : ((m : ℚ) / W).den = W / Nat.gcd m W := by
  set g := Nat.gcd m W
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m hW
  have hm : m = g * (m / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m W)).symm
  have hWg : W = g * (W / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right m W)).symm
  have hW' : 0 < W / g := Nat.div_pos (Nat.le_of_dvd hW (Nat.gcd_dvd_right m W)) hg
  have hq : (m : ℚ) / W = ((m / g : ℕ) : ℤ) / ((W / g : ℕ) : ℤ) := by
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [Int.cast_natCast, Int.cast_natCast, Nat.cast_div (Nat.gcd_dvd_left m W) hgq,
      Nat.cast_div (Nat.gcd_dvd_right m W) hgq]
    field_simp
  have hcop : Nat.Coprime (((m / g : ℕ) : ℤ)).natAbs (((W / g : ℕ) : ℤ)).natAbs := by
    simp only [Int.natAbs_natCast]
    exact Nat.coprime_div_gcd_div_gcd hg
  have := Rat.den_div_eq_of_coprime (by exact_mod_cast hW') hcop
  rw [hq]
  exact_mod_cast this

/-- `gμ` is multiplicative. -/
theorem gμ_mul {m n : ℕ} (h : Nat.Coprime m n) : gμ (m * n) = gμ m * gμ n := by
  unfold gμ
  rw [isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  rw [mul_div_mul_comm]

lemma norm_gμ_le (n : ℕ) : ‖gμ n‖ ≤ 1 := by
  unfold gμ
  rw [norm_div, Complex.norm_intCast, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : (1 : ℝ) ≤ Nat.totient n := by exact_mod_cast Nat.totient_pos.2 h
    rw [div_le_one (by linarith)]
    have : |((μ n : ℤ) : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    linarith

/-- The coefficient sum `Σ_{k<W} e(-kb/W) μ(q_k)/φ(q_k)`, `q_k` the reduced denominator of
`k/W + ρ`. -/
def coefSum (W b : ℕ) (ρ : ℚ) : ℂ :=
  ∑ k ∈ range W, eL (-((k : ℝ) * b / W)) * gμ (((k : ℚ) / W + ρ).den)

/-- `W`-smooth: every prime factor divides `W`. -/
def Smooth (W m : ℕ) : Prop := ∀ p, p.Prime → p ∣ m → p ∣ W

lemma squarefree_smooth_dvd {W s : ℕ} (hW : W ≠ 0) (hs : Squarefree s) (hsm : Smooth W s) :
    s ∣ W := by
  rw [← Nat.factorization_le_iff_dvd hs.ne_zero hW]
  intro p
  have h1 := hs.natFactorization_le_one p
  by_cases h0 : s.factorization p = 0
  · rw [h0]; exact Nat.zero_le _
  · have hp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization s ▸
      Finsupp.mem_support_iff.2 h0)
    have hps : p ∣ s := Nat.dvd_of_factorization_pos h0
    have hpW := hsm p hp hps
    have : 1 ≤ W.factorization p := (hp.dvd_iff_one_le_factorization hW).1 hpW
    omega

lemma den_kW_dvd (k W : ℕ) (hW : 0 < W) : ((k : ℚ) / W).den ∣ W := by
  rw [den_natdiv k W hW]; exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right k W)

/-- If `den ρ₁` is `W`-smooth but does not divide `W`, every `q_k` is not squarefree. -/
theorem coefSum_smooth_zero {W b : ℕ} (hW : 0 < W) {ρ : ℚ} (hsm : Smooth W ρ.den)
    (hnd : ¬ ρ.den ∣ W) : coefSum W b ρ = 0 := by
  unfold coefSum
  refine sum_eq_zero fun k _ => ?_
  set s := ((k : ℚ) / W + ρ).den
  have hns : ¬ Squarefree s := by
    intro hsq
    apply hnd
    have hsms : Smooth W s := by
      intro p hp hps
      have := (Rat.add_den_dvd ((k : ℚ) / W) ρ)
      rcases (Nat.Prime.dvd_mul hp).1 (hps.trans this) with h | h
      · exact h.trans (den_kW_dvd k W hW)
      · exact hsm p hp h
    have hsW := squarefree_smooth_dvd hW.ne' hsq hsms
    have h2 := Rat.add_den_dvd ((k : ℚ) / W + ρ) (-((k : ℚ) / W))
    rw [add_comm ((k : ℚ) / W) ρ, add_neg_cancel_right, Rat.neg_den] at h2
    have h3 : ρ.den ∣ W * W := h2.trans (Nat.mul_dvd_mul (by rw [add_comm]; exact hsW)
      (den_kW_dvd k W hW))
    -- use the lcm version for the sharp statement
    have h4 := Rat.add_den_dvd_lcm ((k : ℚ) / W + ρ) (-((k : ℚ) / W))
    rw [add_comm ((k : ℚ) / W) ρ, add_neg_cancel_right, Rat.neg_den] at h4
    exact h4.trans (Nat.lcm_dvd (by rw [add_comm]; exact hsW) (den_kW_dvd k W hW))
  unfold gμ
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
  simp


/-- Shifting a `W`-periodic function does not change its sum over a period. -/
theorem sum_shift_periodic {W : ℕ} (hW : 0 < W) (G : ℤ → ℂ) (hG : ∀ m, G (m % W) = G m)
    (j : ℤ) : ∑ k ∈ range W, G ((k : ℤ) + j) = ∑ k ∈ range W, G k := by
  have : NeZero W := ⟨hW.ne'⟩
  rw [← LeanLab.PNTPort.Vinogradov.sum_zmod_eq_range (M := W) (fun k => G ((k : ℤ) + j)),
    ← LeanLab.PNTPort.Vinogradov.sum_zmod_eq_range (M := W) (fun k => G (k : ℤ))]
  refine Fintype.sum_equiv (Equiv.addRight (j : ZMod W)) _ _ (fun x => ?_)
  simp only [Equiv.coe_addRight]
  have : (((x + (j : ZMod W)).val : ℕ) : ℤ) = ((x.val : ℤ) + j) % W := by
    rw [← ZMod.val_intCast]; congr 1; push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, hG]

/-- **Closed form, `den ρ ∣ W`**: `coefSum = e(jb/W) W/φ(W)` with `j = ρW`. -/
theorem coefSum_dvd {W b : ℕ} (hW : Squarefree W) (hb : Nat.Coprime b W) {ρ : ℚ}
    (h : ρ.den ∣ W) :
    coefSum W b ρ = eL (((ρ.num * (W / ρ.den : ℕ) : ℤ) : ℝ) * b / W) *
      ((W : ℂ) / (Nat.totient W : ℂ)) := by
  have hW0 : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW0.ne'
  have hWq : (W : ℚ) ≠ 0 := by exact_mod_cast hW0.ne'
  set j : ℤ := ρ.num * (W / ρ.den : ℕ) with hj
  have hρ : ρ = (j : ℚ) / W := by
    have hd0 : (ρ.den : ℚ) ≠ 0 := by exact_mod_cast ρ.den_nz
    rw [hj, Int.cast_mul, Int.cast_natCast, Nat.cast_div h hd0]
    conv_lhs => rw [← Rat.num_div_den ρ]
    field_simp
  set G : ℤ → ℂ := fun m => eL (-((m : ℝ) * b / W)) * gμ (((m : ℚ) / W).den) with hGdef
  have hshift : ∀ m t : ℤ, G (m + W * t) = G m := by
    intro m t
    simp only [hGdef]
    congr 1
    · have : -(((m + W * t : ℤ) : ℝ) * b / W) = -((m : ℝ) * b / W) + ((-(t * b) : ℤ) : ℝ) := by
        push_cast; field_simp; ring
      rw [this, LeanLab.PNTPort.LargeSieve.e_add, LeanLab.PNTPort.LargeSieve.e_int, mul_one]
    · have : ((m + W * t : ℤ) : ℚ) / W = (m : ℚ) / W + (t : ℤ) := by
        push_cast; field_simp
      rw [this, Rat.add_intCast_den]
  have hG : ∀ m, G (m % W) = G m := by
    intro m
    rw [Int.emod_def, sub_eq_add_neg, ← mul_neg, hshift]
  have hterm : ∀ k ∈ range W, eL (-((k : ℝ) * b / W)) * gμ (((k : ℚ) / W + ρ).den) =
      eL ((j : ℝ) * b / W) * G ((k : ℤ) + j) := by
    intro k _
    simp only [hGdef]
    rw [← mul_assoc, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    · congr 1; push_cast; ring
    · congr 2; rw [hρ]; push_cast; field_simp
  unfold coefSum
  rw [sum_congr rfl hterm, ← mul_sum, sum_shift_periodic hW0 G hG j]
  congr 1
  rw [← ram_group hW hb]
  refine sum_congr rfl fun m _ => ?_
  simp only [hGdef]
  rw [← den_natdiv m W hW0]
  push_cast
  rfl

theorem norm_coefSum_dvd {W b : ℕ} (hW : Squarefree W) (hb : Nat.Coprime b W) {ρ : ℚ}
    (h : ρ.den ∣ W) : ‖coefSum W b ρ‖ = (W : ℝ) / Nat.totient W := by
  rw [coefSum_dvd hW hb h, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul, norm_div,
    Complex.norm_natCast, Complex.norm_natCast]

/-- `‖μ(m)/φ(m)‖ ≤ 1/z` when `m ≠ 1` is prime to `W` and every prime `p ≤ z` divides `W`. -/
theorem norm_gμ_coprime {W z m : ℕ} (hz : ∀ p, p.Prime → p ≤ z → p ∣ W) (hz1 : 1 ≤ z)
    (hm : Nat.Coprime m W) (hm1 : m ≠ 1) (hm0 : m ≠ 0) : ‖gμ m‖ ≤ 1 / z := by
  by_cases hsq : Squarefree m
  · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hpW : ¬ p ∣ W := fun h => (Nat.Prime.coprime_iff_not_dvd hp).1
      (hm.coprime_dvd_left hpm) h
    have hpz : z < p := by
      by_contra hc; exact hpW (hz p hp (by omega))
    have hφ : z ≤ Nat.totient m := by
      have h1 : Nat.totient p ∣ Nat.totient m := Nat.totient_dvd_of_dvd hpm
      have h2 := Nat.le_of_dvd (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)) h1
      rw [Nat.totient_prime hp] at h2; omega
    unfold gμ
    rw [norm_div, Complex.norm_intCast, Complex.norm_natCast]
    have hzr : (1 : ℝ) ≤ z := by exact_mod_cast hz1
    have hφr : (z : ℝ) ≤ Nat.totient m := by exact_mod_cast hφ
    have : |((μ m : ℤ) : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    calc |((μ m : ℤ) : ℝ)| / Nat.totient m ≤ 1 / Nat.totient m :=
          div_le_div_of_nonneg_right this (by linarith)
      _ ≤ 1 / z := one_div_le_one_div_of_le (by linarith) hφr
  · unfold gμ
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp


/-- The `W`-smooth part and the part prime to `W` of `d`. -/
def smPart (W d : ℕ) : ℕ := ∏ p ∈ d.primeFactors with p ∣ W, p ^ d.factorization p
def cpPart (W d : ℕ) : ℕ := ∏ p ∈ d.primeFactors with ¬ p ∣ W, p ^ d.factorization p

lemma sm_mul_cp (W d : ℕ) (hd : d ≠ 0) : smPart W d * cpPart W d = d := by
  unfold smPart cpPart
  rw [prod_filter_mul_prod_filter_not, ← Nat.prod_factorization_eq_prod_primeFactors,
    Nat.prod_factorization_pow_eq_self hd]

lemma smooth_smPart (W d : ℕ) : Smooth W (smPart W d) := by
  intro k hk hkd
  unfold smPart at hkd
  obtain ⟨p, hp, hkp⟩ := (Prime.dvd_finsetProd_iff hk.prime _).1 hkd
  rw [mem_filter] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
  have := (Nat.prime_dvd_prime_iff_eq hk hpp).1 (hk.dvd_of_dvd_pow hkp)
  rw [this]; exact hp.2

lemma cpPart_coprime (W d : ℕ) : Nat.Coprime (cpPart W d) W := by
  unfold cpPart
  refine Nat.Coprime.prod_left fun p hp => ?_
  rw [mem_filter] at hp
  exact Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp.1)).2 hp.2)

lemma coprime_of_smooth {W m n : ℕ} (hm : Smooth W m) (hn : Nat.Coprime n W) :
    Nat.Coprime m n := by
  apply Nat.coprime_of_dvd
  intro k hk hkm hkn
  exact (Nat.Prime.coprime_iff_not_dvd hk).1 (hn.coprime_dvd_left hkn) (hm k hk hkm)

lemma den_divq_dvd (a : ℤ) (b : ℕ) : ((a : ℚ) / b).den ∣ b := by
  have := Rat.den_dvd a b
  rw [Rat.divInt_eq_div] at this
  push_cast at this
  exact_mod_cast this

/-- **The coefficient lemma**: for squarefree `W` with every prime `p ≤ z` dividing `W`,
`(b, W) = 1` and `den ρ ∤ W`, `‖Σ_{k<W} e(-kb/W) μ(q_k)/φ(q_k)‖ ≤ W/(φ(W) z)`. -/
theorem coefSum_not_dvd {W b z : ℕ} (hW : Squarefree W) (hb : Nat.Coprime b W)
    (hz : ∀ p, p.Prime → p ≤ z → p ∣ W) (hz1 : 1 ≤ z) {ρ : ℚ} (hnd : ¬ ρ.den ∣ W) :
    ‖coefSum W b ρ‖ ≤ (W : ℝ) / Nat.totient W / z := by
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
  -- factor the sum
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
  rw [hfac, norm_mul]
  by_cases h21 : ρ2.den = 1
  · have hden : ρ.den = ρ1.den := by
      rw [hsplit, den_add_coprime (by rw [h21]; exact Nat.coprime_one_right _), h21, mul_one]
    rw [coefSum_smooth_zero hW0 hsm1 (by rw [← hden]; exact hnd), norm_zero, zero_mul]
    positivity
  · have hg := norm_gμ_coprime hz hz1 hcp2 h21 ρ2.den_nz
    have hc1 : ‖coefSum W b ρ1‖ ≤ (W : ℝ) / Nat.totient W := by
      by_cases h1 : ρ1.den ∣ W
      · exact (norm_coefSum_dvd hW hb h1).le
      · rw [coefSum_smooth_zero hW0 hsm1 h1, norm_zero]; positivity
    calc ‖coefSum W b ρ1‖ * ‖gμ ρ2.den‖ ≤ (W : ℝ) / Nat.totient W * (1 / z) :=
          mul_le_mul hc1 hg (norm_nonneg _) (by positivity)
      _ = (W : ℝ) / Nat.totient W / z := by ring


/-- **The coefficient lemma at `W = z#`**: both cases. -/
theorem coefSum_primorial {z b : ℕ} (hz1 : 1 ≤ z) (hb : Nat.Coprime b (primorial z)) (ρ : ℚ) :
    (ρ.den ∣ primorial z → ‖coefSum (primorial z) b ρ‖ =
        (primorial z : ℝ) / Nat.totient (primorial z)) ∧
    (¬ ρ.den ∣ primorial z → ‖coefSum (primorial z) b ρ‖ ≤
        (primorial z : ℝ) / Nat.totient (primorial z) / z) := by
  have hsq : Squarefree (primorial z) := squarefree_primorial z
  have hz : ∀ p, p.Prime → p ≤ z → p ∣ primorial z := by
    intro p hp hpz
    unfold primorial
    exact Finset.dvd_prod_of_mem _ (mem_filter.2 ⟨mem_range.2 (by omega), hp⟩)
  exact ⟨fun h => norm_coefSum_dvd hsq hb h, fun h => coefSum_not_dvd hsq hb hz hz1 h⟩

/-- Vacuity: at `W = 6`, `b = 1`, `ρ = 1/5` the hypotheses of `coefSum_not_dvd` hold with
`z = 3`. -/
theorem vacuity_coef : Squarefree (primorial 3) ∧ primorial 3 = 6 ∧ Nat.Coprime 1 6 ∧
    ¬ (((1 : ℕ) : ℚ) / ((5 : ℕ) : ℚ)).den ∣ 6 ∧ ∀ p, p.Prime → p ≤ 3 → p ∣ 6 := by
  refine ⟨squarefree_primorial 3, by decide, by norm_num, ?_, ?_⟩
  · rw [den_natdiv 1 5 (by norm_num)]; decide
  · intro p hp hp3
    interval_cases p <;> first | (norm_num at hp; done) | decide

end LeanLab.DensityGoldbach.U1481

