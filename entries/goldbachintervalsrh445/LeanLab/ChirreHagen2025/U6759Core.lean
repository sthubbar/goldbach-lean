module

public import Mathlib
public import LeanLab.ChirreHagen2025.U6743Core

/-!
P0075 line, T2, unit U-6759, CLOUD 20261020T2217Z-cloud52, 2026-10-20.
Core lemmas to tighten the head and the tail of the U-6743 diagonal.
* `pt_norm0`, `piece_sum0`: the U1263Core majorant near the origin and the interval sum by
  BPT counts, for pieces `A/δ < |γ| ≤ B/δ` with `0 < A` and `10^13 δ ≤ A` in place of `1 ≤ A`,
  and with `lam ≤ 7`, the E term then carrying the factor `2 · 1.12`.
* `head_sum0`: `Σ_{|γ| ≤ A₀/δ} |c|² log |γ| ≤ 0.31831 A₀ δ log²(1/δ)` for `10^13 δ ≤ A₀ ≤ 1`.
CONDITIONAL ON `Lemma26B.BPTN γ` and `Ordinates14 γ` where stated; no other inputs.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.U6759
open Real
open LeanLab.ChirreHagen2025.U1263
open LeanLab.ChirreHagen2025.SmoothT2 (cδ Ordinates14)
open LeanLab.ChirreHagen2025.Lemma26B (BPTN Mt Rt M_diff R_sum c_lower part1)

variable {ι : Type*} {γ : ι → ℝ}

/-- `pt_norm` of U1263Core with `0 < A`, `10^13 δ ≤ A` in place of `1 ≤ A`. -/
lemma pt_norm0 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (h14 : Ordinates14 γ)
    (A B lo Q : ℝ) (hA0 : 0 < A) (hAT : 10 ^ 13 * δ ≤ A) (hlo0 : 0 ≤ lo)
    (hlo : lo ≤ A * (1 - 1 / 10 ^ 13))
    (hQ : 2 * (1 + 1 / 10 ^ 13) * (1 / 2 - lo ^ 2 / 24 + B ^ 4 / 720) + 1 / 10 ^ 26 ≤ Q) :
    ∀ i, A / δ < |γ i| → |γ i| ≤ B / δ → ‖cδ γ δ i‖ ^ 2 ≤ Q * δ ^ 2 := by
  intro i hg1 hg2
  have hγ : γ i ≠ 0 := by intro h; have := h14 i; rw [h, abs_zero] at this; norm_num at this
  set g := |γ i| with hgdef
  set t := g * Real.log (1 + δ) with htdef
  obtain ⟨t1, t2, t3⟩ := phase_range hδ hδ1 hA0.le hg1 hg2
  rw [← htdef] at t1 t2 t3
  have hc := c_sq_le γ hδ i hγ
  rw [← hgdef, ← htdef] at hc
  have hg14 : 14 ≤ g := h14 i
  have ht0 : 0 ≤ t := by
    have : 0 ≤ A * (1 - 1 / 10 ^ 13) := mul_nonneg hA0.le (by norm_num)
    linarith
  have hlot : lo ≤ t := by linarith
  set n := 1 / 2 - lo ^ 2 / 24 + B ^ 4 / 720 with hn
  have hbr : 1 / 2 - t ^ 2 / 24 + t ^ 4 / 720 ≤ n := by
    have a1 : lo ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hlo0 hlot 2
    have a2 : t ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ ht0 t2 4
    rw [hn]; linarith
  have hcos : 1 - Real.cos t ≤ t ^ 2 * n := by
    have := one_sub_cos_le t
    have : t ^ 2 * (1 / 2 - t ^ 2 / 24 + t ^ 4 / 720) ≤ t ^ 2 * n :=
      mul_le_mul_of_nonneg_left hbr (sq_nonneg t)
    nlinarith
  have hn0 : 0 ≤ n := by nlinarith [sq_nonneg (t ^ 2 - 30)]
  have hgi : 0 < γ i ^ 2 := by positivity
  have hsq : γ i ^ 2 = g ^ 2 := (sq_abs _).symm
  have ht2 : t ^ 2 ≤ g ^ 2 * δ ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ ht0 t3 2
  have hgbig : 10 ^ 13 ≤ g := by
    have hgA : A < g * δ := by rwa [div_lt_iff₀ hδ] at hg1
    have : 10 ^ 13 * δ < g * δ := by linarith
    exact (lt_of_mul_lt_mul_right this hδ.le).le
  have hg26 : 10 ^ 26 ≤ g ^ 2 := by nlinarith
  rw [hsq] at hc
  have h1c : 0 ≤ 1 - Real.cos t := by linarith [Real.cos_le_one t]
  have hdd : 1 + δ / 2 ≤ 1 + 1 / 10 ^ 13 := by linarith
  calc ‖cδ γ δ i‖ ^ 2 ≤ (δ ^ 2 / 4 + 2 * (1 + δ / 2) * (1 - Real.cos t)) / g ^ 2 := hc
    _ = δ ^ 2 / 4 / g ^ 2 + 2 * (1 + δ / 2) * ((1 - Real.cos t) / g ^ 2) := by ring
    _ ≤ δ ^ 2 * (1 / 10 ^ 26) + 2 * (1 + 1 / 10 ^ 13) * (δ ^ 2 * n) := by
        gcongr
        · rw [div_div, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg δ]
        · rw [div_le_iff₀ (by positivity)]
          calc 1 - Real.cos t ≤ t ^ 2 * n := hcos
            _ ≤ g ^ 2 * δ ^ 2 * n := mul_le_mul_of_nonneg_right ht2 hn0
            _ = δ ^ 2 * n * g ^ 2 := by ring
    _ = (2 * (1 + 1 / 10 ^ 13) * n + 1 / 10 ^ 26) * δ ^ 2 := by ring
    _ ≤ Q * δ ^ 2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg _)

/-- `(Λ + 7)² ≤ 1.12 (Λ + 5)²` for `Λ ≥ 29.8`. -/
lemma sq7_le {Λ lam : ℝ} (hΛ : 29.8 ≤ Λ) (h0 : 0 ≤ lam) (h7 : lam ≤ 7) :
    (Λ + lam) ^ 2 ≤ 1.12 * (Λ + 5) ^ 2 := by
  have : (Λ + lam) ^ 2 ≤ (Λ + 7) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  nlinarith

/-- `piece_sum` of U1263Core with `0 < A`, `10^13 δ ≤ A`, `0 ≤ lam ≤ 7`. -/
lemma piece_sum0 (hN : BPTN γ) (h14 : Ordinates14 γ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 10 ^ 13) (A B Q lam : ℝ) (hA0 : 0 < A) (hAT : 10 ^ 13 * δ ≤ A) (hAB : A ≤ B)
    (hlam : Real.log B ≤ lam) (hlam0 : 0 ≤ lam) (hlam7 : lam ≤ 7) (hQ : 0 ≤ Q)
    (hc : ∀ i, A / δ < |γ i| → |γ i| ≤ B / δ → ‖cδ γ δ i‖ ^ 2 ≤ Q * δ ^ 2) (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => A / δ < |γ i| ∧ |γ i| ≤ B / δ), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ 0.31831 * (Q * (B - A)) * (δ * Real.log (1 / δ) ^ 2
          + (2 * lam - 1.8) * (δ * Real.log (1 / δ)) + (lam ^ 2 - 1.8 * lam) * δ)
        + 2.24 * Q * (δ ^ 2 * (Real.log (1 / δ) + 5) ^ 2) := by
  set T := A / δ with hT
  set t := B / δ with ht
  set Λ := Real.log (1 / δ) with hΛdef
  have hT13 : (10 : ℝ) ^ 13 ≤ T := by
    rw [hT, le_div_iff₀ hδ]; linarith
  have hTt : T ≤ t := div_le_div_of_nonneg_right hAB hδ.le
  have hΛ := Lam_ge hδ hδ1
  have hB0 : 0 < B := by linarith
  have hlt : Real.log t = Real.log B + Λ := log_div_delta hδ hB0
  set S := s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t) with hS
  have hterm : ∀ i ∈ S, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ Q * δ ^ 2 * (Λ + lam) := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    obtain ⟨_, h1, h2⟩ := hi
    have hg0 : 0 < |γ i| := lt_of_le_of_lt (by positivity) h1
    have hlg : Real.log |γ i| ≤ Λ + lam := by
      have := Real.log_le_log hg0 h2; linarith
    have hlg0 : 0 ≤ Real.log |γ i| := Real.log_nonneg (by linarith [h14 i])
    exact mul_le_mul (hc i h1 h2) hlg hlg0 (by positivity)
  have hsum : ∑ i ∈ S, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ (S.card : ℝ) * (Q * δ ^ 2 * (Λ + lam)) := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hcard := hN.2 T t hT13 hTt s
  have hM := M_diff (by linarith) hTt
  have hR := R_sum hT13 hTt
  have hc1 := c_lower
  have hpi := Real.pi_gt_d6
  have hpi0 : 0 < π := Real.pi_pos
  have hdiff : t - T = (B - A) / δ := by rw [ht, hT]; ring
  have hBA : 0 ≤ B - A := by linarith
  have hcount : (S.card : ℝ) ≤ 0.31831 * ((B - A) / δ) * (Λ + lam - 1.8) + 2 * (Λ + lam) := by
    have k1 : (t - T) * (Real.log t - Real.log (2 * π)) ≤ (B - A) / δ * (Λ + lam - 1.8) := by
      rw [hdiff]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hlt]; linarith
    have k2 : 2 * (Mt t - Mt T) ≤ (t - T) * (Real.log t - Real.log (2 * π)) / π := by
      have e2 : (t - T) * (Real.log t - Real.log (2 * π)) / π =
          2 * ((t - T) * (Real.log t - Real.log (2 * π)) / (2 * π)) := by field_simp
      rw [e2]; linarith
    have k3 : (B - A) / δ * (Λ + lam - 1.8) / π ≤ 0.31831 * ((B - A) / δ) * (Λ + lam - 1.8) := by
      rw [div_le_iff₀ hpi0]
      have : 0 ≤ (B - A) / δ * (Λ + lam - 1.8) := mul_nonneg (by positivity) (by linarith)
      nlinarith
    have k4 : (t - T) * (Real.log t - Real.log (2 * π)) / π ≤ (B - A) / δ * (Λ + lam - 1.8) / π :=
      div_le_div_of_nonneg_right k1 hpi0.le
    have hlt' : Real.log t ≤ Λ + lam := by rw [hlt]; linarith
    linarith
  have hfac : 0 ≤ Q * δ ^ 2 * (Λ + lam) := by
    have : 0 ≤ Λ + lam := by linarith
    positivity
  have hfin := mul_le_mul_of_nonneg_right hcount hfac
  have hsq : (Λ + lam) ^ 2 ≤ 1.12 * (Λ + 5) ^ 2 := sq7_le hΛ hlam0 hlam7
  have hE : 2 * Q * (δ ^ 2 * (Λ + lam) ^ 2) ≤ 2.24 * Q * (δ ^ 2 * (Λ + 5) ^ 2) := by
    have h1 : δ ^ 2 * (Λ + lam) ^ 2 ≤ δ ^ 2 * (1.12 * (Λ + 5) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg δ)
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * Q by linarith)
    linarith
  have e : (0.31831 * ((B - A) / δ) * (Λ + lam - 1.8) + 2 * (Λ + lam)) * (Q * δ ^ 2 * (Λ + lam))
      = 0.31831 * (Q * (B - A)) * (δ * Λ ^ 2 + (2 * lam - 1.8) * (δ * Λ) + (lam ^ 2 - 1.8 * lam) * δ)
        + 2 * Q * (δ ^ 2 * (Λ + lam) ^ 2) := by
    field_simp; ring
  rw [e] at hfin
  linarith

/-- The short head: `Σ_{|γ| ≤ A₀/δ} |c|² log |γ| ≤ 0.31831 A₀ δ log²(1/δ)`. -/
lemma head_sum0 (hN : BPTN γ) (h14 : Ordinates14 γ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 10 ^ 13) (A0 : ℝ) (hA0 : 0 < A0) (hA1 : A0 ≤ 1) (hAT : 10 ^ 13 * δ ≤ A0)
    (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => |γ i| ≤ A0 / δ), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ 0.31831 * A0 * (δ * Real.log (1 / δ) ^ 2) := by
  set T := A0 / δ with hT
  have hT13 : (10 : ℝ) ^ 13 ≤ T := by rw [hT, le_div_iff₀ hδ]; linarith
  have hp := part1 hN hT13 s
  have hlog : ∀ i, 0 ≤ Real.log |γ i| := fun i => Real.log_nonneg (by linarith [h14 i])
  have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ δ ^ 2 * ∑ i ∈ s.filter (fun i => |γ i| ≤ T), Real.log |γ i| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hlog i)
    exact pow_le_pow_left₀ (norm_nonneg _) (SmoothT2.coef_le_delta hδ γ i) 2
  have hpi := Real.pi_gt_d6
  have hlT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlT : Real.log T ≤ Real.log (1 / δ) :=
    Real.log_le_log (by linarith) (by rw [hT]; exact div_le_div_of_nonneg_right hA1 hδ.le)
  have hlT2 : Real.log T ^ 2 ≤ Real.log (1 / δ) ^ 2 := pow_le_pow_left₀ hlT0 hlT 2
  have h2 : δ ^ 2 * (T * Real.log T ^ 2 / π) = A0 * δ * Real.log T ^ 2 / π := by
    rw [hT]; field_simp
  have h3 : A0 * δ * Real.log T ^ 2 / π ≤ 0.31831 * A0 * (δ * Real.log (1 / δ) ^ 2) := by
    rw [div_le_iff₀ (by linarith)]
    have a : A0 * δ * Real.log T ^ 2 ≤ A0 * δ * Real.log (1 / δ) ^ 2 :=
      mul_le_mul_of_nonneg_left hlT2 (by positivity)
    have : 0 ≤ A0 * δ * Real.log (1 / δ) ^ 2 := by positivity
    nlinarith
  have := mul_le_mul_of_nonneg_left hp (sq_nonneg δ)
  linarith

end LeanLab.ChirreHagen2025.U6759
