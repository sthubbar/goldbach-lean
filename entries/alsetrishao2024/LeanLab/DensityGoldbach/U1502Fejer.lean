module

public import LeanLab.PNTPort.LargeSieve.Basic

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

Fejer kernels and a positive definite dyadic majorant of `ψ_N(θ) = min(1, 1/(N‖θ‖))`.

* `fej L β = (1/L) |Σ_{n<L} e(nβ)|²`, the Fejer kernel; `fej_lower`: `fej L β ≥ L/4` when
  `8 L ‖β‖ ≤ 1`.
* `Kd N β = 2^{-J} Σ_{i ≤ J} fej(2^i, β)`, `J = log₂ N - 1`; `psi_le_Kd`: `ψ_N ≤ 32 Kd + 8/N`.

Known mathematics, no cited input. AI-written Lean code, Claude, 2026-10-23. Checked only by
the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real Complex
open LeanLab.PNTPort.LargeSieve

noncomputable section
namespace LeanLab.DensityGoldbach.U1502

/-- `ψ_N(θ) = min(1, 1/(N‖θ‖))`, with the value `1` when `N‖θ‖ ≤ 1`. -/
def psiN (N : ℕ) (θ : ℝ) : ℝ :=
  if (N : ℝ) * dist0 θ ≤ 1 then 1 else 1 / ((N : ℝ) * dist0 θ)

lemma psiN_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ psiN N θ := by
  unfold psiN; split_ifs
  · norm_num
  · have : 0 ≤ (N : ℝ) * dist0 θ := mul_nonneg (Nat.cast_nonneg _) (dist0_nonneg θ)
    positivity

lemma psiN_le_one (N : ℕ) (θ : ℝ) : psiN N θ ≤ 1 := by
  unfold psiN; split_ifs with h
  · exact le_rfl
  · push Not at h
    rw [div_le_one (by linarith)]; exact h.le

lemma psiN_le_inv (N : ℕ) (θ : ℝ) (h : 0 < (N : ℝ) * dist0 θ) :
    psiN N θ ≤ 1 / ((N : ℝ) * dist0 θ) := by
  unfold psiN; split_ifs with h1
  · rw [le_div_iff₀ h, one_mul]; exact h1
  · exact le_rfl

/-- The Fejer kernel `(1/L) |Σ_{n<L} e(nβ)|²`. -/
def fej (L : ℕ) (β : ℝ) : ℝ := (1 / (L : ℝ)) * ‖∑ n ∈ range L, e (n * β)‖ ^ 2

lemma fej_nonneg (L : ℕ) (β : ℝ) : 0 ≤ fej L β := by unfold fej; positivity

lemma re_e (x : ℝ) : (e x).re = Real.cos (2 * π * x) := by
  unfold e
  rw [mul_comm, Complex.exp_ofReal_mul_I_re]

lemma e_nat_mul_round (n : ℕ) (β : ℝ) : e (n * β) = e (n * (β - round β)) := by
  have : (n : ℝ) * β = n * (β - round β) + ((n * round β : ℤ) : ℝ) := by push_cast; ring
  rw [this, e_add, e_int, mul_one]

/-- **Fejer lower bound**: `fej L β ≥ L/4` when `8 L ‖β‖ ≤ 1`. -/
theorem fej_lower (L : ℕ) (hL : 1 ≤ L) (β : ℝ) (h : 8 * (L : ℝ) * dist0 β ≤ 1) :
    (L : ℝ) / 4 ≤ fej L β := by
  set t := β - round β with ht
  have htd : |t| = dist0 β := rfl
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpi : π ≤ 4 := Real.pi_le_four
  have hpi0 : 0 < π := Real.pi_pos
  -- each real part is at least 1/2
  have hre : ∀ n ∈ range L, (1 / 2 : ℝ) ≤ (e (n * β)).re := by
    intro n hn
    rw [mem_range] at hn
    rw [e_nat_mul_round, ← ht, re_e]
    have hn' : (n : ℝ) ≤ L := by exact_mod_cast hn.le
    have h1 : |(n : ℝ) * t| ≤ 1 / 8 := by
      rw [abs_mul, Nat.abs_cast, htd]
      have : (n : ℝ) * dist0 β ≤ L * dist0 β :=
        mul_le_mul_of_nonneg_right hn' (dist0_nonneg β)
      nlinarith
    have h2 : (2 * π * (n * t)) ^ 2 ≤ (2 * π / 8) ^ 2 := by
      have hs : ((n : ℝ) * t) ^ 2 ≤ (1 / 8) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have e1 : (2 * π * (n * t)) ^ 2 = (2 * π) ^ 2 * ((n : ℝ) * t) ^ 2 := by ring
      have e2 : (2 * π / 8) ^ 2 = (2 * π) ^ 2 * (1 / 8) ^ 2 := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have h3 := Real.one_sub_sq_div_two_le_cos (x := 2 * π * (n * t))
    have h4 : (2 * π / 8) ^ 2 / 2 ≤ 1 / 2 := by nlinarith
    rw [show 2 * π * (n * t) = 2 * π * ((n : ℝ) * t) by ring] at h3 h2
    linarith
  have hsum : (L : ℝ) / 2 ≤ (∑ n ∈ range L, e (n * β)).re := by
    rw [Complex.re_sum]
    calc (L : ℝ) / 2 = ∑ n ∈ range L, (1 / 2 : ℝ) := by
          rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum hre
  have hnorm : (L : ℝ) / 2 ≤ ‖∑ n ∈ range L, e (n * β)‖ :=
    hsum.trans (Complex.re_le_norm _)
  have hsq : ((L : ℝ) / 2) ^ 2 ≤ ‖∑ n ∈ range L, e (n * β)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hnorm 2
  unfold fej
  rw [show (L : ℝ) / 4 = (1 / (L : ℝ)) * ((L : ℝ) / 2) ^ 2 by field_simp; ring]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- `J = log₂ N - 1`, so `2^{J+1} ≤ N < 2^{J+2}` for `N ≥ 4`. -/
def Jn (N : ℕ) : ℕ := Nat.log 2 N - 1

lemma Jn_spec (N : ℕ) (hN : 4 ≤ N) : 2 ^ (Jn N + 1) ≤ N ∧ N < 2 ^ (Jn N + 2) := by
  have hl : 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have e1 : Jn N + 1 = Nat.log 2 N := by unfold Jn; omega
  refine ⟨?_, ?_⟩
  · rw [e1]; exact Nat.pow_log_le_self 2 (by omega)
  · rw [show Jn N + 2 = (Nat.log 2 N).succ by unfold Jn; omega]
    exact Nat.lt_pow_succ_log_self (by norm_num) N

/-- The dyadic majorant `Kd N β = 2^{-J} Σ_{i ≤ J} fej(2^i, β)`. -/
def Kd (N : ℕ) (β : ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ Jn N) * ∑ i ∈ range (Jn N + 1), fej (2 ^ i) β

lemma Kd_nonneg (N : ℕ) (β : ℝ) : 0 ≤ Kd N β := by
  unfold Kd
  exact mul_nonneg (by positivity) (sum_nonneg fun i _ => fej_nonneg _ _)

lemma Kd_ge_term (N : ℕ) (β : ℝ) (i : ℕ) (hi : i ≤ Jn N) :
    (1 / (2 : ℝ) ^ Jn N) * fej (2 ^ i) β ≤ Kd N β := by
  unfold Kd
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact single_le_sum (f := fun i => fej (2 ^ i) β) (fun j _ => fej_nonneg _ _)
    (mem_range.2 (by omega))

/-- **Majorant**: `ψ_N(β) ≤ 32 Kd N β + 8/N` for `N ≥ 4`. -/
theorem psi_le_Kd (N : ℕ) (hN : 4 ≤ N) (β : ℝ) : psiN N β ≤ 32 * Kd N β + 8 / N := by
  obtain ⟨hJ1, _⟩ := Jn_spec N hN
  set J := Jn N with hJ
  set d := dist0 β with hd
  have hd0 : 0 ≤ d := dist0_nonneg β
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hJr : (2 : ℝ) ^ (J + 1) ≤ N := by exact_mod_cast hJ1
  have hK0 := Kd_nonneg N β
  have h2J : (0 : ℝ) < 2 ^ J := by positivity
  by_cases hA : 8 * (2 : ℝ) ^ J * d ≤ 1
  · -- Case A: the top level already sees `β`
    have hf := fej_lower (2 ^ J) (Nat.one_le_two_pow) β (by push_cast; exact hA)
    have ht := Kd_ge_term N β J le_rfl
    push_cast at hf
    have : (1 / (2 : ℝ) ^ J) * ((2 : ℝ) ^ J / 4) = 1 / 4 := by field_simp
    have h14 : 1 / 4 ≤ Kd N β := by
      calc (1 : ℝ) / 4 = (1 / (2 : ℝ) ^ J) * ((2 : ℝ) ^ J / 4) := this.symm
        _ ≤ (1 / (2 : ℝ) ^ J) * fej (2 ^ J) β := mul_le_mul_of_nonneg_left hf (by positivity)
        _ ≤ Kd N β := ht
    have := psiN_le_one N β
    have : (0 : ℝ) ≤ 8 / N := by positivity
    linarith
  push Not at hA
  have hdpos : 0 < d := by
    by_contra h0; push Not at h0
    have : d = 0 := le_antisymm h0 hd0
    rw [this, mul_zero] at hA; linarith
  have hNd : 0 < (N : ℝ) * d := mul_pos hNr hdpos
  have hpsi := psiN_le_inv N β hNd
  by_cases hB : 8 * d ≤ 1
  · -- Case C: an intermediate level
    set P : ℕ → Prop := fun i => 8 * (2 : ℝ) ^ i * d ≤ 1 with hP
    set i₀ := Nat.findGreatest P J with hi₀
    have hP0 : P 0 := by simp only [P]; simpa using hB
    have hPi : P i₀ := Nat.findGreatest_spec (P := P) (Nat.zero_le J) hP0
    have hi₀J : i₀ ≤ J := Nat.findGreatest_le J
    have hi₀ne : i₀ ≠ J := by
      intro h; rw [h] at hPi; simp only [P] at hPi; linarith
    have hnext : ¬ P (i₀ + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self _)
      (by omega)
    simp only [P, not_le] at hnext
    have hf := fej_lower (2 ^ i₀) (Nat.one_le_two_pow) β (by push_cast; exact hPi)
    have ht := Kd_ge_term N β i₀ hi₀J
    push_cast at hf
    have hlow : (2 : ℝ) ^ i₀ / (4 * 2 ^ J) ≤ Kd N β := by
      calc (2 : ℝ) ^ i₀ / (4 * 2 ^ J) = (1 / (2 : ℝ) ^ J) * ((2 : ℝ) ^ i₀ / 4) := by
            field_simp
        _ ≤ (1 / (2 : ℝ) ^ J) * fej (2 ^ i₀) β := mul_le_mul_of_nonneg_left hf (by positivity)
        _ ≤ Kd N β := ht
    -- `1/(N d) < 16 · 2^{i₀} / N ≤ 8 · 2^{i₀} / 2^J`
    have hd' : 1 < 16 * (2 : ℝ) ^ i₀ * d := by
      rw [pow_succ] at hnext; linarith
    have h1 : 1 / ((N : ℝ) * d) ≤ 16 * (2 : ℝ) ^ i₀ / N := by
      rw [div_le_div_iff₀ hNd hNr]; nlinarith
    have h2 : 16 * (2 : ℝ) ^ i₀ / N ≤ 8 * (2 : ℝ) ^ i₀ / 2 ^ J := by
      rw [div_le_div_iff₀ hNr h2J]
      have : (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J := by rw [pow_succ]; ring
      have h2i : (0 : ℝ) < 2 ^ i₀ := by positivity
      nlinarith
    have h3 : 8 * (2 : ℝ) ^ i₀ / 2 ^ J = 32 * ((2 : ℝ) ^ i₀ / (4 * 2 ^ J)) := by
      field_simp; ring
    have : (0 : ℝ) ≤ 8 / N := by positivity
    linarith
  · -- Case B: far from the integers
    push Not at hB
    have : 1 / ((N : ℝ) * d) ≤ 8 / N := by
      rw [div_le_div_iff₀ hNd hNr]; nlinarith
    linarith

end LeanLab.DensityGoldbach.U1502
