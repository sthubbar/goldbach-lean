module

public import LeanLab.PNTPort.Vinogradov.TernaryAsymp
public import LeanLab.PNTPort.Vinogradov.SingPos

/-!
# Vinogradov's theorem by the circle method: `r₃(n) ≫ n²` for large odd `n`

Lab proof, unit U-5260. AI wrote this file. Known mathematics, no cited input.

* `J_ge`: `J(N, n) ≥ ⌊n/3⌋²` when `n ≤ N + 2`, by taking `x, y ≤ n/3`.
* `r3_lower`: there is `N₀` such that every odd `n ≥ N₀` has `r₃(n) ≥ n²/40` with `N = n`,
  from `vinogradov_asymptotic`, `singP_ge` and `J_ge`; ineffective. Ternary Goldbach for all
  odd `n > 5` is Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Finset Real

lemma J_ge {N n : ℕ} (hn : n ≤ N + 2) : (((n / 3) ^ 2 : ℕ) : ℝ) ≤ J N n := by
  unfold J
  set k := n / 3 with hk
  have hk3 : 3 * k ≤ n := Nat.mul_div_le n 3
  have inner : ∀ x ∈ Icc 1 k, ∀ y ∈ Icc 1 k,
      (1 : ℝ) ≤ ∑ z ∈ Icc 1 N, if x + y + z = n then (1 : ℝ) else 0 := by
    intro x hx y hy
    rw [mem_Icc] at hx hy
    rw [← sum_filter]
    have hz : n - x - y ∈ (Icc 1 N).filter (fun z => x + y + z = n) := by
      rw [mem_filter, mem_Icc]; omega
    rw [sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_pos.2 ⟨_, hz⟩
  have hsub : Icc 1 k ⊆ Icc 1 N := by intro x hx; rw [mem_Icc] at hx ⊢; omega
  have hnn : ∀ x y : ℕ, 0 ≤ ∑ z ∈ Icc 1 N, if x + y + z = n then (1 : ℝ) else 0 :=
    fun x y => sum_nonneg fun z _ => by split_ifs <;> norm_num
  calc (((n / 3) ^ 2 : ℕ) : ℝ) = ∑ x ∈ Icc 1 k, ∑ y ∈ Icc 1 k, (1 : ℝ) := by
        simp [sq, hk]
    _ ≤ ∑ x ∈ Icc 1 k, ∑ y ∈ Icc 1 k, ∑ z ∈ Icc 1 N, if x + y + z = n then (1 : ℝ) else 0 :=
        sum_le_sum fun x hx => sum_le_sum fun y hy => inner x hx y hy
    _ ≤ ∑ x ∈ Icc 1 k, ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, if x + y + z = n then (1 : ℝ) else 0 :=
        sum_le_sum fun x _ => sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => hnn x y
    _ ≤ ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, if x + y + z = n then (1 : ℝ) else 0 :=
        sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
          sum_nonneg fun y _ => hnn x y

lemma half_sing {L : ℝ} (hL : Real.exp 2 ≤ L) :
    2 ≤ ⌊L ^ (2 * (1 : ℝ) + 12)⌋₊ ∧
      Real.exp 8 / Real.sqrt (⌊L ^ (2 * (1 : ℝ) + 12)⌋₊ : ℕ) ≤ 1 / 2 := by
  have hL0 : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
  have h14 : Real.exp 28 ≤ L ^ (2 * (1 : ℝ) + 12) := by
    calc Real.exp 28 = Real.exp 2 ^ (2 * (1 : ℝ) + 12) := by
          rw [← Real.exp_mul]; norm_num
      _ ≤ L ^ (2 * (1 : ℝ) + 12) := Real.rpow_le_rpow hL0 hL (by norm_num)
  have he12 : (8 : ℝ) ≤ Real.exp 12 := by have := Real.add_one_le_exp 12; linarith
  have hbig : 4 * Real.exp 16 ≤ Real.exp 28 / 2 := by
    rw [show Real.exp 28 = Real.exp 16 * Real.exp 12 by rw [← Real.exp_add]; norm_num]
    nlinarith [Real.exp_pos 16]
  have h1 : (1 : ℝ) ≤ L ^ (2 * (1 : ℝ) + 12) := by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 28 by norm_num); linarith
  have hfl := floor_ge_half h1
  set X := L ^ (2 * (1 : ℝ) + 12) with hX
  set F : ℝ := ((⌊X⌋₊ : ℕ) : ℝ) with hF
  have hP : 4 * Real.exp 16 ≤ F := by
    have : X / 2 ≤ F := hfl
    have : Real.exp 28 / 2 ≤ X / 2 := by linarith
    linarith
  have he16 : (1 : ℝ) ≤ Real.exp 16 := Real.one_le_exp (by norm_num)
  refine ⟨?_, ?_⟩
  · have h2F : (2 : ℝ) ≤ F := by linarith
    rw [hF] at h2F
    exact_mod_cast h2F
  · have hs : 2 * Real.exp 8 ≤ Real.sqrt F := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have : (2 * Real.exp 8) ^ 2 = 4 * Real.exp 16 := by
        rw [mul_pow, ← Real.exp_nat_mul]; norm_num
      linarith
    rw [div_le_iff₀ (by linarith [Real.exp_pos 8])]
    linarith

/-- **Vinogradov's theorem by the circle method**: `r₃(n) ≥ n²/40` for all large odd `n`, with
`r₃(n) = ∑_{a + b + c = n} Λ(a)Λ(b)Λ(c)`. Unconditional, ineffective. -/
theorem r3_lower : ∃ N₀ : ℝ, ∀ n : ℕ, N₀ ≤ n → Odd n → (n : ℝ) ^ 2 / 40 ≤ r3 n n := by
  obtain ⟨C, N₁, h⟩ := vinogradov_asymptotic 1 one_pos
  set C' := max C 1 with hC'
  refine ⟨max N₁ (max (Real.exp (max (Real.exp 2) (160 * C'))) 12), ?_⟩
  intro n hn hodd
  have hN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hbig : Real.exp (max (Real.exp 2) (160 * C')) ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have h12 : (12 : ℝ) ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn0 : (0 : ℝ) < n := by linarith
  set L := Real.log n with hL
  have hLge : max (Real.exp 2) (160 * C') ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hbig; rwa [Real.log_exp] at this
  have hLe2 : Real.exp 2 ≤ L := le_trans (le_max_left _ _) hLge
  have hLC : 160 * C' ≤ L := le_trans (le_max_right _ _) hLge
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 2) hLe2
  obtain ⟨hP2, hsing⟩ := half_sing hLe2
  obtain ⟨s, hs, hsge⟩ := singP_ge hodd hP2
  have hs2 : 1 / 2 ≤ s := by linarith
  have hmain := h n hN₁ n (by omega)
  rw [hs, Real.rpow_one] at hmain
  have hnorm : |r3 n n - J n n * s| ≤ C * (n : ℝ) ^ 2 / L := by
    have : ((r3 n n : ℂ) - (J n n : ℂ) * (s : ℂ)) = ((r3 n n - J n n * s : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs] at hmain
    exact hmain
  have hJ := J_ge (N := n) (n := n) (by omega)
  have hk : (n : ℝ) / 4 ≤ ((n / 3 : ℕ) : ℝ) := by
    have h1 : ((n / 3 : ℕ) : ℝ) * 3 + 3 > n := by
      have := Nat.lt_div_mul_add (a := n) (b := 3) (by norm_num)
      have : n < n / 3 * 3 + 3 := this
      exact_mod_cast this
    linarith
  have hJ' : (n : ℝ) ^ 2 / 16 ≤ J n n := by
    refine le_trans ?_ hJ
    push_cast
    have : ((n : ℝ) / 4) ^ 2 ≤ ((n / 3 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hk 2
    linarith
  have hJs : (n : ℝ) ^ 2 / 32 ≤ J n n * s := by
    have hJ0 : 0 ≤ J n n := le_trans (by positivity) hJ'
    nlinarith
  have herr : C * (n : ℝ) ^ 2 / L ≤ (n : ℝ) ^ 2 / 160 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have hC : C ≤ C' := le_max_left _ _
    have hC1 : 0 ≤ C' := le_trans zero_le_one (le_max_right _ _)
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
    nlinarith
  have := neg_abs_le (r3 n n - J n n * s)
  linarith

end LeanLab.PNTPort.Vinogradov

