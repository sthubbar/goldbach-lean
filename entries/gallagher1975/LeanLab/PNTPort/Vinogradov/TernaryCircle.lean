module

public import LeanLab.PNTPort.Vinogradov.MinorArcs

/-!
# The ternary circle method on `ZMod M`, and the minor arc contribution

Lab proof, unit U-5253. AI wrote this file. Known mathematics, no cited input.

* `circle_identity`: for any `Φ : ZMod M → ℂ`,
  `∑_k (𝓕Φ(k))³ e(nk/M) = M ∑_{a + b + c = n} Φ(a)Φ(b)Φ(c)`.
* `ternary_minor`: with `Φ = Λ 1_{[1, N]}`, `N < M`, the minor frequencies contribute at most
  `M B ∑_{n ≤ N} Λ(n)²`, `B = 300 (N/√P + N^{4/5} + √(NQ)) (1 + log N)⁴`; so
  `‖M r₃(n) - ∑_{k major} (𝓕Φ(k))³ e(nk/M)‖ ≤ M B ∑ Λ²`, unconditionally.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ZMod
open scoped ArithmeticFunction.vonMangoldt

/-- The ternary count on `ZMod M`. -/
noncomputable def r3Z {M : ℕ} [NeZero M] (Φ : ZMod M → ℂ) (n : ZMod M) : ℂ :=
  ∑ a, ∑ b, ∑ c, if a + b + c = n then Φ a * Φ b * Φ c else 0

theorem circle_identity {M : ℕ} [NeZero M] (Φ : ZMod M → ℂ) (n : ZMod M) :
    ∑ k, (𝓕 Φ k) ^ 3 * (stdAddChar (n * k) : ℂ) = (M : ℂ) * r3Z Φ n := by
  have key : ∀ k : ZMod M, (𝓕 Φ k) ^ 3 * (stdAddChar (n * k) : ℂ) =
      ∑ a, ∑ b, ∑ c, Φ a * Φ b * Φ c * (stdAddChar (k * (n - a - b - c)) : ℂ) := by
    intro k
    rw [pow_three, dft_apply]
    simp only [smul_eq_mul, sum_mul, mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    have h : (stdAddChar (-(a * k)) : ℂ) * stdAddChar (-(b * k)) * stdAddChar (-(c * k)) *
        stdAddChar (n * k) = stdAddChar (k * (n - a - b - c)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1; ring
    rw [← h]; ring
  rw [sum_congr rfl fun k _ => key k]
  rw [sum_comm]
  unfold r3Z
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [← mul_sum, LeanLab.Routes.R0001.sum_stdAddChar_mul]
  by_cases h : a + b + c = n
  · rw [if_pos (by rw [← h]; ring), if_pos h]; ring
  · rw [if_neg (fun h' => h (by rw [sub_sub, sub_sub, sub_eq_zero] at h'; rw [h']; ring)),
      if_neg h]; ring

/-- The minor arc contribution. -/
theorem ternary_minor {N M P Q : ℕ} [NeZero M] (hNM : N < M) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hQN : Q ≤ N) (n : ZMod M) :
    ‖(M : ℂ) * r3Z (PhiL N M) n -
        ∑ k ∈ univ.filter (fun k => k ∉ minorSet P Q M),
          (𝓕 (PhiL N M) k) ^ 3 * (stdAddChar (n * k) : ℂ)‖
      ≤ (300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) *
          (1 + Real.log N) ^ 4) * ((M : ℝ) *
          ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2) := by
  set B := 300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) *
          (1 + Real.log N) ^ 4 with hB
  rw [← circle_identity, ← sum_filter_add_sum_filter_not univ (fun k => k ∈ minorSet P Q M),
    add_sub_cancel_right]
  have hfil : univ.filter (fun k => k ∈ minorSet P Q M) = minorSet P Q M := by
    ext k; simp
  rw [hfil]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k ∈ minorSet P Q M, ‖(𝓕 (PhiL N M) k) ^ 3 * (stdAddChar (n * k) : ℂ)‖ ≤
      B * ‖𝓕 (PhiL N M) k‖ ^ 2 := by
    intro k hk
    have hm : MinorAt P Q ((k.val : ℝ) / M) := by
      simp only [minorSet, Finset.mem_filter] at hk; exact hk.2
    have h1 : ‖𝓕 (PhiL N M) k‖ ≤ B := by
      rw [dft_PhiL_norm hNM]; exact minor_sup hP hQ hQN hm
    rw [norm_mul, stdAddChar_apply, Circle.norm_coe, mul_one, norm_pow]
    have : ‖𝓕 (PhiL N M) k‖ ^ 3 = ‖𝓕 (PhiL N M) k‖ * ‖𝓕 (PhiL N M) k‖ ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hB0 : 0 ≤ B := by
    have := Real.log_natCast_nonneg N
    have : 0 ≤ (N : ℝ) / Real.sqrt P := by positivity
    positivity
  have hpar := LeanLab.Routes.R0001.dft_parseval_norm (PhiL N M)
  rw [sum_PhiL_sq hNM] at hpar
  calc ∑ k ∈ minorSet P Q M, ‖(𝓕 (PhiL N M) k) ^ 3 * (stdAddChar (n * k) : ℂ)‖
      ≤ ∑ k ∈ minorSet P Q M, B * ‖𝓕 (PhiL N M) k‖ ^ 2 := sum_le_sum hk
    _ ≤ ∑ k, B * ‖𝓕 (PhiL N M) k‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ => by positivity
    _ = B * ((M : ℝ) * ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2) := by
        rw [← mul_sum, hpar]

/-- The weighted ternary count `r₃(n) = ∑_{a + b + c = n, a, b, c ≤ N} Λ(a)Λ(b)Λ(c)`. -/
noncomputable def r3 (N n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
    if a + b + c = n then Λ a * Λ b * Λ c else 0

/-- On `ZMod M` with `3N < M` the count is the integer count. -/
theorem r3Z_eq {N M : ℕ} [NeZero M] (h3 : 3 * N < M) {n : ℕ} (hn : n < M) :
    r3Z (PhiL N M) (n : ZMod M) = (r3 N n : ℂ) := by
  set P' : ℕ → ℂ := fun x => if 1 ≤ x ∧ x ≤ N then (Λ x : ℂ) else 0 with hP'
  set G : ℕ → ℕ → ℕ → ℂ := fun x y z => if x + y + z = n then P' x * P' y * P' z else 0 with hG
  have hpt : ∀ a b c : ZMod M, (if a + b + c = (n : ZMod M) then PhiL N M a * PhiL N M b *
      PhiL N M c else 0) = G a.val b.val c.val := by
    intro a b c
    have hPa : PhiL N M a = P' a.val := by simp only [PhiL, hP']
    have hPb : PhiL N M b = P' b.val := by simp only [PhiL, hP']
    have hPc : PhiL N M c = P' c.val := by simp only [PhiL, hP']
    rw [hPa, hPb, hPc, hG]
    simp only
    by_cases ha : 1 ≤ a.val ∧ a.val ≤ N
    · by_cases hb : 1 ≤ b.val ∧ b.val ≤ N
      · by_cases hc : 1 ≤ c.val ∧ c.val ≤ N
        · have hsum : a + b + c = ((a.val + b.val + c.val : ℕ) : ZMod M) := by
            push_cast; simp only [ZMod.natCast_zmod_val]
          have hiff : a + b + c = (n : ZMod M) ↔ a.val + b.val + c.val = n := by
            rw [hsum, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt hn]
          by_cases h : a.val + b.val + c.val = n
          · rw [if_pos (hiff.2 h), if_pos h]
          · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
        · simp [hP', hc]
      · simp [hP', hb]
    · simp [hP', ha]
  unfold r3Z
  simp_rw [hpt]
  rw [sum_zmod_eq_range (fun x => ∑ b : ZMod M, ∑ c : ZMod M, G x b.val c.val)]
  have hin : Icc 1 N ⊆ range M := by
    intro x hx; rw [mem_Icc] at hx; rw [mem_range]; omega
  have hzero : ∀ x y z, ¬ (1 ≤ x ∧ x ≤ N) ∨ ¬ (1 ≤ y ∧ y ≤ N) ∨ ¬ (1 ≤ z ∧ z ≤ N) →
      G x y z = 0 := by
    intro x y z h
    simp only [hG, hP']
    rcases h with h | h | h <;> simp [h]
  rw [← sum_subset hin (fun x _ hx => by
    rw [sum_eq_zero]; intro b _; rw [sum_eq_zero]; intro c _
    exact hzero _ _ _ (Or.inl (by rw [mem_Icc] at hx; exact hx)))]
  unfold r3
  push_cast
  refine sum_congr rfl fun x hx => ?_
  rw [sum_zmod_eq_range (fun y => ∑ c : ZMod M, G x y c.val)]
  rw [← sum_subset hin (fun y _ hy => by
    rw [sum_eq_zero]; intro c _
    exact hzero _ _ _ (Or.inr (Or.inl (by rw [mem_Icc] at hy; exact hy))))]
  refine sum_congr rfl fun y hy => ?_
  rw [sum_zmod_eq_range (fun z => G x y z)]
  rw [← sum_subset hin (fun z _ hz => hzero _ _ _ (Or.inr (Or.inr
    (by rw [mem_Icc] at hz; exact hz))))]
  refine sum_congr rfl fun z hz => ?_
  rw [mem_Icc] at hx hy hz
  simp only [hG, hP', if_pos hx, if_pos hy, if_pos hz]
  split_ifs <;> push_cast <;> rfl

/-- **The ternary count is its major arc part up to the minor arc bound**, unconditional. -/
theorem r3_minor {N M P Q : ℕ} [NeZero M] (h3 : 3 * N < M) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hQN : Q ≤ N) {n : ℕ} (hn : n < M) :
    ‖(M : ℂ) * (r3 N n : ℂ) -
        ∑ k ∈ univ.filter (fun k => k ∉ minorSet P Q M),
          (𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ)‖
      ≤ (300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) *
          (1 + Real.log N) ^ 4) * ((M : ℝ) *
          ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2) := by
  rw [← r3Z_eq h3 hn]
  exact ternary_minor (by omega) hP hQ hQN (n : ZMod M)

end LeanLab.PNTPort.Vinogradov

