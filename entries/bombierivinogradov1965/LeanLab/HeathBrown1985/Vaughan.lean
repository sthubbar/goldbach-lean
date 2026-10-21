module

public import Mathlib

/-!
P0096 Heath-Brown 1985, Vaughan's identity 3.1 on page 53:
for `u, v ≥ 1`, `Σ_{v < n ≤ N} f(n) Λ(n) = S₁ - S₂ - S₃`. Here `u, v` are read as integers
`U, V ≥ 1`; for real `u, v` take `U = ⌊u⌋`, `V = ⌊v⌋`, every condition `c ≤ u` being `c ≤ ⌊u⌋`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset
open ArithmeticFunction (coe_mul_zeta_apply one_apply_ne coe_moebius_mul_coe_zeta intCoe_apply
  vonMangoldt_mul_zeta log)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

attribute [local instance] Classical.propDecidable

/-- `μ` cut to `n ≤ U`. -/
def muLe (U : ℕ) : ArithmeticFunction ℝ := ⟨fun n => if n ≤ U then (μ n : ℝ) else 0, by simp⟩
/-- `Λ` cut to `n ≤ V`. -/
def lamLe (V : ℕ) : ArithmeticFunction ℝ := ⟨fun n => if n ≤ V then Λ n else 0, by simp⟩
/-- `Λ` cut to `n > V`. -/
def lamGt (V : ℕ) : ArithmeticFunction ℝ := ⟨fun n => if V < n then Λ n else 0, by simp⟩
/-- `d_r = Σ_{c ∣ r, c ≤ U} μ(c)` cut to `r > U`. -/
def dGt (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun r => if U < r then (muLe U * (ζ : ArithmeticFunction ℝ)) r else 0, by simp⟩

theorem lam_split (V : ℕ) : (Λ : ArithmeticFunction ℝ) = lamLe V + lamGt V := by
  ext n
  rw [ArithmeticFunction.add_apply]
  simp only [lamLe, lamGt, ArithmeticFunction.coe_mk]
  split_ifs <;> first | omega | simp

theorem muLe_mul_zeta (U : ℕ) (hU : 1 ≤ U) :
    muLe U * (ζ : ArithmeticFunction ℝ) = 1 + dGt U := by
  ext r
  rw [ArithmeticFunction.add_apply]
  simp only [dGt, ArithmeticFunction.coe_mk]
  split_ifs with h
  · rw [one_apply_ne (by omega)]; ring
  · rw [add_zero, coe_mul_zeta_apply]
    have : ∑ i ∈ r.divisors, muLe U i = ∑ i ∈ r.divisors, ((μ i : ℤ) : ℝ) := by
      apply sum_congr rfl; intro i hi
      simp only [muLe, ArithmeticFunction.coe_mk]
      rw [if_pos ((Nat.divisor_le hi).trans (by omega))]
    rw [this]
    have h2 := congrArg (fun F : ArithmeticFunction ℝ => F r)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    simp only [coe_mul_zeta_apply, intCoe_apply] at h2
    exact h2

/-- **Vaughan's identity in convolution form**:
`Λ_{>V} = μ_{≤U} * log - μ_{≤U} * 1 * Λ_{≤V} - d_{>U} * Λ_{>V}`. -/
theorem vaughan_conv (U V : ℕ) (hU : 1 ≤ U) :
    lamGt V = muLe U * log - muLe U * (ζ : ArithmeticFunction ℝ) * lamLe V - dGt U * lamGt V := by
  rw [← vonMangoldt_mul_zeta, mul_comm (Λ : ArithmeticFunction ℝ), ← mul_assoc,
    muLe_mul_zeta U hU, lam_split V]
  ring

/-- Summing a Dirichlet convolution against `f` up to `N`. -/
theorem sum_conv (g h : ArithmeticFunction ℝ) (f : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Icc 1 N, (g * h) m * f m =
      ∑ c ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / c), g c * h r * f (c * r) := by
  simp_rw [ArithmeticFunction.mul_apply, sum_mul]
  rw [sum_sigma', sum_sigma']
  apply Finset.sum_nbij' (fun p => ⟨p.2.1, p.2.2⟩) (fun p => ⟨p.1 * p.2, (p.1, p.2)⟩)
  · rintro ⟨m, c, r⟩ hp
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hm1, hmN⟩, hcr, hm0⟩ := hp
    subst hcr
    have hc : 1 ≤ c := Nat.pos_of_ne_zero (fun h => by simp [h] at hm0)
    have hr : 1 ≤ r := Nat.pos_of_ne_zero (fun h => by simp [h] at hm0)
    refine ⟨⟨hc, le_trans (Nat.le_mul_of_pos_right c hr) hmN⟩, hr, ?_⟩
    exact (Nat.le_div_iff_mul_le hc).mpr (by linarith [Nat.mul_comm c r])
  · rintro ⟨c, r⟩ hp
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hc1, hcN⟩, hr1, hrN⟩ := hp
    have := (Nat.le_div_iff_mul_le hc1).mp hrN
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), by linarith [Nat.mul_comm c r]⟩, trivial,
      by positivity⟩
  · rintro ⟨m, c, r⟩ hp
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨_, hcr, _⟩ := hp
    subst hcr; rfl
  · rintro ⟨c, r⟩ _; rfl
  · rintro ⟨m, c, r⟩ hp
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨_, hcr, _⟩ := hp
    subst hcr; rfl

/-- `S₁ = Σ_{c ≤ u} μ(c) Σ_{r ≤ N/c} (log r) f(cr)`. -/
def S1 (U N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ c ∈ Icc 1 U, (μ c : ℝ) * ∑ r ∈ Icc 1 (N / c), Real.log r * f (c * r)

/-- `c_k = Σ_{c ≤ u, n ≤ v, cn = k} μ(c) Λ(n)`. -/
def ck (U V k : ℕ) : ℝ :=
  ∑ c ∈ Icc 1 U, ∑ n ∈ Icc 1 V, if c * n = k then (μ c : ℝ) * Λ n else 0

/-- `S₂ = Σ_{k ≤ uv} c_k Σ_{r ≤ N/k} f(kr)`. -/
def S2 (U V N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (U * V), ck U V k * ∑ r ∈ Icc 1 (N / k), f (k * r)

/-- `d_r = Σ_{c ∣ r, c ≤ u} μ(c)`. -/
def dr (U r : ℕ) : ℝ := ∑ c ∈ r.divisors.filter (· ≤ U), (μ c : ℝ)

/-- `S₃ = Σ_{r > u} Σ_{n > v, rn ≤ N} d_r Λ(n) f(rn)`. -/
def S3 (U V N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    if U < r ∧ V < n ∧ r * n ≤ N then dr U r * Λ n * f (r * n) else 0

theorem sum_Icc_eq_of_vanish (N M : ℕ) (G : ℕ → ℝ) (h1 : ∀ k, N < k → G k = 0)
    (h2 : ∀ k, M < k → G k = 0) : ∑ k ∈ Icc 1 N, G k = ∑ k ∈ Icc 1 M, G k := by
  have eN : ∑ k ∈ Icc 1 (min N M), G k = ∑ k ∈ Icc 1 N, G k := by
    apply sum_subset
    · intro k hk; simp only [mem_Icc] at hk ⊢; omega
    · intro k hk hk'
      simp only [mem_Icc, not_and, not_le] at hk hk'
      exact h2 k (by have := hk' hk.1; omega)
  have eM : ∑ k ∈ Icc 1 (min N M), G k = ∑ k ∈ Icc 1 M, G k := by
    apply sum_subset
    · intro k hk; simp only [mem_Icc] at hk ⊢; omega
    · intro k hk hk'
      simp only [mem_Icc, not_and, not_le] at hk hk'
      exact h1 k (by have := hk' hk.1; omega)
  rw [← eN, eM]

theorem sum_S1 (U N : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, (muLe U * log) m * f m = S1 U N f := by
  rw [sum_conv]
  unfold S1
  have e : ∀ c ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / c), muLe U c * log r * f (c * r) =
      if c ≤ U then (μ c : ℝ) * ∑ r ∈ Icc 1 (N / c), Real.log r * f (c * r) else 0 := by
    intro c _
    simp only [muLe, ArithmeticFunction.coe_mk, ArithmeticFunction.log_apply]
    split_ifs
    · rw [mul_sum]; apply sum_congr rfl; intro r _; ring
    · simp
  rw [sum_congr rfl e]
  have hvan : ∀ c, N < c → (μ c : ℝ) * ∑ r ∈ Icc 1 (N / c), Real.log r * f (c * r) = 0 := by
    intro c hc; rw [Nat.div_eq_of_lt hc]; simp
  rw [sum_Icc_eq_of_vanish N U _ (fun c hc => by simp [hvan c hc]) (fun c hc => by
    simp [show ¬ c ≤ U by omega])]
  apply sum_congr rfl; intro c hc
  rw [if_pos (mem_Icc.mp hc).2]

theorem ck_eq (U V k : ℕ) : (muLe U * lamLe V) k = ck U V k := by
  rw [ArithmeticFunction.mul_apply]
  unfold ck
  rw [← sum_product', ← sum_filter]
  simp only [muLe, lamLe, ArithmeticFunction.coe_mk, ite_zero_mul_ite_zero]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext ⟨c, n⟩
  simp only [mem_filter, Nat.mem_divisorsAntidiagonal, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨hcn, hk⟩, hc, hn⟩
    have hc0 : c ≠ 0 := fun h => hk (by rw [← hcn, h, zero_mul])
    have hn0 : n ≠ 0 := fun h => hk (by rw [← hcn, h, mul_zero])
    exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr hc0, hc⟩, Nat.one_le_iff_ne_zero.mpr hn0, hn⟩, hcn⟩
  · rintro ⟨⟨⟨hc1, hc⟩, hn1, hn⟩, hcn⟩
    refine ⟨⟨hcn, ?_⟩, hc, hn⟩
    rw [← hcn]; positivity

theorem ck_eq_zero (U V k : ℕ) (hk : U * V < k) : ck U V k = 0 := by
  unfold ck
  apply sum_eq_zero; intro c hc; apply sum_eq_zero; intro n hn
  rw [if_neg]
  intro h
  simp only [mem_Icc] at hc hn
  have : c * n ≤ U * V := Nat.mul_le_mul hc.2 hn.2
  omega

theorem sum_S2 (U V N : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, (muLe U * (ζ : ArithmeticFunction ℝ) * lamLe V) m * f m = S2 U V N f := by
  rw [show muLe U * (ζ : ArithmeticFunction ℝ) * lamLe V =
    muLe U * lamLe V * (ζ : ArithmeticFunction ℝ) by ring, sum_conv]
  unfold S2
  have e : ∀ c ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / c),
      (muLe U * lamLe V) c * (ζ : ArithmeticFunction ℝ) r * f (c * r) =
      ck U V c * ∑ r ∈ Icc 1 (N / c), f (c * r) := by
    intro c _
    rw [ck_eq, mul_sum]; apply sum_congr rfl; intro r hr
    have hr0 : r ≠ 0 := by have := (mem_Icc.mp hr).1; omega
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hr0]
    push_cast; ring
  rw [sum_congr rfl e]
  apply sum_Icc_eq_of_vanish
  · intro c hc; rw [Nat.div_eq_of_lt hc]; simp
  · intro c hc; rw [ck_eq_zero U V c hc, zero_mul]

theorem dGt_apply (U r : ℕ) : dGt U r = if U < r then dr U r else 0 := by
  simp only [dGt, ArithmeticFunction.coe_mk]
  split_ifs
  · rw [ArithmeticFunction.coe_mul_zeta_apply, dr, sum_filter]
    apply sum_congr rfl; intro c _
    simp only [muLe, ArithmeticFunction.coe_mk]
  · rfl

theorem sum_S3 (U V N : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, (dGt U * lamGt V) m * f m = S3 U V N f := by
  rw [sum_conv]
  unfold S3
  apply sum_congr rfl; intro r hr
  have hr1 := (mem_Icc.mp hr).1
  have hfil : (Icc 1 N).filter (fun n => r * n ≤ N) = Icc 1 (N / r) := by
    ext n; simp only [mem_filter, mem_Icc]
    rw [Nat.le_div_iff_mul_le hr1]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by linarith [Nat.mul_comm r n]⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, by linarith [Nat.mul_comm r n]⟩
      nlinarith
  rw [← hfil, sum_filter]
  apply sum_congr rfl; intro n _
  rw [dGt_apply]
  simp only [lamGt, ArithmeticFunction.coe_mk]
  by_cases h1 : U < r <;> by_cases h2 : V < n <;> by_cases h3 : r * n ≤ N <;> simp [h1, h2, h3]

/-- **Vaughan's identity 3.1, page 53**: for `U ≥ 1`,
`Σ_{V < n ≤ N} f(n) Λ(n) = S₁ - S₂ - S₃`. -/
theorem vaughan (U V N : ℕ) (hU : 1 ≤ U) (f : ℕ → ℝ) :
    ∑ n ∈ (Icc 1 N).filter (V < ·), f n * Λ n = S1 U N f - S2 U V N f - S3 U V N f := by
  rw [← sum_S1, ← sum_S2, ← sum_S3, ← sum_sub_distrib, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl; intro m _
  have h := congrArg (fun F : ArithmeticFunction ℝ => F m) (vaughan_conv U V hU)
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply] at h
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h
  have hl : lamGt V m = if V < m then Λ m else 0 := by
    simp only [lamGt, ArithmeticFunction.coe_mk]
  rw [hl] at h
  split_ifs at h ⊢ with hm
  · rw [h]; ring
  · have : 0 = (muLe U * log) m - (muLe U * (ζ : ArithmeticFunction ℝ) * lamLe V) m -
        (dGt U * lamGt V) m := h
    linear_combination (f m) * this

end LeanLab.HeathBrown1985
