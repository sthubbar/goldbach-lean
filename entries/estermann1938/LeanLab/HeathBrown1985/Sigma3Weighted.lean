module

public import Mathlib
public import LeanLab.HeathBrown1985.Sigma3Cauchy
public import LeanLab.HeathBrown1985.Sigma3Diag
public import LeanLab.HeathBrown1985.Sigma3Off
public import LeanLab.HeathBrown1985.MainTerm

/-!
P0096 Heath-Brown 1985, pages 55 to 56, `BoundSigma3` for large `x` by a weighted Cauchy step:
`Σ₃² ≤ (Σ_{m,n} Λ(n)²/n) · (Σ_{m,n} n T_m(n)²)`. The weight `n` keeps the `Q` saving that the
plain Cauchy step loses: on the diagonal `n < 3x/r` with `r > Q`, and off the diagonal the
sum over `n` is a progression sum of `Δ_Q`, bounded by Lemma 1, 2.7, after Abel summation.
This replaces the paper's dyadic split 3.4.
AI-written Lean code, Claude, run 20261017T0603Z-10326. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-! ### Abel summation and convex sets of naturals -/

theorem abel_identity (c : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, (n : ℝ) * c n =
      b * ∑ n ∈ Ioc a b, c n - ∑ t ∈ Ico a b, ∑ n ∈ Ioc a t, c n := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), sum_Ico_succ_top hab, ih]
    push_cast
    ring

/-- Abel: `|Σ_{a < n ≤ b} n c_n| ≤ 2 b E` when every partial sum from `a` is at most `E`. -/
theorem abel_bound (c : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (E : ℝ)
    (hE : ∀ t, a ≤ t → t ≤ b → |∑ n ∈ Ioc a t, c n| ≤ E) :
    |∑ n ∈ Ioc a b, (n : ℝ) * c n| ≤ 2 * b * E := by
  rw [abel_identity c a b hab]
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE a le_rfl hab)
  have h1 : |(b : ℝ) * ∑ n ∈ Ioc a b, c n| ≤ b * E := by
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (hE b hab le_rfl) (by positivity)
  have h2 : |∑ t ∈ Ico a b, ∑ n ∈ Ioc a t, c n| ≤ b * E := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ t ∈ Ico a b, |∑ n ∈ Ioc a t, c n| ≤ ∑ t ∈ Ico a b, E :=
          sum_le_sum fun t ht => by
            rw [mem_Ico] at ht; exact hE t ht.1 ht.2.le
      _ = (b - a : ℕ) * E := by simp
      _ ≤ b * E := by
          apply mul_le_mul_of_nonneg_right _ hE0
          exact_mod_cast Nat.sub_le b a
  calc _ ≤ |(b : ℝ) * ∑ n ∈ Ioc a b, c n| + |∑ t ∈ Ico a b, ∑ n ∈ Ioc a t, c n| :=
        abs_sub _ _
    _ ≤ b * E + b * E := add_le_add h1 h2
    _ = 2 * b * E := by ring

/-- A nonempty order-convex finite set of positive naturals is an interval `(a, b]`. -/
theorem convex_eq_Ioc (S : Finset ℕ) (hne : S.Nonempty) (h0 : ∀ n ∈ S, 1 ≤ n)
    (hconv : ∀ n₁ ∈ S, ∀ n₃ ∈ S, ∀ n₂, n₁ ≤ n₂ → n₂ ≤ n₃ → n₂ ∈ S) :
    S = Ioc (S.min' hne - 1) (S.max' hne) := by
  have hmin1 := h0 _ (S.min'_mem hne)
  ext n
  rw [mem_Ioc]
  constructor
  · intro hn
    have := S.min'_le n hn
    exact ⟨by omega, S.le_max' n hn⟩
  · rintro ⟨h1, h2⟩
    exact hconv _ (S.min'_mem hne) _ (S.max'_mem hne) n (by omega) h2


/-! ### The weighted Cauchy step -/

/-- `Σ₃² ≤ (Σ_{m,n} Λ(n)²/n) · Σ_{m,n} n T_m(n)²`. -/
theorem sigma3_sq_le_weighted (x Q : ℝ) :
    Sigma3 x Q ^ 2 ≤
      (∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊, Λ n ^ 2 / n) *
        ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊,
          (n : ℝ) * T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n ^ 2 := by
  set N := ⌊3 * x⌋₊
  set T := fun p : ℕ × ℕ => T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ N (fm x Q p.1) p.2
  have h1 : Sigma3 x Q ≤ ∑ p ∈ mRange x ×ˢ Icc 1 N, Λ p.2 * |T p| := by
    rw [sum_product]
    unfold Sigma3
    exact sum_le_sum fun m _ => abs_S3_le _ _ _ _
  have h0 : 0 ≤ Sigma3 x Q := sum_nonneg (fun _ _ => abs_nonneg _)
  have hrw : ∑ p ∈ mRange x ×ˢ Icc 1 N, Λ p.2 * |T p| =
      ∑ p ∈ mRange x ×ˢ Icc 1 N, (Λ p.2 / √(p.2 : ℝ)) * |√(p.2 : ℝ) * T p| := by
    apply sum_congr rfl
    intro p hp
    have hn : (1 : ℝ) ≤ p.2 := by
      have := (mem_Icc.mp (mem_product.mp hp).2).1; exact_mod_cast this
    have hs : 0 < √(p.2 : ℝ) := Real.sqrt_pos.mpr (by linarith)
    rw [abs_mul, abs_of_pos hs]
    field_simp
  have h2 := cauchy_abs (mRange x ×ˢ Icc 1 N) (fun p => Λ p.2 / √(p.2 : ℝ))
    (fun p => √(p.2 : ℝ) * T p)
  have e1 : ∑ p ∈ mRange x ×ˢ Icc 1 N, (Λ p.2 / √(p.2 : ℝ)) ^ 2 =
      ∑ p ∈ mRange x ×ˢ Icc 1 N, Λ p.2 ^ 2 / p.2 := by
    apply sum_congr rfl
    intro p _
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have e2 : ∑ p ∈ mRange x ×ˢ Icc 1 N, (√(p.2 : ℝ) * T p) ^ 2 =
      ∑ p ∈ mRange x ×ˢ Icc 1 N, (p.2 : ℝ) * T p ^ 2 := by
    apply sum_congr rfl
    intro p _
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [e1, e2] at h2
  rw [hrw] at h1
  have := (pow_le_pow_left₀ h0 h1 2).trans h2
  rw [sum_product, sum_product] at this
  exact this

theorem card_mRange_le_floor (x : ℝ) : ((mRange x).card : ℝ) ≤ ⌊3 * x⌋₊ := by
  have : (mRange x).card ≤ ⌊3 * x⌋₊ := (card_filter_le _ _).trans (by simp)
  exact_mod_cast this

/-- The `Λ` factor: `Σ_{m,n} Λ(n)²/n ≤ N (log N)² (1 + log N)` with `N = ⌊3x⌋`. -/
theorem lambda_factor_le (x : ℝ) :
    ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊, Λ n ^ 2 / n ≤
      ⌊3 * x⌋₊ * (Real.log ⌊3 * x⌋₊ ^ 2 * (1 + Real.log ⌊3 * x⌋₊)) := by
  set N := ⌊3 * x⌋₊
  have hinner : ∑ n ∈ Icc 1 N, Λ n ^ 2 / n ≤ Real.log N ^ 2 * (1 + Real.log N) := by
    calc ∑ n ∈ Icc 1 N, Λ n ^ 2 / n ≤ ∑ n ∈ Icc 1 N, Real.log N ^ 2 * (n : ℝ)⁻¹ := by
          apply sum_le_sum
          intro n hn
          rw [mem_Icc] at hn
          have hl : Λ n ≤ Real.log N :=
            ArithmeticFunction.vonMangoldt_le_log.trans
              (Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2))
          have hl0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
          rw [div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_left₀ hl0 hl 2
      _ = Real.log N ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ := by rw [mul_sum]
      _ ≤ Real.log N ^ 2 * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log N) (by positivity)
  calc ∑ m ∈ mRange x, ∑ n ∈ Icc 1 N, Λ n ^ 2 / n
      ≤ ∑ m ∈ mRange x, Real.log N ^ 2 * (1 + Real.log N) := sum_le_sum fun _ _ => hinner
    _ = (mRange x).card * (Real.log N ^ 2 * (1 + Real.log N)) := by simp
    _ ≤ N * (Real.log N ^ 2 * (1 + Real.log N)) := by
        apply mul_le_mul_of_nonneg_right (card_mRange_le_floor x)
        have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
        positivity


/-! ### Expanding `n T²` over pairs `(r₁, r₂)` -/

/-- One term of `T3`. -/
def gT (U V N : ℕ) (f : ℕ → ℝ) (n r : ℕ) : ℝ :=
  if U < r ∧ V < n ∧ r * n ≤ N then dr U r * f (r * n) else 0

/-- The pair sum `X(r₁, r₂) = Σ_{m,n} n g(r₁) g(r₂)`. -/
def Xr (x Q : ℝ) (r₁ r₂ : ℕ) : ℝ :=
  ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊,
    (n : ℝ) * gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r₁ *
      gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r₂

theorem swap4 {α β γ δ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ)
    (F : α → β → γ → δ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d =
      ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, F a b c d := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d
      = ∑ a ∈ s, ∑ c ∈ u, ∑ d ∈ v, ∑ b ∈ t, F a b c d :=
        sum_congr rfl fun a _ => (sum_comm).trans (sum_congr rfl fun c _ => sum_comm)
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, F a b c d := sum_comm
    _ = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, F a b c d :=
        sum_congr rfl fun c _ => sum_comm

theorem sum_nT_sq_eq (x Q : ℝ) :
    ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊,
        (n : ℝ) * T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n ^ 2 =
      ∑ r₁ ∈ Icc 1 ⌊3 * x⌋₊, ∑ r₂ ∈ Icc 1 ⌊3 * x⌋₊, Xr x Q r₁ r₂ := by
  have hT : ∀ m n, T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n =
      ∑ r ∈ Icc 1 ⌊3 * x⌋₊, gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r := fun m n => rfl
  simp_rw [hT, sq, sum_mul_sum, mul_sum]
  unfold Xr
  rw [swap4]
  apply sum_congr rfl; intro r₁ _
  apply sum_congr rfl; intro r₂ _
  apply sum_congr rfl; intro m _
  apply sum_congr rfl; intro n _
  ring

/-- `Xr` vanishes unless both `r` lie in `(U, 3Q²)`. -/
theorem Xr_eq_zero (x Q : ℝ) (hx : 0 < x) (hQ : 0 < Q) (r₁ r₂ : ℕ)
    (h : ¬ ((⌊Q⌋₊ < r₁ ∧ (r₁ : ℝ) < 3 * Q ^ 2) ∧ (⌊Q⌋₊ < r₂ ∧ (r₂ : ℝ) < 3 * Q ^ 2))) :
    Xr x Q r₁ r₂ = 0 := by
  unfold Xr
  apply sum_eq_zero; intro m _
  apply sum_eq_zero; intro n _
  unfold gT
  by_cases h1 : ⌊Q⌋₊ < r₁ ∧ ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊
  · by_cases h2 : ⌊Q⌋₊ < r₂ ∧ ⌊x / Q ^ 2⌋₊ < n ∧ r₂ * n ≤ ⌊3 * x⌋₊
    · exfalso; apply h
      exact ⟨⟨h1.1, S3_term_support x Q hx hQ r₁ n h1.2.1 h1.2.2⟩,
        ⟨h2.1, S3_term_support x Q hx hQ r₂ n h2.2.1 h2.2.2⟩⟩
    · rw [if_neg h2]; ring
  · rw [if_neg h1]; ring

theorem Xr_symm (x Q : ℝ) (r₁ r₂ : ℕ) : Xr x Q r₁ r₂ = Xr x Q r₂ r₁ := by
  unfold Xr
  apply sum_congr rfl; intro m _
  apply sum_congr rfl; intro n _
  ring

/-! ### The diagonal -/

theorem fm_ne_zero_lt {x Q : ℝ} {m k : ℕ} (h : fm x Q m k ≠ 0) (hm : m ∈ mRange x) :
    (k : ℝ) < 3 * x := by
  unfold fm at h
  split_ifs at h with hc
  · have hm' := (mem_filter.mp hm).1
    rw [mem_Icc] at hm'
    have hx : (0 : ℝ) ≤ 3 * x := by
      by_contra hneg; push Not at hneg
      have : ⌊3 * x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    have : (m : ℝ) ≤ 3 * x := (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le hx)
    have : (k : ℝ) < m := by exact_mod_cast hc.2
    linarith
  · exact absurd rfl h

/-- Diagonal: `X(r, r) ≤ d_r² (3x/r)(2x/r) Σ_{k ≤ x} Δ_Q(k)²`. -/
theorem Xr_diag_le (x Q : ℝ) (hx : 1 ≤ x) (r : ℕ) (hr : 1 ≤ r) (hrx : (r : ℝ) ≤ x) :
    Xr x Q r r ≤ dr ⌊Q⌋₊ r ^ 2 * (3 * x / r) * (2 * x / r * ∑ k ∈ Icc 1 ⌊x⌋₊, DeltaQ Q k ^ 2) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hterm : ∀ m ∈ mRange x, ∀ n ∈ Icc 1 ⌊3 * x⌋₊,
      (n : ℝ) * gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r *
        gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r ≤
      dr ⌊Q⌋₊ r ^ 2 * (3 * x / r) * fm x Q m (r * n) ^ 2 := by
    intro m hm n _
    unfold gT
    split_ifs with h
    · by_cases hf : fm x Q m (r * n) = 0
      · rw [hf]; simp
      · have hlt := fm_ne_zero_lt hf hm
        push_cast at hlt
        have hn : (n : ℝ) ≤ 3 * x / r := by
          rw [le_div_iff₀ hrpos]; linarith
        have e : (n : ℝ) * (dr ⌊Q⌋₊ r * fm x Q m (r * n)) * (dr ⌊Q⌋₊ r * fm x Q m (r * n)) =
            n * (dr ⌊Q⌋₊ r ^ 2 * fm x Q m (r * n) ^ 2) := by ring
        rw [e]
        have h0 : 0 ≤ dr ⌊Q⌋₊ r ^ 2 * fm x Q m (r * n) ^ 2 := by positivity
        nlinarith
    · simp only [mul_zero, zero_mul]
      positivity
  calc Xr x Q r r ≤ ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊,
        dr ⌊Q⌋₊ r ^ 2 * (3 * x / r) * fm x Q m (r * n) ^ 2 :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hterm m hm n hn
    _ = dr ⌊Q⌋₊ r ^ 2 * (3 * x / r) *
        ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊, fm x Q m (r * n) ^ 2 := by
        rw [mul_sum]; simp_rw [mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (diag_fm_sq_le x Q hx r _ hr hrx)
        have : 0 ≤ 3 * x / r := by positivity
        positivity


/-! ### Off the diagonal: the substitution `k = m − r₁ n` -/

/-- The `n` range for a given `k`, with `δ = r₁ − r₂`. -/
def Sk (x Q : ℝ) (r₁ r₂ k : ℕ) : Finset ℕ :=
  (Icc 1 ⌊3 * x⌋₊).filter (fun n => ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊ ∧
    k + r₁ * n ∈ mRange x ∧ ((k + r₁ * n : ℕ) : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ))

theorem gT_mul_gT (x Q : ℝ) (r₁ r₂ m n : ℕ) (h21 : r₂ < r₁) (hU : ⌊Q⌋₊ < r₂) :
    (n : ℝ) * gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r₁ *
        gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r₂ =
      dr ⌊Q⌋₊ r₁ * dr ⌊Q⌋₊ r₂ *
        (if ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊ then (n : ℝ) *
          (if (m : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ) ∧ r₁ * n < m then
            DeltaQ Q (m - r₁ * n) * DeltaQ Q (m - r₂ * n) else 0) else 0) := by
  have hle : r₂ * n ≤ r₁ * n := Nat.mul_le_mul_right n h21.le
  have hlec : ((r₂ * n : ℕ) : ℝ) ≤ ((r₁ * n : ℕ) : ℝ) := by exact_mod_cast hle
  unfold gT
  by_cases hn : ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊
  · rw [if_pos ⟨by omega, hn.1, hn.2⟩, if_pos ⟨hU, hn.1, by omega⟩, if_pos hn]
    unfold fm
    by_cases hc : (m : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ) ∧ r₁ * n < m
    · rw [if_pos hc, if_pos ⟨by linarith [hc.1], hc.2⟩, if_pos ⟨hc.1, by omega⟩]
      ring
    · rw [if_neg hc]
      by_cases h1 : (m : ℝ) - x ≤ ((r₁ * n : ℕ) : ℝ) ∧ r₁ * n < m
      · by_cases h2 : (m : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ) ∧ r₂ * n < m
        · exact absurd ⟨h2.1, h1.2⟩ hc
        · rw [if_neg h2]; ring
      · rw [if_neg h1]; ring
  · rw [if_neg hn]
    by_cases h1 : ⌊Q⌋₊ < r₁ ∧ ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊
    · exact absurd ⟨h1.2.1, h1.2.2⟩ hn
    · rw [if_neg h1]; ring

theorem reindex_m (x Q : ℝ) (r₁ r₂ n : ℕ) (h21 : r₂ < r₁) :
    ∑ m ∈ mRange x, (if (m : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ) ∧ r₁ * n < m then
        DeltaQ Q (m - r₁ * n) * DeltaQ Q (m - r₂ * n) else 0) =
      ∑ k ∈ Icc 1 ⌊x⌋₊, (if k + r₁ * n ∈ mRange x ∧
          ((k + r₁ * n : ℕ) : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ) then
        DeltaQ Q k * DeltaQ Q (k + (r₁ - r₂) * n) else 0) := by
  have hle : r₂ * n ≤ r₁ * n := Nat.mul_le_mul_right n h21.le
  have hsub : (r₁ - r₂) * n = r₁ * n - r₂ * n := Nat.sub_mul r₁ r₂ n
  rw [← sum_filter, ← sum_filter]
  refine sum_bij' (fun m _ => m - r₁ * n) (fun k _ => k + r₁ * n) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_filter] at hm ⊢
    obtain ⟨hmR, hc1, hc2⟩ := hm
    have hcast : ((m - r₁ * n : ℕ) : ℝ) = (m : ℝ) - ((r₁ * n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hc2.le]
    have hlec : ((r₂ * n : ℕ) : ℝ) ≤ ((r₁ * n : ℕ) : ℝ) := by exact_mod_cast hle
    have hkx : ((m - r₁ * n : ℕ) : ℝ) ≤ x := by rw [hcast]; linarith
    have hx0 : 0 ≤ x := by
      have : (0 : ℝ) ≤ ((m - r₁ * n : ℕ) : ℝ) := Nat.cast_nonneg _
      by_contra h; push Not at h
      have : (1 : ℝ) ≤ ((m - r₁ * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m - r₁ * n)
      linarith
    refine ⟨mem_Icc.mpr ⟨by omega, Nat.le_floor hkx⟩, ?_, ?_⟩
    · rw [Nat.sub_add_cancel hc2.le]; exact hmR
    · rw [Nat.sub_add_cancel hc2.le]; exact hc1
  · intro k hk
    rw [mem_filter] at hk ⊢
    obtain ⟨hkI, hk1, hk2⟩ := hk
    have := (mem_Icc.mp hkI).1
    exact ⟨hk1, by exact_mod_cast hk2, by omega⟩
  · intro m hm
    have := (mem_filter.mp hm).2.2
    omega
  · intro k _
    omega
  · intro m hm
    have h2 := (mem_filter.mp hm).2.2
    congr 2
    omega

/-- The substitution: for `r₂ < r₁`, `U < r₂`,
`X(r₁, r₂) = d_{r₁} d_{r₂} Σ_{k ≤ x} Δ_Q(k) Σ_{n ∈ S_k} n Δ_Q(k + δ n)`. -/
theorem Xr_offdiag_eq (x Q : ℝ) (r₁ r₂ : ℕ) (h21 : r₂ < r₁) (hU : ⌊Q⌋₊ < r₂) :
    Xr x Q r₁ r₂ = dr ⌊Q⌋₊ r₁ * dr ⌊Q⌋₊ r₂ *
      ∑ k ∈ Icc 1 ⌊x⌋₊, DeltaQ Q k *
        ∑ n ∈ Sk x Q r₁ r₂ k, (n : ℝ) * DeltaQ Q (k + (r₁ - r₂) * n) := by
  unfold Xr
  simp_rw [gT_mul_gT x Q r₁ r₂ _ _ h21 hU]
  rw [sum_comm]
  simp_rw [← mul_sum]
  congr 1
  have e : ∀ n ∈ Icc 1 ⌊3 * x⌋₊, ∑ m ∈ mRange x,
      (if ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊ then (n : ℝ) *
        (if (m : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ) ∧ r₁ * n < m then
          DeltaQ Q (m - r₁ * n) * DeltaQ Q (m - r₂ * n) else 0) else 0) =
      ∑ k ∈ Icc 1 ⌊x⌋₊, (if ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊ ∧ k + r₁ * n ∈ mRange x ∧
          ((k + r₁ * n : ℕ) : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ) then
        DeltaQ Q k * ((n : ℝ) * DeltaQ Q (k + (r₁ - r₂) * n)) else 0) := by
    intro n _
    by_cases hn : ⌊x / Q ^ 2⌋₊ < n ∧ r₁ * n ≤ ⌊3 * x⌋₊
    · simp_rw [if_pos hn]
      rw [← mul_sum, reindex_m x Q r₁ r₂ n h21, mul_sum]
      apply sum_congr rfl; intro k _
      by_cases hk : k + r₁ * n ∈ mRange x ∧ ((k + r₁ * n : ℕ) : ℝ) - x ≤ ((r₂ * n : ℕ) : ℝ)
      · rw [if_pos hk, if_pos ⟨hn.1, hn.2, hk⟩]; ring
      · rw [if_neg hk, if_neg (fun h => hk ⟨h.2.2.1, h.2.2.2⟩)]; ring
    · simp_rw [if_neg hn]
      rw [sum_const_zero]
      symm; apply sum_eq_zero; intro k _
      rw [if_neg (fun h => hn ⟨h.1, h.2.1⟩)]
  rw [sum_congr rfl e, sum_comm]
  apply sum_congr rfl; intro k _
  unfold Sk
  rw [sum_filter, mul_sum]
  apply sum_congr rfl; intro n _
  split_ifs <;> ring


/-! ### The inner `n` sum off the diagonal -/

/-- The 2.7 error at an endpoint `y ∈ [V, x]` with `log y ≥ (log x)/2`. -/
theorem err_le (K A Q x y : ℝ) (δ k : ℕ) (hK : 0 ≤ K) (hA : 0 < A) (hδ : 1 ≤ δ) (hQ : 1 ≤ Q)
    (hy2 : 2 ≤ y) (hyx : y ≤ x) (hlog : Real.log x / 2 ≤ Real.log y) :
    lemma17Err K A Q y δ k ≤
      K * (Q * Real.log x ^ 2 + x * Real.log x / (δ * Q) * (Nat.gcd δ k : ℝ) *
        (δ.divisors.card : ℝ) + 2 ^ A * (x * Real.log x ^ (-A))) := by
  unfold lemma17Err
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlyx : Real.log y ≤ Real.log x := Real.log_le_log hy0 hyx
  have hlx2 : 0 < Real.log x / 2 := by linarith
  apply mul_le_mul_of_nonneg_left _ hK
  have hδQ : 0 < (δ : ℝ) * Q := by
    have : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
    positivity
  have hg : (0 : ℝ) ≤ (Nat.gcd δ k : ℝ) * (δ.divisors.card : ℝ) := by positivity
  have t1 : Q * Real.log y ^ 2 ≤ Q * Real.log x ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact pow_le_pow_left₀ hly.le hlyx 2
  have t2 : y * Real.log y / (δ * Q) * (Nat.gcd δ k : ℝ) * (δ.divisors.card : ℝ) ≤
      x * Real.log x / (δ * Q) * (Nat.gcd δ k : ℝ) * (δ.divisors.card : ℝ) := by
    rw [mul_assoc, mul_assoc (x * Real.log x / (δ * Q))]
    apply mul_le_mul_of_nonneg_right _ hg
    apply div_le_div_of_nonneg_right _ hδQ.le
    exact mul_le_mul hyx hlyx hly.le (by linarith)
  have t3 : y * Real.log y ^ (-A) ≤ 2 ^ A * (x * Real.log x ^ (-A)) := by
    have h1 : Real.log y ^ (-A) ≤ (Real.log x / 2) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos hlx2 hlog (by linarith)
    have h2 : (Real.log x / 2) ^ (-A) = 2 ^ A * Real.log x ^ (-A) := by
      rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    calc y * Real.log y ^ (-A) ≤ x * (2 ^ A * Real.log x ^ (-A)) := by
          rw [← h2]
          exact mul_le_mul hyx h1 (by positivity) (by linarith)
      _ = _ := by ring
  linarith


/-- The uniform error `E(δ, k)` for the inner sums. -/
def Ebd (K A Q x : ℝ) (δ k : ℕ) : ℝ :=
  K * (Q * Real.log x ^ 2 + x * Real.log x / (δ * Q) * (Nat.gcd δ k : ℝ) *
    (δ.divisors.card : ℝ) + 2 ^ A * (x * Real.log x ^ (-A)))

theorem Ebd_nonneg {K A Q x : ℝ} (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hx : 1 ≤ x) (δ k : ℕ) :
    0 ≤ Ebd K A Q x δ k := by
  unfold Ebd
  have : 0 ≤ Real.log x := Real.log_nonneg hx
  have : 0 ≤ x := by linarith
  have : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (by assumption) _
  positivity

theorem lemma17Err_le_abs (K A Q y : ℝ) (k l : ℕ) (hQ : 0 ≤ Q) (hy : 1 ≤ y) :
    lemma17Err K A Q y k l ≤ lemma17Err |K| A Q y k l := by
  unfold lemma17Err
  have : 0 ≤ Real.log y := Real.log_nonneg hy
  have : 0 ≤ y := by linarith
  have : 0 ≤ Real.log y ^ (-A) := Real.rpow_nonneg (by assumption) _
  apply mul_le_mul_of_nonneg_right (le_abs_self K)
  positivity

theorem Sk_convex (x Q : ℝ) (r₁ r₂ k : ℕ) (h21 : r₂ < r₁) :
    ∀ n₁ ∈ Sk x Q r₁ r₂ k, ∀ n₃ ∈ Sk x Q r₁ r₂ k, ∀ n₂, n₁ ≤ n₂ → n₂ ≤ n₃ →
      n₂ ∈ Sk x Q r₁ r₂ k := by
  intro n₁ h₁ n₃ h₃ n₂ h12 h23
  unfold Sk at *
  rw [mem_filter, mem_Icc] at h₁ h₃ ⊢
  obtain ⟨⟨a1, b1⟩, c1, d1, e1, f1⟩ := h₁
  obtain ⟨⟨a3, b3⟩, c3, d3, e3, f3⟩ := h₃
  unfold mRange at e1 e3 ⊢
  rw [mem_filter, mem_Icc] at e1 e3 ⊢
  have hm1 : r₁ * n₁ ≤ r₁ * n₂ := Nat.mul_le_mul_left r₁ h12
  have hm3 : r₁ * n₂ ≤ r₁ * n₃ := Nat.mul_le_mul_left r₁ h23
  refine ⟨⟨by omega, by omega⟩, by omega, by omega, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
  · have : ((k + r₁ * n₁ : ℕ) : ℝ) ≤ ((k + r₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast (by omega)
    linarith [e1.2]
  · push_cast at f3 ⊢
    have hr : (r₂ : ℝ) ≤ r₁ := by exact_mod_cast h21.le
    have hn : (n₂ : ℝ) ≤ n₃ := by exact_mod_cast h23
    nlinarith

theorem offdiag_inner_bound (h7 : Lemma1_7) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x Q : ℝ, 2 ≤ x → 1 ≤ Q → ∀ r₁ r₂ k : ℕ, r₂ < r₁ → 1 ≤ k →
      (2 : ℝ) ≤ ⌊x / Q ^ 2⌋₊ → Q ≤ ⌊x / Q ^ 2⌋₊ → (r₁ : ℝ) ≤ ⌊x / Q ^ 2⌋₊ →
      Real.log x / 2 ≤ Real.log ⌊x / Q ^ 2⌋₊ →
      |∑ n ∈ Sk x Q r₁ r₂ k, (n : ℝ) * DeltaQ Q (k + (r₁ - r₂) * n)| ≤
        2 * (3 * x / r₁) * (2 * Ebd K A Q x (r₁ - r₂) k) := by
  obtain ⟨K0, hK0⟩ := abs_sum_Ioc_DeltaQ_le h7 A hA
  refine ⟨|K0|, abs_nonneg _, ?_⟩
  intro x Q hx hQ r₁ r₂ k h21 hk hV2 hVQ hVr hlogV
  set V : ℕ := ⌊x / Q ^ 2⌋₊ with hVdef
  set δ : ℕ := r₁ - r₂ with hδ
  have hδ1 : 1 ≤ δ := by omega
  have hr1 : (0 : ℝ) < r₁ := by exact_mod_cast (show 0 < r₁ by omega)
  have hE0 : 0 ≤ Ebd |K0| A Q x δ k := Ebd_nonneg (abs_nonneg _) (by linarith) (by linarith) δ k
  set S := Sk x Q r₁ r₂ k with hSdef
  by_cases hS : S.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hS, sum_empty, abs_zero]
    positivity
  have h0 : ∀ n ∈ S, 1 ≤ n := fun n hn => (mem_Icc.mp (mem_filter.mp hn).1).1
  rw [convex_eq_Ioc S hS h0 (Sk_convex x Q r₁ r₂ k h21)]
  set a := S.min' hS - 1 with ha
  set b := S.max' hS with hb
  have hminS := S.min'_mem hS
  have hbS : b ∈ S := S.max'_mem hS
  have hab : a ≤ b := by have := S.min'_le_max' hS; omega
  have hminV : V < S.min' hS := (mem_filter.mp hminS).2.1
  have haV : V ≤ a := by omega
  obtain ⟨-, -, hb1, -, hb2⟩ := mem_filter.mp hbS
  have hb3 : (b : ℝ) ≤ 3 * x / r₁ := by
    rw [le_div_iff₀ hr1]
    have : ((r₁ * b : ℕ) : ℝ) ≤ 3 * x :=
      (Nat.cast_le.mpr hb1).trans (Nat.floor_le (by linarith))
    push_cast at this; linarith
  have hsubb : ((k + δ * b : ℕ) : ℝ) = ((k + r₁ * b : ℕ) : ℝ) - ((r₂ * b : ℕ) : ℝ) := by
    have : r₂ * b ≤ r₁ * b := Nat.mul_le_mul_right b h21.le
    rw [hδ, Nat.sub_mul]
    rw [← Nat.cast_sub (by omega)]
    congr 1; omega
  have hkb : ((k + δ * b : ℕ) : ℝ) ≤ x := by rw [hsubb]; linarith
  have hVr' : (V : ℝ) ≤ ((k + δ * a : ℕ) : ℝ) := by
    have : V ≤ k + δ * a := by
      have : a ≤ δ * a := Nat.le_mul_of_pos_left a (by omega)
      omega
    exact_mod_cast this
  have hδV : (δ : ℝ) ≤ V := by
    have : (δ : ℝ) ≤ r₁ := by exact_mod_cast (show δ ≤ r₁ by omega)
    linarith
  have hloga : Real.log x / 2 ≤ Real.log ((k + δ * a : ℕ) : ℝ) :=
    hlogV.trans (Real.log_le_log (by linarith) hVr')
  have hpart : ∀ t, a ≤ t → t ≤ b →
      |∑ n ∈ Ioc a t, DeltaQ Q (k + δ * n)| ≤ 2 * Ebd |K0| A Q x δ k := by
    intro t hat htb
    have hyt : ((k + δ * a : ℕ) : ℝ) ≤ ((k + δ * t : ℕ) : ℝ) := by
      have := Nat.mul_le_mul_left δ hat; exact_mod_cast (by omega)
    have hytx : ((k + δ * t : ℕ) : ℝ) ≤ x := by
      have := Nat.mul_le_mul_left δ htb
      have : ((k + δ * t : ℕ) : ℝ) ≤ ((k + δ * b : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have h := hK0 Q hQ k δ a t hδ1 hat (by linarith) (by linarith) (by linarith)
    have e1 := (lemma17Err_le_abs K0 A Q _ δ k (by linarith) (by linarith)).trans
      (err_le |K0| A Q x _ δ k (abs_nonneg _) hA hδ1 hQ (by linarith) hytx
        (hloga.trans (Real.log_le_log (by linarith) hyt)))
    have e2 := (lemma17Err_le_abs K0 A Q _ δ k (by linarith) (by linarith)).trans
      (err_le |K0| A Q x _ δ k (abs_nonneg _) hA hδ1 hQ (by linarith) (by linarith) hloga)
    unfold Ebd
    linarith
  have := abel_bound (fun n => DeltaQ Q (k + δ * n)) a b hab _ hpart
  refine this.trans ?_
  have : 0 ≤ 2 * Ebd |K0| A Q x δ k := by linarith
  have := mul_le_mul_of_nonneg_right hb3 this
  linarith


/-! ### Summing over `k` -/

theorem sum_gcd_d_le (δ N : ℕ) (hδ : 1 ≤ δ) :
    ∑ k ∈ Icc 1 N, (Nat.gcd δ k : ℝ) * (k.divisors.card : ℝ) ≤
      N * ((δ.divisors.card : ℝ) ^ 2 * (1 + Real.log N) ^ 2) := by
  have h := sum_gcd_divisors_div_le δ N hδ
  calc ∑ k ∈ Icc 1 N, (Nat.gcd δ k : ℝ) * (k.divisors.card : ℝ)
      = ∑ k ∈ Icc 1 N, (k : ℝ) * ((Nat.gcd k δ : ℝ) * (k.divisors.card : ℝ) / k) := by
        apply sum_congr rfl; intro k hk
        have : (k : ℝ) ≠ 0 := by have := (mem_Icc.mp hk).1; positivity
        rw [Nat.gcd_comm]; field_simp
    _ ≤ ∑ k ∈ Icc 1 N, (N : ℝ) * ((Nat.gcd k δ : ℝ) * (k.divisors.card : ℝ) / k) := by
        apply sum_le_sum; intro k hk
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (mem_Icc.mp hk).2
    _ = N * ∑ k ∈ Icc 1 N, (Nat.gcd k δ : ℝ) * (k.divisors.card : ℝ) / k := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem sum_absDelta_Ebd_le (K A Q x c : ℝ) (δ : ℕ) (hK : 0 ≤ K) (hQ : 1 ≤ Q) (hx : 1 ≤ x)
    (hc : 0 ≤ c) (hδ : 1 ≤ δ)
    (hΔ : ∀ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| ≤ c * Real.log x * (k.divisors.card : ℝ)) :
    ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * Ebd K A Q x δ k ≤
      c * Real.log x * K * (x * ((δ.divisors.card : ℝ) ^ 2 * (1 + Real.log x) ^ 2)) *
        (Q * Real.log x ^ 2 + 2 ^ A * (x * Real.log x ^ (-A)) +
          x * Real.log x / (δ * Q) * (δ.divisors.card : ℝ)) := by
  set L := Real.log x
  have hL : 0 ≤ L := Real.log_nonneg hx
  have hδQ : 0 < (δ : ℝ) * Q := by
    have : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
    positivity
  set P := Q * L ^ 2 + 2 ^ A * (x * L ^ (-A)) + x * L / (δ * Q) * (δ.divisors.card : ℝ)
  have hP : 0 ≤ P := by
    have : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL _
    have : 0 ≤ x := by linarith
    positivity
  have hterm : ∀ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * Ebd K A Q x δ k ≤
      c * L * K * P * ((Nat.gcd δ k : ℝ) * (k.divisors.card : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hg : (1 : ℝ) ≤ Nat.gcd δ k := by
      exact_mod_cast Nat.pos_of_ne_zero (by
        intro h; rw [Nat.gcd_eq_zero_iff] at h; omega)
    have hE : Ebd K A Q x δ k ≤ K * (P * Nat.gcd δ k) := by
      have e1 : Ebd K A Q x δ k = K * (Q * L ^ 2 + x * L / (δ * Q) * (Nat.gcd δ k : ℝ) *
          (δ.divisors.card : ℝ) + 2 ^ A * (x * L ^ (-A))) := rfl
      rw [e1]
      apply mul_le_mul_of_nonneg_left _ hK
      have hx0 : 0 ≤ x := by linarith
      have h0 : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL _
      have h1 : 0 ≤ Q * L ^ 2 := by positivity
      have h2 : 0 ≤ 2 ^ A * (x * L ^ (-A)) := by positivity
      have i1 := le_mul_of_one_le_right h1 hg
      have i2 := le_mul_of_one_le_right h2 hg
      have e : P * Nat.gcd δ k = Q * L ^ 2 * Nat.gcd δ k + 2 ^ A * (x * L ^ (-A)) * Nat.gcd δ k +
          x * L / (δ * Q) * (Nat.gcd δ k : ℝ) * (δ.divisors.card : ℝ) := by
        simp only [P]; ring
      rw [e]
      linarith
    have hE0 : 0 ≤ Ebd K A Q x δ k := Ebd_nonneg hK (by linarith) hx δ k
    calc |DeltaQ Q k| * Ebd K A Q x δ k ≤ (c * L * (k.divisors.card : ℝ)) * (K * (P * Nat.gcd δ k)) :=
          mul_le_mul (hΔ k hk) hE hE0 (by positivity)
      _ = c * L * K * P * ((Nat.gcd δ k : ℝ) * (k.divisors.card : ℝ)) := by ring
  have hN : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogN : Real.log ⌊x⌋₊ ≤ L := by
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h | h
    · rw [h]; simp [hL]
    · exact Real.log_le_log (by exact_mod_cast h) hN
  have hlogN0 : 0 ≤ Real.log ⌊x⌋₊ := Real.log_natCast_nonneg _
  have hsum := sum_gcd_d_le δ ⌊x⌋₊ hδ
  have hsum' : ∑ k ∈ Icc 1 ⌊x⌋₊, (Nat.gcd δ k : ℝ) * (k.divisors.card : ℝ) ≤
      x * ((δ.divisors.card : ℝ) ^ 2 * (1 + L) ^ 2) := by
    refine hsum.trans ?_
    apply mul_le_mul hN _ (by positivity) (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * Ebd K A Q x δ k
      ≤ ∑ k ∈ Icc 1 ⌊x⌋₊, c * L * K * P * ((Nat.gcd δ k : ℝ) * (k.divisors.card : ℝ)) :=
        sum_le_sum hterm
    _ = c * L * K * P * ∑ k ∈ Icc 1 ⌊x⌋₊, (Nat.gcd δ k : ℝ) * (k.divisors.card : ℝ) := by
        rw [mul_sum]
    _ ≤ c * L * K * P * (x * ((δ.divisors.card : ℝ) ^ 2 * (1 + L) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = _ := by ring

/-- Per pair, `r₂ < r₁`: `|X(r₁, r₂)| ≤ |d_{r₁}| |d_{r₂}| Σ_k |Δ_Q(k)| (6x/r₁)(2E)`. -/
theorem Xr_off_le (h7 : Lemma1_7) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x Q : ℝ, 2 ≤ x → 1 ≤ Q →
      (2 : ℝ) ≤ ⌊x / Q ^ 2⌋₊ → Q ≤ ⌊x / Q ^ 2⌋₊ →
      Real.log x / 2 ≤ Real.log ⌊x / Q ^ 2⌋₊ → ∀ r₁ r₂ : ℕ, r₂ < r₁ → ⌊Q⌋₊ < r₂ →
      (r₁ : ℝ) ≤ ⌊x / Q ^ 2⌋₊ →
      |Xr x Q r₁ r₂| ≤ |dr ⌊Q⌋₊ r₁| * |dr ⌊Q⌋₊ r₂| *
        ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * (2 * (3 * x / r₁) * (2 * Ebd K A Q x (r₁ - r₂) k)) := by
  obtain ⟨K, hK, hb⟩ := offdiag_inner_bound h7 A hA
  refine ⟨K, hK, ?_⟩
  intro x Q hx hQ hV2 hVQ hlogV r₁ r₂ h21 hU hVr
  rw [Xr_offdiag_eq x Q r₁ r₂ h21 hU, abs_mul, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact hb x Q hx hQ r₁ r₂ k h21 (mem_Icc.mp hk).1 hV2 hVQ hVr hlogV


/-! ### Summing over pairs `(r₁, r₂)` -/

theorem sum_inv_le_of_subset (R : Finset ℕ) (M : ℝ) (hM : 1 ≤ M)
    (hR : ∀ r ∈ R, 1 ≤ r ∧ (r : ℝ) ≤ M) :
    ∑ r ∈ R, (r : ℝ)⁻¹ ≤ 1 + Real.log M := by
  have hsub : R ⊆ Icc 1 ⌊M⌋₊ := fun r hr =>
    mem_Icc.mpr ⟨(hR r hr).1, Nat.le_floor (hR r hr).2⟩
  calc ∑ r ∈ R, (r : ℝ)⁻¹ ≤ ∑ r ∈ Icc 1 ⌊M⌋₊, (r : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 + Real.log ⌊M⌋₊ := sum_inv_Icc_le_log _
    _ ≤ 1 + Real.log M := by
        have h1 : (1 : ℝ) ≤ ⌊M⌋₊ := by
          have : 1 ≤ ⌊M⌋₊ := Nat.le_floor (by simpa using hM)
          exact_mod_cast this
        have := Real.log_le_log (by linarith) (Nat.floor_le (by linarith : (0:ℝ) ≤ M))
        linarith

theorem sum_inv_sub_le (R : Finset ℕ) (r₁ : ℕ) :
    ∑ r₂ ∈ R.filter (· < r₁), ((r₁ - r₂ : ℕ) : ℝ)⁻¹ ≤ 1 + Real.log r₁ := by
  have himg : (R.filter (· < r₁)).image (fun r₂ => r₁ - r₂) ⊆ Icc 1 r₁ := by
    intro j hj
    obtain ⟨r₂, hr₂, rfl⟩ := mem_image.mp hj
    have := (mem_filter.mp hr₂).2
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hinj : Set.InjOn (fun r₂ => r₁ - r₂) ↑(R.filter (· < r₁)) := by
    intro a ha b hb hab
    have := (mem_filter.mp ha).2; have := (mem_filter.mp hb).2
    simp only at hab; omega
  rw [← sum_image (f := fun j : ℕ => (j : ℝ)⁻¹) hinj]
  calc _ ≤ ∑ j ∈ Icc 1 r₁, (j : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ ≤ _ := sum_inv_Icc_le_log _

theorem sum_abs_pairs_le (R : Finset ℕ) (X : ℕ → ℕ → ℝ) (hsym : ∀ a b, X a b = X b a)
    (α β γ M : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hM : 1 ≤ M)
    (hR : ∀ r ∈ R, 1 ≤ r ∧ (r : ℝ) ≤ M)
    (hdiag : ∀ r ∈ R, |X r r| ≤ γ / r)
    (hoff : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₂ < r₁ →
      |X r₁ r₂| ≤ α / r₁ + β / (r₁ * ((r₁ - r₂ : ℕ) : ℝ))) :
    ∑ r₁ ∈ R, ∑ r₂ ∈ R, |X r₁ r₂| ≤
      γ * (1 + Real.log M) + 2 * (α * M + β * (1 + Real.log M) ^ 2) := by
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  -- split each inner sum into r₂ < r₁, r₂ = r₁, r₁ < r₂
  have hsplit : ∀ r₁ ∈ R, ∑ r₂ ∈ R, |X r₁ r₂| =
      ∑ r₂ ∈ R.filter (· < r₁), |X r₁ r₂| + |X r₁ r₁| + ∑ r₂ ∈ R.filter (r₁ < ·), |X r₁ r₂| := by
    intro r₁ hr₁
    rw [← sum_filter_add_sum_filter_not R (· < r₁)]
    have : R.filter (fun r₂ => ¬ r₂ < r₁) = insert r₁ (R.filter (r₁ < ·)) := by
      ext r; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩; rcases Nat.eq_or_lt_of_le (not_lt.mp h2) with h | h
        · left; exact h.symm
        · right; exact ⟨h1, h⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨hr₁, lt_irrefl _⟩
        · exact ⟨h1, by omega⟩
    rw [this, sum_insert (by simp)]
    ring
  have hupper : ∑ r₁ ∈ R, ∑ r₂ ∈ R.filter (r₁ < ·), |X r₁ r₂| =
      ∑ r₁ ∈ R, ∑ r₂ ∈ R.filter (· < r₁), |X r₁ r₂| := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    rw [hsym]
  have hlow : ∑ r₁ ∈ R, ∑ r₂ ∈ R.filter (· < r₁), |X r₁ r₂| ≤ α * M + β * (1 + Real.log M) ^ 2 := by
    have h1 : ∀ r₁ ∈ R, ∑ r₂ ∈ R.filter (· < r₁), |X r₁ r₂| ≤
        α * ((R.filter (· < r₁)).card / r₁) + β / r₁ * (1 + Real.log M) := by
      intro r₁ hr₁
      have hr1 : (1 : ℝ) ≤ r₁ := by exact_mod_cast (hR r₁ hr₁).1
      calc ∑ r₂ ∈ R.filter (· < r₁), |X r₁ r₂|
          ≤ ∑ r₂ ∈ R.filter (· < r₁), (α / r₁ + β / r₁ * ((r₁ - r₂ : ℕ) : ℝ)⁻¹) := by
            apply sum_le_sum; intro r₂ hr₂
            have := hoff r₁ hr₁ r₂ (mem_filter.mp hr₂).1 (mem_filter.mp hr₂).2
            calc |X r₁ r₂| ≤ _ := this
              _ = _ := by rw [div_mul_eq_div_div]; ring
        _ = α * ((R.filter (· < r₁)).card / r₁) +
            β / r₁ * ∑ r₂ ∈ R.filter (· < r₁), ((r₁ - r₂ : ℕ) : ℝ)⁻¹ := by
            rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := by
            apply add_le_add le_rfl
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine (sum_inv_sub_le R r₁).trans ?_
            have := Real.log_le_log (by linarith) (hR r₁ hr₁).2
            linarith
    have h2 : ∀ r₁ ∈ R, ((R.filter (· < r₁)).card : ℝ) / r₁ ≤ 1 := by
      intro r₁ hr₁
      have hr1 : (0 : ℝ) < r₁ := by exact_mod_cast (hR r₁ hr₁).1
      rw [div_le_one hr1]
      have : (R.filter (· < r₁)).card ≤ r₁ := by
        calc (R.filter (· < r₁)).card ≤ (range r₁).card :=
              card_le_card (fun r hr => mem_range.mpr (mem_filter.mp hr).2)
          _ = r₁ := card_range r₁
      exact_mod_cast this
    have hcardR : (R.card : ℝ) ≤ M := by
      have hsub : R ⊆ Icc 1 ⌊M⌋₊ := fun r hr =>
        mem_Icc.mpr ⟨(hR r hr).1, Nat.le_floor (hR r hr).2⟩
      have := card_le_card hsub
      simp at this
      calc (R.card : ℝ) ≤ ⌊M⌋₊ := by exact_mod_cast this
        _ ≤ M := Nat.floor_le (by linarith)
    calc _ ≤ ∑ r₁ ∈ R, (α * ((R.filter (· < r₁)).card / r₁) + β / r₁ * (1 + Real.log M)) :=
          sum_le_sum h1
      _ ≤ ∑ r₁ ∈ R, (α * 1 + β * (1 + Real.log M) * (r₁ : ℝ)⁻¹) := by
          apply sum_le_sum; intro r₁ hr₁
          have := mul_le_mul_of_nonneg_left (h2 r₁ hr₁) hα
          have e : β / r₁ * (1 + Real.log M) = β * (1 + Real.log M) * (r₁ : ℝ)⁻¹ := by ring
          linarith
      _ = α * R.card + β * (1 + Real.log M) * ∑ r₁ ∈ R, (r₁ : ℝ)⁻¹ := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]; ring
      _ ≤ α * M + β * (1 + Real.log M) * (1 + Real.log M) := by
          apply add_le_add (mul_le_mul_of_nonneg_left hcardR hα)
          exact mul_le_mul_of_nonneg_left (sum_inv_le_of_subset R M hM hR) (by positivity)
      _ = _ := by ring
  have hd : ∑ r₁ ∈ R, |X r₁ r₁| ≤ γ * (1 + Real.log M) := by
    calc ∑ r₁ ∈ R, |X r₁ r₁| ≤ ∑ r₁ ∈ R, γ * (r₁ : ℝ)⁻¹ :=
          sum_le_sum fun r hr => (hdiag r hr).trans (by rw [div_eq_mul_inv])
      _ = γ * ∑ r₁ ∈ R, (r₁ : ℝ)⁻¹ := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_le_of_subset R M hM hR) hγ
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, hupper]
  linarith


/-! ### Large `x` -/

theorem eventually_big (B : ℝ) (hB : 0 < B) (C : ℝ) : ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
    3 ≤ x ∧ 1 ≤ Real.log x ∧ 2 ≤ Real.log x ^ B ∧ C * (Real.log x ^ B) ^ 4 ≤ x := by
  set ε : ℝ := 1 / (8 * B) with hε
  have hε0 : 0 < ε := by positivity
  set c : ℝ := |C| / ε ^ (4 * B) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨max (max 3 (Real.exp (2 ^ (1 / B)) + Real.exp 1)) (c ^ 2 + 1), ?_⟩
  intro x hx
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hx
  have hxe : Real.exp (2 ^ (1 / B)) + Real.exp 1 ≤ x :=
    le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hx
  have hxc : c ^ 2 + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : 0 < Real.exp (2 ^ (1 / B)) := Real.exp_pos _
  have hL1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log he1 (by linarith)
  have hL0 : 0 ≤ Real.log x := by linarith
  refine ⟨hx3, hL1, ?_, ?_⟩
  · have h1 : 2 ^ (1 / B) ≤ Real.log x := by
      rw [← Real.log_exp (2 ^ (1 / B))]; exact Real.log_le_log he2 (by linarith)
    calc (2 : ℝ) = (2 ^ (1 / B)) ^ B := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ Real.log x ^ B := Real.rpow_le_rpow (by positivity) h1 hB.le
  · have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0.le hε0
    have h4 : (Real.log x ^ B) ^ 4 = Real.log x ^ (4 * B) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]; ring_nf
    have h5 : Real.log x ^ (4 * B) ≤ (x ^ ε / ε) ^ (4 * B) :=
      Real.rpow_le_rpow hL0 hlog (by positivity)
    have h6 : (x ^ ε / ε) ^ (4 * B) = √x / ε ^ (4 * B) := by
      rw [Real.div_rpow (by positivity) hε0.le, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]
      congr 2; rw [hε]; field_simp; ring
    have hsq : c ≤ √x := by
      rw [Real.le_sqrt hc0 hx0.le]; linarith
    have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
    have hsx : √x * √x = x := Real.mul_self_sqrt hx0.le
    calc C * (Real.log x ^ B) ^ 4 ≤ |C| * (Real.log x ^ B) ^ 4 := by
          apply mul_le_mul_of_nonneg_right (le_abs_self C); positivity
      _ ≤ |C| * (√x / ε ^ (4 * B)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          rw [h4, ← h6]; exact h5
      _ = c * √x := by rw [hc]; ring
      _ ≤ √x * √x := mul_le_mul_of_nonneg_right hsq hs0
      _ = x := hsx


theorem Xr_self_nonneg (x Q : ℝ) (r : ℕ) : 0 ≤ Xr x Q r r := by
  unfold Xr
  apply sum_nonneg; intro m _
  apply sum_nonneg; intro n _
  have : (n : ℝ) * gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r *
      gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r =
      (n : ℝ) * (gT ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n r) ^ 2 := by ring
  rw [this]; positivity

/-- The pair sum for one large `x`, with explicit `α, β, γ`. -/
theorem S2_pairs (B A K7 Kd cΔ : ℝ) (hK7 : 0 ≤ K7) (hKd : 0 < Kd) (hcΔ : 0 ≤ cΔ)
    (hoffb : ∀ x Q : ℝ, 2 ≤ x → 1 ≤ Q →
      (2 : ℝ) ≤ ⌊x / Q ^ 2⌋₊ → Q ≤ ⌊x / Q ^ 2⌋₊ →
      Real.log x / 2 ≤ Real.log ⌊x / Q ^ 2⌋₊ → ∀ r₁ r₂ : ℕ, r₂ < r₁ → ⌊Q⌋₊ < r₂ →
      (r₁ : ℝ) ≤ ⌊x / Q ^ 2⌋₊ →
      |Xr x Q r₁ r₂| ≤ |dr ⌊Q⌋₊ r₁| * |dr ⌊Q⌋₊ r₂| *
        ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * (2 * (3 * x / r₁) * (2 * Ebd K7 A Q x (r₁ - r₂) k)))
    (hdiv : ∀ x : ℝ, 2 ≤ x → ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ 3 * (Real.log x ^ B) ^ 2 → (r.divisors.card : ℝ) ≤ Kd * Real.log x)
    (x : ℝ) (hx3 : 3 ≤ x) (hL1 : 1 ≤ Real.log x) (hQ2 : 2 ≤ Real.log x ^ B)
    (hV2 : (2 : ℝ) ≤ ⌊x / (Real.log x ^ B) ^ 2⌋₊)
    (hVM : 3 * (Real.log x ^ B) ^ 2 ≤ ⌊x / (Real.log x ^ B) ^ 2⌋₊)
    (hlogV : Real.log x / 2 ≤ Real.log ⌊x / (Real.log x ^ B) ^ 2⌋₊)
    (hΔ : ∀ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ (Real.log x ^ B) k| ≤ cΔ * Real.log x * (k.divisors.card : ℝ)) :
    ∑ r₁ ∈ Icc 1 ⌊3 * x⌋₊, ∑ r₂ ∈ Icc 1 ⌊3 * x⌋₊, |Xr x (Real.log x ^ B) r₁ r₂| ≤
      (48 * Kd ^ 2 * cΔ ^ 2 * x ^ 3 * Real.log x ^ 7 / Real.log x ^ B) *
          (1 + Real.log (3 * (Real.log x ^ B) ^ 2)) +
        2 * ((48 * Kd ^ 4 * cΔ * K7 * x ^ 2 * Real.log x ^ 7 *
            (Real.log x ^ B * Real.log x ^ 2 + 2 ^ A * (x * Real.log x ^ (-A)))) *
              (3 * (Real.log x ^ B) ^ 2) +
          (48 * Kd ^ 5 * cΔ * K7 * x ^ 3 * Real.log x ^ 9 / Real.log x ^ B) *
            (1 + Real.log (3 * (Real.log x ^ B) ^ 2)) ^ 2) := by
  set L := Real.log x with hLdef
  set Q := L ^ B with hQdef
  set N := ⌊3 * x⌋₊
  set M : ℝ := 3 * Q ^ 2 with hM
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hM1 : 1 ≤ M := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  set R := (Icc 1 N).filter (fun r => ⌊Q⌋₊ < r ∧ (r : ℝ) < M) with hR
  have hRsub : R ⊆ Icc 1 N := filter_subset _ _
  have hVx : ((⌊x / Q ^ 2⌋₊ : ℕ) : ℝ) ≤ x := by
    refine (Nat.floor_le (by positivity)).trans ?_
    have hQs : 1 ≤ Q ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]; nlinarith
  -- reduce to R × R
  have hzero : ∀ r₁ r₂ : ℕ, ¬ (r₁ ∈ R ∧ r₂ ∈ R) → r₁ ∈ Icc 1 N → r₂ ∈ Icc 1 N →
      |Xr x Q r₁ r₂| = 0 := by
    intro r₁ r₂ h h1 h2
    rw [abs_eq_zero]
    apply Xr_eq_zero x Q hx0 hQ0
    intro hc
    exact h ⟨mem_filter.mpr ⟨h1, hc.1.1, hc.1.2⟩, mem_filter.mpr ⟨h2, hc.2.1, hc.2.2⟩⟩
  have hred : ∑ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, |Xr x Q r₁ r₂| =
      ∑ r₁ ∈ R, ∑ r₂ ∈ R, |Xr x Q r₁ r₂| := by
    have inner : ∀ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, |Xr x Q r₁ r₂| = ∑ r₂ ∈ R, |Xr x Q r₁ r₂| := by
      intro r₁ h1
      symm
      apply sum_subset hRsub
      intro r₂ h2 hn
      exact hzero r₁ r₂ (fun h => hn h.2) h1 h2
    rw [sum_congr rfl inner]
    symm
    apply sum_subset hRsub
    intro r₁ h1 hn
    apply sum_eq_zero; intro r₂ h2
    exact hzero r₁ r₂ (fun h => hn h.1) h1 (hRsub h2)
  rw [hred]
  have hRprop : ∀ r ∈ R, 1 ≤ r ∧ (r : ℝ) ≤ M := by
    intro r hr
    obtain ⟨h1, -, h3⟩ := mem_filter.mp hr
    exact ⟨(mem_Icc.mp h1).1, h3.le⟩
  have hRQ : ∀ r ∈ R, Q < r := by
    intro r hr
    have := (mem_filter.mp hr).2.1
    have : ((⌊Q⌋₊ + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    push_cast at this
    linarith [Nat.lt_floor_add_one Q]
  have hdR : ∀ r ∈ R, |dr ⌊Q⌋₊ r| ≤ Kd * L := fun r hr =>
    (abs_dr_le _ r).trans (hdiv x (by linarith) r (hRprop r hr).1 (hRprop r hr).2)
  -- the diagonal
  have hD : ∑ k ∈ Icc 1 ⌊x⌋₊, DeltaQ Q k ^ 2 ≤ cΔ ^ 2 * (8 * x * L ^ 5) := by
    have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    have h1 : ∑ k ∈ Icc 1 ⌊x⌋₊, DeltaQ Q k ^ 2 ≤
        ∑ k ∈ Icc 1 ⌊x⌋₊, cΔ ^ 2 * L ^ 2 * (k.divisors.card : ℝ) ^ 2 := by
      apply sum_le_sum; intro k hk
      have := hΔ k hk
      have h0 : 0 ≤ |DeltaQ Q k| := abs_nonneg _
      calc DeltaQ Q k ^ 2 = |DeltaQ Q k| ^ 2 := (sq_abs _).symm
        _ ≤ (cΔ * L * (k.divisors.card : ℝ)) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = _ := by ring
    have h2 : ∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) ^ 2 ≤
        ⌊x⌋₊ * (1 + Real.log ⌊x⌋₊) ^ 3 :=
      (sum_sq_divisors_le ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Hn_nonneg _) (Hn_le _) 3) (by positivity))
    have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hlN : Real.log ⌊x⌋₊ ≤ L := Real.log_le_log (by exact_mod_cast hN1) hNx
    have hlN0 : 0 ≤ Real.log ⌊x⌋₊ := Real.log_natCast_nonneg _
    have h3 : (⌊x⌋₊ : ℝ) * (1 + Real.log ⌊x⌋₊) ^ 3 ≤ x * (8 * L ^ 3) := by
      apply mul_le_mul hNx _ (by positivity) hx0.le
      calc (1 + Real.log ⌊x⌋₊) ^ 3 ≤ (2 * L) ^ 3 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ = 8 * L ^ 3 := by ring
    rw [← mul_sum] at h1
    calc _ ≤ _ := h1
      _ ≤ cΔ ^ 2 * L ^ 2 * (x * (8 * L ^ 3)) := by
          apply mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      _ = _ := by ring
  have hdiag : ∀ r ∈ R, |Xr x Q r r| ≤
      (48 * Kd ^ 2 * cΔ ^ 2 * x ^ 3 * L ^ 7 / Q) / r := by
    intro r hr
    have hr1 := (hRprop r hr).1
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hrx : (r : ℝ) ≤ x := by linarith [(hRprop r hr).2, hVM, hVx]
    rw [abs_of_nonneg (Xr_self_nonneg x Q r)]
    refine (Xr_diag_le x Q (by linarith) r hr1 hrx).trans ?_
    have hd2 : dr ⌊Q⌋₊ r ^ 2 ≤ (Kd * L) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdR r hr) 2
    have hrQ := hRQ r hr
    have hDn : 0 ≤ ∑ k ∈ Icc 1 ⌊x⌋₊, DeltaQ Q k ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    calc dr ⌊Q⌋₊ r ^ 2 * (3 * x / r) * (2 * x / r * ∑ k ∈ Icc 1 ⌊x⌋₊, DeltaQ Q k ^ 2)
        ≤ (Kd * L) ^ 2 * (3 * x / r) * (2 * x / r * (cΔ ^ 2 * (8 * x * L ^ 5))) := by
          gcongr
      _ = 48 * Kd ^ 2 * cΔ ^ 2 * x ^ 3 * L ^ 7 / (r * r) := by field_simp; ring
      _ ≤ 48 * Kd ^ 2 * cΔ ^ 2 * x ^ 3 * L ^ 7 / (Q * r) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hrQ.le hrpos.le
      _ = _ := by field_simp
  -- off the diagonal
  have hoff : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₂ < r₁ →
      |Xr x Q r₁ r₂| ≤ (48 * Kd ^ 4 * cΔ * K7 * x ^ 2 * L ^ 7 *
            (Q * L ^ 2 + 2 ^ A * (x * L ^ (-A)))) / r₁ +
          (48 * Kd ^ 5 * cΔ * K7 * x ^ 3 * L ^ 9 / Q) / (r₁ * ((r₁ - r₂ : ℕ) : ℝ)) := by
    intro r₁ hr₁ r₂ hr₂ h21
    have hr1pos : (0 : ℝ) < r₁ := by exact_mod_cast (hRprop r₁ hr₁).1
    have hδ1 : 1 ≤ r₁ - r₂ := by omega
    have hδpos : (0 : ℝ) < ((r₁ - r₂ : ℕ) : ℝ) := by exact_mod_cast hδ1
    have hVr : (r₁ : ℝ) ≤ ⌊x / Q ^ 2⌋₊ := by linarith [(hRprop r₁ hr₁).2]
    have hb := hoffb x Q (by linarith) hQ1 hV2 (by nlinarith) hlogV r₁ r₂ h21
      (mem_filter.mp hr₂).2.1 hVr
    have hdδ : (((r₁ - r₂).divisors.card : ℕ) : ℝ) ≤ Kd * L :=
      hdiv x (by linarith) _ hδ1 (by
        have : ((r₁ - r₂ : ℕ) : ℝ) ≤ r₁ := by exact_mod_cast Nat.sub_le r₁ r₂
        linarith [(hRprop r₁ hr₁).2])
    have hsumE := sum_absDelta_Ebd_le K7 A Q x cΔ (r₁ - r₂) hK7 hQ1 (by linarith) hcΔ hδ1 hΔ
    have e1 : ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * (2 * (3 * x / r₁) * (2 * Ebd K7 A Q x (r₁ - r₂) k)) =
        12 * x / r₁ * ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * Ebd K7 A Q x (r₁ - r₂) k := by
      rw [mul_sum]; apply sum_congr rfl; intro k _; ring
    rw [e1] at hb
    set dδ := (((r₁ - r₂).divisors.card : ℕ) : ℝ)
    have hdδ0 : 0 ≤ dδ := by positivity
    have hLA : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL0 _
    have hW : ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * Ebd K7 A Q x (r₁ - r₂) k ≤
        cΔ * L * K7 * (x * ((Kd * L) ^ 2 * (4 * L ^ 2))) *
          (Q * L ^ 2 + 2 ^ A * (x * L ^ (-A)) +
            x * L / (((r₁ - r₂ : ℕ) : ℝ) * Q) * (Kd * L)) := by
      refine hsumE.trans ?_
      have h1L : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hx0.le
        apply mul_le_mul (pow_le_pow_left₀ hdδ0 hdδ 2) h1L (by positivity) (by positivity)
      · apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left hdδ (by positivity)
    have hd12 : |dr ⌊Q⌋₊ r₁| * |dr ⌊Q⌋₊ r₂| ≤ (Kd * L) * (Kd * L) :=
      mul_le_mul (hdR r₁ hr₁) (hdR r₂ hr₂) (abs_nonneg _) (by positivity)
    have hW0 : 0 ≤ ∑ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| * Ebd K7 A Q x (r₁ - r₂) k :=
      sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (Ebd_nonneg hK7 hQ0.le (by linarith) _ _)
    calc |Xr x Q r₁ r₂| ≤ _ := hb
      _ ≤ (Kd * L) * (Kd * L) * (12 * x / r₁ * (cΔ * L * K7 * (x * ((Kd * L) ^ 2 * (4 * L ^ 2))) *
          (Q * L ^ 2 + 2 ^ A * (x * L ^ (-A)) +
            x * L / (((r₁ - r₂ : ℕ) : ℝ) * Q) * (Kd * L)))) := by
          apply mul_le_mul hd12 _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by field_simp; ring
  have := sum_abs_pairs_le R (Xr x Q) (Xr_symm x Q) _ _ _ M
    (by positivity) (by positivity) (by positivity) hM1 hRprop hdiag hoff
  refine this.trans (le_of_eq ?_)
  rw [hM]


/-! ### The final arithmetic -/

theorem final_arith (a b c cM P L Q x ℓ X2 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hP : 0 ≤ P) (hL1 : 1 ≤ L) (hQ2 : 2 ≤ Q) (hx : 16 * Q ^ 4 ≤ x) (hx0 : 0 < x)
    (hℓ1 : 1 ≤ ℓ) (hℓ2 : ℓ ^ 2 ≤ cM * L) (hX2 : 0 ≤ X2) (hQX : Q ^ 2 * X2 = 1 / Q) :
    a * x ^ 3 * L ^ 7 / Q * ℓ +
        2 * (b * x ^ 2 * L ^ 7 * (Q * L ^ 2 + P * (x * X2)) * (3 * Q ^ 2) +
          c * x ^ 3 * L ^ 9 / Q * ℓ ^ 2) ≤
      (a * cM + 6 * b * (1 + P) + 2 * c * cM) * x ^ 3 * L ^ 10 / Q := by
  have hQ0 : 0 < Q := by linarith
  have hL0 : 0 < L := by linarith
  have hℓ : ℓ ≤ cM * L := by nlinarith
  have hL8 : L ^ 8 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL9 : L ^ 9 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hx3 : 0 ≤ x ^ 3 := by positivity
  -- term 1
  have t1 : a * x ^ 3 * L ^ 7 / Q * ℓ ≤ a * cM * x ^ 3 * L ^ 10 / Q := by
    calc a * x ^ 3 * L ^ 7 / Q * ℓ ≤ a * x ^ 3 * L ^ 7 / Q * (cM * L) :=
          mul_le_mul_of_nonneg_left hℓ (by positivity)
      _ = a * cM * x ^ 3 * L ^ 8 / Q := by ring
      _ ≤ a * cM * x ^ 3 * L ^ 10 / Q := by
          apply div_le_div_of_nonneg_right _ hQ0.le
          have hcM : 0 ≤ cM := by nlinarith
          exact mul_le_mul_of_nonneg_left hL8 (by positivity)
  -- term 3
  have t3 : 2 * (c * x ^ 3 * L ^ 9 / Q * ℓ ^ 2) ≤ 2 * c * cM * x ^ 3 * L ^ 10 / Q := by
    calc 2 * (c * x ^ 3 * L ^ 9 / Q * ℓ ^ 2) ≤ 2 * (c * x ^ 3 * L ^ 9 / Q * (cM * L)) := by
          gcongr
      _ = _ := by ring
  -- term 2
  have hQ3 : Q ^ 3 * L ^ 2 ≤ x * L ^ 2 / Q := by
    rw [le_div_iff₀ hQ0]
    have : Q ^ 3 * L ^ 2 * Q = Q ^ 4 * L ^ 2 := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith [pow_pos hQ0 4]
  have e2 : b * x ^ 2 * L ^ 7 * (Q * L ^ 2 + P * (x * X2)) * (3 * Q ^ 2) =
      3 * b * x ^ 2 * L ^ 7 * (Q ^ 3 * L ^ 2 + P * x * (Q ^ 2 * X2)) := by ring
  have t2 : 2 * (b * x ^ 2 * L ^ 7 * (Q * L ^ 2 + P * (x * X2)) * (3 * Q ^ 2)) ≤
      6 * b * (1 + P) * x ^ 3 * L ^ 10 / Q := by
    rw [e2, hQX]
    have h1 : Q ^ 3 * L ^ 2 + P * x * (1 / Q) ≤ x * L ^ 2 * (1 + P) / Q := by
      have : P * x * (1 / Q) ≤ P * x * L ^ 2 / Q := by
        rw [mul_one_div]
        apply div_le_div_of_nonneg_right _ hQ0.le
        nlinarith [mul_nonneg hP hx0.le]
      have e : x * L ^ 2 * (1 + P) / Q = x * L ^ 2 / Q + P * x * L ^ 2 / Q := by ring
      rw [e]; linarith
    calc 2 * (3 * b * x ^ 2 * L ^ 7 * (Q ^ 3 * L ^ 2 + P * x * (1 / Q)))
        ≤ 2 * (3 * b * x ^ 2 * L ^ 7 * (x * L ^ 2 * (1 + P) / Q)) := by gcongr
      _ = 6 * b * (1 + P) * x ^ 3 * L ^ 9 / Q := by ring
      _ ≤ 6 * b * (1 + P) * x ^ 3 * L ^ 10 / Q := by
          apply div_le_div_of_nonneg_right _ hQ0.le
          exact mul_le_mul_of_nonneg_left hL9 (by positivity)
  have e : (a * cM + 6 * b * (1 + P) + 2 * c * cM) * x ^ 3 * L ^ 10 / Q =
      a * cM * x ^ 3 * L ^ 10 / Q + 6 * b * (1 + P) * x ^ 3 * L ^ 10 / Q +
        2 * c * cM * x ^ 3 * L ^ 10 / Q := by ring
  rw [e]
  have : 2 * (b * x ^ 2 * L ^ 7 * (Q * L ^ 2 + P * (x * X2)) * (3 * Q ^ 2) +
      c * x ^ 3 * L ^ 9 / Q * ℓ ^ 2) =
      2 * (b * x ^ 2 * L ^ 7 * (Q * L ^ 2 + P * (x * X2)) * (3 * Q ^ 2)) +
        2 * (c * x ^ 3 * L ^ 9 / Q * ℓ ^ 2) := by ring
  rw [this]
  linarith


/-! ### Pages 55 to 56 for large `x`, from Siegel-Walfisz, zero sorry -/

set_option maxHeartbeats 1000000 in
/-- **`Σ₃² ≪ x⁴ L¹³ Q⁻¹` for large `x`**, `Q = L^B`, from Siegel-Walfisz 1.1 alone. The
zero-sorry replacement of `sigma3_eventually_of_siegelWalfisz` in Sigma3.lean. -/
theorem sigma3_eventually_weighted (hSW : SiegelWalfisz) :
    ∀ B : ℝ, 0 < B → ∃ K X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      Sigma3 x (Real.log x ^ B) ^ 2 ≤ K * x ^ 4 * Real.log x ^ 13 / Real.log x ^ B := by
  intro B hB
  set A : ℝ := 3 * B with hAdef
  have h7 := lemma1_7_of (bound2_4_of hSW)
  obtain ⟨K7, hK7, hoffb⟩ := Xr_off_le h7 A (by positivity)
  obtain ⟨Kd, hKd, hdiv⟩ := card_divisors_le_log B hB
  obtain ⟨K5, hK5⟩ := bound2_5
  set cΔ : ℝ := 4 * B ^ 2 * |K5| + 1 with hcΔdef
  have hcΔ : 0 ≤ cΔ := by positivity
  set cM : ℝ := 18 + 32 * B ^ 2 with hcMdef
  set Ctot : ℝ := (48 * Kd ^ 2 * cΔ ^ 2) * cM + 6 * (48 * Kd ^ 4 * cΔ * K7) * (1 + 2 ^ A) +
    2 * (48 * Kd ^ 5 * cΔ * K7) * cM with hCtot
  obtain ⟨X0, hX0⟩ := eventually_big B hB 16
  refine ⟨36 * Ctot, X0, fun x hx => ?_⟩
  obtain ⟨hx3, hL1, hQ2, hQ4⟩ := hX0 x hx
  set L := Real.log x with hLdef
  set Q := L ^ B with hQdef
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 < Q := by linarith
  have hL0 : 0 < L := by linarith
  have hQs : 4 ≤ Q ^ 2 := by nlinarith
  -- the floor V = ⌊x/Q²⌋
  have hxQ : 16 * Q ^ 2 ≤ x / Q ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hVlow : x / Q ^ 2 - 1 ≤ (⌊x / Q ^ 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (x / Q ^ 2); linarith
  have hV2 : (2 : ℝ) ≤ ⌊x / Q ^ 2⌋₊ := by linarith
  have hVM : 3 * Q ^ 2 ≤ ⌊x / Q ^ 2⌋₊ := by linarith
  have hlogV : L / 2 ≤ Real.log ⌊x / Q ^ 2⌋₊ := by
    have h1 : x / (2 * Q ^ 2) ≤ (⌊x / Q ^ 2⌋₊ : ℝ) := by
      have : x / (2 * Q ^ 2) = (x / Q ^ 2) / 2 := by field_simp
      rw [this]; linarith
    have h2 : 2 * Q ^ 2 ≤ √x := by
      rw [Real.le_sqrt (by positivity) hx0.le]; nlinarith
    have hs : 0 < √x := Real.sqrt_pos.mpr hx0
    have h3 : √x ≤ x / (2 * Q ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : √x * √x = x := Real.mul_self_sqrt hx0.le
      nlinarith
    have := Real.log_le_log hs (h3.trans h1)
    rw [Real.log_sqrt hx0.le] at this
    exact this
  have hΔ : ∀ k ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q k| ≤ cΔ * L * (k.divisors.card : ℝ) := by
    intro k hk
    have hk' := mem_Icc.mp hk
    exact abs_DeltaQ_le B K5 x hB hK5 hL1 hQ2 k hk'.1
      ((Nat.cast_le.mpr hk'.2).trans (Nat.floor_le hx0.le))
  have hS2 := S2_pairs B A K7 Kd cΔ hK7 hKd hcΔ hoffb hdiv x hx3 hL1 hQ2 hV2 hVM hlogV hΔ
  -- ℓ = 1 + log(3Q²)
  set ℓ : ℝ := 1 + Real.log (3 * Q ^ 2) with hℓdef
  have hlogQ : Real.log Q = B * Real.log L := Real.log_rpow hL0 B
  have hlog3Q : Real.log (3 * Q ^ 2) = Real.log 3 + 2 * (B * Real.log L) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogQ]; push_cast; ring
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlL2 : Real.log L ^ 2 ≤ 4 * L := log_sq_le L hL1
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, hlog3Q]; nlinarith [mul_nonneg hB.le hlL]
  have hℓ2 : ℓ ^ 2 ≤ cM * L := by
    rw [hℓdef, hlog3Q, hcMdef]
    have hu : 1 + (Real.log 3 + 2 * (B * Real.log L)) ≤ 3 + 2 * B * Real.log L := by linarith
    have hu0 : 0 ≤ 1 + (Real.log 3 + 2 * (B * Real.log L)) := by
      nlinarith [mul_nonneg hB.le hlL]
    calc (1 + (Real.log 3 + 2 * (B * Real.log L))) ^ 2 ≤ (3 + 2 * B * Real.log L) ^ 2 :=
          pow_le_pow_left₀ hu0 hu 2
      _ ≤ 2 * 3 ^ 2 + 2 * (2 * B * Real.log L) ^ 2 := by
          nlinarith [sq_nonneg (3 - 2 * B * Real.log L)]
      _ = 18 + 8 * B ^ 2 * Real.log L ^ 2 := by ring
      _ ≤ 18 + 8 * B ^ 2 * (4 * L) := by gcongr
      _ ≤ (18 + 32 * B ^ 2) * L := by nlinarith
  have hQX : Q ^ 2 * L ^ (-A) = 1 / Q := by
    rw [hQdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, hAdef,
      one_div, ← Real.rpow_neg hL0.le]
    congr 1; push_cast; ring
  have hfin := final_arith (48 * Kd ^ 2 * cΔ ^ 2) (48 * Kd ^ 4 * cΔ * K7) (48 * Kd ^ 5 * cΔ * K7)
    cM (2 ^ A) L Q x ℓ (L ^ (-A)) (by positivity) (by positivity) (by positivity)
    (by positivity) hL1 hQ2 (by linarith) hx0 hℓ1 hℓ2 (Real.rpow_nonneg hL0.le _) hQX
  -- S₂ = Σ n T²
  have hS2eq := sum_nT_sq_eq x Q
  have hS2le : ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊,
      (n : ℝ) * T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n ^ 2 ≤ Ctot * x ^ 3 * L ^ 10 / Q := by
    rw [hS2eq]
    refine (sum_le_sum fun r₁ _ => sum_le_sum fun r₂ _ => le_abs_self (Xr x Q r₁ r₂)).trans ?_
    refine hS2.trans ?_
    exact hfin
  have hS20 : 0 ≤ ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊,
      (n : ℝ) * T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity
  -- the Λ factor
  have hLF := lambda_factor_le x
  have hN1 : 1 ≤ ⌊3 * x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hN : (⌊3 * x⌋₊ : ℝ) ≤ 3 * x := Nat.floor_le (by linarith)
  have hlN : Real.log ⌊3 * x⌋₊ ≤ 2 * L := by
    have h1 : Real.log ⌊3 * x⌋₊ ≤ Real.log (x ^ 2) :=
      Real.log_le_log (by exact_mod_cast hN1) (hN.trans (by nlinarith))
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have hlN0 : 0 ≤ Real.log ⌊3 * x⌋₊ := Real.log_natCast_nonneg _
  have hLF' : ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊, Λ n ^ 2 / n ≤ 36 * x * L ^ 3 := by
    refine hLF.trans ?_
    calc (⌊3 * x⌋₊ : ℝ) * (Real.log ⌊3 * x⌋₊ ^ 2 * (1 + Real.log ⌊3 * x⌋₊))
        ≤ (3 * x) * ((2 * L) ^ 2 * (1 + 2 * L)) := by
          apply mul_le_mul hN _ (by positivity) (by positivity)
          apply mul_le_mul (pow_le_pow_left₀ hlN0 hlN 2) (by linarith) (by positivity)
            (by positivity)
      _ ≤ (3 * x) * ((2 * L) ^ 2 * (3 * L)) := by gcongr; linarith
      _ = 36 * x * L ^ 3 := by ring
  have hLF0 : 0 ≤ ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊, Λ n ^ 2 / n :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity
  have hmain := sigma3_sq_le_weighted x Q
  calc Sigma3 x Q ^ 2 ≤ _ := hmain
    _ ≤ (36 * x * L ^ 3) * (Ctot * x ^ 3 * L ^ 10 / Q) :=
        mul_le_mul hLF' hS2le hS20 (by positivity)
    _ = 36 * Ctot * x ^ 4 * L ^ 13 / Q := by ring

/-- `BoundSigma3` from Siegel-Walfisz, zero sorry. -/
theorem boundSigma3_of_siegelWalfisz' (hSW : SiegelWalfisz) : BoundSigma3 :=
  boundSigma3_of_eventually (sigma3_eventually_weighted hSW)

/-- **Heath-Brown 1985, Theorem 1, from the Siegel-Walfisz theorem 1.1 alone**, zero sorry
in the whole chain: `Σ_{2x < m ≤ 3x} |N₂(m) − x 𝔖(m)| ≪_C x² L^{−C}`. -/
theorem theorem1_of_siegelWalfisz (hSW : SiegelWalfisz) : Theorem1 :=
  theorem1_of_sigma3 (boundSigma3_of_siegelWalfisz' hSW) hSW

end LeanLab.HeathBrown1985
