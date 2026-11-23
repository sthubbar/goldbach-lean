module

public import LeanLab.Grimmelt2019.Discharged

/-!
P0074 L. Grimmelt, "Goldbach Numbers in Short Intervals: A Nonnegative Model Approach",
arXiv 1910.05187 v2. Unit U-6760, run 20261020T2317Z-cloud53.

Proposition 2.1, the circle method with minorants in short intervals, in a finite form, and the
reduction of Theorem 1.1 to the inputs of Section 5.

* Sequences are real functions on `ℤ` supported in a finite set `S`; `conv S f g n` is
  `∑_{m ∈ S} f m g (n - m)`, `fhat S g α = ∑_{n ∈ S} g n e(α n)`, `sqn S f = ∑_{n ∈ S} f n ^ 2`,
  and `win X H` is the set of integers in `[X - H, X]`.
* The one analytic step of the proof of Proposition 2.1, the second moment bound taken "almost
  verbatim" from the proof of Proposition 3.1 of Matomäki, Radziwiłł and Tao 2019 with a
  Schwartz majorant and Poisson summation, is the named cited hypothesis
  `ShortSecondMoment C0`. Everything else in Proposition 2.1 is PROVED here, `prop21_finite`.
  The form proved is slightly stronger than the paper's: the count has `Δ` where the paper has
  `√θ ‖ν‖² ...`; `prop21_paper_form` derives the paper's displayed bound.
* Theorem 1.1 is reduced to the Section 5 inputs, `Section5Inputs`, whose fields are labelled
  by their source: Lemma 5.1, the construction of the models before Lemma 4.2, Lemma 4.2,
  Corollary 4.3, and the main term lower bound at the end of the proof of Theorem 1.1. Following
  the U-6753 QUESTION, the sequence `a` is `Λ'` cut to the window `(X - 3Y, X - Y]`, the support
  of `ω`; then `‖a‖² ≤ (2Y + 1) (log X)²` is PROVED, `sqn_LamCut_le`, and `b = Λ'` needs no norm.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves Theorem 1.1; its analytic inputs stay cited.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019.Prop21
open Real

attribute [local instance] Classical.propDecidable

/-! ### Finite sequences on `ℤ` -/

/-- `f` vanishes outside `S`. -/
def SuppIn (S : Finset ℤ) (f : ℤ → ℝ) : Prop := ∀ n, n ∉ S → f n = 0

/-- The additive convolution `f * g (n) = ∑_{m} f m g (n - m)`, for `f` supported in `S`. -/
noncomputable def conv (S : Finset ℤ) (f g : ℤ → ℝ) (n : ℤ) : ℝ := ∑ m ∈ S, f m * g (n - m)

/-- The Fourier series `ĝ(α) = ∑_{n ∈ S} g n e(α n)`, `e(x) = exp(2πix)`. -/
noncomputable def fhat (S : Finset ℤ) (g : ℤ → ℝ) (α : ℝ) : ℂ :=
  ∑ n ∈ S, (g n : ℂ) * Complex.exp (2 * π * Complex.I * (α : ℂ) * (n : ℂ))

/-- The squared `ℓ²` norm on `S`. -/
noncomputable def sqn (S : Finset ℤ) (f : ℤ → ℝ) : ℝ := ∑ n ∈ S, f n ^ 2

/-- The integers `n` with `X - H ≤ n ≤ X`. -/
noncomputable def win (X H : ℝ) : Finset ℤ := Finset.Icc ⌈X - H⌉ ⌊X⌋

/-- Fourier closeness at scale `1/H` with bound `Δ`:
`sup_α ∫_{-1/H}^{1/H} |ĝ(α + β)|² dβ ≤ Δ`, the shape of conditions (17) and (18). -/
def FourierClose (S : Finset ℤ) (H Δ : ℝ) (g : ℤ → ℝ) : Prop :=
  ∀ α : ℝ, ∫ β in (-(1 / H))..(1 / H), ‖fhat S g (α + β)‖ ^ 2 ≤ Δ

/-- Cited hypothesis, the analytic core of the proof of Proposition 2.1, pages 6 and 7, there
taken from the proof of Proposition 3.1 of Matomäki, Radziwiłł, Tao 2019: a nonnegative
Schwartz `Φ ≥ 1` on `[-1, 1]` with `Φ̂` supported in `[-1/2, 1/2]`, Poisson summation and
Cauchy's inequality give
`∑_{n ∈ [X-H, X]} |f * g (n)|² ≤ C0 H ‖f‖₂² sup_α ∫_{-1/H}^{1/H} |ĝ(α+β)|² dβ`
for `H ≥ 1`, with an absolute constant `C0`. -/
def ShortSecondMoment (C0 : ℝ) : Prop :=
  ∀ (S : Finset ℤ) (f g : ℤ → ℝ) (X H Δ : ℝ), 1 ≤ H → SuppIn S f → SuppIn S g →
    FourierClose S H Δ g → ∑ n ∈ win X H, conv S f g n ^ 2 ≤ C0 * H * sqn S f * Δ

/-! ### Helpers -/

theorem sqn_nonneg (S : Finset ℤ) (f : ℤ → ℝ) : 0 ≤ sqn S f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem suppIn_sub {S : Finset ℤ} {f g : ℤ → ℝ} (hf : SuppIn S f) (hg : SuppIn S g) :
    SuppIn S (fun n => f n - g n) := by
  intro n hn; simp [hf n hn, hg n hn]

theorem conv_sub (S : Finset ℤ) (f g h : ℤ → ℝ) (n : ℤ) :
    conv S f (fun k => g k - h k) n = conv S f g n - conv S f h n := by
  unfold conv; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem conv_mono_right (S : Finset ℤ) {f g h : ℤ → ℝ} (hf : ∀ m, 0 ≤ f m)
    (hgh : ∀ k, g k ≤ h k) (n : ℤ) : conv S f g n ≤ conv S f h n :=
  Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hgh _) (hf m)

theorem conv_mono_left (S : Finset ℤ) {f f' g : ℤ → ℝ} (hff : ∀ m, f m ≤ f' m)
    (hg : ∀ k, 0 ≤ g k) (n : ℤ) : conv S f g n ≤ conv S f' g n :=
  Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right (hff m) (hg _)

theorem fhat_neg_swap (S : Finset ℤ) (f g : ℤ → ℝ) (α : ℝ) :
    fhat S (fun n => f n - g n) α = -fhat S (fun n => g n - f n) α := by
  unfold fhat; rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by push_cast; ring

theorem fourierClose_swap {S : Finset ℤ} {H Δ : ℝ} {f g : ℤ → ℝ}
    (h : FourierClose S H Δ (fun n => f n - g n)) : FourierClose S H Δ (fun n => g n - f n) := by
  intro α
  have := h α
  simpa only [fhat_neg_swap S f g, norm_neg] using this

/-- Chebyshev's inequality for the count of `n` with `F n < -κ`. -/
theorem card_filter_lt_neg_le (W : Finset ℤ) (F : ℤ → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ((W.filter (fun n => F n < -κ)).card : ℝ) ≤ (∑ n ∈ W, F n ^ 2) / κ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  calc ((W.filter (fun n => F n < -κ)).card : ℝ) * κ ^ 2
        = ∑ _n ∈ W.filter (fun n => F n < -κ), κ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ W.filter (fun n => F n < -κ), F n ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have := (Finset.mem_filter.mp hn).2
          nlinarith
    _ ≤ ∑ n ∈ W, F n ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)

/-! ### Proposition 2.1, finite form -/

/-- P0074 Proposition 2.1, finite form, CONDITIONAL ON `ShortSecondMoment C0` only.
Data as in (14): `a, Tp ≥ 0`; minorization (15) `ν ≤ b` and (16) `ω ≤ a`; Fourier closeness
(17) for `ν - Tp` and (18) for `T - Tp`, both with bound `Δ`. Then for any `κ > 0`, all
`n ∈ [X - H, X]` except at most `C0 H (‖a‖² + ‖ω‖²) Δ / κ²` satisfy
`a * b (n) ≥ ω * T (n) - 2κ`, which is the paper's `a * b(n) ≥ ω * Tν(n) + O(κ)`. -/
theorem prop21_finite {C0 : ℝ} (hM : ShortSecondMoment C0) (S : Finset ℤ)
    (a b ω ν T Tp : ℤ → ℝ) (X H Δ κ : ℝ) (hH : 1 ≤ H) (hκ : 0 < κ)
    (ha : SuppIn S a) (hω : SuppIn S ω) (hν : SuppIn S ν) (hT : SuppIn S T)
    (hTp : SuppIn S Tp) (ha0 : ∀ n, 0 ≤ a n) (hTp0 : ∀ n, 0 ≤ Tp n)
    (h15 : ∀ n, ν n ≤ b n) (h16 : ∀ n, ω n ≤ a n)
    (h17 : FourierClose S H Δ (fun n => ν n - Tp n))
    (h18 : FourierClose S H Δ (fun n => T n - Tp n)) :
    (((win X H).filter (fun n => conv S a b n < conv S ω T n - 2 * κ)).card : ℝ)
      ≤ C0 * H * (sqn S a + sqn S ω) * Δ / κ ^ 2 := by
  set F1 : ℤ → ℝ := fun n => conv S a (fun k => ν k - Tp k) n with hF1
  set F2 : ℤ → ℝ := fun n => conv S ω (fun k => Tp k - T k) n with hF2
  have hlow : ∀ n, conv S ω T n + F1 n + F2 n ≤ conv S a b n := by
    intro n
    have e1 : F1 n = conv S a ν n - conv S a Tp n := conv_sub S a ν Tp n
    have e2 : F2 n = conv S ω Tp n - conv S ω T n := conv_sub S ω Tp T n
    have i1 : conv S a ν n ≤ conv S a b n := conv_mono_right S ha0 h15 n
    have i2 : conv S ω Tp n ≤ conv S a Tp n := conv_mono_left S h16 hTp0 n
    linarith
  have hsub : (win X H).filter (fun n => conv S a b n < conv S ω T n - 2 * κ) ⊆
      (win X H).filter (fun n => F1 n < -κ) ∪ (win X H).filter (fun n => F2 n < -κ) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h1 : F1 n < -κ
    · exact Or.inl ⟨hn.1, h1⟩
    · by_cases h2 : F2 n < -κ
      · exact Or.inr ⟨hn.1, h2⟩
      · exfalso
        have := hlow n
        push Not at h1 h2
        linarith [hn.2]
  have m1 : ∑ n ∈ win X H, F1 n ^ 2 ≤ C0 * H * sqn S a * Δ :=
    hM S a _ X H Δ hH ha (suppIn_sub hν hTp) h17
  have m2 : ∑ n ∈ win X H, F2 n ^ 2 ≤ C0 * H * sqn S ω * Δ :=
    hM S ω _ X H Δ hH hω (suppIn_sub hTp hT) (fourierClose_swap h18)
  have hk2 : 0 < κ ^ 2 := by positivity
  calc (((win X H).filter (fun n => conv S a b n < conv S ω T n - 2 * κ)).card : ℝ)
        ≤ (((win X H).filter (fun n => F1 n < -κ) ∪
            (win X H).filter (fun n => F2 n < -κ)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((win X H).filter (fun n => F1 n < -κ)).card +
          ((win X H).filter (fun n => F2 n < -κ)).card := by
          exact_mod_cast Finset.card_union_le _ _
    _ ≤ (∑ n ∈ win X H, F1 n ^ 2) / κ ^ 2 + (∑ n ∈ win X H, F2 n ^ 2) / κ ^ 2 :=
          add_le_add (card_filter_lt_neg_le _ F1 hκ) (card_filter_lt_neg_le _ F2 hκ)
    _ = ((∑ n ∈ win X H, F1 n ^ 2) + ∑ n ∈ win X H, F2 n ^ 2) / κ ^ 2 := by rw [add_div]
    _ ≤ (C0 * H * sqn S a * Δ + C0 * H * sqn S ω * Δ) / κ ^ 2 :=
          div_le_div_of_nonneg_right (add_le_add m1 m2) hk2.le
    _ = C0 * H * (sqn S a + sqn S ω) * Δ / κ ^ 2 := by ring

/-- P0074 Proposition 2.1 with the paper's displayed exception count, CONDITIONAL ON
`ShortSecondMoment C0`: with closeness `≤ K θ ‖ν‖²`, `0 ≤ θ ≤ 1`, the exceptions number at most
`C0 K · H (‖ω‖² + ‖a‖²)(‖ν‖² + ‖Tp‖² + ‖T‖²) √θ / κ²`. -/
theorem prop21_paper_form {C0 K θ : ℝ} (hC0 : 0 ≤ C0) (hK : 0 ≤ K) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hM : ShortSecondMoment C0) (S : Finset ℤ)
    (a b ω ν T Tp : ℤ → ℝ) (X H κ : ℝ) (hH : 1 ≤ H) (hκ : 0 < κ)
    (ha : SuppIn S a) (hω : SuppIn S ω) (hν : SuppIn S ν) (hT : SuppIn S T)
    (hTp : SuppIn S Tp) (ha0 : ∀ n, 0 ≤ a n) (hTp0 : ∀ n, 0 ≤ Tp n)
    (h15 : ∀ n, ν n ≤ b n) (h16 : ∀ n, ω n ≤ a n)
    (h17 : FourierClose S H (K * θ * sqn S ν) (fun n => ν n - Tp n))
    (h18 : FourierClose S H (K * θ * sqn S ν) (fun n => T n - Tp n)) :
    (((win X H).filter (fun n => conv S a b n < conv S ω T n - 2 * κ)).card : ℝ)
      ≤ C0 * K * (H * (sqn S ω + sqn S a) * (sqn S ν + sqn S Tp + sqn S T) * Real.sqrt θ
          / κ ^ 2) := by
  have hs1 : Real.sqrt θ ≤ 1 := by
    have := Real.sqrt_le_sqrt hθ1; rwa [Real.sqrt_one] at this
  have hss : Real.sqrt θ * Real.sqrt θ = θ := Real.mul_self_sqrt hθ0
  have hθs : θ ≤ Real.sqrt θ := by nlinarith [Real.sqrt_nonneg θ]
  have hq : θ * sqn S ν ≤ Real.sqrt θ * (sqn S ν + sqn S Tp + sqn S T) :=
    mul_le_mul hθs (by linarith [sqn_nonneg S Tp, sqn_nonneg S T]) (sqn_nonneg S ν)
      (Real.sqrt_nonneg _)
  have hP : 0 ≤ C0 * K * H * (sqn S a + sqn S ω) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hK) (by linarith))
      (add_nonneg (sqn_nonneg S a) (sqn_nonneg S ω))
  calc _ ≤ C0 * H * (sqn S a + sqn S ω) * (K * θ * sqn S ν) / κ ^ 2 :=
        prop21_finite hM S a b ω ν T Tp X H _ κ hH hκ ha hω hν hT hTp ha0 hTp0 h15 h16 h17 h18
    _ = (C0 * K * H * (sqn S a + sqn S ω)) * (θ * sqn S ν) / κ ^ 2 := by ring
    _ ≤ (C0 * K * H * (sqn S a + sqn S ω)) *
          (Real.sqrt θ * (sqn S ν + sqn S Tp + sqn S T)) / κ ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq hP) (by positivity)
    _ = _ := by ring

/-! ### The weighted primes `Λ'` and the cut sequence `a` -/

/-- `Λ'(n) = log n` for primes `n ≤ X`, else `0`, as on page 2 of the paper. -/
noncomputable def LamP (X : ℝ) (n : ℤ) : ℝ :=
  if 0 < n ∧ n.toNat.Prime ∧ (n : ℝ) ≤ X then Real.log n else 0

/-- `Λ'` cut to the window `(X - 3Y, X - Y]`, the support of `ω` in Lemma 5.1. This is the
choice of `a` that the U-6753 QUESTION recommends in place of the paper's `a = Λ'`. -/
noncomputable def LamCut (X Y : ℝ) (n : ℤ) : ℝ :=
  if X - 3 * Y < (n : ℝ) ∧ (n : ℝ) ≤ X - Y then LamP X n else 0

/-- The common support `[1, X]`. -/
noncomputable def supp (X : ℝ) : Finset ℤ := Finset.Icc 1 ⌊X⌋

theorem LamP_nonneg (X : ℝ) (n : ℤ) : 0 ≤ LamP X n := by
  unfold LamP
  split_ifs with h
  · have h1 : (1 : ℤ) ≤ n := by omega
    exact Real.log_nonneg (by exact_mod_cast h1)
  · exact le_rfl

theorem LamCut_nonneg (X Y : ℝ) (n : ℤ) : 0 ≤ LamCut X Y n := by
  unfold LamCut; split_ifs
  · exact LamP_nonneg X n
  · exact le_rfl

theorem LamP_le_log {X : ℝ} (hX : 1 ≤ X) (n : ℤ) : LamP X n ≤ Real.log X := by
  unfold LamP
  split_ifs with h
  · have h1 : (1 : ℤ) ≤ n := by omega
    have h1' : (0 : ℝ) < n := by exact_mod_cast h.1
    exact Real.log_le_log h1' h.2.2
  · exact Real.log_nonneg hX

theorem LamP_supp (X : ℝ) : SuppIn (supp X) (LamP X) := by
  intro n hn
  unfold LamP
  split_ifs with h
  · exfalso; apply hn
    unfold supp; rw [Finset.mem_Icc]
    exact ⟨by omega, Int.le_floor.mpr h.2.2⟩
  · rfl

theorem LamCut_supp (X Y : ℝ) : SuppIn (supp X) (LamCut X Y) := by
  intro n hn
  unfold LamCut; split_ifs
  · exact LamP_supp X n hn
  · rfl

/-- A positive `Λ'_cut * Λ'` at `n` makes `n` a sum of two primes; so at a non Goldbach `n` the
convolution vanishes. -/
theorem conv_eq_zero_of_not_goldbach (X Y : ℝ) (n : ℕ) (hn : ¬ IsGoldbachSum n) :
    conv (supp X) (LamCut X Y) (LamP X) (n : ℤ) = 0 := by
  unfold conv
  apply Finset.sum_eq_zero
  intro m _
  by_contra hne
  rcases mul_ne_zero_iff.mp hne with ⟨h1, h2⟩
  have h1' : LamP X m ≠ 0 := by
    unfold LamCut at h1
    split_ifs at h1
    · exact h1
    · exact absurd rfl h1
  unfold LamP at h1' h2
  split_ifs at h1' with hm
  swap; · exact h1' rfl
  split_ifs at h2 with hk
  swap; · exact h2 rfl
  apply hn
  refine ⟨m.toNat, ((n : ℤ) - m).toNat, hm.2.1, hk.2.1, ?_⟩
  omega

/-- The U-6753 repair: `‖a‖² ≤ (2Y + 1)(log X)²` for `a = Λ'` cut to `(X - 3Y, X - Y]`. -/
theorem sqn_LamCut_le {X Y : ℝ} (hX : 1 ≤ X) (hY : 0 ≤ Y) :
    sqn (supp X) (LamCut X Y) ≤ (2 * Y + 1) * Real.log X ^ 2 := by
  set W := (supp X).filter (fun n : ℤ => X - 3 * Y < (n : ℝ) ∧ (n : ℝ) ≤ X - Y) with hW
  have h1 : sqn (supp X) (LamCut X Y) ≤ ∑ _n ∈ W, Real.log X ^ 2 := by
    unfold sqn
    rw [hW, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n _
    unfold LamCut
    split_ifs with h
    · have h0 := LamP_nonneg X n
      have h2 := LamP_le_log hX n
      exact pow_le_pow_left₀ h0 h2 2
    · simp
  have hsub : W ⊆ Finset.Icc (⌊X - 3 * Y⌋ + 1) ⌊X - Y⌋ := by
    intro n hn
    rw [hW, Finset.mem_filter] at hn
    rw [Finset.mem_Icc]
    constructor
    · have : ⌊X - 3 * Y⌋ < n := Int.floor_lt.mpr hn.2.1
      omega
    · exact Int.le_floor.mpr hn.2.2
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  have hf1 := Int.floor_le (X - Y)
  have hf2 := Int.lt_floor_add_one (X - 3 * Y)
  have hcard : (W.card : ℝ) ≤ 2 * Y + 1 := by
    set d := ⌊X - Y⌋ + 1 - (⌊X - 3 * Y⌋ + 1) with hd
    have hdr : (d : ℝ) ≤ 2 * Y + 1 := by rw [hd]; push_cast; linarith
    have hc' : (W.card : ℝ) ≤ (d.toNat : ℝ) := by exact_mod_cast hc
    rcases le_or_gt 0 d with h | h
    · have : ((d.toNat : ℤ) : ℝ) ≤ 2 * Y + 1 := by rw [Int.toNat_of_nonneg h]; exact hdr
      have e : ((d.toNat : ℤ) : ℝ) = (d.toNat : ℝ) := by push_cast; rfl
      linarith
    · rw [Int.toNat_of_nonpos h.le] at hc'
      rw [Nat.cast_zero] at hc'
      linarith
  calc sqn (supp X) (LamCut X Y) ≤ ∑ _n ∈ W, Real.log X ^ 2 := h1
    _ = W.card * Real.log X ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Y + 1) * Real.log X ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

/-! ### The inputs of Section 5, cited -/

/-- The objects of Section 5 at one scale `X`, with `Y = X^{21/40+ε}`, `H = Y^{1/9+2ε}`; each
field names its source in P0074. `K`, `B`, `A`, `c` are the implied constants. -/
structure Sec5Objects (X Y H K B A c : ℝ) where
  ν : ℤ → ℝ
  ω : ℤ → ℝ
  T : ℤ → ℝ
  Tp : ℤ → ℝ
  /-- Lemma 5.1: `ν ≤ Λ'`. -/
  nu_le : ∀ n, ν n ≤ LamP X n
  /-- Lemma 5.1: `ω ≤ Λ'`. -/
  omega_le : ∀ n, ω n ≤ LamP X n
  /-- Lemma 5.1: `ω` is supported on `(X - 3Y, X - Y]`. -/
  omega_window : ∀ n : ℤ, ω n ≠ 0 → X - 3 * Y < (n : ℝ) ∧ (n : ℝ) ≤ X - Y
  /-- Lemma 5.1: the sequences live on `[1, X]`. -/
  nu_supp : SuppIn (supp X) ν
  omega_supp : SuppIn (supp X) ω
  /-- Lemma 5.1 coefficient bound `ω(n) ≪ d(n)^{O(1)} log n`, in the form used on page 13:
  `‖ω‖² ≪ Y (log Y)^{O(1)}`. -/
  omega_norm : sqn (supp X) ω ≤ K * Y * Real.log Y ^ B
  /-- Construction of `Tν = cν ΛQ` and `Tν⁺`, before Lemma 4.2: supports and `Tν⁺ ≥ 0`. -/
  T_supp : SuppIn (supp X) T
  Tp_supp : SuppIn (supp X) Tp
  Tp_nonneg : ∀ n, 0 ≤ Tp n
  /-- Lemma 4.2: `Tν` is Fourier close to `Tν⁺`, `≪ Y (log Y)^{-A}`. -/
  lemma42 : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A)) (fun n => T n - Tp n)
  /-- Corollary 4.3: `ν` is Fourier close to `Tν⁺`, `≪ Y (log Y)^{-A}`. -/
  cor43 : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A)) (fun n => ν n - Tp n)
  /-- Proof of Theorem 1.1, pages 13 and 14, from (29) of Lemma 5.1 and the singular series:
  `ω * Tν (n) ≫ Y` for even `n ∈ [X - H, X]` outside `≪ H (log X)^{-A}` exceptions. -/
  mainTerm : (((win X H).filter (fun n => Even n ∧ conv (supp X) ω T n < c * Y)).card : ℝ)
    ≤ K * H / Real.log X ^ A

/-- Cited hypothesis bundle, Section 5 of P0074: for every `ε > 0` there is `B` such that for
every `A > 0` there are constants `K ≥ 0`, `c > 0` and a threshold `X0` with the objects of
`Sec5Objects` at every `X ≥ X0`. -/
def Section5Inputs : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ A : ℝ, 0 < A → ∃ K c X0 : ℝ, 0 ≤ K ∧ 0 < c ∧
    ∀ X : ℝ, X0 ≤ X →
      Nonempty (Sec5Objects X (X ^ (21 / 40 + ε)) ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε))
        K B A c)

/-! ### From Proposition 2.1 to the Lemma 5.1 core -/

theorem omega_le_LamCut {X Y H K B A c : ℝ} (o : Sec5Objects X Y H K B A c) (n : ℤ) :
    o.ω n ≤ LamCut X Y n := by
  unfold LamCut
  split_ifs with h
  · exact o.omega_le n
  · by_cases h0 : o.ω n = 0
    · exact le_of_eq h0
    · exact absurd (o.omega_window n h0) h

/-- Every non Goldbach even `n ≥ 4` in `[X - H, X]` is a main term exception or a
Proposition 2.1 exception with `κ = cY/4`. -/
theorem EXH_le_split (X Y H c : ℝ) (hc : 0 < c) (hY : 0 < Y) (ω T : ℤ → ℝ) :
    (EXH X H : ℝ) ≤
      (((win X H).filter (fun n => Even n ∧ conv (supp X) ω T n < c * Y)).card : ℝ) +
      (((win X H).filter (fun n => conv (supp X) (LamCut X Y) (LamP X) n
          < conv (supp X) ω T n - 2 * (c * Y / 4))).card : ℝ) := by
  unfold EXH
  rw [← Finset.card_image_of_injective _ (Nat.cast_injective (R := ℤ))]
  have hsub : ((Finset.Icc 4 ⌊X⌋₊).filter
      (fun n : ℕ => X - H ≤ (n : ℝ) ∧ Even n ∧ ¬ IsGoldbachSum n)).image (Nat.cast : ℕ → ℤ) ⊆
      (win X H).filter (fun n => Even n ∧ conv (supp X) ω T n < c * Y) ∪
      (win X H).filter (fun n => conv (supp X) (LamCut X Y) (LamP X) n
          < conv (supp X) ω T n - 2 * (c * Y / 4)) := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hz
    obtain ⟨n, ⟨⟨h4, hnX⟩, hlow, hev, hng⟩, rfl⟩ := hz
    have hnX' : (n : ℝ) ≤ X := (Nat.le_floor_iff' (by omega)).mp hnX
    have hwin : (n : ℤ) ∈ win X H := by
      unfold win; rw [Finset.mem_Icc]
      constructor
      · exact Int.ceil_le.mpr (by push_cast; exact hlow)
      · exact Int.le_floor.mpr (by push_cast; exact hnX')
    have hev' : Even (n : ℤ) := by exact_mod_cast hev
    have h0 := conv_eq_zero_of_not_goldbach X Y n hng
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hlt : conv (supp X) ω T n < c * Y
    · exact Or.inl ⟨hwin, hev', hlt⟩
    · refine Or.inr ⟨hwin, ?_⟩
      rw [h0]
      push Not at hlt
      have : 0 < c * Y := mul_pos hc hY
      linarith
  calc (((Finset.Icc 4 ⌊X⌋₊).filter
        (fun n : ℕ => X - H ≤ (n : ℝ) ∧ Even n ∧ ¬ IsGoldbachSum n)).image
          (Nat.cast : ℕ → ℤ)).card
        ≤ (((win X H).filter (fun n => Even n ∧ conv (supp X) ω T n < c * Y) ∪
          (win X H).filter (fun n => conv (supp X) (LamCut X Y) (LamP X) n
            < conv (supp X) ω T n - 2 * (c * Y / 4))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by exact_mod_cast Finset.card_union_le _ _

/-- The final arithmetic: the Proposition 2.1 count with `κ = cY/4`, `‖a‖² ≤ 12 Y L^{B'}`,
`‖ω‖² ≤ K Y L^{B'}`, `Δ = K Y L^{-(A'+B')}` and `log X ≤ 2L` is `≪ H (log X)^{-A'}`. -/
theorem final_arith {C0 K c Y H L lX sa sω A' B' : ℝ} (hC0 : 0 ≤ C0) (hK : 0 ≤ K)
    (hc : 0 < c) (hY : 0 < Y) (hH : 0 ≤ H) (hL : 1 ≤ L) (hlX : 0 < lX) (hlXL : lX ≤ 2 * L)
    (hA' : 0 ≤ A') (hsa : sa ≤ 12 * Y * L ^ B') (hsω : sω ≤ K * Y * L ^ B') :
    C0 * H * (sa + sω) * (K * Y * L ^ (-(A' + B'))) / (c * Y / 4) ^ 2
      ≤ 16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A' * H / lX ^ A' := by
  have hLpos : 0 < L := by linarith
  have hP : L ^ B' * L ^ (-(A' + B')) = (L ^ A')⁻¹ := by
    rw [← Real.rpow_add hLpos, show B' + -(A' + B') = -A' by ring, Real.rpow_neg hLpos.le]
  have hpow : lX ^ A' ≤ 2 ^ A' * L ^ A' := by
    rw [← Real.mul_rpow (by norm_num) hLpos.le]
    exact Real.rpow_le_rpow hlX.le hlXL hA'
  have hLA : 0 < L ^ A' := Real.rpow_pos_of_pos hLpos _
  have hlXA : 0 < lX ^ A' := Real.rpow_pos_of_pos hlX _
  have hinv : (L ^ A')⁻¹ ≤ 2 ^ A' / lX ^ A' := by
    rw [inv_eq_one_div, div_le_div_iff₀ hLA hlXA]; linarith
  have hD : 0 ≤ K * Y * L ^ (-(A' + B')) :=
    mul_nonneg (mul_nonneg hK hY.le) (Real.rpow_nonneg hLpos.le _)
  have hs : sa + sω ≤ (12 + K) * Y * L ^ B' := by linarith
  have hcoef : 0 ≤ 16 * C0 * K * (12 + K) / c ^ 2 * H :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hK)
      (by linarith)) (sq_nonneg c)) hH
  have hYne : Y ≠ 0 := hY.ne'
  have hcne : c ≠ 0 := hc.ne'
  calc C0 * H * (sa + sω) * (K * Y * L ^ (-(A' + B'))) / (c * Y / 4) ^ 2
      ≤ C0 * H * ((12 + K) * Y * L ^ B') * (K * Y * L ^ (-(A' + B'))) / (c * Y / 4) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hD
        exact mul_le_mul_of_nonneg_left hs (mul_nonneg hC0 hH)
    _ = 16 * C0 * K * (12 + K) / c ^ 2 * H * (L ^ B' * L ^ (-(A' + B'))) := by
        field_simp; ring
    _ = 16 * C0 * K * (12 + K) / c ^ 2 * H * (L ^ A')⁻¹ := by rw [hP]
    _ ≤ 16 * C0 * K * (12 + K) / c ^ 2 * H * (2 ^ A' / lX ^ A') :=
        mul_le_mul_of_nonneg_left hinv hcoef
    _ = _ := by ring

/-- CONDITIONAL ON `ShortSecondMoment` and `Section5Inputs`: the Lemma 5.1 core, the estimate
(1) at the single length `H = Y^{1/9+2ε}`, `Y = X^{21/40+ε}`, which is the hypothesis of
`thm1_1_of_lemma51_core'`. Proposition 2.1 is applied with `a = Λ'` cut to `(X - 3Y, X - Y]`,
`b = Λ'`, `θ`-closeness `Δ = K Y (log Y)^{-A}` and `κ = cY/4`. -/
theorem core_of_section5 (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (hS5 : Section5Inputs) :
    ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (EXH X ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε)) : ℝ)
        ≤ C * (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) / Real.log X ^ A := by
  intro ε hε A' hA'
  obtain ⟨C0, hC0, hM⟩ := hMRT
  obtain ⟨B, hB⟩ := hS5 ε hε
  set B' : ℝ := max B 2 with hB'def
  have hB'2 : (2 : ℝ) ≤ B' := le_max_right _ _
  have hBB' : B ≤ B' := le_max_left _ _
  obtain ⟨K, c, X0, hK, hc, hobj⟩ := hB (A' + B') (by linarith)
  refine ⟨K + 16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A', max X0 (Real.exp 2), fun X hX => ?_⟩
  have hXX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hXe
  have hlogX2 : 2 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe
  have hX1 : 1 ≤ X := by have := Real.add_one_le_exp 2; linarith
  obtain ⟨o⟩ := hobj X hXX0
  set Y := X ^ (21 / 40 + ε) with hYdef
  set H := Y ^ (1 / 9 + 2 * ε) with hHdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hX1 (by linarith)
  have hYpos : 0 < Y := by linarith
  have hH1 : 1 ≤ H := Real.one_le_rpow hY1 (by linarith)
  have hLY : Real.log X / 2 ≤ Real.log Y := logY_ge_half_logX hX1 hε.le
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hlXpos : 0 < Real.log X := by linarith
  have hP := prop21_finite hM (supp X) (LamCut X Y) (LamP X) o.ω o.ν o.T o.Tp X H
    (K * Y * L ^ (-(A' + B'))) (c * Y / 4) hH1 (by positivity)
    (LamCut_supp X Y) o.omega_supp o.nu_supp o.T_supp o.Tp_supp
    (LamCut_nonneg X Y) o.Tp_nonneg o.nu_le (omega_le_LamCut o) o.cor43 o.lemma42
  have hsplit := EXH_le_split X Y H c hc hYpos o.ω o.T
  have hmt := o.mainTerm
  have hsa : sqn (supp X) (LamCut X Y) ≤ 12 * Y * L ^ B' := by
    have h1 := sqn_LamCut_le hX1 hYpos.le
    have hlx : Real.log X ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    have hL2 : L ^ 2 ≤ L ^ B' := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hL1 hB'2
    calc sqn (supp X) (LamCut X Y) ≤ (2 * Y + 1) * Real.log X ^ 2 := h1
      _ ≤ (3 * Y) * (4 * L ^ B') :=
          mul_le_mul (by linarith) (by linarith) (sq_nonneg _) (by linarith)
      _ = 12 * Y * L ^ B' := by ring
  have hsω : sqn (supp X) o.ω ≤ K * Y * L ^ B' :=
    le_trans o.omega_norm (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 hBB') (mul_nonneg hK hYpos.le))
  have hH0 : 0 ≤ H := by linarith
  have hlXL : Real.log X ≤ 2 * L := by linarith
  have harith := final_arith hC0 hK hc hYpos hH0 hL1 hlXpos hlXL hA'.le hsa hsω
  have hmt' : K * H / Real.log X ^ (A' + B') ≤ K * H / Real.log X ^ A' := by
    apply div_le_div_of_nonneg_left (mul_nonneg hK (by linarith))
      (Real.rpow_pos_of_pos hlXpos _)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc (EXH X H : ℝ) ≤ _ := hsplit
    _ ≤ K * H / Real.log X ^ (A' + B') +
        C0 * H * (sqn (supp X) (LamCut X Y) + sqn (supp X) o.ω) *
          (K * Y * L ^ (-(A' + B'))) / (c * Y / 4) ^ 2 := add_le_add hmt hP
    _ ≤ K * H / Real.log X ^ A' +
        16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A' * H / Real.log X ^ A' :=
        add_le_add hmt' harith
    _ = (K + 16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A') * H / Real.log X ^ A' := by ring

/-- P0074 Theorem 1.1, CONDITIONAL ON `ShortSecondMoment`, the Matomäki, Radziwiłł, Tao second
moment step inside Proposition 2.1, and on `Section5Inputs`: Lemma 5.1, Lemma 4.2,
Corollary 4.3, the model construction and the main term lower bound. The full interval input
is discharged by the lab, see `thm1_1_of_lemma51_core'`. -/
theorem thm1_1_of_section5 (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (hS5 : Section5Inputs) : ShortIntervalLogSaving (7 / 120) :=
  thm1_1_of_lemma51_core' (core_of_section5 hMRT hS5)

end LeanLab.Grimmelt2019.Prop21
