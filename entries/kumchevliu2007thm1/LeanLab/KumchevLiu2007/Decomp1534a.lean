module

public import LeanLab.KumchevLiu2007.Statements

/-!
Kumchev and Liu 2007, Sums of primes and squares of primes in short intervals, arXiv 0801.0130.
Unit U-1534, run 20261026T0004Z-24325, DECOMPOSE. File a: the endgame of Theorem 2, Section 2.2
and Section 5, split into LEAF lemmas plus two assemblies.

* The vector sieve inequality (39), pointwise and summed.
* The numerical sieve constant: (70) and (71) give sigma >= 0.17 as used in (72).
* The exponent bookkeeping H = Y^theta2, Y = X^theta1 with theta1 = 0.55 + eps, theta2 = 3/5 - 2 eps.
* Counting bookkeeping: exceptions lie in the union of two small bad sets.

Assemblies, no gap of their own, CONDITIONAL ON the leaves below:
* `vecsieve_lower_017`: (39) with main terms (70), (71) gives R(n; varpi, lambda0) >= 0.17 M.
* `thm2_of_sieve_inputs`: the paper's Theorem 2 statement from (35), (40) or (72), and
  Proposition 2, taken as an explicit hypothesis on the circle method output.

AI-written Lean code, Claude, unit U-1534. Checked only by the Lean kernel.
Binary Goldbach is OPEN; these are Hua type problems.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.U1534

open Real LeanLab.KumchevLiu2007

attribute [local instance] Classical.propDecidable

/-- LEAF. Unit U-1534. Vector sieve, pointwise: if `0 ≤ x₁`, `0 ≤ x₂`, `l₁ ≤ x₁ ≤ u₁` and
`l₂ ≤ x₂ ≤ u₂`, then `x₁ x₂ ≥ u₁ l₂ + l₁ u₂ - u₁ u₂`; Section 2.2, eq. (39). -/
theorem vecsieve_pointwise {x₁ x₂ l₁ u₁ l₂ u₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂)
    (hl₁ : l₁ ≤ x₁) (hu₁ : x₁ ≤ u₁) (hl₂ : l₂ ≤ x₂) (hu₂ : x₂ ≤ u₂) :
    u₁ * l₂ + l₁ * u₂ - u₁ * u₂ ≤ x₁ * x₂ := by
  have hprod := mul_nonneg (sub_nonneg.mpr hu₁) (sub_nonneg.mpr hu₂)
  have hleft := mul_nonneg (sub_nonneg.mpr hl₁) (le_trans h₂ hu₂)
  have hright := mul_nonneg (sub_nonneg.mpr hl₂) (le_trans h₁ hu₁)
  nlinarith

/-- LEAF. Unit U-1534. Vector sieve, summed over a finite index set: with the pointwise
hypotheses of eq. (39) at every index, `∑ x₁ x₂ ≥ ∑ u₁ l₂ + ∑ l₁ u₂ - ∑ u₁ u₂`; Section 2.2,
eq. (39). -/
theorem vecsieve_sum {ι : Type*} (s : Finset ι) (x₁ x₂ l₁ u₁ l₂ u₂ : ι → ℝ)
    (h₁ : ∀ i ∈ s, 0 ≤ x₁ i) (h₂ : ∀ i ∈ s, 0 ≤ x₂ i)
    (hl₁ : ∀ i ∈ s, l₁ i ≤ x₁ i) (hu₁ : ∀ i ∈ s, x₁ i ≤ u₁ i)
    (hl₂ : ∀ i ∈ s, l₂ i ≤ x₂ i) (hu₂ : ∀ i ∈ s, x₂ i ≤ u₂ i) :
    (∑ i ∈ s, u₁ i * l₂ i) + (∑ i ∈ s, l₁ i * u₂ i) - (∑ i ∈ s, u₁ i * u₂ i) ≤
      ∑ i ∈ s, x₁ i * x₂ i := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i hi =>
    vecsieve_pointwise (h₁ i hi) (h₂ i hi) (hl₁ i hi) (hu₁ i hi) (hl₂ i hi) (hu₂ i hi)

/-- LEAF. Unit U-1534. The sieve constant: if `a⁻ ≤ a⁺ < 1.01`, `a⁻ > 0.99`, `0.22 < b⁻ ≤ b⁺`
and `b⁺ < 2.26`, then `a⁺ b⁻ + a⁻ b⁺ - a⁺ b⁺ ≥ 0.17`; Section 5, eqs. (70), (71), (72). -/
theorem sigma_ge_017 {ap am bp bm : ℝ} (ha : am ≤ ap) (hap : ap < 101 / 100)
    (ham : 99 / 100 < am) (hbm : 22 / 100 < bm) (hb : bm ≤ bp) (hbp : bp < 226 / 100) :
    17 / 100 ≤ ap * bm + am * bp - ap * bp := by
  have hap0 : 99 / 100 ≤ ap := le_trans ham.le ha
  have hbp0 : 0 ≤ bp := by linarith
  have hmain : (99 / 100 : ℝ) * (22 / 100) ≤ ap * bm :=
    mul_le_mul hap0 hbm.le (by norm_num) (by linarith)
  have herror : (ap - am) * bp ≤ (2 / 100 : ℝ) * (226 / 100) :=
    mul_le_mul (by linarith) hbp.le hbp0 (by norm_num)
  nlinarith

/-- LEAF. Unit U-1534. With `θ₁ = 0.55 + ε` and `θ₂ = 3/5 - 2ε`, `ε > 0`, the exponent
`θ₁ θ₂` of `H = X^{θ₁ θ₂}` is below `0.33`; Section 5, last paragraph, Theorem 2. -/
theorem theta_thm2_lt {ε : ℝ} (hε : 0 < ε) : (55 / 100 + ε) * (3 / 5 - 2 * ε) < 33 / 100 := by
  nlinarith [sq_nonneg ε]

/-- LEAF. Unit U-1534. The improvement remark: with `θ₂ = 0.595 - 2ε` in place of `3/5 - 2ε`,
`(0.55 + ε)(0.595 - 2ε) < 0.3275` for `ε > 0`; Section 1, remark after Theorem 2. -/
theorem theta_thm2_improved_lt {ε : ℝ} (hε : 0 < ε) :
    (55 / 100 + ε) * (595 / 1000 - 2 * ε) < 3275 / 10000 := by
  nlinarith [sq_nonneg ε]

/-- LEAF. Unit U-1534. With `Y = X^{θ₁}` and `H = Y^{θ₂}`, `H = X^{θ₁ θ₂}` for `X > 0`;
Section 2.1, the parameters before eq. (14). -/
theorem rpow_compose {X θ₁ θ₂ : ℝ} (hX : 0 < X) : (X ^ θ₁) ^ θ₂ = X ^ (θ₁ * θ₂) := by
  exact (Real.rpow_mul hX.le θ₁ θ₂).symm

/-- LEAF. Unit U-1534. A saving `L^{-1+δ}` with `δ < 1` beats any fixed constant: for every `K`
there is `L₀` with `K L^{δ - 1} ≤ 1/20` for all `L ≥ L₀`; Section 2.2, eq. (36). -/
theorem small_power_eventually (K δ : ℝ) (hδ : δ < 1) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → K * L ^ (δ - 1) ≤ 1 / 20 := by
  have ht := (tendsto_rpow_neg_atTop (show 0 < 1 - δ by linarith)).const_mul K
  rw [mul_zero] at ht
  have he : ∀ᶠ L : ℝ in Filter.atTop, K * L ^ (-(1 - δ)) < 1 / 20 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
  obtain ⟨L0, hL⟩ := Filter.eventually_atTop.mp he
  refine ⟨max L0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro L h
  have heq : -(1 - δ) = δ - 1 := by ring
  rw [← heq]
  exact (hL L (le_trans (le_max_left _ _) h)).le

/-- LEAF. Unit U-1534. The interval count is monotone in the predicate: `S ⊆ T` gives
`cntIoc S X H ≤ cntIoc T X H`; bookkeeping for the exceptional sets in Theorem 2. -/
theorem cnt_mono {S T : ℕ → Prop} (hST : ∀ n, S n → T n) (X H : ℝ) :
    cntIoc S X H ≤ cntIoc T X H := by
  unfold cntIoc
  have h : ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n)) ⊆ ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ T n)) := by
    intro n
    rw [Finset.mem_filter, Finset.mem_filter]
    rintro ⟨hn1, hXn, hSn⟩
    exact ⟨hn1, hXn, hST n hSn⟩
  exact Finset.card_le_card h

/-- LEAF. Unit U-1534. The interval count of a union is at most the sum of the counts;
bookkeeping for the two exceptional sets of eq. (40) and Proposition 2. -/
theorem cnt_or_le (S T : ℕ → Prop) (X H : ℝ) :
    cntIoc (fun n => S n ∨ T n) X H ≤ cntIoc S X H + cntIoc T X H := by
  simp only [cntIoc, and_or_left, Finset.filter_or]
  exact Finset.card_union_le _ _

/-- LEAF. Unit U-1534. If `M > 0`, `R ≥ 0.16 M` and `R₀ ≤ M / 20`, then `R - R₀ > 0`; the
positivity step that turns eqs. (35), (72) and Proposition 2 into a representation. -/
theorem pos_of_main {M R R0 : ℝ} (hM : 0 < M) (hR : 16 / 100 * M ≤ R) (hR0 : R0 ≤ 1 / 20 * M) :
    0 < R - R0 := by
  linarith

/-! ### Assemblies -/

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `vecsieve_sum` and `sigma_ge_017`.
Eq. (39) summed, with the four sieve main terms equal to `σ₁^± σ₂^± M` and the bounds (70),
(71), gives the lower bound `∑ x₁ x₂ ≥ 0.17 M` of eq. (72). -/
theorem vecsieve_lower_017 {ι : Type*} (s : Finset ι) (x₁ x₂ l₁ u₁ l₂ u₂ : ι → ℝ)
    (h₁ : ∀ i ∈ s, 0 ≤ x₁ i) (h₂ : ∀ i ∈ s, 0 ≤ x₂ i)
    (hl₁ : ∀ i ∈ s, l₁ i ≤ x₁ i) (hu₁ : ∀ i ∈ s, x₁ i ≤ u₁ i)
    (hl₂ : ∀ i ∈ s, l₂ i ≤ x₂ i) (hu₂ : ∀ i ∈ s, x₂ i ≤ u₂ i)
    {M ap am bp bm : ℝ} (hM : 0 ≤ M)
    (e1 : ∑ i ∈ s, u₁ i * l₂ i = ap * bm * M) (e2 : ∑ i ∈ s, l₁ i * u₂ i = am * bp * M)
    (e3 : ∑ i ∈ s, u₁ i * u₂ i = ap * bp * M)
    (ha : am ≤ ap) (hap : ap < 101 / 100) (ham : 99 / 100 < am) (hbm : 22 / 100 < bm)
    (hb : bm ≤ bp) (hbp : bp < 226 / 100) :
    17 / 100 * M ≤ ∑ i ∈ s, x₁ i * x₂ i := by
  have hv := vecsieve_sum s x₁ x₂ l₁ u₁ l₂ u₂ h₁ h₂ hl₁ hu₁ hl₂ hu₂
  have hσ := sigma_ge_017 ha hap ham hbm hb hbp
  rw [e1, e2, e3] at hv
  have : 17 / 100 * M ≤ (ap * bm + am * bp - ap * bp) * M := mul_le_mul_of_nonneg_right hσ hM
  nlinarith

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `small_power_eventually`, `cnt_mono`,
`cnt_or_le` and `pos_of_main`, and on the circle method hypothesis `hin`.
`hin` packages, for each `A`, the output of Sections 2 to 5: weights `Rv = R(n; ϖ, λ₀)`,
`R0 = R₀(n)`, main term `M = r₂(n) 𝔖₂(n, P)`, with `Rv ≥ 0.16 M`, from (72), outside a bad set
`B1`, `R0 ≪ M L^{-1+δ}`, Proposition 2, outside a bad set `B2`, both bad sets of size
`≪ H L^{-A}`, and `Rv - R0 = R₂(n) > 0` forcing `n = p₁ + p₂²`, eq. (35).
The conclusion is exactly the lab's statement of Theorem 2. -/
theorem thm2_of_sieve_inputs
    (hin : ∀ A : ℝ, 0 < A → ∃ C X0 K δ : ℝ, δ < 1 ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (33 / 100 : ℝ) ≤ H → H ≤ X →
      ∃ (Rv R0 M : ℕ → ℝ) (B1 B2 : ℕ → Prop),
        (cntIoc B1 X H : ℝ) ≤ C * H / Real.log X ^ A ∧
        (cntIoc B2 X H : ℝ) ≤ C * H / Real.log X ^ A ∧
        (∀ n, InH2 n → ¬ B1 n → 0 < M n ∧ 16 / 100 * M n ≤ Rv n) ∧
        (∀ n, InH2 n → ¬ B2 n → R0 n ≤ K * M n * Real.log X ^ (δ - 1)) ∧
        (∀ n, InH2 n → 0 < Rv n - R0 n → IsPrimePlusPrimeSq n)) :
    ShortExcBound (fun n => InH2 n ∧ ¬ IsPrimePlusPrimeSq n) (33 / 100) := by
  intro A hA
  obtain ⟨C, X0, K, δ, hδ, h⟩ := hin A hA
  obtain ⟨L0, hL0, hL⟩ := small_power_eventually K δ hδ
  refine ⟨2 * C, max X0 (Real.exp L0), fun X H hX hH1 hH2 => ?_⟩
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp L0 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXe
  have hlog : L0 ≤ Real.log X := by
    rw [← Real.log_exp L0]; exact Real.log_le_log (Real.exp_pos _) hXe
  obtain ⟨Rv, R0, M, B1, B2, hB1, hB2, hmain, hprop2, hrep⟩ := h X H hX0 hH1 hH2
  have hsub : ∀ n, (InH2 n ∧ ¬ IsPrimePlusPrimeSq n) → (B1 n ∨ B2 n) := by
    intro n ⟨hn, hnp⟩
    by_contra hc
    push Not at hc
    obtain ⟨hM, hRv⟩ := hmain n hn hc.1
    have hR0 := hprop2 n hn hc.2
    have hK : K * Real.log X ^ (δ - 1) ≤ 1 / 20 := hL _ hlog
    have hR0' : R0 n ≤ 1 / 20 * M n := by
      calc R0 n ≤ K * M n * Real.log X ^ (δ - 1) := hR0
        _ = (K * Real.log X ^ (δ - 1)) * M n := by ring
        _ ≤ 1 / 20 * M n := mul_le_mul_of_nonneg_right hK hM.le
    exact hnp (hrep n hn (pos_of_main hM hRv hR0'))
  have h1 := cnt_mono hsub X H
  have h2 := cnt_or_le B1 B2 X H
  have h3 : (cntIoc (fun n => InH2 n ∧ ¬ IsPrimePlusPrimeSq n) X H : ℝ) ≤
      (cntIoc B1 X H : ℝ) + cntIoc B2 X H := by exact_mod_cast le_trans h1 h2
  calc (cntIoc (fun n => InH2 n ∧ ¬ IsPrimePlusPrimeSq n) X H : ℝ)
      ≤ C * H / Real.log X ^ A + C * H / Real.log X ^ A := by linarith
    _ = 2 * C * H / Real.log X ^ A := by ring

end LeanLab.KumchevLiu2007.U1534
