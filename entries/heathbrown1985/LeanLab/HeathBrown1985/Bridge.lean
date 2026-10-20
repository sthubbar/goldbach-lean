module

public import Mathlib
public import LeanLab.HeathBrown1985.Statements
public import LeanLab.ChenExplicit.Assembly
public import LeanLab.ExceptionalSet.Statements

/-!
P0096 Heath-Brown 1985: what follows from the stated results by elementary means.
PROVED zero sorry: Λ_Q in Ramanujan sum form, the paper's second expression for Λ_Q;
Corollary 1 from Theorem 1, with the paper's bound 𝔖(m) ≥ 2∏_{p>2}(1 − 1/(p−1)²) ≫ 1 for
even m, p. 58, made explicit as 𝔖(m) ≥ 2 e^{-6} by ChenExplicit.twinC_ge, and a cover of (0, x] by the blocks (2y, 3y] with y = x/3 (2/3)^j.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-! ### Λ_Q, the two forms -/

theorem moebius_identity {q d : ℕ} (hd : d ∣ q) :
    (μ q : ℝ) ^ 2 * (μ d : ℝ) = (μ q : ℝ) * (μ (q / d) : ℝ) := by
  by_cases hq : μ q = 0
  · simp [hq]
  · have hsq : Squarefree q := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hq
    obtain ⟨e, rfl⟩ := hd
    have hq0 : 0 < d * e := Nat.pos_of_ne_zero (Squarefree.ne_zero hsq)
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right hq0
    have he : d * e / d = e := Nat.mul_div_cancel_left e hd0
    rw [he]
    have hcop : d.Coprime e := Nat.coprime_of_squarefree_mul hsq
    have hmul : μ (d * e) = μ d * μ e :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    have hsd : Squarefree d := Squarefree.of_mul_left hsq
    have hse : Squarefree e := Squarefree.of_mul_right hsq
    have h1 : (μ d : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsd
    have h2 : (μ e : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hse
    have hm : (μ (d * e) : ℝ) = (μ d : ℝ) * (μ e : ℝ) := by exact_mod_cast hmul
    rw [hm]
    linear_combination ((μ d : ℝ) * (μ e : ℝ) ^ 2) * h1

/-- The paper's identity `Λ_Q(n) = Σ_{q ≤ Q} μ(q)/φ(q) c_q(n)`. -/
theorem lambdaQ_eq_ramanujan (Q : ℝ) (n : ℕ) :
    LambdaQ Q n = ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) / (Nat.totient q : ℝ)) * ramanujan q n := by
  unfold LambdaQ ramanujan
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdq : d ∣ q := (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hd)).2
  have := moebius_identity (q := q) (d := d) hdq
  by_cases hφ : (Nat.totient q : ℝ) = 0
  · simp [hφ]
  · field_simp
    linear_combination (d : ℝ) * this

/-! ### Corollary 1 from Theorem 1 -/

theorem singular_ge {m : ℕ} (hm : Even m) : 2 * exp (-6) ≤ singular m := by
  unfold singular
  rw [if_pos hm]
  have hprod : (1 : ℝ) ≤ ∏ p ∈ m.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.one_le_prod₀
    intro p hp
    simp only [Finset.mem_filter] at hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    rw [le_div_iff₀ (by linarith)]
    linarith
  have ht := ChenExplicit.twinC_ge
  have he : 0 < exp (-6 : ℝ) := exp_pos _
  calc 2 * exp (-6) ≤ 2 * ChenExplicit.twinC := by linarith
    _ = 2 * ChenExplicit.twinC * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by linarith)

theorem N2_eq_zero {x : ℝ} {m : ℕ} (h : ¬ IsGoldbachSum m) : N2 x m = 0 := by
  unfold N2
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  exact absurd ⟨p, m - p, hp.2.1, hp.2.2.1, by omega⟩ h

/-- Theorem 1 bounds the exceptions in one block `(2x, 3x]`: each contributes `x 𝔖(m) ≥ 2 e^{-6} x`. -/
theorem block_bound (hT : Theorem1) (C : ℝ) (hC : 0 < C) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
    (excCount (2 * x) (3 * x) : ℝ) ≤ K * x * Real.log x ^ (-C) := by
  obtain ⟨K, hK⟩ := hT C hC
  have he : 0 < 2 * exp (-6 : ℝ) := by positivity
  refine ⟨max K 0 / (2 * exp (-6)), div_nonneg (le_max_right _ _) he.le, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set S := (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ)) with hS
  set T := (range (⌊3 * x⌋₊ + 1)).filter
    (fun m : ℕ => 2 * x < ((m : ℕ) : ℝ) ∧ Even m ∧ ¬ IsGoldbachSum m) with hT'
  have hTS : T ⊆ S := by
    intro m hm
    simp only [hT', hS, Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.1⟩
  have h1 : (T.card : ℝ) * (x * (2 * exp (-6))) ≤ ∑ m ∈ S, |N2 x m - x * singular m| := by
    calc (T.card : ℝ) * (x * (2 * exp (-6))) = ∑ _m ∈ T, x * (2 * exp (-6)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ T, |N2 x m - x * singular m| := by
          apply Finset.sum_le_sum
          intro m hm
          simp only [hT', Finset.mem_filter] at hm
          rw [N2_eq_zero hm.2.2.2, zero_sub, abs_neg]
          have hs := singular_ge hm.2.2.1
          rw [abs_of_nonneg (mul_nonneg hx0.le (by linarith))]
          exact mul_le_mul_of_nonneg_left hs hx0.le
      _ ≤ ∑ m ∈ S, |N2 x m - x * singular m| :=
          Finset.sum_le_sum_of_subset_of_nonneg hTS (fun _ _ _ => abs_nonneg _)
  have h2 := hK x hx
  have hL : 0 ≤ Real.log x ^ (-C) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have h3 : K * x ^ 2 * Real.log x ^ (-C) ≤ max K 0 * x ^ 2 * Real.log x ^ (-C) := by
    gcongr; exact le_max_left _ _
  have hcount : excCount (2 * x) (3 * x) = T.card := rfl
  rw [hcount]
  have hpos : 0 < x * (2 * exp (-6 : ℝ)) := mul_pos hx0 he
  have key : (T.card : ℝ) * (x * (2 * exp (-6))) ≤
      (max K 0 / (2 * exp (-6)) * x * Real.log x ^ (-C)) * (x * (2 * exp (-6))) := by
    have : (max K 0 / (2 * exp (-6)) * x * Real.log x ^ (-C)) * (x * (2 * exp (-6))) =
        max K 0 * x ^ 2 * Real.log x ^ (-C) := by
      field_simp
    rw [this]; linarith
  exact le_of_mul_le_mul_right key hpos

/-- Splitting `(a, c]` at `b`. -/
theorem excCount_split (a b c : ℝ) : excCount a c ≤ excCount a b + excCount b c := by
  unfold excCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hm ⊢
  by_cases hb : (m : ℝ) ≤ b
  · left
    have : m ≤ ⌊b⌋₊ := Nat.le_floor hb
    exact ⟨by omega, hm.2⟩
  · right
    exact ⟨hm.1, lt_of_not_ge hb, hm.2.2⟩

/-- The trivial bound. -/
theorem excCount_zero_le (y : ℝ) (hy : 0 ≤ y) : (excCount 0 y : ℝ) ≤ y := by
  have h : excCount 0 y ≤ ⌊y⌋₊ := by
    unfold excCount
    calc #{m ∈ range (⌊y⌋₊ + 1) | (0 : ℝ) < ((m : ℕ) : ℝ) ∧ Even m ∧ ¬ IsGoldbachSum m}
        ≤ #((range (⌊y⌋₊ + 1)).erase 0) := by
          apply Finset.card_le_card
          intro m hm
          simp only [Finset.mem_filter] at hm
          refine Finset.mem_erase.mpr ⟨?_, hm.1⟩
          rintro rfl; simp at hm
      _ = ⌊y⌋₊ := by rw [Finset.card_erase_of_mem (by simp)]; simp
  calc (excCount 0 y : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h
    _ ≤ y := Nat.floor_le hy

/-- The blocks `(2 y_j, 3 y_j]`, `y_j = X/3 (2/3)^j`, with `3 y_0 = X` and `3 y_{j+1} = 2 y_j`. -/
def yj (X : ℝ) (j : ℕ) : ℝ := X / 3 * (2 / 3) ^ j

theorem chain (X : ℝ) : ∀ J : ℕ, excCount 0 X ≤ excCount 0 (3 * yj X J) +
    ∑ j ∈ range J, excCount (2 * yj X j) (3 * yj X j) := by
  intro J
  induction J with
  | zero =>
    have : 3 * yj X 0 = X := by unfold yj; ring
    simp [this]
  | succ J ih =>
    have h3 : 3 * yj X (J + 1) = 2 * yj X J := by unfold yj; ring
    have hs := excCount_split 0 (2 * yj X J) (3 * yj X J)
    rw [Finset.sum_range_succ, h3]
    omega

theorem sum_yj_le (X : ℝ) (hX : 0 ≤ X) (J : ℕ) : ∑ j ∈ range J, yj X j ≤ X := by
  unfold yj
  rw [← Finset.mul_sum]
  have hg : (∑ j ∈ range J, (2 / 3 : ℝ) ^ j) * ((2 / 3 : ℝ) - 1) = (2 / 3) ^ J - 1 :=
    geom_sum_mul _ _
  have hp : 0 ≤ (2 / 3 : ℝ) ^ J := by positivity
  have hs : ∑ j ∈ range J, (2 / 3 : ℝ) ^ j ≤ 3 := by nlinarith
  calc X / 3 * ∑ j ∈ range J, (2 / 3 : ℝ) ^ j ≤ X / 3 * 3 := by gcongr
    _ = X := by ring

/-- **Corollary 1 follows from Theorem 1**, zero sorry. -/
theorem corollary1_of_theorem1 (hT : Theorem1) : Corollary1 := by
  intro C hC
  obtain ⟨A, hA0, hA⟩ := block_bound hT C hC
  set ε : ℝ := 1 / (2 * C) with hε
  have hεpos : 0 < ε := by positivity
  refine ⟨A * 2 ^ C + 3 / ε ^ C + Real.log 4 ^ C, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hLC : 0 < Real.log X ^ (-C) := Real.rpow_pos_of_pos hL _
  have hpos1 : 0 ≤ A * 2 ^ C := by positivity
  have hpos2 : 0 ≤ 3 / ε ^ C := by positivity
  have hpos3 : 0 ≤ Real.log 4 ^ C := by positivity
  have hLL : Real.log X ^ C * Real.log X ^ (-C) = 1 := by
    rw [← Real.rpow_add hL]; simp
  rcases lt_or_ge X 4 with hX4 | hX4
  · have h1 := excCount_zero_le X hX0.le
    have hl4 : Real.log X ≤ Real.log 4 := Real.log_le_log hX0 hX4.le
    have hk : Real.log 4 ^ (-C) ≤ Real.log X ^ (-C) :=
      Real.rpow_le_rpow_of_nonpos hL hl4 (by linarith)
    have hone : Real.log 4 ^ C * Real.log 4 ^ (-C) = 1 := by
      rw [← Real.rpow_add (Real.log_pos (by norm_num))]; simp
    calc (excCount 0 X : ℝ) ≤ X := h1
      _ = Real.log 4 ^ C * Real.log 4 ^ (-C) * X := by rw [hone, one_mul]
      _ ≤ Real.log 4 ^ C * Real.log X ^ (-C) * X := by gcongr
      _ = Real.log 4 ^ C * X * Real.log X ^ (-C) := by ring
      _ ≤ (A * 2 ^ C + 3 / ε ^ C + Real.log 4 ^ C) * X * Real.log X ^ (-C) := by
          gcongr; linarith
  · set s := Real.sqrt X with hsdef
    have hs2 : 2 ≤ s := by
      rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by linarith)
    have hs0 : 0 < s := by linarith
    have hss : s * s = X := Real.mul_self_sqrt hX0.le
    have hex : ∃ j, yj X j < s := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < s / (X / 3) by positivity)
        (show (2 / 3 : ℝ) < 1 by norm_num)
      refine ⟨n, ?_⟩
      rw [lt_div_iff₀ (by positivity)] at hn
      unfold yj; linarith [mul_comm ((2 / 3 : ℝ) ^ n) (X / 3)]
    classical
    set J := Nat.find hex with hJdef
    have hJ : yj X J < s := Nat.find_spec hex
    have hbig : ∀ j < J, s ≤ yj X j := fun j hj => not_lt.mp (Nat.find_min hex hj)
    have hch : (excCount 0 X : ℝ) ≤ (excCount 0 (3 * yj X J) : ℝ) +
        ∑ j ∈ range J, (excCount (2 * yj X j) (3 * yj X j) : ℝ) := by
      exact_mod_cast chain X J
    have hy0 : 0 ≤ yj X J := by unfold yj; positivity
    -- the tail below 3 y_J
    have ht1 : (excCount 0 (3 * yj X J) : ℝ) ≤ 3 * s := by
      have := excCount_zero_le (3 * yj X J) (by linarith)
      linarith
    have hlogle : Real.log X ≤ X ^ ε / ε := Real.log_le_rpow_div hX0.le hεpos
    have hLCle : Real.log X ^ C ≤ s / ε ^ C := by
      calc Real.log X ^ C ≤ (X ^ ε / ε) ^ C := Real.rpow_le_rpow hL.le hlogle hC.le
        _ = X ^ (ε * C) / ε ^ C := by
            rw [Real.div_rpow (Real.rpow_nonneg hX0.le _) hεpos.le, ← Real.rpow_mul hX0.le]
        _ = s / ε ^ C := by
            congr 1
            rw [show ε * C = 1 / 2 by rw [hε]; field_simp, hsdef, Real.sqrt_eq_rpow]
    have ht1' : 3 * s ≤ 3 / ε ^ C * X * Real.log X ^ (-C) := by
      have hεC : 0 < ε ^ C := Real.rpow_pos_of_pos hεpos C
      calc 3 * s = 3 * s * (Real.log X ^ C * Real.log X ^ (-C)) := by rw [hLL, mul_one]
        _ = 3 * (s * Real.log X ^ C) * Real.log X ^ (-C) := by ring
        _ ≤ 3 * (s * (s / ε ^ C)) * Real.log X ^ (-C) := by gcongr
        _ = 3 / ε ^ C * X * Real.log X ^ (-C) := by rw [← hss]; field_simp
    -- the blocks
    have hblock : ∀ j ∈ range J, (excCount (2 * yj X j) (3 * yj X j) : ℝ) ≤
        A * 2 ^ C * Real.log X ^ (-C) * yj X j := by
      intro j hj
      have hjJ := hbig j (Finset.mem_range.mp hj)
      have hy2 : 2 ≤ yj X j := le_trans hs2 hjJ
      have hb := hA (yj X j) hy2
      have hly : Real.log X / 2 ≤ Real.log (yj X j) := by
        rw [← Real.log_sqrt hX0.le]; exact Real.log_le_log hs0 hjJ
      have hL2 : 0 < Real.log X / 2 := by positivity
      have hpow : Real.log (yj X j) ^ (-C) ≤ (Real.log X / 2) ^ (-C) :=
        Real.rpow_le_rpow_of_nonpos hL2 hly (by linarith)
      have hpow2 : (Real.log X / 2) ^ (-C) = 2 ^ C * Real.log X ^ (-C) := by
        rw [Real.div_rpow hL.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      calc (excCount (2 * yj X j) (3 * yj X j) : ℝ)
          ≤ A * yj X j * Real.log (yj X j) ^ (-C) := hb
        _ ≤ A * yj X j * (Real.log X / 2) ^ (-C) := by gcongr
        _ = A * 2 ^ C * Real.log X ^ (-C) * yj X j := by rw [hpow2]; ring
    have hsum : ∑ j ∈ range J, (excCount (2 * yj X j) (3 * yj X j) : ℝ) ≤
        A * 2 ^ C * X * Real.log X ^ (-C) := by
      calc ∑ j ∈ range J, (excCount (2 * yj X j) (3 * yj X j) : ℝ)
          ≤ ∑ j ∈ range J, A * 2 ^ C * Real.log X ^ (-C) * yj X j := Finset.sum_le_sum hblock
        _ = A * 2 ^ C * Real.log X ^ (-C) * ∑ j ∈ range J, yj X j := by rw [Finset.mul_sum]
        _ ≤ A * 2 ^ C * Real.log X ^ (-C) * X := by
            gcongr; exact sum_yj_le X hX0.le J
        _ = A * 2 ^ C * X * Real.log X ^ (-C) := by ring
    have hXL : 0 ≤ X * Real.log X ^ (-C) := by positivity
    calc (excCount 0 X : ℝ) ≤ 3 * s + A * 2 ^ C * X * Real.log X ^ (-C) := by linarith
      _ ≤ 3 / ε ^ C * X * Real.log X ^ (-C) + A * 2 ^ C * X * Real.log X ^ (-C) := by linarith
      _ ≤ (A * 2 ^ C + 3 / ε ^ C + Real.log 4 ^ C) * X * Real.log X ^ (-C) := by
          nlinarith [mul_nonneg hpos3 hXL]

/-- The lab's `E X` counts a subset of what `excCount 0 X` counts. -/
theorem E_le_excCount (X : ℕ) : ExceptionalSet.E X ≤ excCount 0 X := by
  unfold ExceptionalSet.E excCount
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.floor_natCast] at hm ⊢
  refine ⟨by omega, ?_, hm.2.1, ?_⟩
  · have : (4 : ℝ) ≤ m := by exact_mod_cast hm.1.1
    linarith
  · convert hm.2.2

/-- Corollary 1 is the `LogPowerSaving` form of `ExceptionalSet`. -/
theorem logPowerSaving_of_corollary1 (h : Corollary1) : ExceptionalSet.LogPowerSaving := by
  intro A hA
  obtain ⟨K, hK⟩ := h A hA
  refine ⟨K, fun X hX => ?_⟩
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have h1 : (ExceptionalSet.E X : ℝ) ≤ excCount 0 X := by exact_mod_cast E_le_excCount X
  calc (ExceptionalSet.E X : ℝ) ≤ excCount 0 X := h1
    _ ≤ K * X * Real.log X ^ (-A) := hK X hXr
    _ = K * X / Real.log X ^ A := by rw [Real.rpow_neg hL.le]; ring

/-- Heath-Brown's Theorem 1 gives the classical exceptional set bound, hence density zero. -/
theorem logPowerSaving_of_theorem1 (hT : Theorem1) : ExceptionalSet.LogPowerSaving :=
  logPowerSaving_of_corollary1 (corollary1_of_theorem1 hT)

end LeanLab.HeathBrown1985
