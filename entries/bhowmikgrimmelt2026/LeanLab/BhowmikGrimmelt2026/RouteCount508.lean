module

public import LeanLab.BhowmikGrimmelt2026.RouteMode508
public import LeanLab.BhowmikGrimmelt2026.Decomp541a
public import LeanLab.BhowmikGrimmelt2026.RouteWindow508

/-!
ROUTE for `oscillatory_zero_modes508`, part five: the reciprocal zero count under the zero
bound hypothesis of the row itself.
Source: P0029 pages 11 and 12 display 3.7, where the zero sum is bounded under the hypothesis
Re ρ ≤ Θ. The existing leaf `zero_reciprocal_multiplicity508` drops that hypothesis, so as
stated it needs Siegel's theorem to keep zeros away from the origin. With the hypothesis
kept, reflection keeps every zero at distance more than one quarter from the origin and the
only cited input left is the count of zeros in a window of height one.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- P0029 page 11 display 3.7, the zero bound hypothesis keeps every strip zero of every
character, primitive or not, at distance more than one quarter from the origin. -/
theorem character_zero_norm_lower508 {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    1 / 4 < ‖ρ‖ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd := χ.conductor_dvd_level
  have hz : DirichletCharacter.LFunction χ ρ = 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      character_zero_changeLevel508 hd χ.primitiveCharacter h0 h1
  exact primitive_zero_norm_lower541 hΘ hZ χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive (hz.mp hρ) h0 h1

/-- The reciprocal weights of the integer windows sum to at most twice a harmonic sum. -/
theorem int_abs_harmonic508 (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N, 1 / (|(k : ℝ)| + 1) ≤
      2 * (1 + Real.log ((N : ℝ) + 1)) := by
  have hsub : Finset.Icc (-(N : ℤ)) N ⊆
      (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)) ∪
        (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases le_total 0 k with h | h
    · left; exact ⟨k.toNat, by rw [Finset.mem_range]; omega, by omega⟩
    · right; exact ⟨(-k).toNat, by rw [Finset.mem_range]; omega, by omega⟩
  have hh : ∑ j ∈ Finset.range (N + 1), 1 / ((j : ℝ) + 1) ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have h := harmonic_le_one_add_log (N + 1)
    rw [harmonic] at h
    push_cast at h
    simpa [one_div] using h
  have h1 : ∑ k ∈ (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)), 1 / (|(k : ℝ)| + 1) =
      ∑ j ∈ Finset.range (N + 1), 1 / ((j : ℝ) + 1) := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have h2 : ∑ k ∈ (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)), 1 / (|(k : ℝ)| + 1) =
      ∑ j ∈ Finset.range (N + 1), 1 / ((j : ℝ) + 1) := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hun := Finset.sum_union_inter
    (s₁ := (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)))
    (s₂ := (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)))
    (f := fun k : ℤ => 1 / (|(k : ℝ)| + 1))
  have hint : (0 : ℝ) ≤ ∑ k ∈ (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)) ∩
      (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)), 1 / (|(k : ℝ)| + 1) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℤ => 1 / (|(k : ℝ)| + 1))
    hsub (fun _ _ _ => by positivity)
  rw [h1, h2] at hun
  linarith

/-- LEAF: P0029 page 11 display 3.7, the zero count behind the bound of the zero sum, which
the survey uses without stating it. CITED from Davenport, Multiplicative Number Theory,
chapter 16: the zeros of `L (s, χ)` in the open critical strip with ordinate within one of
`t`, counted with multiplicity, number at most a constant times `log (q (|t| + 2))`.
PROVED in RouteWindow508 from the Jensen count of PNTPort U1482 and the functional
equation. -/
theorem zero_window_count508 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
      (Z : Finset ℂ),
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im - t| ≤ 1) →
      ∑ ρ ∈ Z, (mult χ ρ : ℝ) ≤ A * Real.log ((q : ℝ) * (|t| + 2)) := by
  exact zero_window_count_full508

/-- P0029 page 11 display 3.7, the zero list counted with multiplicity and reciprocal
weight, under the zero bound hypothesis. The zeros are sorted by the integer part of the
ordinate; each window holds at most a constant times `log X` of them by
`zero_window_count508`, and the reciprocal weights of the windows sum to a harmonic sum. -/
theorem zero_reciprocal_multiplicity_zeroBound508 (Θ : ℝ) (hΘ : Θ < 3 / 4)
    (hZ : ZeroBound Θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X →
      ∀ χ : DirichletCharacter ℂ q, ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ ≤ K * (X : ℝ) ^ ε := by
  obtain ⟨A, hA0, hA⟩ := zero_window_count508
  refine ⟨360 * A * (2 / ε) ^ 2, by positivity, ?_⟩
  intro X hX2 q _ hqQ χ T hT Z hZset
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hXr
  have hlog : 1 ≤ 2 * Real.log X := by
    have := Real.log_two_gt_d9
    linarith
  have hL0 : 0 ≤ Real.log X := by linarith
  have h3 : 2 * (X : ℝ) + 4 ≤ (X : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hXr) (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ 2 + 2 * X + 2)]
  have hmaps : ∀ ρ ∈ Z, ⌊ρ.im⌋ ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ) := by
    intro ρ hρ
    obtain ⟨-, -, -, him⟩ := (hZset ρ).mp hρ
    have h2 : |ρ.im| ≤ 2 * (X : ℝ) := him.trans hT.2
    obtain ⟨ha, hb⟩ := abs_le.mp h2
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · have hf := Int.floor_le ρ.im
      have : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ (((2 * X + 1 : ℕ) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hfib : ∀ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
      ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖ ≤
        36 * A * Real.log X * (1 / (|(k : ℝ)| + 1)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkR : |(k : ℝ)| ≤ 2 * (X : ℝ) + 1 := by
      rw [abs_le]
      constructor
      · have : ((-((2 * X + 1 : ℕ) : ℤ) : ℤ) : ℝ) ≤ k := by exact_mod_cast hk.1
        push_cast at this; linarith
      · have : ((k : ℤ) : ℝ) ≤ (((2 * X + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hk.2
        push_cast at this; linarith
    have hwin : ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) ≤
        A * Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) := by
      apply hA q χ ((k : ℝ) + 1 / 2)
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h0, h1, _⟩ := (hZset ρ).mp hρ.1
      refine ⟨hz, h0, h1, ?_⟩
      have e1 := Int.floor_le ρ.im
      have e2 := Int.lt_floor_add_one ρ.im
      rw [hρ.2] at e1 e2
      rw [abs_le]; constructor <;> linarith
    have hlogq : Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) ≤ 4 * Real.log X := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
      have hqX : (q : ℝ) ≤ X := by exact_mod_cast hqQ.trans (Nat.sqrt_le_self X)
      have habs : |(k : ℝ) + 1 / 2| ≤ 2 * (X : ℝ) + 2 := by
        have := abs_le.mp hkR
        rw [abs_le]; constructor <;> linarith
      have hle : (q : ℝ) * (|(k : ℝ) + 1 / 2| + 2) ≤ (X : ℝ) ^ 4 := by
        calc (q : ℝ) * (|(k : ℝ) + 1 / 2| + 2) ≤ (X : ℝ) * (2 * (X : ℝ) + 4) :=
              mul_le_mul hqX (by linarith) (by positivity) (by positivity)
          _ ≤ (X : ℝ) * (X : ℝ) ^ 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (X : ℝ) ^ 4 := by ring
      calc Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) ≤ Real.log ((X : ℝ) ^ 4) :=
            Real.log_le_log (mul_pos (by linarith) (by positivity)) hle
        _ = 4 * Real.log X := by rw [Real.log_pow]; norm_num
    have hterm : ∀ ρ ∈ Z.filter (fun ρ => ⌊ρ.im⌋ = k),
        (mult χ ρ : ℝ) / ‖ρ‖ ≤ (mult χ ρ : ℝ) * (9 / (|(k : ℝ)| + 1)) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h0, h1, _⟩ := (hZset ρ).mp hρ.1
      have hn := character_zero_norm_lower508 hΘ hZ χ hz h0 h1
      have him : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
      have e1 := Int.floor_le ρ.im
      have e2 := Int.lt_floor_add_one ρ.im
      rw [hρ.2] at e1 e2
      have hk1 : |(k : ℝ)| ≤ |ρ.im| + 1 := by
        have := le_abs_self ρ.im
        have := neg_abs_le ρ.im
        rw [abs_le]; constructor <;> linarith
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
      linarith
    have hpos : (0 : ℝ) ≤ 9 / (|(k : ℝ)| + 1) := by positivity
    calc ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖
        ≤ ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) * (9 / (|(k : ℝ)| + 1)) :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ)) * (9 / (|(k : ℝ)| + 1)) := by
          rw [Finset.sum_mul]
      _ ≤ (A * (4 * Real.log X)) * (9 / (|(k : ℝ)| + 1)) :=
          mul_le_mul_of_nonneg_right
            (hwin.trans (mul_le_mul_of_nonneg_left hlogq hA0)) hpos
      _ = 36 * A * Real.log X * (1 / (|(k : ℝ)| + 1)) := by ring
  have hharm : 2 * (1 + Real.log (((2 * X + 1 : ℕ) : ℝ) + 1)) ≤ 10 * Real.log X := by
    have hle : (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ (X : ℝ) ^ 3 := by push_cast; linarith
    have : Real.log (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ 3 * Real.log X := by
      calc Real.log (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ Real.log ((X : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) hle
        _ = 3 * Real.log X := by rw [Real.log_pow]; norm_num
    linarith
  have hbud := log_sq_power_budget508 hX1 hε
  calc ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖
      = ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
          ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖ :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
          36 * A * Real.log X * (1 / (|(k : ℝ)| + 1)) := Finset.sum_le_sum hfib
    _ = 36 * A * Real.log X *
          ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
            1 / (|(k : ℝ)| + 1) := by rw [Finset.mul_sum]
    _ ≤ 36 * A * Real.log X * (10 * Real.log X) :=
        mul_le_mul_of_nonneg_left ((int_abs_harmonic508 (2 * X + 1)).trans hharm)
          (by positivity)
    _ = 360 * A * Real.log X ^ 2 := by ring
    _ ≤ 360 * A * ((2 / ε) ^ 2 * (X : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hbud (by positivity)
    _ = 360 * A * (2 / ε) ^ 2 * (X : ℝ) ^ ε := by ring

/-- P0029 pages 11 and 12 displays 3.5 through 3.7 and page 15 display 4.6, the sealed sharp
oscillatory zero mode estimate with the reciprocal zero count taken under the zero bound
hypothesis. CONDITIONAL on the cited window count `zero_window_count508` only. It uses
neither `zero_mode_large_frequency508` nor `zero_reciprocal_multiplicity508`. -/
theorem oscillatory_zero_modes508_route_count (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
          ‖zeroTwist508 χ Z X β‖ ≤
            C * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * X) := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := zero_reciprocal_multiplicity_zeroBound508 Θ hΘ hZ ε hε
  refine ⟨4000 * K, by positivity, ?_⟩
  intro X hX2 q _ hqQ χ T hT Z hZset β hβ
  have hX1 : 1 ≤ X := by omega
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hΘ1 : 1 / 2 ≤ Θ := zeroBound_lower150 hZ
  have hS1 : (1 : ℝ) ≤ Real.sqrt (1 + |β| * (X : ℝ)) :=
    Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (abs_nonneg β) (Nat.cast_nonneg X)])
  have hKsum := hK X hX2 q hqQ χ T hT Z hZset
  have hterm : ∀ ρ ∈ Z,
      ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖ ≤
      (mult χ ρ : ℝ) *
        (4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, him⟩ := (hZset ρ).mp hρ
    have hρT : |ρ.im| ≤ 2 * (X : ℝ) := him.trans hT.2
    have hρΘ : ρ.re ≤ Θ := hZ q χ ρ hz h0 h1
    have hnn : (0 : ℝ) ≤ 4000 * (X : ℝ) ^ Θ / ‖ρ‖ := by positivity
    have hmode : ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
        4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ)) := by
      rcases le_total (|β| * (X : ℝ)) 1 with hs | hl
      · refine (zero_mode_small_frequency508 hΘ1 hX1 h0 hρΘ hs).trans ?_
        have h8 : 8 * (X : ℝ) ^ Θ / ‖ρ‖ ≤ 4000 * (X : ℝ) ^ Θ / ‖ρ‖ := by
          have hp : (0 : ℝ) ≤ (X : ℝ) ^ Θ / ‖ρ‖ := by positivity
          have e1 : 8 * (X : ℝ) ^ Θ / ‖ρ‖ = 8 * ((X : ℝ) ^ Θ / ‖ρ‖) := by ring
          have e2 : 4000 * (X : ℝ) ^ Θ / ‖ρ‖ = 4000 * ((X : ℝ) ^ Θ / ‖ρ‖) := by ring
          rw [e1, e2]; linarith
        nlinarith [hnn, hS1, h8]
      · refine (zero_mode_large_frequency_height508 hΘ1 hX1 h0 hρΘ hρT hl).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by linarith)) hnn
    calc ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
          ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖
        = (mult χ ρ : ℝ) * ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
            ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
              (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ ≤ (mult χ ρ : ℝ) *
            (4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) :=
          mul_le_mul_of_nonneg_left hmode (by positivity)
  unfold zeroTwist508
  calc ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖
      ≤ ∑ ρ ∈ Z, ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
          ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, (mult χ ρ : ℝ) *
          (4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = 4000 * (X : ℝ) ^ Θ * Real.sqrt (1 + |β| * (X : ℝ)) *
          ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
    _ ≤ 4000 * (X : ℝ) ^ Θ * Real.sqrt (1 + |β| * (X : ℝ)) * (K * (X : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hKsum (by positivity)
    _ = 4000 * K * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * (X : ℝ)) := by
        rw [Real.rpow_add hXp]
        ring

end LeanLab.BhowmikGrimmelt2026
