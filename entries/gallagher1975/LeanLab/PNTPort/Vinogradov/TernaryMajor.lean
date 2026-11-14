module

public import LeanLab.PNTPort.Vinogradov.TernaryCircle
public import LeanLab.PNTPort.Vinogradov.MajorArc

/-!
# The ternary major arcs: complete sums of `V³`

Lab proof, unit U-5254. AI wrote this file. Known mathematics, no cited input.

* `J N n = #{(x, y, z) ∈ [1, N]³ : x + y + z = n}`.
* `full_sum_V3`: for `3N < M`, `n < M` and any real `γ`,
  `∑_{k mod M} V(-(k/M - γ))³ e(n(k/M - γ)) = M · J(n)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ZMod
open LeanLab.PNTPort.LargeSieve

/-- The number of `(x, y, z) ∈ [1, N]³` with `x + y + z = n`. -/
noncomputable def J (N n : ℕ) : ℝ :=
  ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, if x + y + z = n then (1 : ℝ) else 0

lemma V_neg_cube (N : ℕ) (θ : ℝ) (n : ℕ) :
    V N (-θ) ^ 3 * e (n * θ) = ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N,
      e (((n : ℤ) - x - y - z : ℤ) * θ) := by
  unfold V
  rw [pow_three]
  simp only [sum_mul, mul_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  rw [← e_add, ← e_add, ← e_add]
  congr 1; push_cast; ring

lemma sum_e_int_zmod {M : ℕ} [NeZero M] (m : ℤ) (hm : |m| < M) (γ : ℝ) :
    ∑ k : ZMod M, e (m * ((k.val : ℝ) / M - γ)) = if m = 0 then (M : ℂ) else 0 := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 : ∀ k : ZMod M, e (m * ((k.val : ℝ) / M - γ)) = e (-(m * γ)) * e (m * k.val / M) := by
    intro k; rw [← e_add]; congr 1; ring
  simp_rw [h1]
  rw [← mul_sum]
  have h2 := sum_zmod_eq_range (M := M) (fun c => e (m * c / M))
  rw [h2, sum_e_mul_div m hM]
  by_cases h0 : m = 0
  · subst h0; simp [e_zero]
  · have : ¬ (M : ℤ) ∣ m := by
      intro hd
      have := Int.eq_zero_of_abs_lt_dvd hd hm
      exact h0 this
    rw [if_neg this, if_neg h0, mul_zero]

/-- The complete sum. -/
theorem full_sum_V3 {N M : ℕ} [NeZero M] (h3 : 3 * N < M) {n : ℕ} (hn : n < M) (γ : ℝ) :
    ∑ k : ZMod M, V N (-((k.val : ℝ) / M - γ)) ^ 3 * e (n * ((k.val : ℝ) / M - γ)) =
      (M : ℂ) * (J N n : ℂ) := by
  simp_rw [V_neg_cube]
  rw [sum_comm]
  unfold J
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun y hy => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun z hz => ?_
  rw [mem_Icc] at hx hy hz
  have hs := sum_e_int_zmod (M := M) ((n : ℤ) - x - y - z)
    (by rw [abs_lt]; constructor <;> omega) γ
  push_cast at hs
  rw [hs]
  by_cases h : x + y + z = n
  · rw [if_pos (by omega), if_pos h]; simp
  · rw [if_neg (by omega), if_neg h]; simp

lemma V_neg_mul_V (N : ℕ) (θ : ℝ) :
    V N (-θ) * V N θ = ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, e (((y : ℤ) - x : ℤ) * θ) := by
  unfold V
  rw [sum_mul_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [← e_add]; congr 1; push_cast; ring

lemma norm_V_sq (N : ℕ) (θ : ℝ) : ((‖V N (-θ)‖ ^ 2 : ℝ) : ℂ) = V N (-θ) * V N θ := by
  have h : V N θ = (starRingEnd ℂ) (V N (-θ)) := by
    unfold V; rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [← e_neg]; congr 1; ring
  rw [h, Complex.mul_conj']; push_cast; ring

/-- Parseval for `V` on the shifted grid. -/
theorem sum_norm_V_sq {N M : ℕ} [NeZero M] (hNM : N < M) (γ : ℝ) :
    ∑ k : ZMod M, ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 = (M : ℝ) * N := by
  have h : ((∑ k : ZMod M, ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 : ℝ) : ℂ) = (M : ℂ) * N := by
    push_cast
    simp_rw [fun k : ZMod M => (by exact_mod_cast norm_V_sq N ((k.val : ℝ) / M - γ) :
      (‖V N (-((k.val : ℝ) / M - γ))‖ : ℂ) ^ 2 =
        V N (-((k.val : ℝ) / M - γ)) * V N ((k.val : ℝ) / M - γ)), V_neg_mul_V]
    rw [sum_comm]
    have hsum : ∀ x ∈ Icc 1 N, ∑ k : ZMod M, ∑ y ∈ Icc 1 N,
        e ((((y : ℤ) - x : ℤ) : ℝ) * ((k.val : ℝ) / M - γ)) = (M : ℂ) := by
      intro x hx
      rw [sum_comm]
      rw [sum_eq_single x]
      · have := sum_e_int_zmod (M := M) ((x : ℤ) - x) (by simp; exact NeZero.pos M) γ
        rw [this]; simp
      · intro y hy hne
        rw [mem_Icc] at hx hy
        rw [sum_e_int_zmod (M := M) ((y : ℤ) - x) (by rw [abs_lt]; constructor <;> omega) γ,
          if_neg (by omega)]
      · intro h; exact absurd hx h
    rw [sum_congr rfl hsum, sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast; ring
  exact_mod_cast h

/-- The tail off an arc of half-width `δ`. -/
theorem tail_V3_le {N M : ℕ} [NeZero M] (hNM : N < M) (γ : ℝ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (T : Finset (ZMod M)) (hT : ∀ k ∈ T, δ < dist0 ((k.val : ℝ) / M - γ)) :
    ‖∑ k ∈ T, V N (-((k.val : ℝ) / M - γ)) ^ 3 * e (n * ((k.val : ℝ) / M - γ))‖ ≤
      (M : ℝ) * N / (2 * δ) := by
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k ∈ T, ‖V N (-((k.val : ℝ) / M - γ)) ^ 3 * e (n * ((k.val : ℝ) / M - γ))‖ ≤
      1 / (2 * δ) * ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 := by
    intro k hk
    set θ := (k.val : ℝ) / M - γ
    have hd := hT k hk
    have h1 : ‖V N (-θ)‖ ≤ 1 / (2 * δ) := by
      have := norm_sum_Ioc_e_le 0 N (-θ)
      have hI : Ioc 0 (0 + N) = Icc 1 N := by ext m; simp only [mem_Ioc, mem_Icc]; omega
      rw [hI] at this
      unfold V
      refine this.trans ((G_le_inv (by rw [dist0_neg]; linarith)).trans ?_)
      rw [dist0_neg]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [norm_mul, norm_e, mul_one, norm_pow]
    have : ‖V N (-θ)‖ ^ 3 = ‖V N (-θ)‖ * ‖V N (-θ)‖ ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  refine (sum_le_sum hk).trans ?_
  rw [← mul_sum]
  calc 1 / (2 * δ) * ∑ k ∈ T, ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2
      ≤ 1 / (2 * δ) * ∑ k : ZMod M, ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
    _ = (M : ℝ) * N / (2 * δ) := by rw [sum_norm_V_sq hNM]; ring

/-- At most `2δM + 1` grid points are within `δ` of `γ` modulo one. -/
theorem card_arc_le {M : ℕ} [NeZero M] (γ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (((univ : Finset (ZMod M)).filter
      (fun k => dist0 ((k.val : ℝ) / M - γ) ≤ δ)).card : ℝ) ≤ 2 * δ * M + 1 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  set s := (univ : Finset (ZMod M)).filter (fun k => dist0 ((k.val : ℝ) / M - γ) ≤ δ)
  set f : ZMod M → ℤ := fun k => (k.val : ℤ) - M * round ((k.val : ℝ) / M - γ) with hf
  have hmem : ∀ k ∈ s, f k ∈ Finset.Icc ⌈M * γ - δ * M⌉ ⌊M * γ + δ * M⌋ := by
    intro k hk
    rw [mem_filter] at hk
    have hd := hk.2
    unfold dist0 at hd
    rw [abs_le] at hd
    rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
    have e1 : ((f k : ℤ) : ℝ) = M * ((k.val : ℝ) / M - γ - round ((k.val : ℝ) / M - γ)) + M * γ := by
      rw [hf]; push_cast; field_simp; ring
    rw [e1]
    constructor <;> nlinarith
  have hinj : Set.InjOn f s := by
    intro k₁ _ k₂ _ h
    simp only [hf] at h
    have h1 : (k₁.val : ℤ) % M = (k₂.val : ℤ) % M := by
      have : (k₁.val : ℤ) = k₂.val + M * (round ((k₁.val : ℝ) / M - γ) -
          round ((k₂.val : ℝ) / M - γ)) := by linarith
      rw [this, Int.add_mul_emod_self_left]
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ZMod.val_lt k₁),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ZMod.val_lt k₂)] at h1
    exact ZMod.val_injective M (by exact_mod_cast h1)
  have hc := card_le_card_of_injOn f hmem hinj
  rw [Int.card_Icc] at hc
  have h2 : ((⌊M * γ + δ * M⌋ + 1 - ⌈M * γ - δ * M⌉).toNat : ℝ) ≤ 2 * δ * M + 1 := by
    rcases le_or_gt (⌊M * γ + δ * M⌋ + 1 - ⌈M * γ - δ * M⌉) 0 with h | h
    · rw [Int.toNat_of_nonpos h]; push_cast; positivity
    · rw [show (((⌊M * γ + δ * M⌋ + 1 - ⌈M * γ - δ * M⌉).toNat : ℕ) : ℝ) =
          (((⌊M * γ + δ * M⌋ + 1 - ⌈M * γ - δ * M⌉ : ℤ)) : ℝ) by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg h.le]]
      push_cast
      have := Int.floor_le (M * γ + δ * M)
      have := Int.le_ceil (M * γ - δ * M)
      linarith
  exact le_trans (by exact_mod_cast hc) h2

end LeanLab.PNTPort.Vinogradov

