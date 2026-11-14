module

public import LeanLab.PNTPort.Vinogradov.TypeI

/-!
# Vinogradov's minor arc bound, the bilinear Type II block

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input.

* `G_neg`: `G Y (-θ) = G Y θ`.
* `sum_G_diff_le`: for `1 ≤ k₁ ≤ K`, `∑_{1 ≤ k₂ ≤ K} G M (α(k₁ - k₂)) ≤ M + 2 ∑_{1 ≤ ℓ ≤ K} G M (αℓ)`.
* `bilinear_block`: for real `A`, `b`, with `K = N / M`,
  `‖∑_{M < m ≤ 2M} A m ∑_{k ≤ N/m} b k e(αmk)‖² ≤ (∑ A²)(∑_{k ≤ K} b²) W`
  whenever `∑_{k₂ ≤ K} G M (α(k₁ - k₂)) ≤ W` for every `k₁ ≤ K`. Cauchy-Schwarz in `m`, then
  the `m` sum for fixed `k₁, k₂` is a geometric sum over an interval of length at most `M`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open LeanLab.PNTPort.LargeSieve

lemma G_neg (Y θ : ℝ) : G Y (-θ) = G Y θ := by unfold G; rw [dist0_neg]

lemma sum_G_diff_le {M : ℝ} (hM : 0 ≤ M) (α : ℝ) {K k₁ : ℕ} (hk : k₁ ∈ Icc 1 K) :
    ∑ k₂ ∈ Icc 1 K, G M (α * ((k₁ : ℝ) - k₂)) ≤
      M + 2 * ∑ ℓ ∈ Icc 1 K, G M (α * ℓ) := by
  have hk' := mem_Icc.1 hk
  have hgl : ∀ ℓ : ℕ, 0 ≤ G M (α * ℓ) := fun ℓ => G_nonneg hM _
  rw [← sum_filter_add_sum_filter_not (Icc 1 K) (fun k₂ => k₂ < k₁),
    ← sum_filter_add_sum_filter_not ((Icc 1 K).filter (fun k₂ => ¬ k₂ < k₁)) (fun k₂ => k₂ = k₁)]
  have hA : ∑ k₂ ∈ (Icc 1 K).filter (fun k₂ => k₂ < k₁), G M (α * ((k₁ : ℝ) - k₂)) ≤
      ∑ ℓ ∈ Icc 1 K, G M (α * ℓ) := by
    set s := (Icc 1 K).filter (fun k₂ => k₂ < k₁) with hs
    have hinj : Set.InjOn (fun k₂ => k₁ - k₂) (s : Set ℕ) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, hs, mem_filter, mem_Icc] at hx hy
      simp only at hxy; omega
    calc ∑ k₂ ∈ s, G M (α * ((k₁ : ℝ) - k₂))
          = ∑ k₂ ∈ s, G M (α * ((k₁ - k₂ : ℕ) : ℝ)) := by
          refine sum_congr rfl fun k₂ hk₂ => ?_
          rw [hs, mem_filter] at hk₂
          rw [Nat.cast_sub hk₂.2.le]
      _ = ∑ ℓ ∈ s.image (fun k₂ => k₁ - k₂), G M (α * (ℓ : ℝ)) :=
          (sum_image (f := fun ℓ : ℕ => G M (α * (ℓ : ℝ))) hinj).symm
      _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro ℓ hℓ
            obtain ⟨k₂, hk₂, rfl⟩ := mem_image.1 hℓ
            rw [hs, mem_filter, mem_Icc] at hk₂
            rw [mem_Icc]; omega
          · intro ℓ _ _; exact hgl ℓ
  have hC : ∑ k₂ ∈ ((Icc 1 K).filter (fun k₂ => ¬ k₂ < k₁)).filter (fun k₂ => ¬ k₂ = k₁),
      G M (α * ((k₁ : ℝ) - k₂)) ≤ ∑ ℓ ∈ Icc 1 K, G M (α * ℓ) := by
    set s := ((Icc 1 K).filter (fun k₂ => ¬ k₂ < k₁)).filter (fun k₂ => ¬ k₂ = k₁) with hs
    have hinj : Set.InjOn (fun k₂ => k₂ - k₁) (s : Set ℕ) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, hs, mem_filter, mem_filter, mem_Icc] at hx hy
      simp only at hxy; omega
    calc ∑ k₂ ∈ s, G M (α * ((k₁ : ℝ) - k₂)) = ∑ k₂ ∈ s, G M (α * ((k₂ - k₁ : ℕ) : ℝ)) := by
          refine sum_congr rfl fun k₂ hk₂ => ?_
          rw [hs, mem_filter, mem_filter] at hk₂
          rw [Nat.cast_sub (by omega), ← G_neg]
          congr 1; ring
      _ = ∑ ℓ ∈ s.image (fun k₂ => k₂ - k₁), G M (α * (ℓ : ℝ)) :=
          (sum_image (f := fun ℓ : ℕ => G M (α * (ℓ : ℝ))) hinj).symm
      _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro ℓ hℓ
            obtain ⟨k₂, hk₂, rfl⟩ := mem_image.1 hℓ
            rw [hs, mem_filter, mem_filter, mem_Icc] at hk₂
            rw [mem_Icc]; omega
          · intro ℓ _ _; exact hgl ℓ
  have hB : ∑ k₂ ∈ ((Icc 1 K).filter (fun k₂ => ¬ k₂ < k₁)).filter (fun k₂ => k₂ = k₁),
      G M (α * ((k₁ : ℝ) - k₂)) ≤ M := by
    have : ((Icc 1 K).filter (fun k₂ => ¬ k₂ < k₁)).filter (fun k₂ => k₂ = k₁) = {k₁} := by
      ext x; simp only [mem_filter, mem_Icc, mem_singleton]; omega
    rw [this, sum_singleton]
    exact G_le _ _
  linarith

/-- The `m`-set where both `m k₁ ≤ N` and `m k₂ ≤ N`, inside `(M, 2M]`, is an interval. -/
lemma filter_Ioc_eq (M N k₁ k₂ : ℕ) (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂) :
    (Ioc M (M + M)).filter (fun m => m * k₁ ≤ N ∧ m * k₂ ≤ N) =
      Ioc M (M + min M (min (N / k₁) (N / k₂) - M)) := by
  ext m
  simp only [mem_filter, mem_Ioc]
  rw [← Nat.le_div_iff_mul_le (by omega), ← Nat.le_div_iff_mul_le (by omega)]
  omega

lemma e_mul_conj (x y : ℝ) : e x * (starRingEnd ℂ) (e y) = e (x - y) := by
  rw [← e_neg, ← e_add]; ring_nf

/-- The bilinear block bound. -/
theorem bilinear_block (A b : ℕ → ℝ) (N M : ℕ) (α : ℝ) {W : ℝ}
    (hW : ∀ k₁ ∈ Icc 1 (N / M), ∑ k₂ ∈ Icc 1 (N / M), G M (α * ((k₁ : ℝ) - k₂)) ≤ W) :
    ‖∑ m ∈ Ioc M (M + M), ∑ k ∈ Icc 1 (N / m), ((A m * b k : ℝ) : ℂ) * e ((m * k : ℕ) * α)‖ ^ 2
      ≤ (∑ m ∈ Ioc M (M + M), A m ^ 2) * (∑ k ∈ Icc 1 (N / M), b k ^ 2) * W := by
  set K := N / M with hK
  set c : ℕ → ℕ → ℂ := fun m k =>
    if m * k ≤ N then (b k : ℂ) * e ((m * k : ℕ) * α) else 0 with hc
  set x : ℕ → ℂ := fun m => ∑ k ∈ Icc 1 K, c m k with hx
  -- step 1: rewrite the inner sums
  have hstep1 : ∀ m ∈ Ioc M (M + M),
      ∑ k ∈ Icc 1 (N / m), ((A m * b k : ℝ) : ℂ) * e ((m * k : ℕ) * α) = (A m : ℂ) * x m := by
    intro m hm
    have hm' := mem_Ioc.1 hm
    have hmono : N / m ≤ N / M := Nat.div_le_div_left hm'.1.le (by omega)
    have hfilt : (Icc 1 K).filter (fun k => m * k ≤ N) = Icc 1 (N / m) := by
      ext k
      simp only [mem_filter, mem_Icc]
      rw [Nat.le_div_iff_mul_le (by omega : 0 < m), Nat.mul_comm k m]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        rw [hK]; refine le_trans ?_ hmono
        rw [Nat.le_div_iff_mul_le (by omega : 0 < m), Nat.mul_comm k m]; exact h3
    rw [← hfilt, sum_filter, hx, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [hc]
    split_ifs
    · push_cast; ring
    · simp
  rw [sum_congr rfl hstep1]
  -- step 2: Cauchy-Schwarz
  have hCS : ‖∑ m ∈ Ioc M (M + M), (A m : ℂ) * x m‖ ^ 2 ≤
      (∑ m ∈ Ioc M (M + M), A m ^ 2) * ∑ m ∈ Ioc M (M + M), ‖x m‖ ^ 2 := by
    have h1 : ‖∑ m ∈ Ioc M (M + M), (A m : ℂ) * x m‖ ≤ ∑ m ∈ Ioc M (M + M), |A m| * ‖x m‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun m _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := sum_mul_sq_le_sq_mul_sq (Ioc M (M + M)) (fun m => |A m|) (fun m => ‖x m‖)
    simp only [sq_abs] at h2
    calc _ ≤ (∑ m ∈ Ioc M (M + M), |A m| * ‖x m‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  refine hCS.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun m _ => sq_nonneg _)
  -- step 3: expand the squares
  have hexp : ∑ m ∈ Ioc M (M + M), ‖x m‖ ^ 2 ≤
      ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K,
        ‖∑ m ∈ Ioc M (M + M), c m k₁ * (starRingEnd ℂ) (c m k₂)‖ := by
    have hm : ∀ m, ((‖x m‖ : ℝ) : ℂ) ^ 2 =
        ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, c m k₁ * (starRingEnd ℂ) (c m k₂) := by
      intro m
      rw [← Complex.mul_conj', hx]
      simp only
      rw [map_sum, sum_mul_sum]
    have h1 : ((∑ m ∈ Ioc M (M + M), ‖x m‖ ^ 2 : ℝ) : ℂ) =
        ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K,
          ∑ m ∈ Ioc M (M + M), c m k₁ * (starRingEnd ℂ) (c m k₂) := by
      push_cast
      rw [sum_congr rfl (fun m _ => hm m), sum_comm]
      exact sum_congr rfl fun k₁ _ => sum_comm
    have h2 : ∑ m ∈ Ioc M (M + M), ‖x m‖ ^ 2 =
        ‖((∑ m ∈ Ioc M (M + M), ‖x m‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun m _ => sq_nonneg _)]
    rw [h2, h1]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k₁ _ => norm_sum_le _ _)
  refine hexp.trans ?_
  -- step 4: each m sum is a geometric sum
  have hpair : ∀ k₁ ∈ Icc 1 K, ∀ k₂ ∈ Icc 1 K,
      ‖∑ m ∈ Ioc M (M + M), c m k₁ * (starRingEnd ℂ) (c m k₂)‖ ≤
        |b k₁| * |b k₂| * G M (α * ((k₁ : ℝ) - k₂)) := by
    intro k₁ hk₁ k₂ hk₂
    have h1 := (mem_Icc.1 hk₁).1
    have h2 := (mem_Icc.1 hk₂).1
    have hsum : ∑ m ∈ Ioc M (M + M), c m k₁ * (starRingEnd ℂ) (c m k₂) =
        ((b k₁ * b k₂ : ℝ) : ℂ) * ∑ m ∈ (Ioc M (M + M)).filter (fun m => m * k₁ ≤ N ∧ m * k₂ ≤ N),
          e (m * (α * ((k₁ : ℝ) - k₂))) := by
      rw [mul_sum, sum_filter]
      refine sum_congr rfl fun m _ => ?_
      simp only [hc]
      by_cases ha : m * k₁ ≤ N
      · by_cases hb : m * k₂ ≤ N
        · rw [if_pos ha, if_pos hb, if_pos ⟨ha, hb⟩, map_mul, Complex.conj_ofReal,
            mul_mul_mul_comm, e_mul_conj]
          rw [show ((m * k₁ : ℕ) : ℝ) * α - ((m * k₂ : ℕ) : ℝ) * α = m * (α * ((k₁ : ℝ) - k₂)) by
            push_cast; ring]
          push_cast; ring
        · rw [if_neg hb, if_neg (show ¬(m * k₁ ≤ N ∧ m * k₂ ≤ N) from fun h => hb h.2)]; simp
      · rw [if_neg ha, if_neg (show ¬(m * k₁ ≤ N ∧ m * k₂ ≤ N) from fun h => ha h.1)]; simp
    rw [hsum, filter_Ioc_eq M N k₁ k₂ h1 h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sum_Ioc_e_le _ _ _).trans (G_mono ?_ _)
    exact_mod_cast min_le_left _ _
  refine (sum_le_sum fun k₁ hk₁ => sum_le_sum fun k₂ hk₂ => hpair k₁ hk₁ k₂ hk₂).trans ?_
  -- step 5: AM-GM and symmetry
  have hG : ∀ k₁ k₂ : ℕ, 0 ≤ G M (α * ((k₁ : ℝ) - k₂)) := fun _ _ => G_nonneg (Nat.cast_nonneg M) _
  have hsym : ∀ k₁ k₂ : ℕ, G M (α * ((k₁ : ℝ) - k₂)) = G M (α * ((k₂ : ℝ) - k₁)) := by
    intro k₁ k₂; rw [← G_neg]; congr 1; ring
  set F : ℕ → ℕ → ℝ := fun k₁ k₂ => b k₁ ^ 2 / 2 * G M (α * ((k₁ : ℝ) - k₂)) with hF
  have hcomm : ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, F k₂ k₁ = ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, F k₁ k₂ :=
    Finset.sum_comm
  calc ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, |b k₁| * |b k₂| * G M (α * ((k₁ : ℝ) - k₂))
      ≤ ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, (F k₁ k₂ + F k₂ k₁) := by
        refine sum_le_sum fun k₁ _ => sum_le_sum fun k₂ _ => ?_
        simp only [hF]
        rw [← hsym k₁ k₂, ← add_mul]
        apply mul_le_mul_of_nonneg_right _ (hG k₁ k₂)
        have := sq_nonneg (|b k₁| - |b k₂|)
        rw [← sq_abs (b k₁), ← sq_abs (b k₂)]
        nlinarith
    _ = 2 * ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, F k₁ k₂ := by
        simp only [sum_add_distrib]; rw [hcomm]; ring
    _ = ∑ k₁ ∈ Icc 1 K, b k₁ ^ 2 * ∑ k₂ ∈ Icc 1 K, G M (α * ((k₁ : ℝ) - k₂)) := by
        rw [mul_sum]
        refine sum_congr rfl fun k₁ _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun k₂ _ => ?_
        simp only [hF]; ring
    _ ≤ ∑ k₁ ∈ Icc 1 K, b k₁ ^ 2 * W := by
        refine sum_le_sum fun k₁ hk₁ => mul_le_mul_of_nonneg_left (hW k₁ hk₁) (sq_nonneg _)
    _ = (∑ k ∈ Icc 1 K, b k ^ 2) * W := by rw [sum_mul]

end LeanLab.PNTPort.Vinogradov

