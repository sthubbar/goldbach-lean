module

public import LeanLab.PNTPort.Vinogradov.Basic

/-!
# P0058 Languasco-Zaccagnini 2016, Lemma 5, explicit

Lab proof, unit U-5855, CLOUD 20261020T0014Z-cloud30. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 4, (7) and Lemma 5: with `t_H(m) = H - |m|` and
`T_H(N, y; α) = ∑_{N - H ≤ n ≤ N + y} t_H(n - N) e(nα)`, for integers `1 ≤ H ≤ N`,
`T_H(N, y; α) ≪ H min(H, 1/‖α‖)` for `y ∈ [-H, H)` and `T_H(N, H; α) ≪ min(H², 1/‖α‖²)`.

Here, with `G H α = min(H, 1/(2‖α‖))`, read as `H` when `‖α‖ = 0`, the lab's
`PNTPort.Vinogradov.G`:
* `lemma5_partial`: `‖T_H(N, y; α)‖ ≤ 3 H G H α` for every real `y ∈ [-H, H)`;
* `lemma5_full`: `T_H(N, H; α) = e(Nα) ‖∑_{0 < j ≤ H} e(jα)‖²`, so `‖T_H(N, H; α)‖ ≤ (G H α)²`.
The first is Abel summation with partial sums of `e(nα)` at most `1/(2‖α‖)` and weights of
total variation below `2H`; the second is the Fejér identity the paper uses.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

/-- `T_H(N, y; α) = ∑_{N - H ≤ n ≤ N + y} (H - |n - N|) e(nα)`, the paper's (7). -/
noncomputable def TH (N H : ℕ) (y α : ℝ) : ℂ :=
  ∑ n ∈ (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + y),
    (((H : ℝ) - |(n : ℝ) - N| : ℝ) : ℂ) * e (n * α)

/-- Abel summation on an interval `[A, A + L)`: weights bounded by `H` with steps at most `1`
against `e(nα)` give at most `(H + L) / (2‖α‖)`. -/
lemma abel_interval (A L : ℕ) (w : ℕ → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hw : ∀ j < L, |w (A + j)| ≤ H)
    (hstep : ∀ n, |w (n + 1) - w n| ≤ 1) {α : ℝ} (hα : 0 < dist0 α) :
    ‖∑ j ∈ range L, ((w (A + j) : ℝ) : ℂ) * e ((A + j : ℕ) * α)‖
      ≤ (H + L) * (1 / (2 * dist0 α)) := by
  set Gs : ℕ → ℂ := fun k => ∑ j ∈ range k, e ((A + j : ℕ) * α) with hGs
  have hG : ∀ k, ‖Gs k‖ ≤ 1 / (2 * dist0 α) := by
    intro k
    have : Gs k = e (A * α) * ∑ j ∈ range k, e (j * α) := by
      rw [hGs, mul_sum]; refine sum_congr rfl fun j _ => ?_
      rw [← e_add]; congr 1; push_cast; ring
    rw [this, norm_mul, norm_e, one_mul]
    exact norm_geom_le k hα
  rcases Nat.eq_zero_or_pos L with hL0 | hL0
  · subst hL0; simp only [sum_range_zero, norm_zero, CharP.cast_eq_zero, add_zero]; positivity
  have hparts := sum_range_by_parts (fun j => w (A + j)) (fun j => e ((A + j : ℕ) * α)) L
  have hsmul : ∀ j, ((w (A + j) : ℝ) : ℂ) * e ((A + j : ℕ) * α)
      = (w (A + j)) • e ((A + j : ℕ) * α) := fun j => by rw [Complex.real_smul]
  simp_rw [hsmul]
  rw [hparts]
  have hD : 0 ≤ 1 / (2 * dist0 α) := by positivity
  calc ‖w (A + (L - 1)) • Gs L - ∑ i ∈ range (L - 1),
          (w (A + (i + 1)) - w (A + i)) • Gs (i + 1)‖
      ≤ ‖w (A + (L - 1)) • Gs L‖ + ‖∑ i ∈ range (L - 1),
          (w (A + (i + 1)) - w (A + i)) • Gs (i + 1)‖ := norm_sub_le _ _
    _ ≤ H * (1 / (2 * dist0 α)) + ∑ i ∈ range (L - 1), 1 * (1 / (2 * dist0 α)) := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hw (L - 1) (by omega)) (hG L) (norm_nonneg _) hH
        · refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (by simpa [add_assoc] using hstep (A + i)) (hG _) (norm_nonneg _)
            zero_le_one
    _ ≤ (H + L) * (1 / (2 * dist0 α)) := by
        rw [sum_const, card_range, nsmul_eq_mul, one_mul, ← add_mul]
        apply mul_le_mul_of_nonneg_right _ hD
        have : ((L - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
        linarith

/-- The summation range of `T_H(N, y; α)` is the interval `[N - H, N - H + L)` with `L ≤ 2H`. -/
lemma range_TH {N H : ℕ} (hHN : H ≤ N) {y : ℝ} (hy0 : -(H : ℝ) ≤ y) (hyH : y < H) :
    ∃ L ≤ 2 * H, (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + y)
      = (range L).map (addLeftEmbedding (N - H)) := by
  set M := ⌊(N : ℝ) + y⌋₊ with hM
  have hpos : (0 : ℝ) ≤ N + y := by
    have : (H : ℝ) ≤ N := by exact_mod_cast hHN
    linarith
  have hM1 : ((N - H : ℕ) : ℝ) ≤ N + y := by
    rw [Nat.cast_sub hHN]; linarith
  have hM2 : N - H ≤ M := Nat.le_floor hM1
  have hM3 : M < N + H := by
    rw [hM, Nat.floor_lt hpos]; push_cast; linarith
  refine ⟨M + 1 - (N - H), by omega, ?_⟩
  ext n
  simp only [mem_filter, mem_Icc, mem_map, mem_range, addLeftEmbedding_apply]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    have : n ≤ M := Nat.le_floor h3
    exact ⟨n - (N - H), by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have : N - H + j ≤ M := by omega
    calc ((N - H + j : ℕ) : ℝ) ≤ M := by exact_mod_cast this
      _ ≤ N + y := Nat.floor_le hpos

/-- **Lemma 5, first part, explicit**: `‖T_H(N, y; α)‖ ≤ 3 H min(H, 1/(2‖α‖))` for
`y ∈ [-H, H)`. -/
theorem lemma5_partial {N H : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) {y : ℝ} (hy0 : -(H : ℝ) ≤ y)
    (hyH : y < H) (α : ℝ) : ‖TH N H y α‖ ≤ 3 * H * G H α := by
  obtain ⟨L, hL, hset⟩ := range_TH hHN hy0 hyH
  set w : ℕ → ℝ := fun n => (H : ℝ) - |(n : ℝ) - N| with hw
  have hT : TH N H y α = ∑ j ∈ range L, ((w (N - H + j) : ℝ) : ℂ) * e ((N - H + j : ℕ) * α) := by
    unfold TH; rw [hset, sum_map]; rfl
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hLr : (L : ℝ) ≤ 2 * H := by exact_mod_cast hL
  -- on the range the weights lie in `[0, H]`
  have hwj : ∀ j < L, |w (N - H + j)| ≤ H := by
    intro j hj
    have hn : (N - H + j : ℕ) ≤ N + H := by omega
    have h1 : ((N - H + j : ℕ) : ℝ) ≤ N + H := by exact_mod_cast hn
    have h2 : (N : ℝ) - H ≤ ((N - H + j : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hHN]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hab : |((N - H + j : ℕ) : ℝ) - N| ≤ H := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hw]; dsimp only
    rw [abs_of_nonneg (by linarith)]
    linarith [abs_nonneg (((N - H + j : ℕ) : ℝ) - N)]
  -- the trivial bound `2 H²`
  have htriv : ‖TH N H y α‖ ≤ 2 * H * H := by
    rw [hT]
    calc ‖∑ j ∈ range L, ((w (N - H + j) : ℝ) : ℂ) * e ((N - H + j : ℕ) * α)‖
        ≤ ∑ j ∈ range L, ‖((w (N - H + j) : ℝ) : ℂ) * e ((N - H + j : ℕ) * α)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ range L, (H : ℝ) := by
          refine sum_le_sum fun j hj => ?_
          rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact hwj j (mem_range.mp hj)
      _ = L * H := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ 2 * H * H := mul_le_mul_of_nonneg_right hLr (by positivity)
  have hstep : ∀ n, |w (n + 1) - w n| ≤ 1 := by
    intro n; rw [hw]; dsimp only
    have := abs_abs_sub_abs_le (((n + 1 : ℕ) : ℝ) - N) ((n : ℝ) - N)
    rw [show ((n + 1 : ℕ) : ℝ) - N - ((n : ℝ) - N) = 1 by push_cast; ring, abs_one] at this
    rw [show (H : ℝ) - |((n + 1 : ℕ) : ℝ) - N| - ((H : ℝ) - |(n : ℝ) - N|)
        = -(|((n + 1 : ℕ) : ℝ) - N| - |(n : ℝ) - N|) by ring, abs_neg]
    exact this
  unfold G
  split_ifs with h0
  · nlinarith
  · have hα : 0 < dist0 α := lt_of_le_of_ne (dist0_nonneg α) (Ne.symm h0)
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min (by nlinarith) ?_
    have hab := abel_interval (N - H) L w (H := H) (by positivity) hwj hstep hα
    rw [← hT] at hab
    refine hab.trans ?_
    rw [mul_one_div, mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

/-- The Fejér identity `∑_{|m| ≤ H} (H - |m|) e((N + m)α) = e(Nα) ‖∑_{0 < j ≤ H} e(jα)‖²`. -/
lemma fiber_card {N H n : ℕ} (hn : n ∈ Icc (N - H) (N + H)) (hHN : H ≤ N) :
    (((Ioc 0 H ×ˢ Ioc 0 H).filter (fun p : ℕ × ℕ => N + p.1 - p.2 = n)).card : ℝ)
      = (H : ℝ) - |(n : ℝ) - N| := by
  rw [mem_Icc] at hn
  rcases le_or_gt N n with h | h
  · have hset : (Ioc 0 H ×ˢ Ioc 0 H).filter (fun p : ℕ × ℕ => N + p.1 - p.2 = n)
        = (Ioc 0 (H - (n - N))).image (fun k => (k + (n - N), k)) := by
      ext ⟨j, k⟩
      simp only [mem_filter, mem_product, mem_Ioc, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩; exact ⟨k, ⟨by omega, by omega⟩, by omega, rfl⟩
      · rintro ⟨k', ⟨h1, h2⟩, rfl, rfl⟩; refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩
    rw [hset, card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).2), Nat.card_Ioc,
      Nat.sub_zero, Nat.cast_sub (by omega), Nat.cast_sub h,
      abs_of_nonneg (by rw [sub_nonneg]; exact_mod_cast h)]
  · have hset : (Ioc 0 H ×ˢ Ioc 0 H).filter (fun p : ℕ × ℕ => N + p.1 - p.2 = n)
        = (Ioc 0 (H - (N - n))).image (fun j => (j, j + (N - n))) := by
      ext ⟨j, k⟩
      simp only [mem_filter, mem_product, mem_Ioc, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩; exact ⟨j, ⟨by omega, by omega⟩, rfl, by omega⟩
      · rintro ⟨j', ⟨h1, h2⟩, rfl, rfl⟩; refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩
    rw [hset, card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1), Nat.card_Ioc,
      Nat.sub_zero, Nat.cast_sub (by omega), Nat.cast_sub h.le,
      abs_of_neg (by rw [sub_neg]; exact_mod_cast h)]
    ring

/-- The Fejér identity `T_H(N, H; α) = e(Nα) ‖∑_{0 < j ≤ H} e(jα)‖²`. -/
theorem lemma5_full_eq {N H : ℕ} (hHN : H ≤ N) (α : ℝ) :
    TH N H H α = e (N * α) * ((‖∑ j ∈ Ioc 0 H, e (j * α)‖ ^ 2 : ℝ) : ℂ) := by
  have hfilt : (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + H) = Icc (N - H) (N + H) := by
    apply filter_true_of_mem; intro n hn; rw [mem_Icc] at hn; exact_mod_cast hn.2
  -- the right side as a sum over pairs
  have hR : e (N * α) * ((‖∑ j ∈ Ioc 0 H, e (j * α)‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ Ioc 0 H ×ˢ Ioc 0 H, e ((N + p.1 - p.2 : ℕ) * α) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum, mul_sum, sum_product]
    refine sum_congr rfl fun i hi => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hp : (i, j) ∈ Ioc 0 H ×ˢ Ioc 0 H := mem_product.mpr ⟨hi, hj⟩
    set p : ℕ × ℕ := (i, j)
    rw [mem_product, mem_Ioc, mem_Ioc] at hp
    rw [← e_neg, ← e_add, ← e_add]
    congr 1
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hR, ← sum_fiberwise_of_maps_to (s := Ioc 0 H ×ˢ Ioc 0 H) (t := Icc (N - H) (N + H))
    (g := fun p : ℕ × ℕ => N + p.1 - p.2)]
  · unfold TH; rw [hfilt]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_congr rfl (g := fun _ => e (n * α)) (fun p hp => by rw [(mem_filter.mp hp).2]),
      sum_const, nsmul_eq_mul, ← fiber_card hn hHN]
    push_cast; ring
  · intro p hp
    rw [mem_product, mem_Ioc, mem_Ioc] at hp
    rw [mem_Icc]; omega

/-- **Lemma 5, second part, explicit**: `‖T_H(N, H; α)‖ ≤ min(H, 1/(2‖α‖))²`. -/
theorem lemma5_full {N H : ℕ} (hHN : H ≤ N) (α : ℝ) : ‖TH N H H α‖ ≤ G H α ^ 2 := by
  rw [lemma5_full_eq hHN, norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h := norm_sum_Ioc_e_le 0 H α
  simp only [zero_add] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end LeanLab.LZCesaroShort

