module

public import LeanLab.Song2020.Characteristic139

/-!
AI wrote the Lean code, Codex by OpenAI.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, page 3, Lemma 1.
This is the cited trigonometric majorant, with its coefficient families quantified together.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Repair591FourierMajorant

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

private theorem norm_eC591G (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : (2 * Real.pi * Complex.I * x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem geom_sum_eC591G (m : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range m, eC (t * (j : ℝ))) * (eC t - 1) = eC (t * (m : ℝ)) - 1 := by
  induction m with
  | zero => simp [eC]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h : eC (t * ((n + 1 : ℕ) : ℝ)) = eC (t * (n : ℝ)) * eC t := by
      unfold eC
      rw [← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [h]; ring

private theorem norm_eC_sub_one591G (t : ℝ) : ‖eC t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  unfold eC
  have h : (2 * Real.pi * Complex.I * t : ℂ) = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have h2 : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [h2]; simp

/-- A1. Geometric sum bounds for the Dirichlet type sum. -/
theorem geom_sum_bounds591 (m : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ ≤ (m : ℝ) ∧
    ‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ * (4 * min t (1 - t)) ≤ 2 := by
  have hpi := Real.pi_pos
  have hsin : 2 * min t (1 - t) ≤ Real.sin (Real.pi * t) := by
    rcases le_total t (1 / 2) with h | h
    · have h1 := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith)
      have h2 : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
      rw [h2] at h1
      have := min_le_left t (1 - t)
      linarith
    · have h1 := Real.mul_le_sin (x := Real.pi * (1 - t)) (by nlinarith) (by nlinarith)
      have h2 : 2 / Real.pi * (Real.pi * (1 - t)) = 2 * (1 - t) := by field_simp
      have h3 : Real.sin (Real.pi * (1 - t)) = Real.sin (Real.pi * t) := by
        rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub]
      rw [h2, h3] at h1
      have := min_le_right t (1 - t)
      linarith
  refine ⟨?_, ?_⟩
  · calc ‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖
        ≤ ∑ j ∈ Finset.range m, ‖eC (t * (j : ℝ))‖ := norm_sum_le _ _
      _ = (m : ℝ) := by simp [norm_eC591G]
  · have hg := congrArg norm (geom_sum_eC591G m t)
    rw [norm_mul, norm_eC_sub_one591G] at hg
    have hle : ‖eC (t * (m : ℝ)) - 1‖ ≤ 2 := by
      calc ‖eC (t * (m : ℝ)) - 1‖ ≤ ‖eC (t * (m : ℝ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_eC591G]; norm_num
    have habs : 4 * min t (1 - t) ≤ 2 * |Real.sin (Real.pi * t)| := by
      have := le_abs_self (Real.sin (Real.pi * t))
      linarith
    calc ‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ * (4 * min t (1 - t))
        ≤ ‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ * (2 * |Real.sin (Real.pi * t)|) :=
          mul_le_mul_of_nonneg_left habs (norm_nonneg _)
      _ ≤ 2 := by rw [hg]; exact hle

private theorem eC_add591J (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem eC_conj591J (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, Complex.conj_ofReal]
  simp [Complex.conj_ofReal, h2]

private theorem norm_pow_four591J (z : ℂ) :
    ((‖z‖ ^ 4 : ℝ) : ℂ) = (starRingEnd ℂ) z * ((starRingEnd ℂ) z * (z * z)) := by
  have h : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : ((‖z‖ ^ 4 : ℝ) : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
    push_cast; ring
  rw [h2, ← h]; ring

private theorem expand591J (m : ℕ) (t : ℝ) :
    ((‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ ^ 4 : ℝ) : ℂ) =
      ∑ q ∈ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m,
        eC (t * (((q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 : ℤ) : ℝ)) := by
  rw [norm_pow_four591J]
  simp only [Finset.sum_product, map_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [eC_conj591J, ← eC_add591J]
  congr 1
  push_cast
  ring

private theorem count591J (H m : ℕ) (hm : 1 ≤ m) (hH : 2 * (m - 1) ≤ H) :
    ∃ N : ℤ → ℕ, (m : ℝ) ^ 3 / 8 ≤ (N 0 : ℝ) ∧ (∀ h, N (-h) = N h) ∧
      (∀ h, N h ≤ m ^ 3) ∧
      ∀ t : ℝ, ((‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ ^ 4 : ℝ) : ℂ) =
        ∑ h ∈ Finset.Icc (-(H : ℤ)) H, (N h : ℂ) * eC (t * h) := by
  refine ⟨fun h => ((Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ
      Finset.range m).filter
        (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = h)).card,
    ?_, ?_, ?_, ?_⟩
  · -- lower bound
    have hinj : (Finset.range ((m + 1) / 2) ×ˢ Finset.range ((m + 1) / 2) ×ˢ
        Finset.range ((m + 1) / 2)).card ≤
        ((Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ
      Finset.range m).filter
        (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = 0)).card := by
      apply Finset.card_le_card_of_injOn
        (fun p : ℕ × ℕ × ℕ => (p.1, p.2.1 + p.2.2, p.2.1, p.1 + p.2.2))
      · show ∀ p ∈ (Finset.range ((m + 1) / 2) ×ˢ Finset.range ((m + 1) / 2) ×ˢ
          Finset.range ((m + 1) / 2)),
          (p.1, p.2.1 + p.2.2, p.2.1, p.1 + p.2.2) ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = 0)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m))
        intro p hp
        obtain ⟨u, v, w⟩ := p
        simp only [Finset.mem_product, Finset.mem_range] at hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
        push_cast
        ring
      · intro p _ p' _ heq
        obtain ⟨u, v, w⟩ := p
        obtain ⟨u', v', w'⟩ := p'
        have heq : (u, v + w, v, u + w) = (u', v' + w', v', u' + w') := heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨h1, h2, h3, h4⟩ := heq
        simp only [Prod.mk.injEq]
        omega
    simp only [Finset.card_product, Finset.card_range] at hinj
    have h2 : (m : ℝ) / 2 ≤ (((m + 1) / 2 : ℕ) : ℝ) := by
      have : m ≤ 2 * ((m + 1) / 2) := by omega
      have h' : (m : ℝ) ≤ 2 * (((m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have h3 : ((m : ℝ) / 2) ^ 3 ≤ (((m + 1) / 2 : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h2 3
    have h4 : ((m + 1) / 2) ^ 3 ≤ _ :=
      le_of_eq_of_le (by ring : ((m + 1) / 2) ^ 3 = _) hinj
    have h5 := (Nat.cast_le (α := ℝ)).mpr h4
    rw [Nat.cast_pow] at h5
    refine le_trans ?_ h5
    rw [show (m : ℝ) ^ 3 / 8 = ((m : ℝ) / 2) ^ 3 by ring]
    exact h3
  · intro h
    apply Finset.card_nbij' (fun q : ℕ × ℕ × ℕ × ℕ => (q.2.2.1, q.2.2.2, q.1, q.2.1))
      (fun q : ℕ × ℕ × ℕ × ℕ => (q.2.2.1, q.2.2.2, q.1, q.2.1))
    · show ∀ q ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = -h)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m)),
          (q.2.2.1, q.2.2.2, q.1, q.2.1) ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = h)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m))
      intro q hq
      obtain ⟨a, b, c, d⟩ := q
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq ⊢
      refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩
    · show ∀ q ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = h)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m)),
          (q.2.2.1, q.2.2.2, q.1, q.2.1) ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = -h)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m))
      intro q hq
      obtain ⟨a, b, c, d⟩ := q
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq ⊢
      refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩
    · rintro ⟨a, b, c, d⟩ _; rfl
    · rintro ⟨a, b, c, d⟩ _; rfl
  · intro h
    have hinj : ((Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ
      Finset.range m).filter
        (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = h)).card ≤
        (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m).card := by
      apply Finset.card_le_card_of_injOn
        (fun q : ℕ × ℕ × ℕ × ℕ => (q.1, q.2.1, q.2.2.1))
      · show ∀ q ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = h)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m)),
          (q.1, q.2.1, q.2.2.1) ∈ (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m)
        intro q hq
        obtain ⟨a, b, c, d⟩ := q
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq ⊢
        exact ⟨by omega, by omega, by omega⟩
      · show ∀ q ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = h)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m)), ∀ q' ∈ (Finset.filter (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 = h)
          (Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m)),
          (q.1, q.2.1, q.2.2.1) = (q'.1, q'.2.1, q'.2.2.1) → q = q'
        intro q hq q' hq' heq
        obtain ⟨a, b, c, d⟩ := q
        obtain ⟨a', b', c', d'⟩ := q'
        have hq := Finset.mem_filter.1 hq
        have hq' := Finset.mem_filter.1 hq'
        have heq : (a, b, c) = (a', b', c') := heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨h1, h2, h3⟩ := heq
        have e1 : (a : ℤ) + b - c - d = h := hq.2
        have e2 : (a' : ℤ) + b' - c' - d' = h := hq'.2
        simp only [Prod.mk.injEq]
        omega
    simp only [Finset.card_product, Finset.card_range] at hinj
    calc _ ≤ m * (m * m) := hinj
      _ = m ^ 3 := by ring
  · intro t
    rw [expand591J]
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc (-(H : ℤ)) H)
      (g := fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2)]
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => eC (t * (h : ℝ)))]
      · rw [Finset.sum_const, nsmul_eq_mul]
      · intro q hq
        rw [(Finset.mem_filter.mp hq).2]
    · intro q hq
      obtain ⟨a, b, c, d⟩ := q
      simp only [Finset.mem_product, Finset.mem_range] at hq
      simp only [Finset.mem_Icc]
      omega

/-- A2. Jackson type kernel: the fourth power of the Dirichlet type sum, normalised, as a
trigonometric polynomial with real, even, bounded coefficients and constant coefficient one. -/
theorem jackson_expand591 (H m : ℕ) (hm : 1 ≤ m) (hH : 2 * (m - 1) ≤ H) :
    ∃ (k : ℤ → ℝ) (c : ℝ), (m : ℝ) ^ 3 / 8 ≤ c ∧ k 0 = 1 ∧ (∀ h, k (-h) = k h) ∧
      (∀ h, |k h| ≤ 8) ∧
      ∀ t : ℝ, ∑ h ∈ Finset.Icc (-(H : ℤ)) H, (k h : ℂ) * eC (t * h) =
        ((‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ ^ 4 / c : ℝ) : ℂ) := by
  obtain ⟨N, h0, hsym, hle, hexp⟩ := count591J H m hm hH
  have hmpos : (0 : ℝ) < (m : ℝ) ^ 3 / 8 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hc : (0 : ℝ) < (N 0 : ℝ) := lt_of_lt_of_le hmpos h0
  refine ⟨fun h => (N h : ℝ) / (N 0 : ℝ), (N 0 : ℝ), h0, div_self hc.ne', ?_, ?_, ?_⟩
  · intro h
    simp only [hsym h]
  · intro h
    have hN : (N h : ℝ) ≤ (m : ℝ) ^ 3 := by exact_mod_cast hle h
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hc]
    linarith
  · intro t
    have hc' : ((N 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [Complex.ofReal_div, hexp t, Finset.sum_div]
    refine Finset.sum_congr rfl fun h _ => ?_
    push_cast
    ring

/-- A. Jackson type kernel with its decay bound. -/
theorem jackson_kernel591 (H m : ℕ) (hm : 1 ≤ m) (hH : 2 * (m - 1) ≤ H) :
    ∃ k : ℤ → ℝ, k 0 = 1 ∧ (∀ h, k (-h) = k h) ∧ (∀ h, |k h| ≤ 8) ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        ‖∑ h ∈ Finset.Icc (-(H : ℤ)) H, (k h : ℂ) * eC (t * h)‖ ≤
          128 * (m : ℝ) / (1 + 2 * (m : ℝ) * min t (1 - t)) ^ 4 := by
  obtain ⟨k, c, hc, hk0, hsym, hbd, hsum⟩ := jackson_expand591 H m hm hH
  refine ⟨k, hk0, hsym, hbd, fun t ht0 ht1 => ?_⟩
  obtain ⟨h1, h2⟩ := geom_sum_bounds591 m t ht0 ht1
  rw [hsum t, Complex.norm_real]
  have hN0 : 0 ≤ ‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ := norm_nonneg _
  generalize ‖∑ j ∈ Finset.range m, eC (t * (j : ℝ))‖ = N at h1 h2 hN0 ⊢
  have hd : 0 < min t (1 - t) := lt_min ht0 (by linarith)
  generalize min t (1 - t) = d at h2 hd ⊢
  have hM : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  generalize (m : ℝ) = M at h1 hc hM ⊢
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have hc0 : 0 < c := by linarith
  have hNd : N * d ≤ 1 / 2 := by linarith
  have hkey : N * (1 + 2 * M * d) ≤ 2 * M := by
    nlinarith [mul_le_mul_of_nonneg_left hNd hM0]
  have hp : 0 < 1 + 2 * M * d := by
    have := mul_nonneg hM0 hd.le
    linarith
  have h4 := pow_le_pow_left₀ (mul_nonneg hN0 hp.le) hkey 4
  rw [mul_pow] at h4
  have h5 := mul_le_mul_of_nonneg_left hc hM0
  rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg hN0 4) hc0.le),
    div_le_div_iff₀ hc0 (pow_pos hp 4)]
  nlinarith [h4, h5]

private lemma sum_odd591S (H : ℕ) (f : ℤ → ℂ) (hf : ∀ h, f (-h) = - f h) :
    ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), f h = 0 := by
  have h1 : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), f h =
      ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), f (-h) := by
    refine Finset.sum_nbij' (fun h => -h) (fun h => -h) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
      omega
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
      omega
    · intro h _; simp
    · intro h _; simp
    · intro h _; simp
  simp only [hf, Finset.sum_neg_distrib] at h1
  exact self_eq_neg.mp h1

private lemma eC_half_neg591S (h : ℤ) :
    eC (1 / 2 * ((-h : ℤ) : ℝ)) = eC (1 / 2 * (h : ℝ)) := by
  unfold eC
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-h, ?_⟩
  push_cast
  ring

private lemma eC_deriv591S (h : ℤ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => eC (y * h)) (2 * Real.pi * Complex.I * h * eC (y * h)) y := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * Real.pi * Complex.I * (((y * (h : ℝ) : ℝ)) : ℂ))
      (2 * Real.pi * Complex.I * h) y := by
    have := ((hasDerivAt_id y).ofReal_comp.mul_const ((h : ℝ) : ℂ)).const_mul
      (2 * Real.pi * Complex.I)
    convert this using 1
    · funext z; simp
    · simp
  have h2 := h1.cexp
  unfold eC
  convert h2 using 1
  ring

private lemma E_deriv591S (H : ℕ) (k : ℤ → ℝ) (hk0 : k 0 = 1) (y : ℝ) :
    HasDerivAt (fun y : ℝ => ((y - 1 / 2 : ℝ) : ℂ) -
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
          (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (y * h))
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, (k h : ℂ) * eC (y * h)) y := by
  have h1 : HasDerivAt (fun y : ℝ => ((y - 1 / 2 : ℝ) : ℂ)) 1 y := by
    have := ((hasDerivAt_id y).sub_const (1 / 2)).ofReal_comp
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ =>
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
          (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (y * h))
      (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
          (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) *
            (2 * Real.pi * Complex.I * h * eC (y * h))) y :=
    HasDerivAt.fun_sum (fun h _ => (eC_deriv591S h y).const_mul _)
  have h3 := h1.sub h2
  convert h3 using 1
  rw [Finset.sum_filter]
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := by
    simp only [Finset.mem_Icc]; omega
  have h4 : (1 : ℂ) = ∑ h ∈ Finset.Icc (-(H : ℤ)) H, if h = 0 then (1 : ℂ) else 0 := by
    rw [Finset.sum_ite_eq' _ (0 : ℤ) (fun _ => (1 : ℂ))]
    simp [h0]
  rw [h4, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  by_cases hh : h = 0
  · subst hh; simp [hk0, eC]
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    simp only [hh, ite_false, ne_eq, not_false_eq_true, ite_true]
    field_simp
    linear_combination ((k h : ℂ) * eC (y * h)) * Complex.I_sq

private lemma mvt_core591S (m : ℝ) (hm : 1 ≤ m) (G G' : ℝ → ℂ)
    (hG : ∀ t, HasDerivAt G (G' t) t) (x : ℝ) (hx : 0 < x) (hx2 : x ≤ 1 / 2)
    (hb : ∀ t, x ≤ t → t < 1 / 2 → ‖G' t‖ ≤ 128 * m / (1 + 2 * m * t) ^ 4)
    (h0 : G (1 / 2) = 0) : ‖G x‖ ≤ (64 / 3) / (1 + 2 * m * x) ^ 3 := by
  have hpos : ∀ t, x ≤ t → 0 < 1 + 2 * m * t := fun t ht => by
    have : 0 ≤ m * t := mul_nonneg (by linarith) (by linarith)
    linarith
  have hBd : ∀ t, x ≤ t → HasDerivAt
      (fun t => -(64 / 3) * ((1 + 2 * m * t) ^ 3)⁻¹ + (64 / 3) / (1 + 2 * m * x) ^ 3)
      (128 * m / (1 + 2 * m * t) ^ 4) t := by
    intro t ht
    have hp := hpos t ht
    have h1 : HasDerivAt (fun t => 1 + 2 * m * t) (2 * m) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * m)).const_add 1
    have h2 : HasDerivAt (fun t => (1 + 2 * m * t) ^ 3)
        (3 * (1 + 2 * m * t) ^ 2 * (2 * m)) t := by
      simpa using h1.fun_pow 3
    have h3 : HasDerivAt (fun t => ((1 + 2 * m * t) ^ 3)⁻¹)
        (-(3 * (1 + 2 * m * t) ^ 2 * (2 * m)) / ((1 + 2 * m * t) ^ 3) ^ 2) t :=
      h2.fun_inv (by positivity)
    have h4 := (h3.const_mul (-(64 / 3))).add_const ((64 / 3) / (1 + 2 * m * x) ^ 3)
    convert h4 using 1
    field_simp
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun t => G t - G x) (f' := G') (a := x) (b := 1 / 2)
    (B := fun t => -(64 / 3) * ((1 + 2 * m * t) ^ 3)⁻¹ + (64 / 3) / (1 + 2 * m * x) ^ 3)
    (B' := fun t => 128 * m / (1 + 2 * m * t) ^ 4)
    (fun t _ => ((hG t).sub_const (G x)).continuousAt.continuousWithinAt)
    (fun t _ => ((hG t).sub_const (G x)).hasDerivWithinAt)
    (by
      have := hpos x le_rfl
      simp only [sub_self, norm_zero]
      apply le_of_eq
      ring)
    (fun t ht => (hBd t ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (hBd t ht.1).hasDerivWithinAt)
    (fun t ht => hb t ht.1 ht.2)
    (Set.right_mem_Icc.mpr hx2)
  simp only [h0, zero_sub, norm_neg] at key
  refine key.trans ?_
  have hp := hpos (1 / 2) hx2
  have : 0 ≤ (64 / 3 : ℝ) * ((1 + 2 * m * (1 / 2)) ^ 3)⁻¹ := by positivity
  linarith

/-- B. The sawtooth minus the smoothed Fourier sum is an antiderivative of the kernel that
vanishes at one half; integrating the kernel bound gives cubic decay. -/
theorem saw_approx591 (H m : ℕ) (hm : 1 ≤ m) (k : ℤ → ℝ) (hk0 : k 0 = 1)
    (hksym : ∀ h, k (-h) = k h)
    (hK : ∀ t : ℝ, 0 < t → t < 1 →
        ‖∑ h ∈ Finset.Icc (-(H : ℤ)) H, (k h : ℂ) * eC (t * h)‖ ≤
          128 * (m : ℝ) / (1 + 2 * (m : ℝ) * min t (1 - t)) ^ 4) :
    (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
        (k h : ℂ) * (Complex.I / (2 * Real.pi * h))) = 0 ∧
    ∀ x : ℝ, 0 < x → x < 1 →
      ‖((x - 1 / 2 : ℝ) : ℂ) -
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
          (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (x * h)‖ ≤
        (64 / 3) / (1 + 2 * (m : ℝ) * min x (1 - x)) ^ 3 := by
  refine ⟨?_, ?_⟩
  · apply sum_odd591S
    intro h
    rw [hksym]
    push_cast
    by_cases hh : (h : ℂ) = 0
    · simp [hh]
    · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
  · intro x hx0 hx1
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hE := E_deriv591S H k hk0
    have hhalf : ((fun y : ℝ => ((y - 1 / 2 : ℝ) : ℂ) -
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
          (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (y * h)) (1 / 2)) = 0 := by
      have : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
          (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (1 / 2 * h) = 0 := by
        apply sum_odd591S
        intro h
        rw [hksym, eC_half_neg591S]
        push_cast
        by_cases hh : (h : ℂ) = 0
        · simp [hh]
        · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
          field_simp
      simp only [sub_self, Complex.ofReal_zero, zero_sub, neg_eq_zero]
      exact this
    rcases le_or_gt x (1 / 2) with hx2 | hx2
    · rw [min_eq_left (by linarith)]
      refine mvt_core591S m hm' _ _ hE x hx0 hx2 (fun t ht1 ht2 => ?_) hhalf
      have := hK t (by linarith) (by linarith)
      rwa [min_eq_left (by linarith)] at this
    · rw [min_eq_right (by linarith)]
      have hG : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (fun y : ℝ => ((y - 1 / 2 : ℝ) : ℂ) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
            (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (y * h)) (1 - t))
          (-(∑ h ∈ Finset.Icc (-(H : ℤ)) H, (k h : ℂ) * eC ((1 - t) * h))) t := by
        intro t
        exact (hE (1 - t)).comp_const_sub 1 t
      have key := mvt_core591S m hm' _ _ hG (1 - x) (by linarith) (by linarith)
        (fun t ht1 ht2 => ?_) (by norm_num; simpa using hhalf)
      · simpa using key
      · have := hK (1 - t) (by linarith) (by linarith)
        rw [norm_neg]
        rwa [min_eq_right (by linarith), sub_sub_cancel] at this

private theorem eC_addFF (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_eCFF (θ : ℝ) : ‖eC θ‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

private theorem norm_eC_sub_one_leFF (θ : ℝ) : ‖eC θ - 1‖ ≤ 2 * Real.pi * |θ| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * θ)
  have e : eC θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
    unfold eC
    congr 1
    push_cast
    ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

private theorem eC_mul_conjFF (x y : ℝ) : eC x * (starRingEnd ℂ) (eC y) = eC (x - y) := by
  unfold eC
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

private theorem eC_intCastFF (n : ℤ) : eC (n : ℝ) = 1 := by
  unfold eC
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1
  push_cast
  ring

private theorem eC_halfFF : eC (1 / 2) = -1 := by
  unfold eC
  rw [← Complex.exp_pi_mul_I]
  congr 1
  push_cast
  ring

private theorem D_periodFF (m : ℕ) (y y' : ℝ) (n : ℤ) (h : y' = y + n) :
    ∑ j ∈ Finset.range m, eC (y' * (j : ℝ)) = ∑ j ∈ Finset.range m, eC (y * (j : ℝ)) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : y' * (j : ℝ) = y * j + ((n * (j : ℤ) : ℤ) : ℝ) := by
    rw [h]; push_cast; ring
  rw [e, eC_addFF, eC_intCastFF, mul_one]

private theorem D_geomFF (m : ℕ) (y : ℝ) :
    (∑ j ∈ Finset.range m, eC (y * (j : ℝ))) * (eC y - 1) = eC ((m : ℝ) * y) - 1 := by
  induction m with
  | zero =>
    have : eC 0 = 1 := by simpa using eC_intCastFF 0
    simp [this]
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have e : ((k + 1 : ℕ) : ℝ) * y = y * k + y := by push_cast; ring
    rw [e, eC_addFF, mul_comm (k : ℝ) y]; ring

private theorem D_lowerFF (m : ℕ) (y : ℝ) :
    ‖eC ((m : ℝ) * y) - 1‖ ≤
      ‖∑ j ∈ Finset.range m, eC (y * (j : ℝ))‖ * (2 * Real.pi * |y|) := by
  rw [← D_geomFF, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_eC_sub_one_leFF y) (norm_nonneg _)

private theorem two_ptFF (m : ℕ) (hm : 1 ≤ m) (y1 y2 r : ℝ)
    (h12 : y2 = y1 + 1 / (2 * (m : ℝ))) (h1 : |y1| ≤ r) (h2 : |y2| ≤ r) :
    4 ≤ (‖∑ j ∈ Finset.range m, eC (y1 * (j : ℝ))‖ ^ 2 +
      ‖∑ j ∈ Finset.range m, eC (y2 * (j : ℝ))‖ ^ 2) * (2 * Real.pi * r) ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have a1 := D_lowerFF m y1
  have a2 := D_lowerFF m y2
  have hz : eC ((m : ℝ) * y2) = - eC ((m : ℝ) * y1) := by
    have e : (m : ℝ) * y2 = m * y1 + 1 / 2 := by rw [h12]; field_simp
    rw [e, eC_addFF, eC_halfFF]; ring
  rw [hz] at a2
  have hzn : ‖eC ((m : ℝ) * y1)‖ = 1 := norm_eCFF _
  generalize eC ((m : ℝ) * y1) = z at a1 a2 hzn
  generalize (∑ j ∈ Finset.range m, eC (y1 * (j : ℝ))) = D1 at a1 ⊢
  generalize (∑ j ∈ Finset.range m, eC (y2 * (j : ℝ))) = D2 at a2 ⊢
  have par : ‖z - 1‖ ^ 2 + ‖-z - 1‖ ^ 2 = 4 := by
    have h1' : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hzn]; norm_num
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im]
    linear_combination 2 * h1'
  have hr : 0 ≤ r := (abs_nonneg _).trans h1
  have hpi := Real.pi_pos
  have b1 : ‖z - 1‖ ^ 2 ≤ ‖D1‖ ^ 2 * (2 * Real.pi * r) ^ 2 := by
    have : ‖z - 1‖ ≤ ‖D1‖ * (2 * Real.pi * r) :=
      a1.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h1 (by positivity)) (norm_nonneg _))
    calc ‖z - 1‖ ^ 2 ≤ (‖D1‖ * (2 * Real.pi * r)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by ring
  have b2 : ‖-z - 1‖ ^ 2 ≤ ‖D2‖ ^ 2 * (2 * Real.pi * r) ^ 2 := by
    have : ‖-z - 1‖ ≤ ‖D2‖ * (2 * Real.pi * r) :=
      a2.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h2 (by positivity)) (norm_nonneg _))
    calc ‖-z - 1‖ ^ 2 ≤ (‖D2‖ * (2 * Real.pi * r)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by ring
  linarith

private theorem D_sqFF (H m : ℕ) (hH : m - 1 ≤ H) (y : ℝ) :
    ((‖∑ j ∈ Finset.range m, eC (y * (j : ℝ))‖ : ℝ) : ℂ) ^ 2 =
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        ((((Finset.range m ×ˢ Finset.range m).filter
          (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card : ℕ) : ℂ) * eC (y * h) := by
  rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ p ∈ Finset.range m ×ˢ Finset.range m,
      ((p.1 : ℤ) - p.2) ∈ Finset.Icc (-(H : ℤ)) H := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_Icc]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [eC_mul_conjFF, ← hp.2]; congr 1; push_cast; ring

private theorem N_leFF (m : ℕ) (h : ℤ) :
    ((Finset.range m ×ˢ Finset.range m).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card ≤ m := by
  calc ((Finset.range m ×ˢ Finset.range m).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card ≤ (Finset.range m).card := by
        refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact hp.1.1
        · intro p hp q hq hpq
          simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
          have hpq' : p.1 = q.1 := hpq
          exact Prod.ext hpq' (by have := hp.2; have := hq.2; omega)
    _ = m := Finset.card_range m

/-- C. Two shifted Fejer kernels give a real trigonometric polynomial majorant with small
coefficients and a quadratic lower bound. -/
theorem fejer_majorant591 (H m : ℕ) (hm : 1 ≤ m) (hH : m - 1 ≤ H) :
    ∃ g : ℤ → ℂ, (∀ h, ‖g h‖ ≤ 2 / (m : ℝ)) ∧
      ∀ x : ℝ, 0 ≤ x → x < 1 →
        (∑ h ∈ Finset.Icc (-(H : ℤ)) H, g h * eC (x * h)).im = 0 ∧
        4 / (Real.pi ^ 2 * (1 + 2 * (m : ℝ) * min x (1 - x)) ^ 2) ≤
          (∑ h ∈ Finset.Icc (-(H : ℤ)) H, g h * eC (x * h)).re := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  refine ⟨fun h => ((((Finset.range m ×ˢ Finset.range m).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card : ℕ) : ℂ) *
      (1 + eC ((h : ℝ) / (2 * (m : ℝ)))) / (m : ℂ) ^ 2, ?_, ?_⟩
  · intro h
    beta_reduce
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    have h1 : ‖(1 : ℂ) + eC ((h : ℝ) / (2 * (m : ℝ)))‖ ≤ 2 :=
      (norm_add_le _ _).trans (by rw [norm_one, norm_eCFF]; norm_num)
    have h2 : ((((Finset.range m ×ˢ Finset.range m).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card : ℕ) : ℝ) ≤ m := by
      exact_mod_cast N_leFF m h
    rw [div_le_div_iff₀ (by positivity) hm0]
    have h3 := mul_le_mul h2 h1 (norm_nonneg _) hm0.le
    nlinarith [mul_le_mul_of_nonneg_right h3 hm0.le]
  · intro x hx0 hx1
    beta_reduce
    have hx' : ∃ x' : ℝ, x' = x + 1 / (2 * (m : ℝ)) := ⟨_, rfl⟩
    obtain ⟨x', hx'⟩ := hx'
    have hpos : 0 < 1 / (2 * (m : ℝ)) := by positivity
    have key : ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        ((((Finset.range m ×ˢ Finset.range m).filter
          (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card : ℕ) : ℂ) *
          (1 + eC ((h : ℝ) / (2 * (m : ℝ)))) / (m : ℂ) ^ 2 * eC (x * h) =
        (((‖∑ j ∈ Finset.range m, eC (x * (j : ℝ))‖ ^ 2 +
          ‖∑ j ∈ Finset.range m, eC (x' * (j : ℝ))‖ ^ 2) / (m : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [D_sqFF H m hH x, D_sqFF H m hH x', ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun h _ => ?_
      have e : eC (x' * h) = eC (x * h) * eC ((h : ℝ) / (2 * (m : ℝ))) := by
        rw [← eC_addFF]; congr 1; rw [hx']; ring
      rw [e]; ring
    rw [key]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    have hd0 : 0 ≤ min x (1 - x) := le_min hx0 (by linarith)
    have main : 4 ≤ (‖∑ j ∈ Finset.range m, eC (x * (j : ℝ))‖ ^ 2 +
          ‖∑ j ∈ Finset.range m, eC (x' * (j : ℝ))‖ ^ 2) *
          (2 * Real.pi * (min x (1 - x) + 1 / (2 * (m : ℝ)))) ^ 2 := by
      rcases le_or_gt x (1 / 2) with hx | hx
      · have hd : min x (1 - x) = x := min_eq_left (by linarith)
        rw [hd]
        exact two_ptFF m hm x x' _ hx' (by rw [abs_of_nonneg hx0]; linarith)
          (by rw [abs_of_nonneg (by linarith)]; linarith)
      · have hd : min x (1 - x) = 1 - x := min_eq_right (by linarith)
        rw [hd]
        have p1 := D_periodFF m x (x - 1) (-1) (by push_cast; ring)
        have p2 := D_periodFF m x' (x' - 1) (-1) (by push_cast; ring)
        have t := two_ptFF m hm (x - 1) (x' - 1) (1 - x + 1 / (2 * (m : ℝ)))
          (by rw [hx']; ring) (abs_le.mpr ⟨by linarith, by linarith⟩)
          (abs_le.mpr ⟨by linarith, by linarith⟩)
        rw [p1, p2] at t
        exact t
    generalize min x (1 - x) = d at hd0 main ⊢
    generalize (‖∑ j ∈ Finset.range m, eC (x * (j : ℝ))‖ ^ 2 +
          ‖∑ j ∈ Finset.range m, eC (x' * (j : ℝ))‖ ^ 2) = S at main ⊢
    have hq : 0 < 1 + 2 * (m : ℝ) * d := by
      have := mul_nonneg hm0.le hd0; linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (2 * Real.pi * (d + 1 / (2 * (m : ℝ)))) ^ 2 * (m : ℝ) ^ 2 =
        Real.pi ^ 2 * (1 + 2 * (m : ℝ) * d) ^ 2 := by
      field_simp; ring
    calc 4 * (m : ℝ) ^ 2 ≤ (S * (2 * Real.pi * (d + 1 / (2 * (m : ℝ)))) ^ 2) * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right main (by positivity)
      _ = S * (Real.pi ^ 2 * (1 + 2 * (m : ℝ) * d) ^ 2) := by rw [mul_assoc, e]

private theorem eC_fract591M (x : ℝ) (h : ℤ) :
    eC (x * (h : ℝ)) = eC (Int.fract x * (h : ℝ)) := by
  have hx : x = Int.fract x + (⌊x⌋ : ℝ) := (Int.fract_add_floor x).symm
  unfold eC
  have : (2 * (Real.pi : ℂ) * Complex.I * ((x * (h : ℝ) : ℝ) : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((Int.fract x * (h : ℝ) : ℝ) : ℂ) +
        ((⌊x⌋ * h : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    conv_lhs => rw [hx]
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem perH591M (H : ℕ) : ∃ aH bH : ℤ → ℂ, 1 ≤ H →
      (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ‖aH h‖ ≤ (4 * (16 * Real.pi ^ 2 / 3)) / |(h : ℝ)|) ∧
      (∀ h : ℤ, |h| ≤ (H : ℤ) → ‖bH h‖ ≤ (4 * (16 * Real.pi ^ 2 / 3)) / (H : ℝ)) ∧
      ∀ x : ℝ,
        (∑ h ∈ Finset.Icc (-(H : ℤ)) H, bH h * eC (x * h)).im = 0 ∧
        ‖(Decomp139.saw x : ℂ) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
            aH h * eC (x * h)‖ ≤
          (∑ h ∈ Finset.Icc (-(H : ℤ)) H, bH h * eC (x * h)).re := by
  by_cases hH : 1 ≤ H
  swap
  · exact ⟨0, 0, fun h => absurd h hH⟩
  have hpi := Real.pi_gt_three
  have hpos := Real.pi_pos
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = H / 2 + 1 := ⟨_, rfl⟩
  have hm : 1 ≤ m := by omega
  have h2 : 2 * (m - 1) ≤ H := by omega
  have h3 : m - 1 ≤ H := by omega
  have hHm : (H : ℝ) ≤ 2 * (m : ℝ) := by
    have : H ≤ 2 * m := by omega
    exact_mod_cast this
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨k, hk0, hksym, hkb, hK⟩ := jackson_kernel591 H m hm h2
  obtain ⟨hS0, hS⟩ := saw_approx591 H m hm k hk0 hksym hK
  obtain ⟨g, hg, hG⟩ := fejer_majorant591 H m hm h3
  have hBc : (0 : ℝ) ≤ 16 * Real.pi ^ 2 / 3 := by positivity
  refine ⟨fun h => (k h : ℂ) * (Complex.I / (2 * Real.pi * h)),
    fun h => ((16 * Real.pi ^ 2 / 3 : ℝ) : ℂ) * g h, fun _ => ⟨?_, ?_, ?_⟩⟩
  · intro h hh _
    have hhabs : (0 : ℝ) < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
    have hn : ‖(Complex.I / (2 * Real.pi * h) : ℂ)‖ = 1 / (2 * Real.pi * |(h : ℝ)|) := by
      have : (2 * (Real.pi : ℂ) * (h : ℂ)) = ((2 * Real.pi * (h : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [norm_div, Complex.norm_I, this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_two, abs_of_pos hpos]
    show ‖(k h : ℂ) * (Complex.I / (2 * Real.pi * h))‖ ≤ _
    rw [norm_mul, hn, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |k h| * (1 / (2 * Real.pi * |(h : ℝ)|)) ≤ 8 * (1 / (2 * Real.pi * |(h : ℝ)|)) :=
      mul_le_mul_of_nonneg_right (hkb h) (by positivity)
    have h4 : 8 * (1 / (2 * Real.pi * |(h : ℝ)|)) = (4 / Real.pi) / |(h : ℝ)| := by
      field_simp; ring
    have h5 : 4 / Real.pi ≤ 4 * (16 * Real.pi ^ 2 / 3) := by
      have : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
      nlinarith
    calc _ ≤ _ := h1
      _ = _ := h4
      _ ≤ _ := div_le_div_of_nonneg_right h5 hhabs.le
  · intro h _
    show ‖((16 * Real.pi ^ 2 / 3 : ℝ) : ℂ) * g h‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBc]
    have h1 : (16 * Real.pi ^ 2 / 3) * ‖g h‖ ≤ (16 * Real.pi ^ 2 / 3) * (2 / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (hg h) hBc
    have h4 : (2 : ℝ) / m ≤ 4 / H := by
      rw [div_le_div_iff₀ hmpos hHpos]; linarith
    have h5 : (16 * Real.pi ^ 2 / 3) * (2 / (m : ℝ)) ≤ (16 * Real.pi ^ 2 / 3) * (4 / (H : ℝ)) :=
      mul_le_mul_of_nonneg_left h4 hBc
    calc _ ≤ _ := h1
      _ ≤ _ := h5
      _ = _ := by ring
  · intro x
    have e1 : ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        (((16 * Real.pi ^ 2 / 3 : ℝ) : ℂ) * g h) * eC (x * h) =
        ((16 * Real.pi ^ 2 / 3 : ℝ) : ℂ) *
          ∑ h ∈ Finset.Icc (-(H : ℤ)) H, g h * eC (Int.fract x * h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [eC_fract591M, mul_assoc]
    have e2 : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
        (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (x * h) =
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
        (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (Int.fract x * h) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [eC_fract591M]
    have hsaw : Decomp139.saw x = Int.fract x - 1 / 2 := by
      unfold Decomp139.saw Int.fract; rfl
    have key : ∀ y : ℝ, 0 ≤ y → y < 1 →
        ‖((y - 1 / 2 : ℝ) : ℂ) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
            (k h : ℂ) * (Complex.I / (2 * Real.pi * h)) * eC (y * h)‖ ≤
          (64 / 3) / (1 + 2 * (m : ℝ) * min y (1 - y)) ^ 2 := by
      intro y hy0 hy1
      rcases eq_or_lt_of_le hy0 with hy | hy
      · subst hy
        have eC0 : ∀ h : ℤ, eC (0 * (h : ℝ)) = 1 := by intro h; simp [eC]
        rw [Finset.sum_congr rfl (fun h _ => by rw [eC0, mul_one]), hS0]
        have h7 : ((0 - 1 / 2 : ℝ) : ℂ) - 0 = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
        have h8 : min (0 : ℝ) (1 - 0) = 0 := by norm_num
        rw [h7, Complex.norm_real, Real.norm_eq_abs, h8, abs_le]
        constructor <;> norm_num
      · have hu : 0 ≤ 2 * (m : ℝ) * min y (1 - y) :=
          mul_nonneg (by positivity) (le_min hy0 (by linarith))
        refine (hS y hy hy1).trans ?_
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_right₀ (by linarith) (by norm_num))
    obtain ⟨hGi, hGr⟩ := hG (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x)
    have hk := key (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x)
    have hu : 0 ≤ 2 * (m : ℝ) * min (Int.fract x) (1 - Int.fract x) :=
      mul_nonneg (by positivity)
        (le_min (Int.fract_nonneg x) (by linarith [Int.fract_lt_one x]))
    beta_reduce
    rw [e1, e2, hsaw, Complex.im_ofReal_mul, Complex.re_ofReal_mul, hGi, mul_zero]
    refine ⟨rfl, hk.trans ?_⟩
    have h9 := mul_le_mul_of_nonneg_left hGr hBc
    refine le_trans (le_of_eq ?_) h9
    field_simp
    ring

/-- Song 2012.06322, page 3, Lemma 1, citing Graham and Kolesnik, Appendix.
One coefficient pair works for all real x at each positive truncation level.
The majorant is real. Its real part is used for the ordered inequality.
The coefficient estimates are uniform in the truncation level and frequency. -/
theorem song_lemma1_majorant591 :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a b : ℕ → ℤ → ℂ, ∀ H : ℕ, 1 ≤ H →
      (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ‖a H h‖ ≤ C / |(h : ℝ)|) ∧
      (∀ h : ℤ, |h| ≤ (H : ℤ) → ‖b H h‖ ≤ C / (H : ℝ)) ∧
      ∀ x : ℝ,
        (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).im = 0 ∧
        ‖(Decomp139.saw x : ℂ) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
            a H h * eC (x * h)‖ ≤
          (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).re := by
  
  refine ⟨4 * (16 * Real.pi ^ 2 / 3), by positivity, ?_⟩
  choose a b hab using perH591M
  exact ⟨a, b, hab⟩

end LeanLab.Song2020.Repair591FourierMajorant
