module

public import LeanLab.Linnik.ExplicitFormula.LeftHalf
public import LeanLab.HardyLittlewood1923.U1482ZeroCount

/-!
# Zero sums for primitive `L(s, χ)`, uniform in `q`, Davenport ch. 16

AI wrote the Lean code. Binary Goldbach is OPEN.
From `LeanLab.HardyLittlewood1923.U1482.zeroCountUnit`, which counts nontrivial zeros with
multiplicity in unit windows uniformly in `q`, and `zero_left_strip` for `-1/2 ≤ Re ρ ≤ 0`.
The theorems are ordered by dependency: unit window, up to height `T`, dyadic tail, total sum,
summability. They rest on `zero_left_strip` and `mult_zero_le_one` of `LeftHalf.lean`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- elementary, Davenport ch. 16: a zero in `Zall` of a primitive `L(s, χ)` is nontrivial or `0`,
from `zero_left_strip` and Mathlib's nonvanishing on `Re s ≥ 1`. -/
lemma Zall_nt_or_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : ρ ∈ Zall χ) : LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ ∨ ρ = 0 := by
  obtain ⟨h0, h1, h2⟩ := hρ
  by_cases hre : ρ.re ≤ 0
  · exact Or.inr (zero_left_strip hχ h0 h1 hre)
  · by_cases hre1 : 1 ≤ ρ.re
    · exact absurd h0 (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr h2) hre1)
    · exact Or.inl ⟨h0, by linarith, by linarith⟩

/-- Davenport ch. 16: zeros in `Zall` with `t ≤ |Im ρ| ≤ t + 1`, with multiplicity, number at most
`A log(q(t + 2))`, uniformly in the primitive character. -/
theorem zero_mult_unit_window : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ, 0 ≤ t → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ Zall χ ∧ t ≤ |ρ.im| ∧ |ρ.im| ≤ t + 1) →
        (∑ ρ ∈ S, (mult χ ρ : ℝ)) ≤ A * Real.log (q * (t + 2)) := by
  classical
  obtain ⟨A0, hA0, hcount⟩ := LeanLab.HardyLittlewood1923.U1482.zeroCountUnit
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A0 + 1 / Real.log 2, by positivity, fun q _ χ hχ t ht S hS => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL2 : Real.log 2 ≤ Real.log (q * (t + 2)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hLpos : 0 < Real.log (q * (t + 2)) := lt_of_lt_of_le hl2 hL2
  rw [← Finset.sum_filter_add_sum_filter_not S
    (fun ρ => LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ)]
  have h1 : ∑ ρ ∈ S.filter (fun ρ => LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ),
      (mult χ ρ : ℝ) ≤ A0 * Real.log (q * (t + 2)) := by
    have := (hcount q χ hχ t ht).2 (S.filter (fun ρ => LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ))
      (fun ρ hρ => by
        rw [Finset.mem_filter] at hρ
        exact ⟨hρ.2, (hS ρ hρ.1).2⟩)
    simpa [LeanLab.HardyLittlewood1923.U1479.mult, mult] using this
  have h2 : ∑ ρ ∈ S.filter (fun ρ => ¬ LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ),
      (mult χ ρ : ℝ) ≤ 1 / Real.log 2 * Real.log (q * (t + 2)) := by
    have hsub : S.filter (fun ρ => ¬ LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ) ⊆ {0} := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      rcases Zall_nt_or_zero hχ (hS ρ hρ.1).1 with h | h
      · exact absurd h hρ.2
      · simp [h]
    calc _ ≤ ∑ ρ ∈ ({0} : Finset ℂ), (mult χ ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 1 := by simpa using (show ((mult χ 0 : ℕ) : ℝ) ≤ 1 by exact_mod_cast mult_zero_le_one hχ)
      _ ≤ 1 / Real.log 2 * Real.log (q * (t + 2)) := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl2]; linarith
  rw [add_mul]; linarith

/-- Zeros up to height `T`, with multiplicity: `≤ C (T + 1) log(q(T + 2))`. -/
theorem zero_mult_up_to : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 0 ≤ T → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ Zall χ ∧ |ρ.im| ≤ T) →
        (∑ ρ ∈ S, (mult χ ρ : ℝ)) ≤ C * (T + 1) * Real.log (q * (T + 2)) := by
  classical
  obtain ⟨A, hA, hw⟩ := zero_mult_unit_window
  refine ⟨A, hA, fun q _ χ hχ T hT S hS => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hmaps : ∀ ρ ∈ S, (fun ρ : ℂ => ⌊|ρ.im|⌋₊) ρ ∈ range (⌊T⌋₊ + 1) := by
    intro ρ hρ
    simp only [mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (hS ρ hρ).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ range (⌊T⌋₊ + 1),
      ∑ ρ ∈ S with ⌊|ρ.im|⌋₊ = k, (mult χ ρ : ℝ) ≤ A * Real.log (q * (T + 2)) := by
    intro k hk
    simp only [mem_range, Nat.lt_succ_iff] at hk
    have hkT : (k : ℝ) ≤ T := (Nat.cast_le.mpr hk).trans (Nat.floor_le hT)
    refine (hw q χ hχ k (by positivity) _ (fun ρ hρ => ?_)).trans ?_
    · rw [Finset.mem_filter] at hρ
      refine ⟨(hS ρ hρ.1).1, ?_, ?_⟩
      · rw [← hρ.2]; exact Nat.floor_le (abs_nonneg _)
      · rw [← hρ.2]; exact (Nat.lt_floor_add_one _).le
    · apply mul_le_mul_of_nonneg_left _ hA
      apply Real.log_le_log (by positivity)
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hLnn : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
  calc _ ≤ ∑ k ∈ range (⌊T⌋₊ + 1), A * Real.log (q * (T + 2)) := Finset.sum_le_sum hfib
    _ = (⌊T⌋₊ + 1 : ℕ) * (A * Real.log (q * (T + 2))) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (T + 1) * (A * Real.log (q * (T + 2))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        push_cast; linarith [Nat.floor_le hT]
    _ = A * (T + 1) * Real.log (q * (T + 2)) := by ring

/-- elementary: `Σ_{j < N} (j + 2)/2^j = 6 - (2N + 6)/2^N`. -/
lemma sum_jtwo_eq (N : ℕ) :
    ∑ j ∈ range N, ((j : ℝ) + 2) / 2 ^ j = 6 - (2 * (N : ℝ) + 6) / 2 ^ N := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]; push_cast
    field_simp; ring

/-- elementary: `Σ_{j < N} (j + 2)/2^j ≤ 6`. -/
lemma sum_jtwo_le (N : ℕ) : ∑ j ∈ range N, ((j : ℝ) + 2) / 2 ^ j ≤ 6 := by
  rw [sum_jtwo_eq]; have : 0 ≤ (2 * (N : ℝ) + 6) / 2 ^ N := by positivity
  linarith

/-- elementary: `|Im ρ|² ≤ ‖(ρ + 1)(ρ + 2)‖`. -/
lemma im_sq_le_norm_mul (ρ : ℂ) : ρ.im ^ 2 ≤ ‖(ρ + 1) * (ρ + 2)‖ := by
  rw [norm_mul]
  have h1 : |ρ.im| ≤ ‖ρ + 1‖ := by
    simpa using Complex.abs_im_le_norm (ρ + 1)
  have h2 : |ρ.im| ≤ ‖ρ + 2‖ := by
    simpa using Complex.abs_im_le_norm (ρ + 2)
  rw [← sq_abs]; rw [sq]
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

/-- elementary: the dyadic index `j = log₂ ⌊y/T⌋` of `y > T > 0` has `T 2^j ≤ y < T 2^(j+1)`. -/
lemma dyadic_index {T y : ℝ} (hT : 0 < T) (hy : T < y) :
    T * 2 ^ (Nat.log 2 ⌊y / T⌋₊) ≤ y ∧ y < T * 2 ^ (Nat.log 2 ⌊y / T⌋₊ + 1) := by
  set n := ⌊y / T⌋₊ with hn
  have h1 : 1 < y / T := by rw [lt_div_iff₀ hT]; linarith
  have hn0 : n ≠ 0 := by
    rw [hn]; exact (Nat.floor_pos.mpr h1.le).ne'
  have hlo : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hhi : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hlo' : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast hlo
  have hhi' : (n : ℝ) + 1 ≤ 2 ^ (Nat.log 2 n + 1) := by exact_mod_cast hhi
  have hfl : (n : ℝ) ≤ y / T := Nat.floor_le (by linarith)
  have hfl2 : y / T < n + 1 := Nat.lt_floor_add_one _
  have hyT : y = T * (y / T) := by field_simp
  constructor
  · rw [hyT]; exact mul_le_mul_of_nonneg_left (hlo'.trans hfl) hT.le
  · rw [hyT]; exact mul_lt_mul_of_pos_left (hfl2.trans_le hhi') hT

/-- The tail of the zero sum above height `T`: `≤ C log(q(T + 2))/T`, uniformly. -/
theorem zero_sum_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 1 ≤ T → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ Zall χ ∧ T < |ρ.im|) →
        (∑ ρ ∈ S, (mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖) ≤ C * Real.log (q * (T + 2)) / T := by
  classical
  obtain ⟨C0, hC0, hup⟩ := zero_mult_up_to
  refine ⟨18 * C0, by positivity, fun q _ χ hχ T hT S hS => ?_⟩
  have hT0 : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set L := Real.log (q * (T + 2)) with hL
  have hl2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set jf : ℂ → ℕ := fun ρ => Nat.log 2 ⌊|ρ.im| / T⌋₊ with hjf
  set N := S.sup jf + 1 with hN
  have hmaps : ∀ ρ ∈ S, jf ρ ∈ range N := by
    intro ρ hρ; rw [mem_range, hN, Nat.lt_succ_iff]; exact Finset.le_sup (f := jf) hρ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ range N, ∑ ρ ∈ S with jf ρ = j, (mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖ ≤
      3 * C0 * L / T * (((j : ℝ) + 2) / 2 ^ j) := by
    intro j _
    have hpj : (0 : ℝ) < 2 ^ j := by positivity
    have hterm : ∀ ρ ∈ S.filter (fun ρ => jf ρ = j), (mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖ ≤
        (mult χ ρ : ℝ) * (1 / (T * 2 ^ j) ^ 2) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hd := (dyadic_index hT0 (hS ρ hρ.1).2).1
      rw [show Nat.log 2 ⌊|ρ.im| / T⌋₊ = j from hρ.2] at hd
      have hpos : 0 < T * 2 ^ j := by positivity
      have hsq : (T * 2 ^ j) ^ 2 ≤ ‖(ρ + 1) * (ρ + 2)‖ := by
        refine le_trans ?_ (im_sq_le_norm_mul ρ)
        rw [← sq_abs ρ.im]; exact pow_le_pow_left₀ hpos.le hd 2
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact one_div_le_one_div_of_le (by positivity) hsq
    have hcount : ∑ ρ ∈ S with jf ρ = j, (mult χ ρ : ℝ) ≤
        C0 * (T * 2 ^ (j + 1) + 1) * Real.log (q * (T * 2 ^ (j + 1) + 2)) := by
      apply hup q χ hχ _ (by positivity)
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hd := (dyadic_index hT0 (hS ρ hρ.1).2).2
      rw [show Nat.log 2 ⌊|ρ.im| / T⌋₊ = j from hρ.2] at hd
      exact ⟨(hS ρ hρ.1).1, hd.le⟩
    have hlog : Real.log (q * (T * 2 ^ (j + 1) + 2)) ≤ ((j : ℝ) + 2) * L := by
      have hp1 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
      calc Real.log (q * (T * 2 ^ (j + 1) + 2)) ≤ Real.log (q * (T + 2) * 2 ^ (j + 1)) := by
            apply Real.log_le_log (by positivity)
            have : T * 2 ^ (j + 1) + 2 ≤ (T + 2) * 2 ^ (j + 1) := by nlinarith
            nlinarith
        _ = L + (j + 1) * Real.log 2 := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ L + (j + 1) * L := by gcongr
        _ = ((j : ℝ) + 2) * L := by ring
    have hcnt3 : T * 2 ^ (j + 1) + 1 ≤ 3 * (T * 2 ^ j) := by
      have : (1 : ℝ) ≤ T * 2 ^ j := by nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := j) (by norm_num)]
      rw [pow_succ]; linarith
    have hLnn : 0 ≤ L := le_trans hl2p.le hl2
    calc _ ≤ ∑ ρ ∈ S with jf ρ = j, (mult χ ρ : ℝ) * (1 / (T * 2 ^ j) ^ 2) := sum_le_sum hterm
      _ = (∑ ρ ∈ S with jf ρ = j, (mult χ ρ : ℝ)) * (1 / (T * 2 ^ j) ^ 2) := by rw [sum_mul]
      _ ≤ (C0 * (3 * (T * 2 ^ j)) * (((j : ℝ) + 2) * L)) * (1 / (T * 2 ^ j) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          refine hcount.trans ?_
          apply mul_le_mul (mul_le_mul_of_nonneg_left hcnt3 hC0) hlog
            (Real.log_nonneg (by
              have h2p : (0 : ℝ) ≤ T * 2 ^ (j + 1) := by positivity
              nlinarith))
            (by positivity)
      _ = 3 * C0 * L / T * (((j : ℝ) + 2) / 2 ^ j) := by
          field_simp
  have hLnn : 0 ≤ L := le_trans hl2p.le hl2
  calc _ ≤ ∑ j ∈ range N, 3 * C0 * L / T * (((j : ℝ) + 2) / 2 ^ j) := sum_le_sum hfib
    _ = 3 * C0 * L / T * ∑ j ∈ range N, (((j : ℝ) + 2) / 2 ^ j) := by rw [mul_sum]
    _ ≤ 3 * C0 * L / T * 6 := mul_le_mul_of_nonneg_left (sum_jtwo_le N) (by positivity)
    _ = 18 * C0 * L / T := by ring

/-- elementary: for `Re ρ ≥ -1/2`, `3/4 ≤ ‖(ρ + 1)(ρ + 2)‖`. -/
lemma norm_mul_ge_of_re {ρ : ℂ} (h : -1 / 2 ≤ ρ.re) : 3 / 4 ≤ ‖(ρ + 1) * (ρ + 2)‖ := by
  rw [norm_mul]
  have h1 : 1 / 2 ≤ ‖ρ + 1‖ := le_trans (by simp; linarith) (Complex.re_le_norm (ρ + 1))
  have h2 : 3 / 2 ≤ ‖ρ + 2‖ := le_trans (by simp; linarith) (Complex.re_le_norm (ρ + 2))
  nlinarith

/-- elementary: `log (3q) ≤ 2 log (q + 2)` for `q ≥ 1`. -/
lemma log_three_q_le {q : ℝ} (hq : 1 ≤ q) : Real.log (q * (1 + 2)) ≤ 2 * Real.log (q + 2) := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by positivity)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  nlinarith

/-- Davenport ch. 17: the zero sum `Σ m(ρ)/|(ρ+1)(ρ+2)|` over any finite set of zeros is
`≤ C log(q + 2)`, uniformly. -/
theorem zero_sum_total : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ Zall χ) →
      (∑ ρ ∈ S, (mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖) ≤ C * Real.log (q + 2) := by
  classical
  obtain ⟨C0, hC0, hup⟩ := zero_mult_up_to
  obtain ⟨C1, hC1, htail⟩ := zero_sum_tail
  refine ⟨2 * (8 / 3 * C0 + C1), by positivity, fun q _ χ hχ S hS => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL := log_three_q_le hq1
  have hL0 : 0 ≤ Real.log ((q : ℝ) * (1 + 2)) := Real.log_nonneg (by nlinarith)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => |ρ.im| ≤ 1)]
  have hlow : ∑ ρ ∈ S with |ρ.im| ≤ 1, (mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖ ≤
      8 / 3 * C0 * Real.log ((q : ℝ) * (1 + 2)) := by
    calc _ ≤ ∑ ρ ∈ S with |ρ.im| ≤ 1, (mult χ ρ : ℝ) * (4 / 3) := by
          apply sum_le_sum; intro ρ hρ
          rw [Finset.mem_filter] at hρ
          have hn := norm_mul_ge_of_re (hS ρ hρ.1).2.1
          rw [div_eq_mul_one_div]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by linarith)]; nlinarith
      _ = (∑ ρ ∈ S with |ρ.im| ≤ 1, (mult χ ρ : ℝ)) * (4 / 3) := by rw [sum_mul]
      _ ≤ (C0 * (1 + 1) * Real.log ((q : ℝ) * (1 + 2))) * (4 / 3) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          apply hup q χ hχ 1 (by norm_num)
          intro ρ hρ; rw [Finset.mem_filter] at hρ; exact ⟨hS ρ hρ.1, hρ.2⟩
      _ = 8 / 3 * C0 * Real.log ((q : ℝ) * (1 + 2)) := by ring
  have hhigh : ∑ ρ ∈ S with ¬ |ρ.im| ≤ 1, (mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖ ≤
      C1 * Real.log ((q : ℝ) * (1 + 2)) := by
    have := htail q χ hχ 1 le_rfl (S.filter (fun ρ => ¬ |ρ.im| ≤ 1)) (fun ρ hρ => by
      rw [Finset.mem_filter] at hρ; exact ⟨hS ρ hρ.1, not_le.mp hρ.2⟩)
    simpa using this
  have e1 := mul_le_mul_of_nonneg_left hL (show 0 ≤ 8 / 3 * C0 by positivity)
  have e2 := mul_le_mul_of_nonneg_left hL hC1
  refine le_trans (add_le_add hlow hhigh) (le_trans (add_le_add e1 e2) (le_of_eq ?_))
  ring

/-- elementary: for `x > 0` and `-1/2 ≤ σ ≤ 1`, `x^σ ≤ x^(-1/2) + x`. -/
lemma rpow_le_sum_of_mem {x σ : ℝ} (hx : 0 < x) (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 1) :
    x ^ σ ≤ x ^ (-1 / 2 : ℝ) + x := by
  have ha : 0 ≤ x ^ (-1 / 2 : ℝ) := by positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_le hx1 h2
    rw [Real.rpow_one] at this; linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1.le h1
    linarith

/-- The full zero sum converges. -/
theorem summable_zterm {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) : Summable (fun ρ : Zall χ => zterm χ x ρ) := by
  classical
  obtain ⟨C, hC, htot⟩ := zero_sum_total
  have hg : Summable (fun ρ : Zall χ => (mult χ ρ : ℝ) / ‖((ρ : ℂ) + 1) * ((ρ : ℂ) + 2)‖) := by
    refine summable_of_sum_le (c := C * Real.log (q + 2)) (fun _ => by positivity) (fun u => ?_)
    have := htot q χ hχ (u.map (Function.Embedding.subtype _)) (fun ρ hρ => by
      rw [Finset.mem_map] at hρ
      obtain ⟨a, _, rfl⟩ := hρ
      exact a.2)
    simpa [Finset.sum_map] using this
  refine Summable.of_norm_bounded (hg.mul_left (x ^ (-1 / 2 : ℝ) + x)) (fun ρ => ?_)
  have hre : -1 / 2 ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 := by
    refine ⟨ρ.2.2.1, ?_⟩
    rcases Zall_nt_or_zero hχ ρ.2 with h | h
    · exact h.2.2.le
    · rw [h]; simp
  have hb := rpow_le_sum_of_mem hx hre.1 hre.2
  simp only [zterm, norm_mul, norm_div, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hm : (0 : ℝ) ≤ (mult χ ρ : ℝ) := by positivity
  have hn : 0 ≤ ‖(ρ : ℂ) + 1‖ * ‖(ρ : ℂ) + 2‖ := by positivity
  calc (mult χ ρ : ℝ) * (x ^ (ρ : ℂ).re / (‖(ρ : ℂ) + 1‖ * ‖(ρ : ℂ) + 2‖))
      = (mult χ ρ : ℝ) / (‖(ρ : ℂ) + 1‖ * ‖(ρ : ℂ) + 2‖) * x ^ (ρ : ℂ).re := by ring
    _ ≤ (mult χ ρ : ℝ) / (‖(ρ : ℂ) + 1‖ * ‖(ρ : ℂ) + 2‖) * (x ^ (-1 / 2 : ℝ) + x) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring
end LeanLab.Linnik.ExplicitFormula
