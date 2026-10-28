module

public import LeanLab.Halupczok2012.Statements

/-!
# P0077 Halupczok 2012, Theorem 2: combinatorial steps of the reduction, unit U-1439

AI wrote the Lean code, Claude, run 20261021T1603Z-28836. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Everything here is elementary and PROVED, no cited input.

* `ternSum_eq`: the ternary sum of Theorem 2 is `∑_{p₁} log p₁ · binSum(n - p₁)`, the
  substitution `2k₁ = n - p₁` of the paper's proof of Theorem 2.
* `card_cong_le`: at most `y/l + 1` integers of a window of length `y` lie in one class mod `l`.
* `sum_inv_lcm_le`: `∑_{q₁, q₂ ≤ Q} 1/[q₁, q₂] ≤ (1 + log Q)³`.
* `divisor_moment`: `∑_{m ∈ W} (#{q ≤ Q : q ∣ m - a})² ≤ y (1 + log Q)³ + Q²` for `W` inside a
  window of length `y`.
* `sum_q_abs_sq_le`: Cauchy-Schwarz,
  `(∑_{q ≤ Q} |∑_{m ∈ W, m ≡ a (q)} w m|)² ≤ (∑_{m∈W} w m²) · ∑_{m∈W} (#{q ≤ Q : m ≡ a (q)})²`.
  For `Q² ≪ y` this replaces the paper's Lemma 1, which is needed only for larger `Q`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-- The primes `p₁ ∈ [X₁, X₁ + Y₁]`, `p₁ ≡ a (q)`, `p₁ ≤ n`. -/
noncomputable def P1 (n : ℕ) (X1 Y1 : ℝ) (q : ℕ) (a : ℤ) : Finset ℕ :=
  (range (n + 1)).filter (fun p => p.Prime ∧ X1 < p ∧ (p : ℝ) ≤ X1 + Y1 ∧ (p : ℤ) ≡ a [ZMOD q])

/-- **The substitution of the proof of Theorem 2.** -/
theorem ternSum_eq (n : ℕ) (X1 Y1 X2 Y2 : ℝ) (q : ℕ) (a : ℤ) :
    ternSum n X1 Y1 X2 Y2 q a =
      ∑ p ∈ P1 n X1 Y1 q a, Real.log p * binSum X2 Y2 (n - p) := by
  unfold ternSum P1
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hc : i.Prime ∧ X1 < i ∧ (i : ℝ) ≤ X1 + Y1 ∧ (i : ℤ) ≡ a [ZMOD q]
  · rw [if_pos hc]
    unfold binSum binSumAP
    rw [Finset.mul_sum, Finset.sum_filter]
    have hsub : range (n - i + 1) ⊆ range (n + 1) := Finset.range_subset_range.mpr (by omega)
    refine (Finset.sum_subset hsub ?hz).symm.trans ?main
    case hz =>
      intro j _ hj
      rw [if_neg]
      rintro ⟨-, -, hij, -⟩
      exact hj (Finset.mem_range.mpr (by omega))
    case main =>
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ n - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hij : i + j ≤ n := by omega
      by_cases h2 : j.Prime ∧ (n - i - j).Prime ∧ X2 < j ∧ (j : ℝ) ≤ X2 + Y2 ∧
          (j : ℤ) ≡ 0 [ZMOD ((1 : ℕ) : ℤ)]
      · rw [if_pos h2, if_pos ⟨hc.1, h2.1, hij, h2.2.1, hc.2.1, hc.2.2.1, h2.2.2.1, h2.2.2.2.1,
          hc.2.2.2⟩]
        ring
      · rw [if_neg h2, if_neg]
        rintro ⟨-, h1, -, h3, -, -, h5, h6, -⟩
        exact h2 ⟨h1, h3, h5, h6, Int.modEq_one⟩
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    rintro ⟨h1, -, -, -, h5, h6, -, -, h9⟩
    exact hc ⟨h1, h5, h6, h9⟩

/-- **Counting in one residue class.** -/
theorem card_cong_le {S : Finset ℕ} {x y : ℝ} {l : ℕ} (hl : 0 < l) (hy : 0 ≤ y)
    (hS : ∀ m ∈ S, x < m ∧ (m : ℝ) ≤ x + y)
    (hc : ∀ m ∈ S, ∀ m' ∈ S, (m : ℤ) ≡ (m' : ℤ) [ZMOD l]) :
    (S.card : ℝ) ≤ y / l + 1 := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  rcases S.eq_empty_or_nonempty with h | hne
  · simp [h]; positivity
  set m0 := S.min' hne with hm0
  have hm0S : m0 ∈ S := S.min'_mem hne
  have key : ∀ m ∈ S, m0 ≤ m ∧ l ∣ m - m0 ∧ (((m - m0) / l : ℕ) : ℝ) ≤ y / l := by
    intro m hm
    have hle : m0 ≤ m := S.min'_le m hm
    have hd : l ∣ m - m0 := by
      have := (hc m0 hm0S m hm).dvd
      rw [← Int.natCast_dvd_natCast, Nat.cast_sub hle]
      exact this
    refine ⟨hle, hd, ?_⟩
    rw [le_div_iff₀ hl']
    have h1 : (((m - m0) / l : ℕ) : ℝ) * l = ((m - m0 : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
    rw [h1, Nat.cast_sub hle]
    have := (hS m hm).2
    have := (hS m0 hm0S).1
    linarith
  have hinj : Set.InjOn (fun m => (m - m0) / l) S := by
    intro m hm m' hm' he
    simp only at he
    obtain ⟨h1, h2, -⟩ := key m hm
    obtain ⟨h1', h2', -⟩ := key m' hm'
    have e1 := Nat.div_mul_cancel h2
    have e2 := Nat.div_mul_cancel h2'
    rw [he] at e1
    omega
  have hmaps : Set.MapsTo (fun m => (m - m0) / l) S (range (⌊y / l⌋₊ + 1)) := by
    intro m hm
    simp only [Finset.coe_range, Set.mem_Iio]
    have := (key m hm).2.2
    have := Nat.le_floor this
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  calc (S.card : ℝ) ≤ ((⌊y / l⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ y / l + 1 := by
      push_cast
      have := Nat.floor_le (div_nonneg hy hl'.le)
      linarith

/-- The real harmonic bound. -/
theorem sum_inv_Icc_le (N : ℕ) : ∑ i ∈ Icc 1 N, ((i : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have := harmonic_le_one_add_log N
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
  exact this

theorem one_add_log_nonneg (N : ℕ) : 0 ≤ 1 + Real.log N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast h)
    linarith

/-- The multiples of `d` in `[1, N]`. -/
theorem sum_dvd_inv_le (N d : ℕ) (hd : 0 < d) :
    ∑ q ∈ Icc 1 N, (if d ∣ q then ((q : ℝ))⁻¹ else 0) ≤ (d : ℝ)⁻¹ * (1 + Real.log N) := by
  rw [← Finset.sum_filter]
  have hsub : (Icc 1 N).filter (fun q => d ∣ q) ⊆ (Icc 1 N).image (fun j => d * j) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩ := hq
    rw [Finset.mem_image]
    refine ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · simp [h] at h1
      · exact h
    · calc j ≤ d * j := Nat.le_mul_of_pos_left j hd
        _ ≤ N := h2
  calc ∑ q ∈ (Icc 1 N).filter (fun q => d ∣ q), ((q : ℝ))⁻¹
      ≤ ∑ q ∈ (Icc 1 N).image (fun j => d * j), ((q : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ j ∈ Icc 1 N, ((d * j : ℕ) : ℝ)⁻¹ := by
        rw [Finset.sum_image]
        intro x _ y _ h
        exact Nat.eq_of_mul_eq_mul_left hd h
    _ = (d : ℝ)⁻¹ * ∑ j ∈ Icc 1 N, ((j : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        rw [mul_inv]
    _ ≤ (d : ℝ)⁻¹ * (1 + Real.log N) := by
        gcongr
        exact sum_inv_Icc_le N

/-- **`∑_{q₁, q₂ ≤ N} 1/[q₁, q₂] ≤ (1 + log N)³`.** -/
theorem sum_inv_lcm_le (N : ℕ) :
    ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ ≤ (1 + Real.log N) ^ 3 := by
  set H := 1 + Real.log N with hH
  have hH0 : 0 ≤ H := one_add_log_nonneg N
  -- `1/[q₁,q₂] = (q₁,q₂)/(q₁q₂) ≤ ∑_{d ∣ q₁, d ∣ q₂} d/(q₁q₂)`
  have step1 : ∀ q1 ∈ Icc 1 N, ∀ q2 ∈ Icc 1 N, ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ ≤
      ∑ d ∈ Icc 1 N, ((d : ℕ) : ℝ) * ((if (d : ℕ) ∣ q1 then ((q1 : ℝ))⁻¹ else 0) *
        (if (d : ℕ) ∣ q2 then ((q2 : ℝ))⁻¹ else 0)) := by
    intro q1 hq1 q2 hq2
    rw [Finset.mem_Icc] at hq1 hq2
    have hg : Nat.gcd q1 q2 ∈ Icc 1 N := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.gcd_pos_of_pos_left _ (by omega),
        (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left q1 q2)).trans hq1.2⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun d : ℕ => (d : ℝ) *
      ((if d ∣ q1 then ((q1 : ℝ))⁻¹ else 0) * (if d ∣ q2 then ((q2 : ℝ))⁻¹ else 0)))
      (fun d _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by split_ifs <;> positivity)
        (by split_ifs <;> positivity))) hg)
    simp only [Nat.gcd_dvd_left, Nat.gcd_dvd_right, if_true]
    have hq1' : (0 : ℝ) < q1 := by exact_mod_cast (show 0 < q1 by omega)
    have hq2' : (0 : ℝ) < q2 := by exact_mod_cast (show 0 < q2 by omega)
    have e : ((Nat.gcd q1 q2 : ℕ) : ℝ) * ((Nat.lcm q1 q2 : ℕ) : ℝ) = (q1 : ℝ) * q2 := by
      rw [← Nat.cast_mul, Nat.gcd_mul_lcm]; push_cast; ring
    have hl : (0 : ℝ) < ((Nat.lcm q1 q2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lcm_pos (by omega) (by omega)
    rw [le_iff_eq_or_lt]; left
    field_simp
    linarith [e]
  calc ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹
      ≤ ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, ∑ d ∈ Icc 1 N, ((d : ℕ) : ℝ) *
          ((if (d : ℕ) ∣ q1 then ((q1 : ℝ))⁻¹ else 0) *
            (if (d : ℕ) ∣ q2 then ((q2 : ℝ))⁻¹ else 0)) :=
        Finset.sum_le_sum (fun q1 h1 => Finset.sum_le_sum (fun q2 h2 => step1 q1 h1 q2 h2))
    _ = ∑ d ∈ Icc 1 N, ((d : ℕ) : ℝ) *
          ((∑ q ∈ Icc 1 N, (if (d : ℕ) ∣ q then ((q : ℝ))⁻¹ else 0)) *
          (∑ q ∈ Icc 1 N, (if (d : ℕ) ∣ q then ((q : ℝ))⁻¹ else 0))) := by
        rw [eq_comm]
        simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_comm.trans ?_
        apply Finset.sum_congr rfl
        intro q1 _
        exact Finset.sum_comm
    _ ≤ ∑ d ∈ Icc 1 N, ((d : ℕ) : ℝ) * (((d : ℝ))⁻¹ * H * (((d : ℝ))⁻¹ * H)) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
        have hb := sum_dvd_inv_le N d hd0
        have hnn : 0 ≤ ∑ q ∈ Icc 1 N, (if (d : ℕ) ∣ q then ((q : ℝ))⁻¹ else 0) :=
          Finset.sum_nonneg (fun q _ => by split_ifs <;> positivity)
        gcongr
    _ = H ^ 2 * ∑ d ∈ Icc 1 N, ((d : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : (d : ℝ) ≠ 0 := by
          have := (Finset.mem_Icc.mp hd).1; positivity
        field_simp
    _ ≤ H ^ 2 * H := by gcongr; exact sum_inv_Icc_le N
    _ = H ^ 3 := by ring

/-- The number of `q ≤ N` with `m ≡ a (q)`. -/
noncomputable def Dq (N : ℕ) (a : ℤ) (m : ℕ) : ℕ :=
  #((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a [ZMOD q]))

theorem modEq_lcm {m : ℤ} {a : ℤ} {q1 q2 : ℕ} (h1 : m ≡ a [ZMOD q1]) (h2 : m ≡ a [ZMOD q2]) :
    m ≡ a [ZMOD (Nat.lcm q1 q2 : ℕ)] := by
  have d1 := h1.symm.dvd
  have d2 := h2.symm.dvd
  rw [Int.natCast_dvd] at d1 d2
  have : Nat.lcm q1 q2 ∣ (m - a).natAbs := Nat.lcm_dvd d1 d2
  rw [← Int.natCast_dvd] at this
  exact (Int.ModEq.symm (Int.modEq_of_dvd this))

/-- **The divisor moment.** -/
theorem divisor_moment {W : Finset ℕ} {x y : ℝ} (hy : 0 ≤ y)
    (hW : ∀ m ∈ W, x < m ∧ (m : ℝ) ≤ x + y) (N : ℕ) (a : ℤ) :
    ∑ m ∈ W, ((Dq N a m : ℕ) : ℝ) ^ 2 ≤ y * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2 := by
  have hsq : ∀ m, ((Dq N a m : ℕ) : ℝ) ^ 2 = ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N,
      (if (m : ℤ) ≡ a [ZMOD q1] ∧ (m : ℤ) ≡ a [ZMOD q2] then (1 : ℝ) else 0) := by
    intro m
    unfold Dq
    rw [Finset.card_filter, sq]
    push_cast
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro q1 _
    apply Finset.sum_congr rfl; intro q2 _
    by_cases h1 : (m : ℤ) ≡ a [ZMOD q1] <;> by_cases h2 : (m : ℤ) ≡ a [ZMOD q2] <;> simp [h1, h2]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hrow : ∀ q1 ∈ Icc 1 N, ∀ q2 ∈ Icc 1 N, ∑ m ∈ W,
      (if (m : ℤ) ≡ a [ZMOD q1] ∧ (m : ℤ) ≡ a [ZMOD q2] then (1 : ℝ) else 0) ≤
      y * ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ + 1 := by
    intro q1 hq1 q2 hq2
    rw [Finset.mem_Icc] at hq1 hq2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hl : 0 < Nat.lcm q1 q2 := Nat.lcm_pos (by omega) (by omega)
    have := card_cong_le (S := W.filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q1] ∧
      (m : ℤ) ≡ a [ZMOD q2])) (x := x) (y := y) hl hy
      (fun m hm => hW m (Finset.mem_filter.mp hm).1)
      (fun m hm m' hm' => by
        obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hm
        obtain ⟨-, h1', h2'⟩ := Finset.mem_filter.mp hm'
        exact (modEq_lcm h1 h2).trans (modEq_lcm h1' h2').symm)
    rw [div_eq_mul_inv] at this
    exact this
  calc ∑ q1 ∈ Icc 1 N, ∑ m ∈ W, ∑ q2 ∈ Icc 1 N,
        (if (m : ℤ) ≡ a [ZMOD q1] ∧ (m : ℤ) ≡ a [ZMOD q2] then (1 : ℝ) else 0)
      = ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, ∑ m ∈ W,
        (if (m : ℤ) ≡ a [ZMOD q1] ∧ (m : ℤ) ≡ a [ZMOD q2] then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro q1 _; rw [Finset.sum_comm]
    _ ≤ ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, (y * ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ + 1) :=
        Finset.sum_le_sum (fun q1 h1 => Finset.sum_le_sum (fun q2 h2 => hrow q1 h1 q2 h2))
    _ = y * ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ + (N : ℝ) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
          mul_one, Finset.mul_sum]
        push_cast; ring
    _ ≤ y * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2 := by
        gcongr; exact sum_inv_lcm_le N

/-- **Cauchy-Schwarz over the moduli.** -/
theorem sum_q_abs_sq_le (W : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) (a : ℤ) :
    (∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q]), w m|) ^ 2 ≤
      (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((Dq N a m : ℕ) : ℝ) ^ 2 := by
  have h1 : ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q]), w m| ≤
      ∑ m ∈ W, |w m| * ((Dq N a m : ℕ) : ℝ) := by
    calc ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q]), w m|
        ≤ ∑ q ∈ Icc 1 N, ∑ m ∈ W, (if (m : ℤ) ≡ a [ZMOD q] then |w m| else 0) := by
          apply Finset.sum_le_sum; intro q _
          rw [← Finset.sum_filter]
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m ∈ W, |w m| * ((Dq N a m : ℕ) : ℝ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro m _
          unfold Dq
          rw [Finset.card_filter]; push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _
          split_ifs <;> simp
  have h0 : 0 ≤ ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q]), w m| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc _ ≤ (∑ m ∈ W, |w m| * ((Dq N a m : ℕ) : ℝ)) ^ 2 := by gcongr
    _ ≤ (∑ m ∈ W, |w m| ^ 2) * ∑ m ∈ W, ((Dq N a m : ℕ) : ℝ) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((Dq N a m : ℕ) : ℝ) ^ 2 := by simp_rw [sq_abs]

end LeanLab.Halupczok2012
