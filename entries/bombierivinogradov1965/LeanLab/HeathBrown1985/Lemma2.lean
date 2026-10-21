module

public import Mathlib
public import LeanLab.HeathBrown1985.Elementary

/-!
P0096 Heath-Brown 1985, Lemma 2, 2.11, deduced from Lemma 1, 2.7, the bound 2.5 and the
divisor moments 2.2 with t = 2 and t = 3, following pages 50 to 52 of the paper.
The divisor moments are named inputs `DivMoment2` and `DivMoment3`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- 2.2 with `t = 2`: `Σ_{n ≤ N} d(n)² ≪ N (log N)³`, written with `1 + log N`. -/
def DivMoment2 : Prop :=
  ∃ c : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 2 ≤ c * N * (1 + Real.log N) ^ 3

/-- 2.2 with `t = 3`: `Σ_{n ≤ N} d(n)³ ≪ N (log N)⁷`, written with `1 + log N`. -/
def DivMoment3 : Prop :=
  ∃ c : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 3 ≤ c * N * (1 + Real.log N) ^ 7

/-! ### Divisor function facts -/

theorem card_divisors_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [Nat.divisors_mul]; exact Finset.card_mul_le

theorem sum_card_divisors_divisors_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ a ∈ m.divisors, (a.divisors.card : ℝ) ≤ (m.divisors.card : ℝ) ^ 2 := by
  calc ∑ a ∈ m.divisors, (a.divisors.card : ℝ) ≤ ∑ a ∈ m.divisors, (m.divisors.card : ℝ) := by
        apply sum_le_sum
        intro a ha
        have hdvd := Nat.dvd_of_mem_divisors ha
        exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd (by omega) hdvd)
    _ = _ := by rw [sum_const, nsmul_eq_mul, sq]

/-- The `t⁻¹` form of 2.3, as used on page 52:
`Σ_{t ≤ N} t⁻¹ (t, m) d(t) ≤ d(m)² (1 + log N)²`. -/
theorem sum_gcd_divisors_div_le (m N : ℕ) (hm : 1 ≤ m) :
    ∑ t ∈ Icc 1 N, (Nat.gcd t m : ℝ) * (t.divisors.card : ℝ) / t ≤
      (m.divisors.card : ℝ) ^ 2 * (1 + Real.log N) ^ 2 := by
  -- (t, m) ≤ Σ_{a ∣ m, a ∣ t} a
  have hg : ∀ t ∈ Icc 1 N, (Nat.gcd t m : ℝ) ≤ ∑ a ∈ m.divisors.filter (· ∣ t), (a : ℝ) := by
    intro t ht
    have hmem : Nat.gcd t m ∈ m.divisors.filter (· ∣ t) := by
      simp only [mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.gcd_dvd_right t m, by omega⟩, Nat.gcd_dvd_left t m⟩
    exact single_le_sum (f := fun a : ℕ => (a : ℝ)) (fun _ _ => by positivity) hmem
  have hD : 0 ≤ ∑ b ∈ Icc 1 N, (b.divisors.card : ℝ) / b :=
    sum_nonneg (fun _ _ => by positivity)
  calc ∑ t ∈ Icc 1 N, (Nat.gcd t m : ℝ) * (t.divisors.card : ℝ) / t
      ≤ ∑ t ∈ Icc 1 N, (∑ a ∈ m.divisors.filter (· ∣ t), (a : ℝ)) * (t.divisors.card : ℝ) / t := by
        apply sum_le_sum; intro t ht
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (hg t ht) (by positivity)
    _ = ∑ a ∈ m.divisors, ∑ t ∈ (Icc 1 N).filter (a ∣ ·), (a : ℝ) * (t.divisors.card : ℝ) / t := by
        simp_rw [sum_mul, sum_div]
        rw [Finset.sum_comm' (t' := m.divisors) (s' := fun a => (Icc 1 N).filter (a ∣ ·))]
        intro t a
        simp only [mem_filter]
        tauto
    _ ≤ ∑ a ∈ m.divisors, (a.divisors.card : ℝ) * ∑ b ∈ Icc 1 N, (b.divisors.card : ℝ) / b := by
        apply sum_le_sum; intro a ha
        have ha1 : 1 ≤ a := Nat.pos_of_mem_divisors ha
        have hsub : (Icc 1 N).filter (a ∣ ·) ⊆ (Icc 1 N).image (a * ·) := by
          intro k hk
          simp only [mem_filter, mem_Icc] at hk
          obtain ⟨⟨hk1, hkN⟩, b, rfl⟩ := hk
          simp only [mem_image, mem_Icc]
          refine ⟨b, ⟨?_, ?_⟩, rfl⟩
          · rcases Nat.eq_zero_or_pos b with h | h
            · subst h; simp at hk1
            · exact h
          · exact le_trans (Nat.le_mul_of_pos_left b (by omega)) hkN
        calc ∑ t ∈ (Icc 1 N).filter (a ∣ ·), (a : ℝ) * (t.divisors.card : ℝ) / t
            ≤ ∑ t ∈ (Icc 1 N).image (a * ·), (a : ℝ) * (t.divisors.card : ℝ) / t :=
              sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ = ∑ b ∈ Icc 1 N, (a : ℝ) * ((a * b).divisors.card : ℝ) / ((a * b : ℕ) : ℝ) := by
              rw [sum_image]; intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h
          _ ≤ ∑ b ∈ Icc 1 N, (a.divisors.card : ℝ) * ((b.divisors.card : ℝ) / b) := by
              apply sum_le_sum; intro b hb
              have hb1 : 1 ≤ b := (mem_Icc.mp hb).1
              have hd : ((a * b).divisors.card : ℝ) ≤ (a.divisors.card : ℝ) * b.divisors.card := by
                exact_mod_cast card_divisors_mul_le a b
              have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
              have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
              push_cast
              rw [show (a : ℝ) * ((a * b).divisors.card : ℝ) / (a * b) =
                ((a * b).divisors.card : ℝ) / b by field_simp]
              rw [mul_div_assoc']
              exact div_le_div_of_nonneg_right hd hb0.le
          _ = _ := by rw [mul_sum]
    _ = (∑ a ∈ m.divisors, (a.divisors.card : ℝ)) * ∑ b ∈ Icc 1 N, (b.divisors.card : ℝ) / b := by
        rw [sum_mul]
    _ ≤ (m.divisors.card : ℝ) ^ 2 * (1 + Real.log N) ^ 2 :=
        mul_le_mul (sum_card_divisors_divisors_le m hm) (sum_divisors_div_le_log N) hD
          (by positivity)

/-- `(log y)² ≤ 4 y` for `y ≥ 1`. -/
theorem log_sq_le (y : ℝ) (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by
  have hy0 : 0 < y := by linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [← Real.log_rpow hs, show ((Real.sqrt y) ^ (2 : ℝ)) = y by
      rw [Real.rpow_two, Real.sq_sqrt hy0.le]]
  have h0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h3 : Real.log y ≤ 2 * Real.sqrt y := by linarith
  calc Real.log y ^ 2 ≤ (2 * Real.sqrt y) ^ 2 := pow_le_pow_left₀ h0 h3 2
    _ = 4 * y := by rw [mul_pow, Real.sq_sqrt hy0.le]; ring

/-! ### Residue form of `δ₁` and the lifting `δ₁(x,k,Q) ≤ δ₁(x,jk,Q)` -/

/-- `Σ_{n ≤ N, n ≡ r mod k} f(n)`. -/
def resSum (f : ℕ → ℝ) (N k r : ℕ) : ℝ := ∑ n ∈ (Icc 1 N).filter (fun n => n % k = r), f n

/-- Summing `F (l % k)` over `l ∈ [1, k]` is summing `F r` over `r < k`. -/
theorem sum_Icc_mod_eq (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ) :
    ∑ l ∈ Icc 1 k, F (l % k) = ∑ r ∈ range k, F r := by
  apply Finset.sum_nbij' (fun l => l % k) (fun r => if r = 0 then k else r)
  · intro l _; simp only [mem_range]; exact Nat.mod_lt _ (by omega)
  · intro r hr
    simp only [mem_range] at hr
    simp only [mem_Icc]
    split_ifs with h <;> omega
  · intro l hl
    simp only [mem_Icc] at hl
    split_ifs with h
    · rcases lt_or_eq_of_le hl.2 with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at h; omega
      · exact h'.symm
    · rcases lt_or_eq_of_le hl.2 with h' | h'
      · exact Nat.mod_eq_of_lt h'
      · subst h'; simp at h
  · intro r hr
    simp only [mem_range] at hr
    split_ifs with h
    · subst h; simp
    · exact Nat.mod_eq_of_lt hr
  · intro l _; rfl

theorem delta1_eq (x : ℝ) (k : ℕ) (Q : ℝ) (hk : 1 ≤ k) :
    delta1 x k Q = ∑ r ∈ range k, |resSum (DeltaQ Q) ⌊x⌋₊ k r| := by
  unfold delta1 apSum
  exact sum_Icc_mod_eq k hk (fun r => |resSum (DeltaQ Q) ⌊x⌋₊ k r|)

theorem resSum_split (f : ℕ → ℝ) (N k j r : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    resSum f N k r =
      ∑ s ∈ (range (k * j)).filter (fun s => s % k = r), resSum f N (k * j) s := by
  unfold resSum
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Icc 1 N).filter (fun n => n % k = r))
    (t := (range (k * j)).filter (fun s => s % k = r)) (g := fun n => n % (k * j))]
  · apply sum_congr rfl
    intro s hs
    simp only [mem_filter, mem_range] at hs
    apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [← Nat.mod_mul_right_mod n k j, h3, hs.2]
  · intro n hn
    simp only [mem_filter] at hn
    simp only [mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    rw [Nat.mod_mul_right_mod, hn.2]

theorem delta1_le_mul (x : ℝ) (k j : ℕ) (Q : ℝ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    delta1 x k Q ≤ delta1 x (k * j) Q := by
  rw [delta1_eq x k Q hk, delta1_eq x (k * j) Q (Nat.one_le_iff_ne_zero.mpr (by positivity))]
  calc ∑ r ∈ range k, |resSum (DeltaQ Q) ⌊x⌋₊ k r|
      ≤ ∑ r ∈ range k, ∑ s ∈ (range (k * j)).filter (fun s => s % k = r),
          |resSum (DeltaQ Q) ⌊x⌋₊ (k * j) s| := by
        apply sum_le_sum; intro r _
        rw [resSum_split _ _ k j r hk hj]
        exact abs_sum_le_sum_abs _ _
    _ = _ := by
        apply Finset.sum_fiberwise_of_maps_to
        intro s _; simp only [mem_range]; exact Nat.mod_lt _ (by omega)

/-! ### Averaging over multiples, page 51 -/

theorem delta1_nonneg (x : ℝ) (k : ℕ) (Q : ℝ) : 0 ≤ delta1 x k Q :=
  sum_nonneg (fun _ _ => abs_nonneg _)

theorem avg_one (x Q : ℝ) (M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    delta1 x k Q / k ≤ (2 / M) * ∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q := by
  set q := M / k with hq
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).mpr hkM
  have hlt : M < k * (q + 1) := by
    have := Nat.lt_mul_div_succ M (show 0 < k by omega); rw [hq]; linarith
  have hkq : k * q ≤ M := Nat.mul_div_le M k
  have h2 : M ≤ 2 * (k * q) := by nlinarith
  have hsub : (Icc 1 q).image (fun i => k * (q + i)) ⊆ (Ioc M (2 * M)).filter (k ∣ ·) := by
    intro h hh
    simp only [mem_image, mem_Icc] at hh
    obtain ⟨i, ⟨hi1, hiq⟩, rfl⟩ := hh
    simp only [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · calc M < k * (q + 1) := hlt
        _ ≤ k * (q + i) := Nat.mul_le_mul_left _ (by omega)
    · calc k * (q + i) ≤ k * (q + q) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (k * q) := by ring
        _ ≤ 2 * M := by omega
  have hinj : Set.InjOn (fun i => k * (q + i)) (Icc 1 q : Set ℕ) := by
    intro a _ b _ hab
    have := Nat.eq_of_mul_eq_mul_left (show 0 < k by omega) hab
    omega
  have hsum : (q : ℝ) * delta1 x k Q ≤
      ∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q := by
    calc (q : ℝ) * delta1 x k Q = ∑ i ∈ Icc 1 q, delta1 x k Q := by
          rw [sum_const, nsmul_eq_mul]; simp
      _ ≤ ∑ i ∈ Icc 1 q, delta1 x (k * (q + i)) Q := by
          apply sum_le_sum; intro i hi
          exact delta1_le_mul x k (q + i) Q hk (by omega)
      _ = ∑ h ∈ (Icc 1 q).image (fun i => k * (q + i)), delta1 x h Q := by
          rw [sum_image hinj]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => delta1_nonneg _ _ _)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h2R : (M : ℝ) ≤ 2 * (k * q) := by exact_mod_cast h2
  have hd := delta1_nonneg x k Q
  rw [div_le_iff₀ hkR]
  calc delta1 x k Q = (2 / M) * (M / 2 * delta1 x k Q) := by field_simp
    _ ≤ (2 / M) * ((k * q) * delta1 x k Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hd; linarith
    _ ≤ (2 / M) * ((∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q) * k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = _ := by ring

theorem sum_avg (x Q : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Icc 1 M, delta1 x k Q / k ≤
      (2 / M) * ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) * delta1 x h Q := by
  calc ∑ k ∈ Icc 1 M, delta1 x k Q / k
      ≤ ∑ k ∈ Icc 1 M, (2 / M) * ∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q := by
        apply sum_le_sum; intro k hk
        exact avg_one x Q M k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    _ = (2 / M) * ∑ h ∈ Ioc M (2 * M), ∑ k ∈ (Icc 1 M).filter (· ∣ h), delta1 x h Q := by
        rw [← mul_sum]; congr 1
        rw [Finset.sum_comm' (t' := Ioc M (2 * M)) (s' := fun h => (Icc 1 M).filter (· ∣ h))]
        intro k h; simp only [mem_filter]; tauto
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum; intro h hh
        rw [sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (delta1_nonneg _ _ _)
        have hh0 : h ≠ 0 := by simp only [mem_Ioc] at hh; omega
        exact_mod_cast card_le_card (fun k hk => by
          simp only [mem_filter, mem_Icc] at hk
          exact Nat.mem_divisors.mpr ⟨hk.2, hh0⟩)

/-! ### Cauchy's inequality twice, 2.12 to 2.13 -/

/-- `δ₂` in residue form. -/
def delta2 (f : ℕ → ℝ) (N h : ℕ) : ℝ := ∑ r ∈ range h, (resSum f N h r) ^ 2

theorem delta1_sq_le (x : ℝ) (h : ℕ) (Q : ℝ) (hh : 1 ≤ h) :
    delta1 x h Q ^ 2 ≤ h * delta2 (DeltaQ Q) ⌊x⌋₊ h := by
  rw [delta1_eq x h Q hh]
  unfold delta2
  have := sq_sum_le_card_mul_sum_sq (s := range h) (f := fun r => |resSum (DeltaQ Q) ⌊x⌋₊ h r|)
  simpa [sq_abs] using this

theorem delta2_nonneg (f : ℕ → ℝ) (N h : ℕ) : 0 ≤ delta2 f N h :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem cauchy_main (x Q : ℝ) (M : ℕ) (hM : 1 ≤ M) (W : ℝ)
    (hW : ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2 ≤ W) :
    (∑ k ∈ Icc 1 M, delta1 x k Q / k) ^ 2 ≤
      (4 / (M : ℝ) ^ 2) * W * (2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set T := ∑ k ∈ Icc 1 M, delta1 x k Q / k
  set U := ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) * delta1 x h Q
  have hT0 : 0 ≤ T := sum_nonneg (fun k _ => div_nonneg (delta1_nonneg _ _ _) (by positivity))
  have hTU : T ≤ (2 / M) * U := sum_avg x Q M hM
  have hU2 : U ^ 2 ≤ (∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2) *
      ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
  have hd1 : ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 ≤
      2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h := by
    rw [mul_sum]; apply sum_le_sum; intro h hh
    simp only [mem_Ioc] at hh
    refine (delta1_sq_le x h Q (by omega)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (delta2_nonneg _ _ _)
    exact_mod_cast hh.2
  have hS0 : 0 ≤ ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hW0 : 0 ≤ W := le_trans (sum_nonneg (fun _ _ => sq_nonneg _)) hW
  calc T ^ 2 ≤ ((2 / M) * U) ^ 2 := pow_le_pow_left₀ hT0 hTU 2
    _ = (4 / (M : ℝ) ^ 2) * U ^ 2 := by ring
    _ ≤ (4 / (M : ℝ) ^ 2) * ((∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2) *
          ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2) :=
        mul_le_mul_of_nonneg_left hU2 (by positivity)
    _ ≤ (4 / (M : ℝ) ^ 2) * (W * (2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hW hd1 hS0 hW0
    _ = _ := by ring

/-! ### Expanding `δ₂`, 2.14 -/

/-- `Σ_{n ≤ N, n > m, n ≡ m (h)} f(n)`. -/
def up (f : ℕ → ℝ) (N h m : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ n % h = m % h), f n

theorem delta2_expand (f : ℕ → ℝ) (N h : ℕ) (hh : 1 ≤ h) :
    delta2 f N h = ∑ m ∈ Icc 1 N, f m ^ 2 + 2 * ∑ m ∈ Icc 1 N, f m * up f N h m := by
  unfold delta2
  -- step 1: as a double sum over congruent pairs
  have e1 : ∑ r ∈ range h, (resSum f N h r) ^ 2 =
      ∑ m ∈ Icc 1 N, f m * ∑ n ∈ (Icc 1 N).filter (fun n => n % h = m % h), f n := by
    have : ∀ r ∈ range h, (resSum f N h r) ^ 2 =
        ∑ m ∈ (Icc 1 N).filter (fun m => m % h = r),
          f m * ∑ n ∈ (Icc 1 N).filter (fun n => n % h = m % h), f n := by
      intro r _
      rw [sq]
      unfold resSum
      rw [sum_mul]
      apply sum_congr rfl
      intro m hm
      simp only [mem_filter] at hm
      rw [hm.2]
    rw [sum_congr rfl this]
    apply Finset.sum_fiberwise_of_maps_to (g := fun m => m % h)
    intro m _; simp only [mem_range]; exact Nat.mod_lt _ (by omega)
  rw [e1]
  -- step 2: split each inner sum into n = m, n > m, n < m
  have e2 : ∀ m ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (fun n => n % h = m % h), f n =
      f m + up f N h m + ∑ n ∈ (Icc 1 N).filter (fun n => n < m ∧ n % h = m % h), f n := by
    intro m hm
    have hsplit : (Icc 1 N).filter (fun n => n % h = m % h) =
        {m} ∪ ((Icc 1 N).filter (fun n => m < n ∧ n % h = m % h) ∪
          (Icc 1 N).filter (fun n => n < m ∧ n % h = m % h)) := by
      ext n; simp only [mem_filter, mem_union, mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy n m with h3 | h3 | h3
        · exact Or.inr (Or.inr ⟨h1, h3, h2⟩)
        · exact Or.inl h3
        · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
      · rintro (h3 | ⟨h1, _, h2⟩ | ⟨h1, _, h2⟩)
        · subst h3; exact ⟨hm, rfl⟩
        · exact ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
    rw [hsplit, sum_union, sum_union, sum_singleton, up]
    · ring
    · rw [disjoint_filter]; intro n _ h1 h2; omega
    · rw [disjoint_singleton_left]
      simp only [mem_union, mem_filter, not_or, not_and]
      exact ⟨fun _ h => absurd h (lt_irrefl m), fun _ h => absurd h (lt_irrefl m)⟩
  rw [sum_congr rfl (fun m hm => by rw [e2 m hm])]
  simp_rw [mul_add, sum_add_distrib]
  -- step 3: the n < m part equals the n > m part by symmetry
  have e3 : ∑ m ∈ Icc 1 N, f m * ∑ n ∈ (Icc 1 N).filter (fun n => n < m ∧ n % h = m % h), f n =
      ∑ m ∈ Icc 1 N, f m * up f N h m := by
    simp_rw [mul_sum, up, mul_sum]
    rw [Finset.sum_comm' (t' := Icc 1 N)
      (s' := fun n => (Icc 1 N).filter (fun m => n < m ∧ m % h = n % h))]
    · apply sum_congr rfl; intro n _; apply sum_congr rfl; intro m _; ring
    · intro m n
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h3, h4.symm⟩, h2⟩
      · rintro ⟨⟨h1, h3, h4⟩, h2⟩; exact ⟨h1, h2, h3, h4.symm⟩
  rw [e3]
  simp_rw [sq]
  ring

/-! ### Re-indexing `n - m = k t`, page 51 -/

/-- The interval sum `Σ_{n ≤ N, m + Mt < n ≤ m + 2Mt, n ≡ m (t)} f(n)`. -/
def inner (f : ℕ → ℝ) (N M m t : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => m + M * t < n ∧ n ≤ m + 2 * M * t ∧ n % t = m % t), f n

theorem mod_eq_iff_dvd_sub {m n h : ℕ} (hmn : m < n) : n % h = m % h ↔ h ∣ n - m := by
  rw [eq_comm]; exact Nat.modEq_iff_dvd' hmn.le

theorem sum_up_eq (f : ℕ → ℝ) (N M m : ℕ) :
    ∑ h ∈ Ioc M (2 * M), up f N h m = ∑ t ∈ Icc 1 N, inner f N M m t := by
  unfold up inner
  rw [Finset.sum_comm' (t' := (Icc 1 N).filter (fun n => m < n))
      (s' := fun n => (Ioc M (2 * M)).filter (fun h => n % h = m % h))]
  rw [Finset.sum_comm' (s := Icc 1 N) (t' := (Icc 1 N).filter (fun n => m < n))
      (s' := fun n => (Icc 1 N).filter
        (fun t => m + M * t < n ∧ n ≤ m + 2 * M * t ∧ n % t = m % t))]
  · apply sum_congr rfl
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    rw [sum_const, sum_const]
    congr 1
    -- the two counts agree, by `h ↦ (n - m) / h`
    apply Finset.card_nbij' (fun h => (n - m) / h) (fun t => (n - m) / t)
    · intro h hh
      simp only [mem_coe, mem_filter, mem_Ioc] at hh
      obtain ⟨⟨hM, h2M⟩, hmod⟩ := hh
      have hd := (mod_eq_iff_dvd_sub hn.2).mp hmod
      obtain ⟨t, ht⟩ := hd
      have hpos : 0 < h := by omega
      have htv : (n - m) / h = t := by rw [ht]; exact Nat.mul_div_cancel_left t hpos
      simp only [mem_coe, mem_filter, mem_Icc]
      rw [htv]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; omega
        · exact h0
      have hlt : t ≤ n - m := by rw [ht]; exact Nat.le_mul_of_pos_left t hpos
      refine ⟨⟨ht1, by omega⟩, ?_, ?_, ?_⟩
      · have : M * t < h * t := Nat.mul_lt_mul_of_pos_right hM ht1
        omega
      · have : h * t ≤ 2 * M * t := Nat.mul_le_mul_right t h2M
        omega
      · exact (mod_eq_iff_dvd_sub hn.2).mpr ⟨h, by rw [ht]; ring⟩
    · intro t ht
      simp only [mem_coe, mem_filter, mem_Icc] at ht
      obtain ⟨⟨ht1, _⟩, hlo, hhi, hmod⟩ := ht
      have hmn : m < n := by omega
      have hd := (mod_eq_iff_dvd_sub hmn).mp hmod
      obtain ⟨h, hh⟩ := hd
      have htv : (n - m) / t = h := by rw [hh]; exact Nat.mul_div_cancel_left h (by omega)
      simp only [mem_coe, mem_filter, mem_Ioc]
      rw [htv]
      refine ⟨⟨?_, ?_⟩, (mod_eq_iff_dvd_sub hmn).mpr ⟨t, by rw [hh]; ring⟩⟩
      · by_contra hc
        have : t * h ≤ t * M := Nat.mul_le_mul_left t (by omega)
        have : M * t = t * M := Nat.mul_comm M t
        omega
      · by_contra hc
        have : t * (2 * M) < t * h := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        have : 2 * M * t = t * (2 * M) := by ring
        omega
    · intro h hh
      simp only [mem_coe, mem_filter, mem_Ioc] at hh
      have hd := (mod_eq_iff_dvd_sub hn.2).mp hh.2
      exact Nat.div_div_self hd (by omega)
    · intro t ht
      simp only [mem_coe, mem_filter, mem_Icc] at ht
      obtain ⟨⟨ht1, _⟩, hlo, hhi, hmod⟩ := ht
      have hmn : m < n := by omega
      exact Nat.div_div_self ((mod_eq_iff_dvd_sub hmn).mp hmod) (by omega)
  · intro t n
    simp only [mem_filter, mem_Icc]
    omega
  · intro h n
    simp only [mem_filter, mem_Ioc, mem_Icc]
    omega

/-- The interval sum is a difference of two progression sums. -/
theorem inner_eq (f : ℕ → ℝ) (N M m t : ℕ) :
    inner f N M m t =
      resSum f (min (m + 2 * M * t) N) t (m % t) - resSum f (min (m + M * t) N) t (m % t) := by
  unfold inner resSum
  have h2 : 2 * M * t = M * t + M * t := by ring
  rw [h2]
  rw [eq_sub_iff_add_eq]
  rw [← sum_filter_add_sum_filter_not ((Icc 1 (min (m + (M * t + M * t)) N)).filter
    (fun n => n % t = m % t)) (fun n => n ≤ min (m + M * t) N)]
  rw [add_comm]
  congr 1
  · apply sum_congr _ (fun _ _ => rfl)
    ext n; simp only [mem_filter, mem_Icc]; omega
  · apply sum_congr _ (fun _ _ => rfl)
    ext n; simp only [mem_filter, mem_Icc]; omega

/-! ### The size bounds used on page 51 to 52 -/

/-- From 2.5: `Δ_Q(n) ≪ L d(n)` for `Q = L^B ≥ 2`, `1 ≤ n ≤ x`. -/
theorem abs_DeltaQ_le (B K5 x : ℝ) (hB : 0 < B)
    (h5 : ∀ Q : ℝ, 2 ≤ Q → ∀ n : ℕ, 1 ≤ n →
      |LambdaQ Q n| ≤ K5 * (n.divisors.card : ℝ) * Real.log Q ^ 2)
    (hL1 : 1 ≤ Real.log x) (hQ2 : 2 ≤ Real.log x ^ B) (n : ℕ) (hn : 1 ≤ n)
    (hnx : (n : ℝ) ≤ x) :
    |DeltaQ (Real.log x ^ B) n| ≤ (4 * B ^ 2 * |K5| + 1) * Real.log x * (n.divisors.card : ℝ) := by
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hd1 : (1 : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Finset.card_eq_zero, Nat.divisors_eq_empty]; omega)
  have hlogQ : Real.log (L ^ B) ^ 2 ≤ B ^ 2 * (4 * L) := by
    rw [Real.log_rpow hL0, mul_pow]
    exact mul_le_mul_of_nonneg_left (log_sq_le L hL1) (by positivity)
  have hLQ := h5 _ hQ2 n hn
  have hLam : Λ n ≤ L := by
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    exact Real.log_le_log (by exact_mod_cast hn) hnx
  have hLam0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  unfold DeltaQ
  have hA : |LambdaQ (L ^ B) n| ≤ |K5| * (n.divisors.card : ℝ) * (B ^ 2 * (4 * L)) := by
    refine hLQ.trans ?_
    calc K5 * (n.divisors.card : ℝ) * Real.log (L ^ B) ^ 2
        ≤ |K5| * (n.divisors.card : ℝ) * Real.log (L ^ B) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogQ (by positivity)
  calc |LambdaQ (L ^ B) n - Λ n| ≤ |LambdaQ (L ^ B) n| + |Λ n| := abs_sub _ _
    _ ≤ |K5| * (n.divisors.card : ℝ) * (B ^ 2 * (4 * L)) + L * n.divisors.card := by
        rw [abs_of_nonneg hLam0]
        apply add_le_add hA
        nlinarith
    _ = _ := by ring

/-- The innermost sum on page 52, bounded by 2.7: the second term dominates. -/
theorem abs_inner_le (x Q A K7 : ℝ) (M m t : ℕ)
    (h7 : ∀ y : ℝ, 2 ≤ y → ∀ Q' : ℝ, 1 ≤ Q' → Q' ≤ y → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ y →
      |apSum (DeltaQ Q') y k l| ≤
        K7 * (Q' * Real.log y ^ 2 + y * Real.log y / (k * Q') * (Nat.gcd k l : ℝ) *
          (k.divisors.card : ℝ) + y * Real.log y ^ (-A)))
    (hA0 : 0 < A) (hL1 : 1 ≤ Real.log x) (hQ1 : 1 ≤ Q) (hM2 : 2 ≤ M) (hMQ : Q ≤ M)
    (hMx : x ≤ (M : ℝ) ^ 2) (hxM : x ≤ 2 * Q * M) (hQ3 : 2 * Q ^ 3 * Real.log x ≤ x)
    (hA : 2 * Q ^ 2 * (Real.log x / 2) ^ (-A) ≤ Real.log x) (ht : 1 ≤ t) :
    |inner (DeltaQ Q) ⌊x⌋₊ M m t| ≤
      6 * |K7| * (x * Real.log x / (t * Q) * (Nat.gcd t m : ℝ) * (t.divisors.card : ℝ)) := by
  set L := Real.log x with hLdef
  set N := ⌊x⌋₊
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hQ3
  have hQ0 : 0 < Q := by linarith
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hg : (1 : ℝ) ≤ Nat.gcd t m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp only [Nat.gcd_zero_right]; exact htR
    · exact_mod_cast Nat.gcd_pos_of_pos_left m (by omega)
  have hd : (1 : ℝ) ≤ t.divisors.card := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Finset.card_eq_zero, Nat.divisors_eq_empty]; omega)
  set W := x * L / (t * Q) * (Nat.gcd t m : ℝ) * (t.divisors.card : ℝ) with hW
  have hW0 : 0 ≤ W := by positivity
  have hK : 0 ≤ |K7| := abs_nonneg _
  rcases le_or_gt N (m + M * t) with hc | hc
  · rw [inner_eq]
    have h2 : 2 * M * t = M * t + M * t := by ring
    rw [min_eq_right hc, min_eq_right (by omega : N ≤ m + 2 * M * t)]
    simp only [sub_self, abs_zero]
    positivity
  -- the nonempty case
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hMt : (M : ℝ) * t < x := by
    have : ((M * t : ℕ) : ℝ) < N := by exact_mod_cast (show M * t < N by omega)
    push_cast at this; linarith
  have ht2Q : (t : ℝ) ≤ 2 * Q := by
    by_contra h; push_neg at h
    have : 2 * Q * M < t * M := by nlinarith
    nlinarith
  have hW1 : x * L / (2 * Q ^ 2) ≤ W := by
    have h1 : x * L / (2 * Q ^ 2) ≤ x * L / (t * Q) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have h2 : x * L / (t * Q) ≤ x * L / (t * Q) * (Nat.gcd t m : ℝ) := le_mul_of_one_le_right
      (by positivity) hg
    have h3 : x * L / (t * Q) * (Nat.gcd t m : ℝ) ≤ W := le_mul_of_one_le_right
      (by positivity) hd
    linarith
  have hres : ∀ y : ℕ, m + M * t ≤ y → y ≤ N →
      |resSum (DeltaQ Q) y t (m % t)| ≤ 3 * |K7| * W := by
    intro y hy1 hy2
    have hyR1 : (M : ℝ) * t ≤ y := by
      have : ((M * t : ℕ) : ℝ) ≤ y := by exact_mod_cast (show M * t ≤ y by omega)
      push_cast at this; exact this
    have hMy : (M : ℝ) ≤ y := by nlinarith
    have hy2' : (2 : ℝ) ≤ y := by linarith
    have hyx : (y : ℝ) ≤ x := le_trans (by exact_mod_cast hy2) hNx
    have hty : (t : ℝ) ≤ y := by nlinarith
    have hy0 : (0 : ℝ) < y := by linarith
    have hlogy : Real.log y ≤ L := Real.log_le_log hy0 hyx
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hlogyL : L / 2 ≤ Real.log y := by
      have h1 : Real.log x ≤ Real.log ((M : ℝ) ^ 2) := Real.log_le_log hx0 hMx
      rw [Real.log_pow] at h1
      have h2 : Real.log M ≤ Real.log y := Real.log_le_log (by linarith) hMy
      push_cast at h1
      linarith
    have he : resSum (DeltaQ Q) y t (m % t) = apSum (DeltaQ Q) (y : ℝ) t m := by
      unfold resSum apSum; rw [Nat.floor_natCast]
    rw [he]
    have hb := h7 y hy2' Q hQ1 (by linarith) t m ht hty
    have hpos : 0 ≤ Q * Real.log y ^ 2 + y * Real.log y / (t * Q) * (Nat.gcd t m : ℝ) *
        (t.divisors.card : ℝ) + y * Real.log y ^ (-A) := by positivity
    refine hb.trans ?_
    have e1 : Q * Real.log y ^ 2 ≤ W := by
      have : Q * Real.log y ^ 2 ≤ Q * L ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogy0 hlogy 2) hQ0.le
      refine this.trans (le_trans ?_ hW1)
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have e2 : y * Real.log y / (t * Q) * (Nat.gcd t m : ℝ) * (t.divisors.card : ℝ) ≤ W := by
      rw [hW]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hyx hlogy hlogy0 hx0.le
    have e3 : y * Real.log y ^ (-A) ≤ W := by
      have h1 : Real.log y ^ (-A) ≤ (L / 2) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hlogyL (by linarith)
      have h2 : (L / 2) ^ (-A) ≤ L / (2 * Q ^ 2) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      calc y * Real.log y ^ (-A) ≤ x * (L / (2 * Q ^ 2)) :=
            mul_le_mul hyx (h1.trans h2) (by positivity) hx0.le
        _ = x * L / (2 * Q ^ 2) := by ring
        _ ≤ W := hW1
    calc K7 * (Q * Real.log y ^ 2 + y * Real.log y / (t * Q) * (Nat.gcd t m : ℝ) *
          (t.divisors.card : ℝ) + y * Real.log y ^ (-A))
        ≤ |K7| * (Q * Real.log y ^ 2 + y * Real.log y / (t * Q) * (Nat.gcd t m : ℝ) *
          (t.divisors.card : ℝ) + y * Real.log y ^ (-A)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hpos
      _ ≤ |K7| * (W + W + W) := mul_le_mul_of_nonneg_left (by linarith) hK
      _ = 3 * |K7| * W := by ring
  rw [inner_eq]
  have hy1 := hres (min (m + M * t) N) (by omega) (min_le_right _ _)
  have hy2 := hres (min (m + 2 * M * t) N) (by
    have : 2 * M * t = M * t + M * t := by ring
    omega) (min_le_right _ _)
  calc _ ≤ |resSum (DeltaQ Q) (min (m + 2 * M * t) N) t (m % t)| +
        |resSum (DeltaQ Q) (min (m + M * t) N) t (m % t)| := abs_sub _ _
    _ ≤ 3 * |K7| * W + 3 * |K7| * W := add_le_add hy2 hy1
    _ = _ := by ring

/-! ### The bound for `S`, page 51 to 52 -/

theorem S_bound (x Q A K7 c5 c2 c3 : ℝ) (M : ℕ)
    (h7 : ∀ y : ℝ, 2 ≤ y → ∀ Q' : ℝ, 1 ≤ Q' → Q' ≤ y → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ y →
      |apSum (DeltaQ Q') y k l| ≤
        K7 * (Q' * Real.log y ^ 2 + y * Real.log y / (k * Q') * (Nat.gcd k l : ℝ) *
          (k.divisors.card : ℝ) + y * Real.log y ^ (-A)))
    (hA0 : 0 < A) (hL1 : 1 ≤ Real.log x) (hQ1 : 1 ≤ Q) (hM2 : 2 ≤ M) (hMQ : Q ≤ M)
    (hMx : x ≤ (M : ℝ) ^ 2) (hxM : x ≤ 2 * Q * M) (hQ3 : 2 * Q ^ 3 * Real.log x ≤ x)
    (hA : 2 * Q ^ 2 * (Real.log x / 2) ^ (-A) ≤ Real.log x)
    (hc5 : 0 ≤ c5)
    (hD : ∀ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n| ≤ c5 * Real.log x * (n.divisors.card : ℝ))
    (hN1 : 1 ≤ ⌊x⌋₊)
    (hc2 : ∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) ^ 2 ≤
      c2 * ⌊x⌋₊ * (1 + Real.log ⌊x⌋₊) ^ 3)
    (hc3 : ∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) ^ 3 ≤
      c3 * ⌊x⌋₊ * (1 + Real.log ⌊x⌋₊) ^ 7) :
    ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h ≤
      M * (c5 ^ 2 * Real.log x ^ 2 * (c2 * ⌊x⌋₊ * (1 + Real.log ⌊x⌋₊) ^ 3)) +
      2 * (c5 * Real.log x * (6 * |K7| * (x * Real.log x / Q)) * (1 + Real.log ⌊x⌋₊) ^ 2 *
        (c3 * ⌊x⌋₊ * (1 + Real.log ⌊x⌋₊) ^ 7)) := by
  set L := Real.log x
  set N := ⌊x⌋₊
  set D := DeltaQ Q
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hQ3
  have hQ0 : 0 < Q := by linarith
  have hlogN : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N); linarith
  have e : ∑ h ∈ Ioc M (2 * M), delta2 D N h =
      M * ∑ m ∈ Icc 1 N, D m ^ 2 + 2 * ∑ m ∈ Icc 1 N, D m * ∑ t ∈ Icc 1 N, inner D N M m t := by
    rw [sum_congr rfl (fun h hh => delta2_expand D N h (by simp only [mem_Ioc] at hh; omega))]
    rw [sum_add_distrib, sum_const, Nat.card_Ioc, nsmul_eq_mul, ← mul_sum]
    congr 2
    · rw [show 2 * M - M = M by omega]
    · rw [sum_comm]
      apply sum_congr rfl; intro m _
      rw [← mul_sum, sum_up_eq]
  rw [e]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ m ∈ Icc 1 N, D m ^ 2 ≤ ∑ m ∈ Icc 1 N, (c5 * L * (m.divisors.card : ℝ)) ^ 2 := by
          apply sum_le_sum; intro m hm
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hD m hm) 2
      _ = c5 ^ 2 * L ^ 2 * ∑ m ∈ Icc 1 N, (m.divisors.card : ℝ) ^ 2 := by
          rw [mul_sum]; apply sum_congr rfl; intro m _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc2 (by positivity)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hK : 0 ≤ 6 * |K7| * (x * L / Q) := by positivity
    calc ∑ m ∈ Icc 1 N, D m * ∑ t ∈ Icc 1 N, inner D N M m t
        ≤ ∑ m ∈ Icc 1 N, |D m| * ∑ t ∈ Icc 1 N, |inner D N M m t| := by
          apply sum_le_sum; intro m _
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ ∑ m ∈ Icc 1 N, (c5 * L * (m.divisors.card : ℝ)) * (6 * |K7| * (x * L / Q) *
            ((m.divisors.card : ℝ) ^ 2 * (1 + Real.log N) ^ 2)) := by
          apply sum_le_sum; intro m hm
          have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
          apply mul_le_mul (hD m hm) _ (sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
          calc ∑ t ∈ Icc 1 N, |inner D N M m t|
              ≤ ∑ t ∈ Icc 1 N, 6 * |K7| * (x * L / (t * Q) * (Nat.gcd t m : ℝ) *
                  (t.divisors.card : ℝ)) := by
                apply sum_le_sum; intro t ht
                exact abs_inner_le x Q A K7 M m t h7 hA0 hL1 hQ1 hM2 hMQ hMx hxM hQ3 hA
                  (mem_Icc.mp ht).1
            _ = 6 * |K7| * (x * L / Q) * ∑ t ∈ Icc 1 N,
                  (Nat.gcd t m : ℝ) * (t.divisors.card : ℝ) / t := by
                rw [mul_sum]; apply sum_congr rfl; intro t ht
                have : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
                field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left (sum_gcd_divisors_div_le m N hm1) hK
      _ = c5 * L * (6 * |K7| * (x * L / Q)) * (1 + Real.log N) ^ 2 *
            ∑ m ∈ Icc 1 N, (m.divisors.card : ℝ) ^ 3 := by
          rw [mul_sum]; apply sum_congr rfl; intro m _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc3 (by positivity)

/-! ### Lemma 2 in the main range -/

theorem sq_le_to_le (T C x L Q : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hx : 0 ≤ x) (hL : 0 ≤ L)
    (hQ : 0 < Q) (h : T ^ 2 ≤ C * x ^ 2 * L ^ 14 / Q) :
    T ≤ Real.sqrt C * x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 := by
  have hq : Q ^ (-(1 : ℝ) / 2) = (Real.sqrt Q)⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hQ.le, Real.sqrt_eq_rpow]
  rw [hq]
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hR : 0 ≤ Real.sqrt C * x * (Real.sqrt Q)⁻¹ * L ^ 7 := by positivity
  apply le_of_pow_le_pow_left₀ two_ne_zero hR
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC, inv_pow, Real.sq_sqrt hQ.le]
  ring

theorem lemma2_big (B A K7 K5 c2 c3 : ℝ) (hB : 0 < B) (hA0 : 0 < A)
    (h7 : ∀ y : ℝ, 2 ≤ y → ∀ Q' : ℝ, 1 ≤ Q' → Q' ≤ y → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ y →
      |apSum (DeltaQ Q') y k l| ≤
        K7 * (Q' * Real.log y ^ 2 + y * Real.log y / (k * Q') * (Nat.gcd k l : ℝ) *
          (k.divisors.card : ℝ) + y * Real.log y ^ (-A)))
    (h5 : ∀ Q : ℝ, 2 ≤ Q → ∀ n : ℕ, 1 ≤ n →
      |LambdaQ Q n| ≤ K5 * (n.divisors.card : ℝ) * Real.log Q ^ 2)
    (hc2 : ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 2 ≤ c2 * N * (1 + Real.log N) ^ 3)
    (hc3 : ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 3 ≤ c3 * N * (1 + Real.log N) ^ 7)
    (x : ℝ) (hL1 : 1 ≤ Real.log x) (hQ2 : 2 ≤ Real.log x ^ B)
    (hQ3 : 2 * (Real.log x ^ B) ^ 3 * Real.log x ≤ x)
    (hA : 2 * (Real.log x ^ B) ^ 2 * (Real.log x / 2) ^ (-A) ≤ Real.log x) :
    ∑ k ∈ Icc 1 ⌊x / Real.log x ^ B⌋₊, delta1 x k (Real.log x ^ B) / k ≤
      Real.sqrt (128 * c2 * (8 * (4 * B ^ 2 * |K5| + 1) ^ 2 * c2 +
        6144 * (4 * B ^ 2 * |K5| + 1) * |K7| * c3)) *
        x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7 := by
  set L := Real.log x with hLdef
  set Q := L ^ B with hQdef
  set c5 := 4 * B ^ 2 * |K5| + 1 with hc5def
  have hc5 : 0 ≤ c5 := by positivity
  have hL0 : 0 < L := by linarith
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hQ3
  have hxQ3 : 2 * Q ^ 3 ≤ x := by nlinarith [pow_pos hQ0 3]
  have hx2 : 2 ≤ x := by nlinarith [pow_pos hQ0 3]
  -- c2, c3 are at least 1
  have hc2_1 : 1 ≤ c2 := by have := hc2 1 le_rfl; simpa using this
  have hc3_1 : 1 ≤ c3 := by have := hc3 1 le_rfl; simpa using this
  set M := ⌊x / Q⌋₊ with hMdef
  have hMle : (M : ℝ) ≤ x / Q := Nat.floor_le (by positivity)
  have hMge : x / Q - 1 < M := by have := Nat.lt_floor_add_one (x / Q); linarith
  have hxQ : 2 * Q ^ 2 ≤ x / Q := by
    rw [le_div_iff₀ hQ0]; nlinarith
  have hMR2 : (2 : ℝ) ≤ M := by nlinarith
  have hM2 : 2 ≤ M := by exact_mod_cast hMR2
  have hMQ : Q ≤ M := by nlinarith
  have hxM : x ≤ 2 * Q * M := by
    have : x / Q * Q = x := div_mul_cancel₀ x hQ0.ne'
    nlinarith
  have hMx : x ≤ (M : ℝ) ^ 2 := by
    have h1 : x / (2 * Q) ≤ M := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : x ≤ (x / (2 * Q)) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith [div_nonneg hx0.le (by positivity : (0:ℝ) ≤ 2 * Q)]
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hP : 1 + Real.log N ≤ 2 * L := by
    have : Real.log N ≤ L := Real.log_le_log (by exact_mod_cast hN1) hNx
    linarith
  have hP0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N); linarith
  have hD : ∀ n ∈ Icc 1 N, |DeltaQ Q n| ≤ c5 * L * (n.divisors.card : ℝ) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.mp hn).2) hNx
    exact abs_DeltaQ_le B K5 x hB h5 hL1 hQ2 n hn1 hnx
  have hS := S_bound x Q A K7 c5 c2 c3 M h7 hA0 hL1 hQ1 hM2 hMQ hMx hxM hQ3 hA hc5 hD hN1
    (hc2 N hN1) (hc3 N hN1)
  set S := ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) N h
  have hS' : S ≤ x ^ 2 / Q * L ^ 11 * (8 * c5 ^ 2 * c2 + 6144 * c5 * |K7| * c3) := by
    refine hS.trans ?_
    have hK : 0 ≤ |K7| := abs_nonneg _
    have hL5 : L ^ 5 ≤ L ^ 11 := pow_le_pow_right₀ hL1 (by norm_num)
    have e1 : (M : ℝ) * (c5 ^ 2 * L ^ 2 * (c2 * N * (1 + Real.log N) ^ 3)) ≤
        x / Q * (c5 ^ 2 * L ^ 2 * (c2 * x * (2 * L) ^ 3)) := by gcongr
    have e2 : 2 * (c5 * L * (6 * |K7| * (x * L / Q)) * (1 + Real.log N) ^ 2 *
        (c3 * N * (1 + Real.log N) ^ 7)) ≤
        2 * (c5 * L * (6 * |K7| * (x * L / Q)) * (2 * L) ^ 2 * (c3 * x * (2 * L) ^ 7)) := by
      gcongr
    have e3 : x / Q * (c5 ^ 2 * L ^ 2 * (c2 * x * (2 * L) ^ 3)) =
        x ^ 2 / Q * L ^ 5 * (8 * c5 ^ 2 * c2) := by ring
    have e4 : 2 * (c5 * L * (6 * |K7| * (x * L / Q)) * (2 * L) ^ 2 * (c3 * x * (2 * L) ^ 7)) =
        x ^ 2 / Q * L ^ 11 * (6144 * c5 * |K7| * c3) := by ring
    have e5 : x ^ 2 / Q * L ^ 5 * (8 * c5 ^ 2 * c2) ≤ x ^ 2 / Q * L ^ 11 * (8 * c5 ^ 2 * c2) := by
      gcongr
    refine (add_le_add e1 e2).trans ?_
    rw [e3, e4]
    have e6 : x ^ 2 / Q * L ^ 11 * (8 * c5 ^ 2 * c2 + 6144 * c5 * |K7| * c3) =
        x ^ 2 / Q * L ^ 11 * (8 * c5 ^ 2 * c2) + x ^ 2 / Q * L ^ 11 * (6144 * c5 * |K7| * c3) := by
      ring
    linarith
  -- the Cauchy step
  have hW : ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2 ≤
      c2 * (2 * M : ℕ) * (1 + Real.log (2 * M : ℕ)) ^ 3 := by
    refine le_trans ?_ (hc2 (2 * M) (by omega))
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
    intro h hh; simp only [mem_Ioc] at hh; simp only [mem_Icc]; omega
  have hC := cauchy_main x Q M (by omega) _ hW
  have h2M : (1 + Real.log (2 * M : ℕ)) ≤ 2 * L := by
    have h1 : ((2 * M : ℕ) : ℝ) ≤ x := by
      push_cast
      have : x / Q ≤ x / 2 := div_le_div_of_nonneg_left hx0.le (by norm_num) hQ2
      linarith
    have : Real.log (2 * M : ℕ) ≤ L := Real.log_le_log (by positivity) h1
    linarith
  have h2M0 : 0 ≤ 1 + Real.log (2 * M : ℕ) := by
    have := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega) : (1 : ℝ) ≤ (2 * M : ℕ))
    linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hS0 : 0 ≤ S := sum_nonneg (fun _ _ => delta2_nonneg _ _ _)
  set T := ∑ k ∈ Icc 1 M, delta1 x k Q / k
  have hT2 : T ^ 2 ≤ 128 * c2 * (8 * c5 ^ 2 * c2 + 6144 * c5 * |K7| * c3) * x ^ 2 * L ^ 14 / Q := by
    refine hC.trans ?_
    have e : (4 / (M : ℝ) ^ 2) * (c2 * ((2 * M : ℕ) : ℝ) * (1 + Real.log (2 * M : ℕ)) ^ 3) *
        (2 * M * S) = 16 * c2 * (1 + Real.log (2 * M : ℕ)) ^ 3 * S := by
      push_cast; field_simp; ring
    rw [e]
    have hc0 : 0 ≤ 16 * c2 := by linarith
    calc 16 * c2 * (1 + Real.log (2 * M : ℕ)) ^ 3 * S ≤ 16 * c2 * (2 * L) ^ 3 *
          (x ^ 2 / Q * L ^ 11 * (8 * c5 ^ 2 * c2 + 6144 * c5 * |K7| * c3)) := by
          gcongr
      _ = _ := by ring
  have hT0 : 0 ≤ T := sum_nonneg (fun k _ => div_nonneg (delta1_nonneg _ _ _) (by positivity))
  have hsub : ∑ k ∈ Icc 1 M, delta1 x k Q / k = T := rfl
  have hfin := sq_le_to_le T _ x L Q hT0 (by positivity) hx0.le hL0.le hQ0 hT2
  calc _ = T := rfl
    _ ≤ _ := by
      refine hfin.trans (le_of_eq ?_)
      congr 3

/-! ### The bounded range `2 ≤ x ≤ X0` -/

theorem abs_LambdaQ_le_cube (Q : ℝ) (hQ : 0 ≤ Q) (n : ℕ) : |LambdaQ Q n| ≤ Q ^ 3 := by
  unfold LambdaQ
  set F := ⌊Q⌋₊
  have hF : (F : ℝ) ≤ Q := Nat.floor_le hQ
  have hterm : ∀ q ∈ Icc 1 F, |((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
      ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| ≤ (F : ℝ) ^ 2 := by
    intro q hq
    have hq1 := (mem_Icc.mp hq).1
    have hqF := (mem_Icc.mp hq).2
    have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hμ : (μ q : ℝ) ^ 2 ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := q)
      have h' : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast h
      nlinarith [abs_nonneg (μ q : ℝ), sq_abs (μ q : ℝ)]
    have hc : 0 ≤ (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) := by positivity
    have hc1 : (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have hg : n.gcd q ≤ q := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right n q)
    have hsum : |∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| ≤ (F : ℝ) ^ 2 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ d ∈ (n.gcd q).divisors, |(d : ℝ) * (μ d : ℝ)|
          ≤ ∑ d ∈ (n.gcd q).divisors, (F : ℝ) := by
            apply sum_le_sum; intro d hd
            rw [abs_mul, Nat.abs_cast]
            have h1 : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            have h2 : (d : ℝ) ≤ F := by
              exact_mod_cast (Nat.divisor_le hd).trans (hg.trans hqF)
            nlinarith [abs_nonneg (μ d : ℝ), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
        _ = ((n.gcd q).divisors.card : ℝ) * F := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (F : ℝ) * F := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (Nat.card_divisors_le_self _).trans (hg.trans hqF)
        _ = _ := by ring
    rw [abs_mul, abs_of_nonneg hc]
    calc _ ≤ 1 * (F : ℝ) ^ 2 := mul_le_mul hc1 hsum (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc _ ≤ ∑ q ∈ Icc 1 F, |((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
        ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Icc 1 F, (F : ℝ) ^ 2 := sum_le_sum hterm
    _ = (F : ℝ) ^ 3 := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ ≤ Q ^ 3 := pow_le_pow_left₀ (by positivity) hF 3

theorem delta1_div_le (x Q : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    delta1 x k Q / k ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n| := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hkR]
  unfold delta1 apSum
  calc ∑ l ∈ Icc 1 k, |∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), DeltaQ Q n|
      ≤ ∑ l ∈ Icc 1 k, ∑ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n| := by
        apply sum_le_sum; intro l _
        refine (abs_sum_le_sum_abs _ _).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

theorem lemma2_small (B : ℝ) (hB : 0 < B) (X0 : ℝ) : ∃ Cs : ℝ, ∀ x : ℝ, 2 ≤ x → x ≤ X0 →
    ∀ K : ℝ, K ≤ x / Real.log x ^ B →
      ∑ k ∈ Icc 1 ⌊K⌋₊, delta1 x k (Real.log x ^ B) / k ≤
        Cs * x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7 := by
  set X := max X0 2
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  set LX := Real.log X
  have hLX : l2 ≤ LX := Real.log_le_log (by norm_num) (le_max_right _ _)
  have hX0 : (0 : ℝ) < X := by positivity
  set QX := LX ^ B
  have hQX : 0 < QX := Real.rpow_pos_of_pos (by linarith) _
  have hLX0 : 0 < LX := by linarith
  have hA0 : 0 ≤ QX ^ 3 + LX := by have := pow_pos hQX 3; linarith
  set bound := X / l2 ^ B * (X * (QX ^ 3 + LX))
  set low := 2 * QX ^ (-(1 : ℝ) / 2) * l2 ^ 7
  have hlow : 0 < low := by positivity
  refine ⟨bound / low, ?_⟩
  intro x hx2 hxX K hK
  have hx0 : 0 < x := by linarith
  have hxM : x ≤ X := le_trans hxX (le_max_left _ _)
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx2
  have hL0 : 0 < L := by linarith
  have hLLX : L ≤ LX := Real.log_le_log hx0 hxM
  set Q := L ^ B
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hL0 _
  have hQQX : Q ≤ QX := Real.rpow_le_rpow hL0.le hLLX hB.le
  have hQl : l2 ^ B ≤ Q := Real.rpow_le_rpow hl2.le hL2 hB.le
  have hl2B : 0 < l2 ^ B := Real.rpow_pos_of_pos hl2 _
  -- each term
  have hDn : ∀ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n| ≤ QX ^ 3 + LX := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.mp hn).2) (Nat.floor_le hx0.le)
    unfold DeltaQ
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · exact (abs_LambdaQ_le_cube Q hQ0.le n).trans (pow_le_pow_left₀ hQ0.le hQQX 3)
    · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
      exact (Real.log_le_log (by exact_mod_cast hn1) hnx).trans hLLX
  have hsumD : ∑ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n| ≤ X * (QX ^ 3 + LX) := by
    calc _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (QX ^ 3 + LX) := sum_le_sum hDn
      _ = (⌊x⌋₊ : ℝ) * (QX ^ 3 + LX) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ X * (QX ^ 3 + LX) := by
          apply mul_le_mul_of_nonneg_right _ hA0
          exact (Nat.floor_le hx0.le).trans hxM
  have hKfl : (⌊K⌋₊ : ℝ) ≤ X / l2 ^ B := by
    rcases le_or_gt K 0 with h | h
    · rw [Nat.floor_of_nonpos h]; simp; positivity
    · refine (Nat.floor_le h.le).trans (hK.trans ?_)
      exact div_le_div₀ (by positivity) hxM hl2B hQl
  have hLHS : ∑ k ∈ Icc 1 ⌊K⌋₊, delta1 x k Q / k ≤ bound := by
    calc _ ≤ ∑ k ∈ Icc 1 ⌊K⌋₊, X * (QX ^ 3 + LX) := by
          apply sum_le_sum; intro k hk
          exact (delta1_div_le x Q k (mem_Icc.mp hk).1).trans hsumD
      _ = (⌊K⌋₊ : ℝ) * (X * (QX ^ 3 + LX)) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ bound := mul_le_mul_of_nonneg_right hKfl (mul_nonneg hX0.le hA0)
  have hRHS : low ≤ x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 := by
    have h1 : QX ^ (-(1 : ℝ) / 2) ≤ Q ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hQ0 hQQX (by norm_num)
    have h2 : l2 ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ hl2.le hL2 7
    have h3 : 0 ≤ QX ^ (-(1 : ℝ) / 2) := by positivity
    calc low = 2 * QX ^ (-(1 : ℝ) / 2) * l2 ^ 7 := rfl
      _ ≤ x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 := by gcongr
  have hb0 : 0 ≤ bound := mul_nonneg (div_nonneg hX0.le hl2B.le) (mul_nonneg hX0.le hA0)
  refine hLHS.trans ?_
  calc bound = bound / low * low := by field_simp
    _ ≤ bound / low * (x * Q ^ (-(1 : ℝ) / 2) * L ^ 7) :=
        mul_le_mul_of_nonneg_left hRHS (by positivity)
    _ = _ := by ring

/-! ### Lemma 2 -/

theorem eventually_conditions (B : ℝ) (hB : 0 < B) : ∃ X1 : ℝ, ∀ x : ℝ, X1 ≤ x →
    1 ≤ Real.log x ∧ 2 ≤ Real.log x ^ B ∧ 2 * (Real.log x ^ B) ^ 3 * Real.log x ≤ x ∧
    2 * (Real.log x ^ B) ^ 2 * (Real.log x / 2) ^ (-(2 * B + 2)) ≤ Real.log x := by
  set Lc := max (max 1 ((2 : ℝ) ^ (1 / B))) ((2 : ℝ) ^ ((2 * B + 3) / 3))
  have ev1 := Real.tendsto_log_atTop.eventually_ge_atTop Lc
  have ev2 := (isLittleO_log_rpow_rpow_atTop (3 * B + 1) one_pos).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have ev3 := eventually_gt_atTop (0 : ℝ)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp (ev1.and (ev2.and ev3))
  refine ⟨X1, fun x hx => ?_⟩
  obtain ⟨hLc, hbig, hx0⟩ := hX1 x hx
  set L := Real.log x
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLc
  have hL0 : 0 < L := by linarith
  have hLB : (2 : ℝ) ^ (1 / B) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLc
  have hL3 : (2 : ℝ) ^ ((2 * B + 3) / 3) ≤ L := le_trans (le_max_right _ _) hLc
  refine ⟨hL1, ?_, ?_, ?_⟩
  · calc (2 : ℝ) = ((2 : ℝ) ^ (1 / B)) ^ B := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hB.ne', Real.rpow_one]
      _ ≤ L ^ B := Real.rpow_le_rpow (by positivity) hLB hB.le
  · have e : (L ^ B) ^ 3 * L = L ^ (3 * B + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, Real.rpow_add hL0, Real.rpow_one]
      congr 2; push_cast; ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_pos hx0,
      abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hbig
    rw [mul_assoc, e]; linarith
  · have e1 : (L / 2) ^ (-(2 * B + 2)) = L ^ (-(2 * B + 2)) * (2 : ℝ) ^ (2 * B + 2) := by
      rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    have e2 : (L ^ B) ^ 2 * L ^ (-(2 * B + 2)) = L ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
      congr 1; push_cast; ring
    have e3 : L ^ (-(2 : ℝ)) = 1 / L ^ 2 := by
      rw [Real.rpow_neg hL0.le, one_div]; norm_cast
    have h3 : (2 : ℝ) ^ (2 * B + 3) ≤ L ^ 3 := by
      calc (2 : ℝ) ^ (2 * B + 3) = ((2 : ℝ) ^ ((2 * B + 3) / 3)) ^ (3 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
        _ ≤ L ^ 3 := pow_le_pow_left₀ (by positivity) hL3 3
    have e4 : (2 : ℝ) ^ (2 * B + 3) = 2 * (2 : ℝ) ^ (2 * B + 2) := by
      rw [show 2 * B + 3 = (2 * B + 2) + 1 by ring, Real.rpow_add_one (by norm_num)]; ring
    calc 2 * (L ^ B) ^ 2 * (L / 2) ^ (-(2 * B + 2))
        = 2 * (2 : ℝ) ^ (2 * B + 2) * ((L ^ B) ^ 2 * L ^ (-(2 * B + 2))) := by rw [e1]; ring
      _ = (2 : ℝ) ^ (2 * B + 3) / L ^ 2 := by rw [e2, e3, e4]; ring
      _ ≤ L ^ 3 / L ^ 2 := div_le_div_of_nonneg_right h3 (by positivity)
      _ = L := by field_simp

/-- **Lemma 2 of Heath-Brown 1985 from Lemma 1, 2.7, the bound 2.5 and the divisor moments 2.2
with `t = 2, 3`**, as on pages 50 to 52. Fully proved; the four inputs are hypotheses. -/
theorem lemma2_of (h7 : Lemma1_7) (h5 : Bound2_5) (hd2 : DivMoment2) (hd3 : DivMoment3) :
    Lemma2 := by
  intro B hB
  obtain ⟨K7, hK7⟩ := h7 (2 * B + 2) (by positivity)
  obtain ⟨K5, hK5⟩ := h5
  obtain ⟨c2, hc2⟩ := hd2
  obtain ⟨c3, hc3⟩ := hd3
  obtain ⟨X1, hX1⟩ := eventually_conditions B hB
  set X0 := max X1 2
  obtain ⟨Cs, hCs⟩ := lemma2_small B hB X0
  set Cb := Real.sqrt (128 * c2 * (8 * (4 * B ^ 2 * |K5| + 1) ^ 2 * c2 +
        6144 * (4 * B ^ 2 * |K5| + 1) * |K7| * c3))
  refine ⟨max Cs Cb, ?_⟩
  intro x hx2 K hK
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hpos : 0 ≤ x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7 := by positivity
  have key : ∀ c, c ≤ max Cs Cb → c * x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7 ≤
      max Cs Cb * x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7 := by
    intro c hc
    calc c * x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7
        = c * (x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7) := by ring
      _ ≤ max Cs Cb * (x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7) :=
          mul_le_mul_of_nonneg_right hc hpos
      _ = _ := by ring
  rcases le_or_gt x X0 with hx | hx
  · exact (hCs x hx2 hx K hK).trans (key Cs (le_max_left _ _))
  · obtain ⟨hL1, hQ2, hQ3, hA⟩ := hX1 x (le_trans (le_max_left _ _) hx.le)
    have hbig := lemma2_big B (2 * B + 2) K7 K5 c2 c3 hB (by positivity) hK7 hK5 hc2 hc3 x
      hL1 hQ2 hQ3 hA
    have hQ0 : 0 < Real.log x ^ B := by linarith
    have hsub : ∑ k ∈ Icc 1 ⌊K⌋₊, delta1 x k (Real.log x ^ B) / k ≤
        ∑ k ∈ Icc 1 ⌊x / Real.log x ^ B⌋₊, delta1 x k (Real.log x ^ B) / k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Icc] at hk ⊢
        exact ⟨hk.1, hk.2.trans (Nat.floor_le_floor hK)⟩
      · intro k _ _; exact div_nonneg (delta1_nonneg _ _ _) (by positivity)
    exact hsub.trans (hbig.trans (key Cb (le_max_right _ _)))

end LeanLab.HeathBrown1985
