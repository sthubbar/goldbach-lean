module

public import LeanLab.PNTPort.Vinogradov.Basic

/-!
# Vinogradov's minor arc bound, one block of `q` consecutive multipliers

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input.

`block_bound`: if `(a, q) = 1`, `q ≥ 1` and `|α - a/q| ≤ 1/q²`, then for every `h` and `Y ≥ 0`,
`∑_{h < m ≤ h + q} G Y (α m) ≤ 4 Y + q (1 + log q)`.

The points `α m` lie within `1/q` of the shifted grid `c₀ + j/q`, `0 ≤ c₀ < 1/q`, one point per
`j`, since `m ↦ a m` is a bijection mod `q`; at most four `j` are near an integer.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open LeanLab.PNTPort.LargeSieve

/-- `μ q j = min (j, q - 1 - j)`, as a real. -/
noncomputable def mu (q j : ℕ) : ℝ := min (j : ℝ) ((q : ℝ) - 1 - j)

/-- The majorant of one term. -/
noncomputable def phi (q : ℕ) (Y : ℝ) (j : ℕ) : ℝ :=
  if 2 ≤ mu q j then q / (2 * (mu q j - 1)) else Y

lemma sum_shift_harm (q : ℕ) :
    ∑ j ∈ range q, (if 2 ≤ j then 1 / ((j : ℝ) - 1) else 0) = (harmonic (q - 2) : ℝ) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.lt_or_ge n 2 with h | h
    · rw [if_neg (by omega)]
      interval_cases n <;> simp
    · rw [if_pos h, show n + 1 - 2 = (n - 2) + 1 by omega, harmonic_succ]
      push_cast
      rw [Nat.cast_sub (by omega : 2 ≤ n)]
      push_cast; ring

lemma sum_B_le (q : ℕ) :
    ∑ j ∈ range q, (if 2 ≤ j then 1 / ((j : ℝ) - 1) else 0) ≤ 1 + Real.log q := by
  rw [sum_shift_harm]
  refine (harmonic_le_one_add_log _).trans ?_
  rcases Nat.lt_or_ge q 3 with h | h
  · rw [show q - 2 = 0 by omega]
    simpa using Real.log_natCast_nonneg q
  · gcongr
    · exact_mod_cast (show 0 < q - 2 by omega)
    · exact_mod_cast Nat.sub_le q 2

lemma sum_C_le (q : ℕ) :
    ∑ j ∈ range q, (if j + 3 ≤ q then 1 / ((q : ℝ) - 2 - j) else 0) ≤ 1 + Real.log q := by
  rw [← sum_range_reflect]
  refine le_of_eq_of_le (sum_congr rfl fun i hi => ?_) (sum_B_le q)
  have hi' := mem_range.1 hi
  by_cases h2 : 2 ≤ i
  · have hc : ((q - 1 - i : ℕ) : ℝ) = (q : ℝ) - 1 - i := by
      rw [show q - 1 - i = q - (i + 1) by omega, Nat.cast_sub (by omega : i + 1 ≤ q)]
      push_cast; ring
    rw [if_pos (by omega), if_pos h2, hc]
    ring_nf
  · rw [if_neg (by omega), if_neg h2]

lemma sum_phi_le {q : ℕ} {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ j ∈ range q, phi q Y j ≤ 4 * Y + q * (1 + Real.log q) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have key : ∀ j ∈ range q, phi q Y j ≤ (if j < 2 ∨ q < j + 3 then Y else 0)
      + (q / 2) * (if 2 ≤ j then 1 / ((j : ℝ) - 1) else 0)
      + (q / 2) * (if j + 3 ≤ q then 1 / ((q : ℝ) - 2 - j) else 0) := by
    intro j hj
    have hj' := mem_range.1 hj
    have hB : 0 ≤ (if 2 ≤ j then 1 / ((j : ℝ) - 1) else 0) := by
      split_ifs with h
      · have : (2 : ℝ) ≤ j := by exact_mod_cast h
        exact div_nonneg zero_le_one (by linarith)
      · exact le_rfl
    have hC : 0 ≤ (if j + 3 ≤ q then 1 / ((q : ℝ) - 2 - j) else 0) := by
      split_ifs with h
      · have : (j : ℝ) + 3 ≤ q := by exact_mod_cast h
        exact div_nonneg zero_le_one (by linarith)
      · exact le_rfl
    unfold phi
    by_cases hm : 2 ≤ mu q j
    · rw [if_pos hm]
      unfold mu at hm
      have hj2r : (2 : ℝ) ≤ j := (le_min_iff.1 hm).1
      have hj3r : (j : ℝ) + 3 ≤ q := by have := (le_min_iff.1 hm).2; linarith
      have hj2 : 2 ≤ j := by exact_mod_cast hj2r
      have hj3 : j + 3 ≤ q := by exact_mod_cast hj3r
      rw [if_neg (by omega), if_pos hj2, if_pos hj3]
      unfold mu
      rcases min_choice (j : ℝ) ((q : ℝ) - 1 - j) with hmin | hmin
      · rw [hmin]
        have : q / (2 * ((j : ℝ) - 1)) = (q / 2) * (1 / ((j : ℝ) - 1)) := by
          field_simp
        rw [this]
        have : 0 ≤ (q / 2) * (1 / ((q : ℝ) - 2 - j)) :=
          mul_nonneg (by positivity) (div_nonneg zero_le_one (by linarith))
        linarith
      · rw [hmin]
        have : q / (2 * ((q : ℝ) - 1 - j - 1)) = (q / 2) * (1 / ((q : ℝ) - 2 - j)) := by
          rw [show (q : ℝ) - 1 - j - 1 = q - 2 - j by ring]; field_simp
        rw [this]
        have : 0 ≤ (q / 2) * (1 / ((j : ℝ) - 1)) :=
          mul_nonneg (by positivity) (div_nonneg zero_le_one (by linarith))
        linarith
    · rw [if_neg hm]
      have h2 : ¬ (2 ≤ j ∧ j + 3 ≤ q) := by
        rintro ⟨ha, hb⟩
        apply hm
        unfold mu
        have : (2 : ℝ) ≤ j := by exact_mod_cast ha
        have : (j : ℝ) + 3 ≤ q := by exact_mod_cast hb
        exact le_min (by linarith) (by linarith)
      have : j < 2 ∨ q < j + 3 := by omega
      rw [if_pos this]
      have := mul_nonneg (show (0 : ℝ) ≤ q / 2 by positivity) hB
      have := mul_nonneg (show (0 : ℝ) ≤ q / 2 by positivity) hC
      linarith
  refine (sum_le_sum key).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  have hA : ∑ j ∈ range q, (if j < 2 ∨ q < j + 3 then Y else 0) ≤ 4 * Y := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    gcongr
    have hsub : (range q).filter (fun j => j < 2 ∨ q < j + 3) ⊆ {0, 1, q - 2, q - 1} := by
      intro j hj
      simp only [mem_filter, mem_range] at hj
      simp only [mem_insert, mem_singleton]
      omega
    have := card_le_card hsub
    have h4 : ({0, 1, q - 2, q - 1} : Finset ℕ).card ≤ 4 := by
      refine (card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
      simp
    exact_mod_cast this.trans h4
  have := sum_B_le q
  have := sum_C_le q
  have h1 : (q / 2 : ℝ) * ∑ j ∈ range q, (if 2 ≤ j then 1 / ((j : ℝ) - 1) else 0)
      ≤ (q / 2) * (1 + Real.log q) := mul_le_mul_of_nonneg_left (sum_B_le q) (by positivity)
  have h2 : (q / 2 : ℝ) * ∑ j ∈ range q, (if j + 3 ≤ q then 1 / ((q : ℝ) - 2 - j) else 0)
      ≤ (q / 2) * (1 + Real.log q) := mul_le_mul_of_nonneg_left (sum_C_le q) (by positivity)
  linarith

lemma phi_nonneg (q : ℕ) {Y : ℝ} (hY : 0 ≤ Y) (j : ℕ) : 0 ≤ phi q Y j := by
  unfold phi; split_ifs with h
  · exact div_nonneg (Nat.cast_nonneg q) (by linarith)
  · exact hY

/-- One block of `q` consecutive multipliers. -/
theorem block_bound {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (h : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ m ∈ Ioc h (h + q), G Y (α * m) ≤ 4 * Y + q * (1 + Real.log q) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  set c : ℝ := α * h with hc
  set k : ℤ := ⌊c * q⌋ with hk
  set c0 : ℝ := c - k / q with hc0
  have hk1 : (k : ℝ) ≤ c * q := Int.floor_le _
  have hk2 : c * q < k + 1 := Int.lt_floor_add_one _
  have hc0a : 0 ≤ c0 := by
    rw [hc0, sub_nonneg, div_le_iff₀ hqpos]; exact hk1
  have hc0b : c0 < 1 / q := by
    rw [hc0, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hqpos]; linarith
  set T : ℕ → ℤ := fun m => k + a * ((m : ℤ) - h) with hT
  set J : ℕ → ℕ := fun m => (T m % (q : ℤ)).toNat with hJ
  have hJnn : ∀ m, 0 ≤ T m % (q : ℤ) := fun m => Int.emod_nonneg _ hqz.ne'
  have hJcast : ∀ m, ((J m : ℕ) : ℤ) = T m % (q : ℤ) := fun m => Int.toNat_of_nonneg (hJnn m)
  have hJlt : ∀ m, J m < q := by
    intro m
    have := Int.emod_lt_of_pos (T m) hqz
    have h2 := hJcast m
    omega
  -- the term bound
  have hterm : ∀ m ∈ Ioc h (h + q), G Y (α * m) ≤ phi q Y (J m) := by
    intro m hm
    have hm' := mem_Ioc.1 hm
    set r : ℕ := m - h with hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hrq : (r : ℝ) ≤ q := by exact_mod_cast (show r ≤ q by omega)
    have hmr : (m : ℝ) = h + r := by
      rw [hr, Nat.cast_sub (by omega)]; ring
    have hmrz : (m : ℤ) - h = r := by rw [hr]; push_cast [Nat.cast_sub (show h ≤ m by omega)]; ring
    set δ : ℝ := (α - a / q) * r with hδ
    have hδb : |δ| ≤ 1 / q := by
      rw [hδ, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r)]
      calc |α - a / q| * r ≤ 1 / (q : ℝ) ^ 2 * q := by gcongr
        _ = 1 / q := by field_simp
    set x : ℝ := c0 + (J m : ℝ) / q with hx
    have hJq : (J m : ℝ) + 1 ≤ q := by exact_mod_cast hJlt m
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := by
      rw [hx]
      have : (J m : ℝ) / q ≤ (q - 1) / q := by gcongr; linarith
      have : (q - 1 : ℝ) / q = 1 - 1 / q := by field_simp
      linarith
    -- decomposition of α m
    have hdiv := Int.mul_ediv_add_emod (T m) (q : ℤ)
    have hTr : (T m : ℝ) = k + a * r := by
      simp only [hT]; push_cast; rw [hmr]; ring
    have hdecomp : α * m = x + ((T m / (q : ℤ) : ℤ) : ℝ) + δ := by
      have h1 : (T m : ℝ) = q * ((T m / (q : ℤ) : ℤ) : ℝ) + (J m : ℝ) := by
        have : ((J m : ℕ) : ℝ) = ((T m % (q : ℤ) : ℤ) : ℝ) := by exact_mod_cast hJcast m
        rw [this]; exact_mod_cast hdiv.symm
      have h2 : ((T m / (q : ℤ) : ℤ) : ℝ) = ((T m : ℝ) - J m) / q := by
        field_simp; linarith
      rw [h2, hx, hδ, hc0, hTr, hmr, hc]
      field_simp; ring
    have hlow := dist0_ge hx0 hx1 (T m / (q : ℤ)) (y := δ)
    rw [← hdecomp] at hlow
    have hmin : mu q (J m) / q ≤ min x (1 - x) := by
      unfold mu
      rw [le_min_iff]; constructor
      · calc min (J m : ℝ) (q - 1 - J m) / q ≤ (J m : ℝ) / q := by
              gcongr; exact min_le_left _ _
          _ ≤ x := by rw [hx]; linarith
      · calc min (J m : ℝ) (q - 1 - J m) / q ≤ ((q : ℝ) - 1 - J m) / q := by
              gcongr; exact min_le_right _ _
          _ = 1 - 1 / q - (J m : ℝ) / q := by field_simp
          _ ≤ 1 - x := by rw [hx]; linarith
    have hd : (mu q (J m) - 1) / q ≤ dist0 (α * m) := by
      have : (mu q (J m) - 1) / q = mu q (J m) / q - 1 / q := by ring
      linarith
    unfold phi
    split_ifs with h2
    · have hpos : 0 < (mu q (J m) - 1) / q := by apply div_pos <;> linarith
      have hdpos : 0 < dist0 (α * m) := lt_of_lt_of_le hpos hd
      refine (G_le_inv hdpos).trans ?_
      calc 1 / (2 * dist0 (α * m)) ≤ 1 / (2 * ((mu q (J m) - 1) / q)) := by gcongr
        _ = q / (2 * (mu q (J m) - 1)) := by field_simp
    · exact G_le Y _
  -- injectivity
  have hinj : Set.InjOn J (Ioc h (h + q) : Set ℕ) := by
    intro m1 hm1 m2 hm2 heq
    simp only [coe_Ioc, Set.mem_Ioc] at hm1 hm2
    have h1 : T m1 % (q : ℤ) = T m2 % (q : ℤ) := by
      rw [← hJcast, ← hJcast]; exact_mod_cast heq
    have h2 : (q : ℤ) ∣ T m1 - T m2 := Int.ModEq.dvd h1.symm
    have h3 : T m1 - T m2 = ((m1 : ℤ) - m2) * a := by simp only [hT]; ring
    rw [h3] at h2
    have h4 : (q : ℤ) ∣ (m1 : ℤ) - m2 := hcop.symm.dvd_of_dvd_mul_right h2
    have h5 : |(m1 : ℤ) - m2| < q := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd h4 h5
    omega
  calc ∑ m ∈ Ioc h (h + q), G Y (α * m) ≤ ∑ m ∈ Ioc h (h + q), phi q Y (J m) :=
        sum_le_sum hterm
    _ = ∑ j ∈ (Ioc h (h + q)).image J, phi q Y j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ range q, phi q Y j := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨m, _, rfl⟩ := mem_image.1 hj
          exact mem_range.2 (hJlt m)
        · intro j _ _; exact phi_nonneg q hY j
    _ ≤ 4 * Y + q * (1 + Real.log q) := sum_phi_le hY

end LeanLab.PNTPort.Vinogradov

