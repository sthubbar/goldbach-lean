module

public import LeanLab.Halupczok2012.U1460SingSeriesProof

/-!
# P0077 Halupczok 2012, `SingSeriesApprox` reduced to two explicit tail inequalities, U-1460

AI wrote the Lean code, Claude, run 20261022T0003Z-15508. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

`SingSeriesTails` fixes the choice in `SingSeriesApprox`: `Z` is the set of squarefree
`s ≤ min(L^D, X₁)`, and `g_s = gW n (primeFactors s)`, the Ramanujan weight with the 2 adic
factor. It asserts only the two inequalities, TAIL and EULER, for this explicit choice.

* `abs_gW_le_one`: `|gW n t m| ≤ 1`. PROVED.
* `gS_periodic`: `g_s` is `s`-periodic for squarefree `s`. PROVED.
* `singSeriesApprox_of_tails : SingSeriesTails → SingSeriesApprox`. PROVED.
* `theorem2Zeroed_of_tails`: the F-0008 repair CONDITIONAL ON `Theorem3`, `Theorem5` and
  `SingSeriesTails`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-- The squarefree `s ≤ z` with `s ≤ X₁`. -/
noncomputable def Zsq (z X1 : ℝ) : Finset ℕ :=
  (Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ (s : ℝ) ≤ X1)

/-- `g_s(m) = ∏_{p ∣ s} c_p(n - m)/(p - 1)²`. -/
noncomputable def gS (n s m : ℕ) : ℝ := gW n s.primeFactors m

theorem abs_gW_le_one (n : ℕ) {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) (m : ℕ) :
    |gW n t m| ≤ 1 := by
  unfold gW
  rw [abs_prod]
  apply prod_le_one₀ (fun p _ => abs_nonneg _)
  intro p hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (ht p hp).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h1 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := pow_pos hp1 2
  rw [abs_div, abs_of_pos h1, div_le_one h1]
  unfold cPZ
  split_ifs
  · rw [abs_of_nonneg (by linarith)]; nlinarith
  · rw [abs_neg, abs_one]; nlinarith

theorem gS_periodic {n s : ℕ} (hs : Squarefree s) (m : ℕ) : gS n s m = gS n s (m % s) := by
  unfold gS
  conv_lhs => rw [gW_periodic n s.primeFactors m]
  rw [Nat.prod_primeFactors_of_squarefree hs]

/-- **The explicit tail inequalities**, a prime free named input. -/
def SingSeriesTails : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ D : ℝ, 0 ≤ D ∧
  ∀ B : ℝ, 0 < B → ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ,
  ∃ C Y0 : ℝ, ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 →
    Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        ∑ m ∈ W1 n X1 Y1 q a, Real.log m *
          |S (n - m) - ∑ s ∈ Zsq (Real.log Y2 ^ D) X1, gS n s m|
          ≤ C * Y1 * Real.log Y2 ^ (-A) ∧
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        |∑ s ∈ Zsq (Real.log Y2 ^ D) X1, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) *
            ∑ b ∈ crtG a q s, gS n s b - T n q a * Y1| ≤ C * Y1 * Real.log Y2 ^ (-A)

/-- **`SingSeriesTails` implies `SingSeriesApprox`.** -/
theorem singSeriesApprox_of_tails (h : SingSeriesTails) : SingSeriesApprox := by
  intro A ε ε1 ε2 hA hε hε1 hε2
  obtain ⟨D, hD, hT⟩ := h A ε ε1 ε2 hA hε hε1 hε2
  refine ⟨D, hD, fun B hB c hc c7 hc7 a => ?_⟩
  obtain ⟨C, Y0, hC⟩ := hT B hB c hc c7 hc7 a
  refine ⟨C, 1, max Y0 1, fun n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ ha => ?_⟩
  have hY2' : 1 ≤ Y2 := le_trans (le_max_right _ _) hY2
  obtain ⟨htail, heul⟩ := hC n X1 Y1 X2 Y2 Q (le_trans (le_max_left _ _) hY1)
    (le_trans (le_max_left _ _) hY2) hH hQ ha
  have hz0 : 0 ≤ Real.log Y2 ^ D := Real.rpow_nonneg (Real.log_nonneg hY2') D
  refine ⟨Zsq (Real.log Y2 ^ D) X1, gS n, ?_, ?_, ?_, ?_, htail, heul⟩
  · intro s hs
    simp only [Zsq, mem_filter, mem_Icc] at hs
    refine ⟨by omega, hs.2.2, ?_⟩
    exact le_trans (by exact_mod_cast hs.1.2) (Nat.floor_le hz0)
  · calc ((Zsq (Real.log Y2 ^ D) X1).card : ℝ) ≤ ((Icc 1 ⌊Real.log Y2 ^ D⌋₊).card : ℝ) := by
          exact_mod_cast card_filter_le _ _
      _ = (⌊Real.log Y2 ^ D⌋₊ : ℝ) := by rw [Nat.card_Icc]; simp
      _ ≤ _ := Nat.floor_le hz0
  · intro s hs m
    simp only [Zsq, mem_filter] at hs
    exact gS_periodic hs.2.1 m
  · intro s _ m
    exact abs_gW_le_one n (fun p hp => Nat.prime_of_mem_primeFactors hp) m

/-- **The F-0008 repair, CONDITIONAL ON `Theorem3`, `Theorem5` and `SingSeriesTails`.** -/
theorem theorem2Zeroed_of_tails (h3 : Theorem3) (h5 : Theorem5) (h : SingSeriesTails) :
    Theorem2Zeroed :=
  theorem2Zeroed_of_three h3 h5 (singSeriesApprox_of_tails h)

/-- Vacuity of the weight: `gS 7 6 1 = c_2(6) c_3(6)/4 = 1 · 2/4 = 1/2`. -/
theorem gS_instance : gS 7 6 1 = 1 / 2 := by
  have h : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    rfl
  unfold gS gW
  rw [h, prod_insert (by decide), prod_singleton]
  unfold cPZ
  norm_num

end LeanLab.Halupczok2012
