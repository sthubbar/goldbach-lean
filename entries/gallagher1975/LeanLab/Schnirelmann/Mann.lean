module

public import LeanLab.Ramare1995.Theorem91
public import Mathlib.Combinatorics.Schnirelmann

/-!
Mann's theorem, `σ(A + B) ≥ min(1, σ(A) + σ(B))` for Schnirelmann density, and its `H`-set form.
Proved from the rank `h` case of Dyson's theorem (Dyson 1945) with `γ ≤ 1`, following
M. B. Nathanson, "Additive number theory and the Dyson transform", arXiv:2407.12253v4,
Sections 3-5. Reuses the Dyson transform lemmas of `LeanLab.Ramare1995.Theorem91`.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0803Z-2223. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

/-- Dyson's hypothesis with a real `δ`. -/
def DysonHypR (A : ℕ → Set ℕ) (k n : ℕ) (δ : ℝ) : Prop :=
  ∀ m, 1 ≤ m → m ≤ n → δ * m ≤ phi A k m

/-- The sumset `A 0 + ⋯ + A (k-1)` (each summand may be `0`). -/
def SumSet (A : ℕ → Set ℕ) (k : ℕ) : Set ℕ := {p | Rep A k p}

lemma cnt_mono_le {S T : Set ℕ} {m : ℕ} (h : ∀ p, 1 ≤ p → p ≤ m → p ∈ S → p ∈ T) :
    cnt S m ≤ cnt T m := by
  unfold cnt
  exact card_le_card (fun x hx => by
    simp only [mem_filter, mem_Icc] at hx ⊢
    exact ⟨hx.1, h x hx.1.1 hx.1.2 hx.2⟩)

lemma rep_succ {A : ℕ → Set ℕ} {h p : ℕ} (hr : Rep A (h + 1) p) : Rep A (h + 2) p := by
  obtain ⟨f, hf, hs⟩ := hr
  refine ⟨Function.update f (h + 1) 0, fun i hi => ?_, ?_⟩
  · by_cases hi' : i = h + 1
    · subst hi'; simp
    · simp only [Function.update_of_ne hi']; exact hf i (by omega)
  · rw [sum_range_succ, Function.update_self, add_zero, ← hs]
    apply sum_congr rfl
    intro i hi
    simp at hi
    exact Function.update_of_ne (by omega) _ _

/-- Theorem 6 of Nathanson with `γ = δ ≤ 1`. -/
lemma hyp_trR {A : ℕ → Set ℕ} {h n a₀ ℓ₀ : ℕ} {δ : ℝ} (hδ : δ ≤ 1) (hℓ : ℓ₀ ≤ h)
    (hmin : ∀ a < a₀, ∀ ℓ c, ¬ Trip A h n a ℓ c) (hyp : DysonHypR A (h + 2) n δ) :
    DysonHypR (tr A h n a₀ ℓ₀) (h + 2) n δ := by
  set T := Tset A h n a₀ ℓ₀ with hTdef
  set ψ : ℕ → ℕ := fun m => phi A (h + 1) m with hψ
  have hTsub : T ⊆ A (h + 1) := fun c hc => hc.1
  have F1 : ∀ m, phi A (h + 2) m = ψ m + cnt (A (h + 1)) m := by
    intro m; simp [hψ, phi, sum_range_succ]
  have F2 : ∀ m, phi (tr A h n a₀ ℓ₀) (h + 2) m =
      phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A (h + 1) \ T) m := by
    intro m; simp only [phi, sum_range_succ (n := h + 1), tr_last, hTdef]
  have F3 : ∀ m, phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A ℓ₀) m =
      ψ m + cnt (A ℓ₀ ∪ Tsh A h n a₀ ℓ₀) m := by
    intro m
    have := sum_one (s := range (h + 1)) (f := fun i => cnt (tr A h n a₀ ℓ₀ i) m)
      (g := fun i => cnt (A i) m) (a := ℓ₀) (mem_range.2 (by omega))
      (fun i hi h2 => by rw [tr_ne A (by simp at hi; omega) h2])
    simpa [phi, hψ, tr_l A hℓ] using this
  have F4 : ∀ m, m ≤ n → cnt (A ℓ₀) m + cnt T (m - a₀) ≤ cnt (A ℓ₀ ∪ Tsh A h n a₀ ℓ₀) m := by
    intro m hm
    exact cnt_union_shift (A ℓ₀) T a₀ m n hm (fun c hc => hc.2.2.2)
  have F5 : ∀ m, cnt (A (h + 1) \ T) m + cnt T m = cnt (A (h + 1)) m :=
    fun m => cnt_diff hTsub m
  have L6 : ∀ m c, c ∈ A (h + 1) → 1 ≤ c → m - a₀ < c → c ≤ m → m ≤ n →
      ψ (m - c) + (h + 1) + ψ (c - 1) ≤ ψ m := by
    intro m c hc hc1 hca hcm hmn
    have each : ∀ ℓ ∈ range (h + 1),
        cnt (A ℓ) (m - c) + 1 + cnt (A ℓ) (c - 1) ≤ cnt (A ℓ) m := by
      intro ℓ hℓ'
      simp only [mem_range] at hℓ'
      apply cnt_shift_lower (A ℓ) hc1 hcm
      intro a ha hmem
      by_contra hno
      apply hmin a (by omega) ℓ c
      exact ⟨by omega, hmem, by omega, hc, hc1, by omega, fun _ => by rwa [add_comm]⟩
    have := sum_le_sum each
    simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one] at this
    simp only [hψ, phi]; omega
  have hyp0 : ∀ m, m ≤ n → δ * m ≤ (phi A (h + 2) m : ℝ) := by
    intro m hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact hyp m hm hmn
  have Z : ∀ z, z < a₀ → z ≤ n → δ * z ≤ (ψ z : ℝ) := by
    intro z
    induction z using Nat.strong_induction_on with
    | _ z ih =>
      intro hz hzn
      by_cases hc : ∃ c, c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ z
      · obtain ⟨c, hc, hc1, hcz⟩ := hc
        have l6 := L6 z c hc hc1 (by omega) hcz hzn
        have i1 := ih (z - c) (by omega) (by omega) (by omega)
        have i2 := ih (c - 1) (by omega) (by omega) (by omega)
        have l6' : ((ψ (z - c) : ℕ) : ℝ) + (h + 1) + ψ (c - 1) ≤ ψ z := by exact_mod_cast l6
        rw [Nat.cast_sub hcz] at i1
        rw [Nat.cast_sub hc1] at i2
        push_cast at i1 i2
        nlinarith
      · push Not at hc
        have h0 : cnt (A (h + 1)) z = 0 := cnt_eq_zero (fun x h1 h2 hx => by
          have := hc x hx h1; omega)
        have := hyp0 z hzn
        rw [F1, h0, add_zero] at this
        exact this
  intro m hm1 hmn
  rw [F2]
  have f3 := F3 m
  have f4 := F4 m hmn
  have f5 := F5 m
  by_cases hb : ∃ b, b ∈ A (h + 1) ∧ m - a₀ < b ∧ b ≤ m
  · set b := Nat.find hb with hbdef
    obtain ⟨hbA, hb1, hb2⟩ := Nat.find_spec hb
    have F7 : cnt T m + cnt (A (h + 1)) (b - 1) ≤ cnt (A (h + 1)) m + cnt T (m - a₀) := by
      rw [cnt_split T (show m - a₀ ≤ m by omega),
        cnt_split (A (h + 1)) (show b - 1 ≤ m by omega)]
      have : #{x ∈ Ioc (m - a₀) m | x ∈ T} ≤ #{x ∈ Ioc (b - 1) m | x ∈ A (h + 1)} := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_Ioc] at hx ⊢
        have hxA := hTsub hx.2
        have : b ≤ x := Nat.find_min' hb ⟨hxA, hx.1.1, hx.1.2⟩
        exact ⟨⟨by omega, hx.1.2⟩, hxA⟩
      omega
    have l6 := L6 m b hbA (by omega) hb1 hb2 hmn
    have z := Z (m - b) (by omega) (by omega)
    have hb0 := hyp0 (b - 1) (by omega)
    rw [F1] at hb0
    have key : ψ (m - b) + (h + 1) + (ψ (b - 1) + cnt (A (h + 1)) (b - 1)) ≤
        phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A (h + 1) \ T) m := by omega
    have key' : ((ψ (m - b) : ℕ) : ℝ) + (h + 1) + ((ψ (b - 1) + cnt (A (h + 1)) (b - 1) : ℕ) : ℝ)
        ≤ ((phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A (h + 1) \ T) m : ℕ) : ℝ) := by
      exact_mod_cast key
    rw [Nat.cast_sub (show b ≤ m by omega)] at z
    rw [Nat.cast_sub (show 1 ≤ b by omega)] at hb0
    push_cast at z hb0 key' ⊢
    nlinarith
  · push Not at hb
    have F6 : cnt T m ≤ cnt T (m - a₀) := by
      rw [cnt_split T (show m - a₀ ≤ m by omega)]
      have : #{x ∈ Ioc (m - a₀) m | x ∈ T} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro x hx hxT
        simp only [mem_Ioc] at hx
        have := hb x (hTsub hxT) hx.1; omega
      omega
    have := hyp m hm1 hmn
    rw [F1] at this
    have key : ψ m + cnt (A (h + 1)) m ≤
        phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A (h + 1) \ T) m := by omega
    have key' : ((ψ m + cnt (A (h + 1)) m : ℕ) : ℝ) ≤
        ((phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A (h + 1) \ T) m : ℕ) : ℝ) := by
      exact_mod_cast key
    push_cast at key' this ⊢
    linarith

/-- **Dyson's theorem, rank `h`**, for `δ ≤ 1`: if `A_0(m) + ⋯ + A_h(m) ≥ δ m` for
`1 ≤ m ≤ n`, then `(A_0 + ⋯ + A_h)(n) ≥ δ n`. -/
theorem dysonR : ∀ (h n : ℕ) (A : ℕ → Set ℕ) (δ : ℝ), δ ≤ 1 → DysonHypR A (h + 1) n δ →
    δ * n ≤ cnt (SumSet A (h + 1)) n := by
  intro h
  induction h with
  | zero =>
    intro n A δ _ hyp
    have hss : A 0 ⊆ SumSet A 1 := fun p hp => ⟨fun _ => p, fun i hi => by
        have : i = 0 := by omega
        subst this; exact Or.inr hp, by simp⟩
    have hsub : cnt (A 0) n ≤ cnt (SumSet A 1) n := cnt_mono_set hss n
    show δ * n ≤ cnt (SumSet A 1) n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := hyp n hn le_rfl
      simp only [phi, zero_add, sum_range_one] at this
      have : (cnt (A 0) n : ℝ) ≤ cnt (SumSet A 1) n := by exact_mod_cast hsub
      linarith
  | succ h ih =>
    intro n
    suffices H : ∀ k (A : ℕ → Set ℕ) (δ : ℝ), δ ≤ 1 → cnt (A (h + 1)) n = k →
        DysonHypR A (h + 2) n δ → δ * n ≤ cnt (SumSet A (h + 2)) n from
      fun A δ hδ hyp => H _ A δ hδ rfl hyp
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro A δ hδ hk hyp
      by_cases hc : ∃ c, c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ n
      · obtain ⟨c, hcA, hc1, hcn⟩ := hc
        have hex : ∃ a, ∃ ℓ c, Trip A h n a ℓ c := by
          set a := Nat.findGreatest (fun a => a = 0 ∨ a ∈ A 0) n with ha
          have hP : a = 0 ∨ a ∈ A 0 := by
            rcases Nat.eq_zero_or_pos a with h0 | h0
            · exact Or.inl h0
            · exact Nat.findGreatest_of_ne_zero rfl h0.ne'
          refine ⟨a, 0, c, by omega, hP, Nat.findGreatest_le n, hcA, hc1, hcn, ?_⟩
          intro hle hmem
          have := Nat.le_findGreatest (P := fun a => a = 0 ∨ a ∈ A 0) hle (Or.inr hmem)
          omega
        set a₀ := Nat.find hex with ha₀
        obtain ⟨ℓ₀, c₀, htrip⟩ := Nat.find_spec hex
        have hmin : ∀ a < a₀, ∀ ℓ c, ¬ Trip A h n a ℓ c := by
          intro a ha ℓ c ht
          exact Nat.find_min hex ha ⟨ℓ, c, ht⟩
        obtain ⟨hℓ, ha, -, hcA0, hc01, hc0n, hc0⟩ := htrip
        have hyp' := hyp_trR hδ hℓ hmin hyp
        have hlt : cnt (tr A h n a₀ ℓ₀ (h + 1)) n < k := by
          rw [tr_last]
          have e := cnt_diff (B := A (h + 1)) (T := Tset A h n a₀ ℓ₀) (fun x hx => hx.1) n
          have p := cnt_pos (A := Tset A h n a₀ ℓ₀) (m := n) (c := c₀)
            ⟨hcA0, hc01, hc0n, hc0⟩ hc01 hc0n
          omega
        have i1 := ihk _ hlt _ δ hδ rfl hyp'
        have i2 : cnt (SumSet (tr A h n a₀ ℓ₀) (h + 2)) n ≤ cnt (SumSet A (h + 2)) n :=
          cnt_mono_le (fun p _ hp hr => rep_back hℓ ha hp hr)
        have : (cnt (SumSet (tr A h n a₀ ℓ₀) (h + 2)) n : ℝ) ≤ cnt (SumSet A (h + 2)) n := by
          exact_mod_cast i2
        linarith
      · push Not at hc
        have h0 : ∀ m, m ≤ n → cnt (A (h + 1)) m = 0 := fun m hm =>
          cnt_eq_zero (fun x h1 h2 hx => by have := hc x hx h1; omega)
        have hyp1 : DysonHypR A (h + 1) n δ := by
          intro m hm1 hmn
          have := hyp m hm1 hmn
          simp only [phi, sum_range_succ (n := h + 1), h0 m hmn, add_zero] at this
          simpa [phi] using this
        have i1 := ih n A δ hδ hyp1
        have i2 : cnt (SumSet A (h + 1)) n ≤ cnt (SumSet A (h + 2)) n :=
          cnt_mono_set (fun p hp => rep_succ hp) n
        have : (cnt (SumSet A (h + 1)) n : ℝ) ≤ cnt (SumSet A (h + 2)) n := by exact_mod_cast i2
        linarith

/-! ### Schnirelmann density -/

lemma card_ioc_eq_cnt (S : Set ℕ) (n : ℕ) : #{a ∈ Ioc 0 n | a ∈ S} = cnt S n := by
  unfold cnt
  congr 1

lemma density_mul_le_cnt (S : Set ℕ) (n : ℕ) : schnirelmannDensity S * n ≤ cnt S n := by
  rw [← card_ioc_eq_cnt]
  exact schnirelmannDensity_mul_le_card_filter

lemma le_density_of {S : Set ℕ} {x : ℝ} (h : ∀ n, 1 ≤ n → x * n ≤ cnt S n) :
    x ≤ schnirelmannDensity S := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  rw [card_ioc_eq_cnt, le_div_iff₀ (by exact_mod_cast hn)]
  exact h n hn

/-- **Mann's theorem** in its `H`-set form: `σ(A_0 + ⋯ + A_h) ≥ min(1, Σ σ(A_i))`. -/
theorem mann_sum (A : ℕ → Set ℕ) (h : ℕ) :
    min 1 (∑ i ∈ range (h + 1), schnirelmannDensity (A i)) ≤
      schnirelmannDensity (SumSet A (h + 1)) := by
  apply le_density_of
  intro n _
  apply dysonR h n A _ (min_le_left _ _)
  intro m _ _
  calc min 1 (∑ i ∈ range (h + 1), schnirelmannDensity (A i)) * m
      ≤ (∑ i ∈ range (h + 1), schnirelmannDensity (A i)) * m :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg m)
    _ = ∑ i ∈ range (h + 1), schnirelmannDensity (A i) * m := by rw [sum_mul]
    _ ≤ ∑ i ∈ range (h + 1), (cnt (A i) m : ℝ) :=
        sum_le_sum (fun i _ => density_mul_le_cnt (A i) m)
    _ = phi A (h + 1) m := by simp [phi]

/-- **Mann's theorem** (the `α + β` theorem): for `0 ∈ A`, `0 ∈ B`,
`σ(A + B) ≥ min(1, σ(A) + σ(B))`. -/
theorem mann (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ schnirelmannDensity (A + B) := by
  set F : ℕ → Set ℕ := fun i => if i = 0 then A else B with hF
  have h1 := mann_sum F 1
  have e : ∑ i ∈ range (1 + 1), schnirelmannDensity (F i) =
      schnirelmannDensity A + schnirelmannDensity B := by
    simp [sum_range_succ, hF]
  rw [e] at h1
  refine h1.trans (schnirelmannDensity_le_of_subset ?_)
  intro p hp
  obtain ⟨f, hf, hs⟩ := hp
  have h0 : f 0 ∈ A := by
    rcases hf 0 (by omega) with h | h
    · rw [h]; exact hA
    · simpa [hF] using h
  have h1' : f 1 ∈ B := by
    rcases hf 1 (by omega) with h | h
    · rw [h]; exact hB
    · simpa [hF] using h
  refine ⟨f 0, h0, f 1, h1', ?_⟩
  rw [← hs]
  simp [sum_range_succ]

end LeanLab.Schnirelmann.Mann
