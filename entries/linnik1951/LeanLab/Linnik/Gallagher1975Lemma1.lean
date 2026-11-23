module

public import Mathlib

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, Lemma 1, p.132,
the digit lemma, for g = 2, read from the page image of papers/P0094.pdf, PDF page 9.
Unit U-6824, CLOUD 20261021T0217Z-cloud56. AI-written Lean code, Claude, 2026-10-21.
Checked only by the Lean kernel. Binary Goldbach is OPEN.

The page: `G(α) = Σ_{ν=1}^{L} e(g^ν α)`; `(g-1) α ≡ Σ_{μ ≥ 1} a_μ g^{-μ} mod 1`, `0 ≤ a_μ < g`.
Lemma 1: let `|G(α)| ≥ (1-η) L`; then with `≪ ηL` exceptions the `a_1, ..., a_L` are `0` or
`g-1`; after deleting the exceptions there are `≪ ηL` changes from `0` to `g-1` or back;
constants uniform for `0 ≤ η ≤ 1`, `L ≥ 2`, depending on `g`.

For g = 2 every digit is 0 or 1 = g-1, so the first clause is empty and the content is the
count of changes. We take `a_μ = ⌊2^μ α⌋ mod 2`, the greedy binary digits of `α mod 1`.

* `lemma1`: PROVED, with the explicit constant 4: if `(1-η) L ≤ |G(α)|` then the number of
  `m ∈ [2, L]` with `a_m ≠ a_{m+1}` is at most `4 η L`, for every real `α`, `η` and every `L`.
  This is the range the paper's proof controls, `ν ∈ (1, L]` in (2).
* `lemma1_paper_range`: PROVED, over the printed range `a_1, ..., a_L`: at most `4 η L + 1`.
* `lemma1_literal_fails`: PROVED, the printed form with no `+1` fails at `η = 0`: `α = 1/2`
  gives `G = L` and `a_1 = 1 ≠ 0 = a_2`. With `η = 0` the exceptions number `≪ 0`, so none may
  be deleted, under any reading of the deletion. A boundary slip only: Lemma 2 and the rest of
  the paper lose nothing, a QUESTION, not a FINDING.
-/

@[expose] public section

open Finset Complex

noncomputable section
namespace LeanLab.Linnik.Gallagher1975Lemma1

/-- `e(x) = exp(2πix)`. -/
def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)

/-- Gallagher's `G(α) = Σ_{ν=1}^{L} e(2^ν α)`, p.132, `g = 2`. -/
def G (L : ℕ) (α : ℝ) : ℂ := ∑ ν ∈ Icc 1 L, e (2 ^ ν * α)

/-- The binary digit `a_μ` of `α mod 1`, `α ≡ Σ a_μ 2^{-μ}`, display (1), p.132, `g = 2`. -/
def digit (α : ℝ) (μ : ℕ) : ℤ := ⌊(2 : ℝ) ^ μ * α⌋ % 2

/-- The changes `a_m ≠ a_{m+1}` with `m ∈ [2, L]`, the range of the paper's proof. -/
def changes (α : ℝ) (L : ℕ) : Finset ℕ := {m ∈ Icc 2 L | digit α m ≠ digit α (m + 1)}

/-- The changes among the printed `a_1, ..., a_L`: `a_m ≠ a_{m+1}`, `m ∈ [1, L-1]`. -/
def changesPaper (α : ℝ) (L : ℕ) : Finset ℕ :=
  {m ∈ Icc 1 (L - 1) | digit α m ≠ digit α (m + 1)}

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := norm_exp_ofReal_mul_I _

theorem re_e (x : ℝ) : (e x).re = Real.cos (2 * Real.pi * x) := exp_ofReal_mul_I_re _

theorem e_two_mul (x : ℝ) : e (2 * x) = e x ^ 2 := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

/-- For `‖a‖ = 1`, `‖a - 1‖² = 2 - 2 Re a`. -/
theorem norm_sub_one_sq {a : ℂ} (ha : ‖a‖ = 1) : ‖a - 1‖ ^ 2 = 2 - 2 * a.re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq, ha]
  simp; ring

/-- The digit step of (2): if `cos(2π 2^ν α) > 0`, the fractional part of `2^ν α` lies in
`[0, 1/4) ∪ (3/4, 1)`, so `a_{ν+1} = a_{ν+2}`. -/
theorem digit_eq_of_cos_pos (α : ℝ) (ν : ℕ) (h : 0 < Real.cos (2 * Real.pi * (2 ^ ν * α))) :
    digit α (ν + 1) = digit α (ν + 2) := by
  set t := (2 : ℝ) ^ ν * α with ht
  set n := ⌊t⌋ with hn
  set f := t - n with hf
  have hf0 : 0 ≤ f := by rw [hf]; linarith [Int.floor_le t]
  have hf1 : f < 1 := by rw [hf]; linarith [Int.lt_floor_add_one t]
  have hcos : Real.cos (2 * Real.pi * t) = Real.cos (2 * Real.pi * f) := by
    have : 2 * Real.pi * t = 2 * Real.pi * f + (n : ℝ) * (2 * Real.pi) := by rw [hf]; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  have hpi := Real.pi_pos
  have hcase : f < 1 / 4 ∨ 3 / 4 < f := by
    by_contra hc
    push Not at hc
    have : Real.cos (2 * Real.pi * f) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [hc.1]) (by nlinarith [hc.2])
    rw [← hcos] at this
    linarith
  have e1 : (2 : ℝ) ^ (ν + 1) * α = 2 * n + 2 * f := by rw [pow_succ, hf, ht]; ring
  have e2 : (2 : ℝ) ^ (ν + 2) * α = 4 * n + 4 * f := by rw [pow_add, hf, ht]; ring
  unfold digit
  rw [e1, e2]
  rcases hcase with hc | hc
  · have h1 : ⌊(2 : ℝ) * n + 2 * f⌋ = 2 * n := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have h2 : ⌊(4 : ℝ) * n + 4 * f⌋ = 4 * n := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [h1, h2]; omega
  · have h1 : ⌊(2 : ℝ) * n + 2 * f⌋ = 2 * n + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have h2 : ⌊(4 : ℝ) * n + 4 * f⌋ = 4 * n + 3 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [h1, h2]; omega

/-- A rotation `w`, `‖w‖ = 1`, with `Re(w G) = ‖G‖`: the paper's choice of `β`. -/
theorem exists_rot (z : ℂ) : ∃ w : ℂ, ‖w‖ = 1 ∧ (w * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
    refine ⟨(starRingEnd ℂ) z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hn.le,
        div_self hn.ne']
    · rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [show ((‖z‖ ^ 2 : ℝ) : ℂ) / (‖z‖ : ℂ) = ((‖z‖ : ℝ) : ℂ) by
        rw [div_eq_iff (by exact_mod_cast hn.ne')]; push_cast; ring]
      simp

/-- The pair step: a change at `m = ν + 1` forces `D_ν + D_{ν+1} ≥ 1/2`, where
`D_ν = 1 - Re(w e(2^ν α))`. -/
theorem pair_step {w : ℂ} (hw : ‖w‖ = 1) (α : ℝ) (ν : ℕ)
    (hch : digit α (ν + 1) ≠ digit α (ν + 2)) :
    1 / 2 ≤ (1 - (w * e (2 ^ ν * α)).re) + (1 - (w * e (2 ^ (ν + 1) * α)).re) := by
  set z := e (2 ^ ν * α) with hz
  have hz1 : ‖z‖ = 1 := norm_e _
  have hcos : Real.cos (2 * Real.pi * (2 ^ ν * α)) ≤ 0 := by
    by_contra hc; push Not at hc; exact hch (digit_eq_of_cos_pos α ν hc)
  have hb : e (2 ^ (ν + 1) * α) = z ^ 2 := by
    rw [hz, ← e_two_mul]; congr 1; rw [pow_succ]; ring
  rw [hb]
  set a := w * z
  set b := w * z ^ 2
  have ha1 : ‖a‖ = 1 := by simp [a, hw, hz1]
  have hb1 : ‖b‖ = 1 := by simp [b, hw, hz1]
  have hzre : z.re ≤ 0 := by rw [hz, re_e]; exact hcos
  have hz2 : 2 ≤ ‖z - 1‖ ^ 2 := by rw [norm_sub_one_sq hz1]; linarith
  have hba : ‖b - a‖ = ‖z - 1‖ := by
    have : b - a = w * z * (z - 1) := by simp only [a, b]; ring
    rw [this, norm_mul, norm_mul, hw, hz1]; ring
  have htri : ‖b - a‖ ≤ ‖b - 1‖ + ‖a - 1‖ := by
    have : b - a = (b - 1) - (a - 1) := by ring
    rw [this]; exact norm_sub_le _ _
  have hA := norm_sub_one_sq ha1
  have hB := norm_sub_one_sq hb1
  have h0 : 0 ≤ ‖b - 1‖ := norm_nonneg _
  have h0' : 0 ≤ ‖a - 1‖ := norm_nonneg _
  have hsq : ‖b - a‖ ^ 2 ≤ 2 * (‖b - 1‖ ^ 2 + ‖a - 1‖ ^ 2) := by
    have h1 : ‖b - a‖ ^ 2 ≤ (‖b - 1‖ + ‖a - 1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖b - 1‖ - ‖a - 1‖)]
  rw [hba] at hsq
  linarith

/-- **Gallagher 1975, Lemma 1, p.132, g = 2**, PROVED with constant 4: if
`|G(α)| ≥ (1-η) L` then at most `4 η L` of the `m ∈ [2, L]` have `a_m ≠ a_{m+1}`. -/
theorem lemma1 (α η : ℝ) (L : ℕ) (h : (1 - η) * L ≤ ‖G L α‖) :
    (#(changes α L) : ℝ) ≤ 4 * η * L := by
  obtain ⟨w, hw, hwG⟩ := exists_rot (G L α)
  set D : ℕ → ℝ := fun ν => 1 - (w * e (2 ^ ν * α)).re with hD
  have hD0 : ∀ ν, 0 ≤ D ν := by
    intro ν
    have : (w * e (2 ^ ν * α)).re ≤ 1 := by
      calc (w * e (2 ^ ν * α)).re ≤ ‖w * e (2 ^ ν * α)‖ := Complex.re_le_norm _
        _ = 1 := by rw [norm_mul, hw, norm_e, one_mul]
    simp only [hD]; linarith
  have hsum : ∑ ν ∈ Icc 1 L, D ν ≤ η * L := by
    have : ∑ ν ∈ Icc 1 L, D ν = L - (w * G L α).re := by
      simp only [hD, sum_sub_distrib, sum_const, Nat.card_Icc, G, mul_sum, re_sum]
      simp
    rw [this, hwG]; linarith
  have hpair : ∀ m ∈ changes α L, 1 / 2 ≤ D (m - 1) + D m := by
    intro m hm
    simp only [changes, mem_filter, mem_Icc] at hm
    have hm1 : m - 1 + 1 = m := by omega
    have hm2 : m - 1 + 2 = m + 1 := by omega
    have := pair_step hw α (m - 1) (by rw [hm1, hm2]; exact hm.2)
    simp only [hD]; rw [hm1] at this; exact this
  have hsub : changes α L ⊆ Icc 2 L := filter_subset _ _
  have hshift : ∑ m ∈ Icc 2 L, D (m - 1) ≤ ∑ ν ∈ Icc 1 L, D ν := by
    rw [← sum_image (s := Icc 2 L) (g := fun m => m - 1) (f := D)]
    · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => hD0 _)
      intro x hx
      simp only [mem_image, mem_Icc] at hx ⊢
      omega
    · intro x hx y hy hxy
      simp only [coe_Icc, Set.mem_Icc] at hx hy
      simp only at hxy
      omega
  have hself : ∑ m ∈ Icc 2 L, D m ≤ ∑ ν ∈ Icc 1 L, D ν :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) le_rfl)
      (fun _ _ _ => hD0 _)
  have hcount : (#(changes α L) : ℝ) * (1 / 2) ≤ ∑ m ∈ Icc 2 L, (D (m - 1) + D m) := by
    calc (#(changes α L) : ℝ) * (1 / 2) = ∑ _m ∈ changes α L, (1 / 2 : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ changes α L, (D (m - 1) + D m) := sum_le_sum hpair
      _ ≤ ∑ m ∈ Icc 2 L, (D (m - 1) + D m) :=
          sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => add_nonneg (hD0 _) (hD0 _))
  rw [sum_add_distrib] at hcount
  linarith

/-- Lemma 1 over the printed digits `a_1, ..., a_L`: at most `4 η L + 1` changes. -/
theorem lemma1_paper_range (α η : ℝ) (L : ℕ) (h : (1 - η) * L ≤ ‖G L α‖) :
    (#(changesPaper α L) : ℝ) ≤ 4 * η * L + 1 := by
  have hsub : changesPaper α L ⊆ insert 1 (changes α L) := by
    intro m hm
    simp only [changesPaper, changes, mem_filter, mem_Icc, mem_insert] at hm ⊢
    by_cases h1 : m = 1
    · exact Or.inl h1
    · exact Or.inr ⟨⟨by omega, by omega⟩, hm.2⟩
  have h1 : #(changesPaper α L) ≤ #(changes α L) + 1 :=
    (card_le_card hsub).trans (card_insert_le _ _)
  have h2 : (#(changesPaper α L) : ℝ) ≤ #(changes α L) + 1 := by exact_mod_cast h1
  linarith [lemma1 α η L h]

/-- `G(1/2) = L`: every `2^ν / 2` with `ν ≥ 1` is an integer. -/
theorem G_half (L : ℕ) : G L (1 / 2) = L := by
  unfold G
  rw [show (L : ℂ) = ∑ _ν ∈ Icc 1 L, (1 : ℂ) by simp]
  apply sum_congr rfl
  intro ν hν
  simp only [mem_Icc] at hν
  unfold e
  have : ((2 * Real.pi * ((2 : ℝ) ^ ν * (1 / 2)) : ℝ) : ℂ) * I
      = ((2 ^ (ν - 1) : ℕ) : ℂ) * (2 * Real.pi * I) := by
    obtain ⟨k, rfl⟩ : ∃ k, ν = k + 1 := ⟨ν - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast; ring
  rw [this, Complex.exp_nat_mul_two_pi_mul_I]

/-- At `α = 1/2`: `a_1 = 1`, `a_2 = 0`. -/
theorem digit_half_one : digit (1 / 2) 1 = 1 := by norm_num [digit]

theorem digit_half_two : digit (1 / 2) 2 = 0 := by norm_num [digit]

/-- **The printed form of Lemma 1 fails at `η = 0`**: no constant `C` gives
`#changes(a_1, ..., a_L) ≤ C η L` uniformly for `0 ≤ η ≤ 1`, `L ≥ 2`. Witness
`α = 1/2`, `η = 0`, `L = 2`. -/
theorem lemma1_literal_fails :
    ¬ ∃ C : ℝ, ∀ (α η : ℝ) (L : ℕ), 0 ≤ η → η ≤ 1 → 2 ≤ L →
      (1 - η) * L ≤ ‖G L α‖ → (#(changesPaper α L) : ℝ) ≤ C * η * L := by
  rintro ⟨C, hC⟩
  have hG : (1 - 0) * ((2 : ℕ) : ℝ) ≤ ‖G 2 (1 / 2)‖ := by
    rw [G_half]; simp
  have h := hC (1 / 2) 0 2 le_rfl (by norm_num) le_rfl hG
  have hmem : 1 ∈ changesPaper (1 / 2) 2 := by
    simp only [changesPaper, mem_filter, mem_Icc]
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    rw [digit_half_one, show (1 + 1 : ℕ) = 2 from rfl, digit_half_two]; norm_num
  have hpos : (1 : ℝ) ≤ #(changesPaper (1 / 2) 2) := by
    exact_mod_cast card_pos.2 ⟨1, hmem⟩
  rw [mul_zero, zero_mul] at h
  linarith

/-- Vacuity: the hypothesis of `lemma1` holds at `α = 1/2`, `η = 0`, `L = 5`, so the lemma
says those digits `a_2, ..., a_6` never change, and indeed they are all 0. -/
theorem lemma1_instance : (1 - 0) * ((5 : ℕ) : ℝ) ≤ ‖G 5 (1 / 2)‖ ∧
    changes (1 / 2) 5 = ∅ := by
  have hG : (1 - 0) * ((5 : ℕ) : ℝ) ≤ ‖G 5 (1 / 2)‖ := by rw [G_half]; simp
  refine ⟨hG, ?_⟩
  have h := lemma1 (1 / 2) 0 5 hG
  simp only [mul_zero, zero_mul] at h
  exact card_eq_zero.1 (by exact_mod_cast le_antisymm (by exact_mod_cast h) (Nat.zero_le _))

end LeanLab.Linnik.Gallagher1975Lemma1

