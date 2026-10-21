module

public import LeanLab.PNTSieve.Bonferroni

/-!
# Weighted Bonferroni: the main term of Brun's pure sieve

Lab proof, unit U-5323, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.
For weights `0 ≤ x_p ≤ 1` on a finset `P`, the truncations of `∏_{p ∈ P} (1 - x_p) =
Σ_{T ⊆ P} (-1)^{|T|} ∏_{p ∈ T} x_p` alternate around the product:

* `avg_identity`: `Σ_{S ⊆ P} w(S) trunc(S, r) = Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} ∏_T x_p`, where
  `w(S) = ∏_S x_p ∏_{P \ S} (1 - x_p)` are the probabilities of independent events;
* `weighted_odd`, `weighted_even`: the truncation at odd `r` is `≤ ∏_P (1 - x_p)`, at even `r` it is `≥`;
* `weighted_dev`, U-5324: the error is at most `e_{r+1}(x) = Σ_{|T| = r + 1} ∏_T x_p`.
With `Bonferroni.brun_lower` this is the main term step of Brun's pure sieve, IDEAS I-5051.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

variable {α : Type*} [DecidableEq α]

/-- `w(S) = ∏_{p ∈ S} x_p ∏_{p ∈ P \ S} (1 - x_p)`. -/
def wt (x : α → ℝ) (P S : Finset α) : ℝ := (∏ p ∈ S, x p) * ∏ p ∈ P \ S, (1 - x p)

lemma wt_nonneg (x : α → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (P S : Finset α) :
    0 ≤ wt x P S :=
  mul_nonneg (prod_nonneg fun p _ => hx0 p) (prod_nonneg fun p _ => by linarith [hx1 p])

/-- `Σ_{S ⊆ P} w(S) = 1`. -/
lemma sum_wt (x : α → ℝ) (P : Finset α) : ∑ S ∈ P.powerset, wt x P S = 1 := by
  have h := prod_add (fun p => x p) (fun p => 1 - x p) P
  simp only [add_sub_cancel, prod_const_one] at h
  unfold wt
  exact h.symm

/-- `Σ_{S ⊆ P, T ⊆ S} w(S) = ∏_T x_p` for `T ⊆ P`. -/
lemma sum_wt_superset (x : α → ℝ) (P T : Finset α) (hT : T ⊆ P) :
    ∑ S ∈ P.powerset.filter (fun S => T ⊆ S), wt x P S = ∏ p ∈ T, x p := by
  have himg : P.powerset.filter (fun S => T ⊆ S) = (P \ T).powerset.image (fun U => T ∪ U) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hSP, hTS⟩
      refine ⟨S \ T, sdiff_subset_sdiff hSP le_rfl, ?_⟩
      exact union_sdiff_of_subset hTS
    · rintro ⟨U, hU, rfl⟩
      exact ⟨union_subset hT (hU.trans sdiff_subset), subset_union_left⟩
  have hinj : ∀ U₁ ∈ (P \ T).powerset, ∀ U₂ ∈ (P \ T).powerset, T ∪ U₁ = T ∪ U₂ → U₁ = U₂ := by
    intro U₁ h₁ U₂ h₂ he
    rw [mem_powerset] at h₁ h₂
    have d₁ : Disjoint T U₁ := disjoint_of_subset_right h₁ disjoint_sdiff
    have d₂ : Disjoint T U₂ := disjoint_of_subset_right h₂ disjoint_sdiff
    calc U₁ = (T ∪ U₁) \ T := (union_sdiff_cancel_left d₁).symm
      _ = (T ∪ U₂) \ T := by rw [he]
      _ = U₂ := union_sdiff_cancel_left d₂
  rw [himg, sum_image hinj]
  have hterm : ∀ U ∈ (P \ T).powerset, wt x P (T ∪ U) =
      (∏ p ∈ T, x p) * ((∏ p ∈ U, x p) * ∏ p ∈ (P \ T) \ U, (1 - x p)) := by
    intro U hU
    rw [mem_powerset] at hU
    have d : Disjoint T U := disjoint_of_subset_right hU disjoint_sdiff
    unfold wt
    have e : P \ (T ∪ U) = (P \ T) \ U := by ext p; simp only [mem_sdiff, mem_union]; tauto
    rw [prod_union d, e]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have h := prod_add (fun p => x p) (fun p => 1 - x p) (P \ T)
  simp only [add_sub_cancel, prod_const_one] at h
  rw [← h, mul_one]

/-- `Σ_{S ⊆ P} w(S) trunc(S, r) = Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} ∏_T x_p`. -/
lemma avg_identity (x : α → ℝ) (P : Finset α) (r : ℕ) :
    ∑ S ∈ P.powerset, wt x P S * (trunc S r : ℝ) =
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p := by
  unfold trunc
  push_cast
  simp_rw [mul_sum]
  rw [Finset.sum_comm' (t' := P.powerset.filter (fun T => T.card ≤ r))
    (s' := fun T => P.powerset.filter (fun S => T ⊆ S))]
  · refine sum_congr rfl (fun T hT => ?_)
    rw [mem_filter, mem_powerset] at hT
    rw [← sum_mul, sum_wt_superset x P T hT.1, mul_comm]
  · intro S T
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨hS, hTS, hr⟩; exact ⟨⟨hS, hTS⟩, hTS.trans hS, hr⟩
    · rintro ⟨⟨hS, hTS⟩, -, hr⟩; exact ⟨hS, hTS, hr⟩

/-- `∏_P (1 - x_p) = Σ_{S ⊆ P} w(S) [S = ∅]`. -/
lemma prod_eq_wt_empty (x : α → ℝ) (P : Finset α) :
    ∏ p ∈ P, (1 - x p) = ∑ S ∈ P.powerset, wt x P S * (if S = ∅ then (1 : ℤ) else 0 : ℤ) := by
  rw [sum_eq_single_of_mem ∅ (empty_mem_powerset P)]
  · simp [wt]
  · intro S _ hS; simp [hS]

/-- Odd truncation: `Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} ∏_T x_p ≤ ∏_P (1 - x_p)` for `0 ≤ x_p ≤ 1`. -/
theorem weighted_odd (x : α → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (P : Finset α)
    {r : ℕ} (hr : Odd r) :
    ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p ≤
      ∏ p ∈ P, (1 - x p) := by
  rw [← avg_identity, prod_eq_wt_empty]
  apply sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (wt_nonneg x hx0 hx1 P S)
  exact_mod_cast bonferroni_odd S hr

/-- Even truncation: `∏_P (1 - x_p) ≤ Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} ∏_T x_p` for `0 ≤ x_p ≤ 1`. -/
theorem weighted_even (x : α → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (P : Finset α)
    {r : ℕ} (hr : Even r) :
    ∏ p ∈ P, (1 - x p) ≤
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p := by
  rw [← avg_identity, prod_eq_wt_empty]
  apply sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (wt_nonneg x hx0 hx1 P S)
  exact_mod_cast bonferroni_even S hr

/-- Pointwise deviation: `|trunc(S, r) - [S = ∅]| ≤ C(|S|, r + 1)`. -/
lemma trunc_dev (S : Finset α) (r : ℕ) :
    |(trunc S r : ℝ) - (if S = ∅ then (1 : ℤ) else 0 : ℤ)| ≤ ((S.card).choose (r + 1) : ℝ) := by
  by_cases h : S = ∅
  · subst h; simp [trunc_empty]
  · obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
      ⟨S.card - 1, by have := card_pos.mpr (nonempty_iff_ne_empty.mpr h); omega⟩
    rw [if_neg h, trunc_sum_eq S m r hm, hm, Nat.choose_succ_succ]
    push_cast
    rw [sub_zero, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg _)]
    have : (0 : ℝ) ≤ (m.choose (r + 1) : ℝ) := Nat.cast_nonneg _
    linarith

/-- `Σ_{S ⊆ P} w(S) C(|S|, r + 1) = Σ_{T ⊆ P, |T| = r + 1} ∏_T x_p`. -/
lemma sum_wt_choose (x : α → ℝ) (P : Finset α) (r : ℕ) :
    ∑ S ∈ P.powerset, wt x P S * ((S.card).choose (r + 1) : ℝ) =
      ∑ T ∈ P.powersetCard (r + 1), ∏ p ∈ T, x p := by
  have h1 : ∀ S ∈ P.powerset, wt x P S * ((S.card).choose (r + 1) : ℝ) =
      ∑ T ∈ S.powersetCard (r + 1), wt x P S := by
    intro S _
    rw [sum_const, card_powersetCard, nsmul_eq_mul, mul_comm]
  rw [sum_congr rfl h1, Finset.sum_comm' (t' := P.powersetCard (r + 1))
    (s' := fun T => P.powerset.filter (fun S => T ⊆ S))]
  · refine sum_congr rfl (fun T hT => ?_)
    exact sum_wt_superset x P T (mem_powersetCard.mp hT).1
  · intro S T
    simp only [mem_powerset, mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨hS, hTS, hc⟩; exact ⟨⟨hS, hTS⟩, hTS.trans hS, hc⟩
    · rintro ⟨⟨hS, hTS⟩, -, hc⟩; exact ⟨hS, hTS, hc⟩

/-- The error of the truncation: `|Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} ∏_T x_p - ∏_P (1 - x_p)| ≤
Σ_{T ⊆ P, |T| = r + 1} ∏_T x_p`, the elementary symmetric function `e_{r+1}(x)`, for `0 ≤ x_p ≤ 1`. -/
theorem weighted_dev (x : α → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (P : Finset α)
    (r : ℕ) :
    |∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p -
      ∏ p ∈ P, (1 - x p)| ≤ ∑ T ∈ P.powersetCard (r + 1), ∏ p ∈ T, x p := by
  rw [← avg_identity, prod_eq_wt_empty, ← sum_sub_distrib, ← sum_wt_choose]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun S _ => ?_))
  rw [← mul_sub, abs_mul, abs_of_nonneg (wt_nonneg x hx0 hx1 P S)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast trunc_dev S r) (wt_nonneg x hx0 hx1 P S)

end LeanLab.PNTSieve.Bonferroni

