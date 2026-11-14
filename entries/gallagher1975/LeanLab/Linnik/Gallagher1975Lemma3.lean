module

public import Mathlib
public import LeanLab.Linnik.Gallagher1975Lemma1

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, Lemma 3, p.133,
for g = 2, read from the page image of papers/P0094.pdf, PDF page 10.
Unit U-6824, CLOUD 20261021T0217Z-cloud56. AI-written Lean code, Claude, 2026-10-21.
Checked only by the Lean kernel. Binary Goldbach is OPEN.

The page: if `α` is rational with denominator `q` prime to `g` and `g - 1`, and
`1 < e(q) ≤ L`, `e(q)` the order of `g` mod `q`, then `|G(α)| ≤ (1 - C/e(q)) L`, `C > 0`.
Proof on the page: `g^{e(q)} β ≡ β mod 1`, so the digits have period dividing `e(q)`; there
are `≫ L/e(q)` changes among `a_1, ..., a_L`; then Lemma 1.

* `lemma3`: PROVED with `C = 1/16`, in the form: `α` not an integer, `(2^e - 1) α` an
  integer, `2 ≤ e ≤ L` give `|G(α)| < (1 - 1/(16e)) L`. With `e = e(q)` and `α = a/q`, `q`
  odd, `q > 1`, these are the paper's hypotheses: `q | 2^{e(q)} - 1`, and `e(q) > 1` forces
  `q > 1`, so `α ∉ ℤ` once `a/q` is in lowest terms.
* `lemma3_instance`: vacuity, `α = 1/3`, `e = 2`, `L = 2`.
-/

@[expose] public section

open Finset

noncomputable section
namespace LeanLab.Linnik.Gallagher1975Lemma1

/-- The digits have period `e` once `(2^e - 1) α ∈ ℤ`. -/
theorem digit_periodic {α : ℝ} {e : ℕ} (hper : ∃ z : ℤ, ((2 : ℝ) ^ e - 1) * α = z)
    {μ : ℕ} (hμ : 1 ≤ μ) : digit α (μ + e) = digit α μ := by
  obtain ⟨z, hz⟩ := hper
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
  have h : (2 : ℝ) ^ (k + 1 + e) * α = (2 : ℝ) ^ (k + 1) * α + ((2 * (2 ^ k * z) : ℤ) : ℝ) := by
    push_cast
    rw [← hz, pow_add, pow_succ]; ring
  unfold digit
  rw [h, Int.floor_add_intCast]
  omega

theorem digit_periodic_mul {α : ℝ} {e : ℕ} (hper : ∃ z : ℤ, ((2 : ℝ) ^ e - 1) * α = z)
    {μ : ℕ} (hμ : 1 ≤ μ) (t : ℕ) : digit α (μ + t * e) = digit α μ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show μ + (t + 1) * e = (μ + t * e) + e by ring, digit_periodic hper (by omega), ih]

/-- No change in `[s, s+e-2]` makes `a_s = ... = a_{s+e-1}`. -/
theorem const_window {α : ℝ} {s e : ℕ}
    (h : ∀ m ∈ Icc s (s + e - 2), digit α m = digit α (m + 1)) (he : 2 ≤ e) :
    ∀ j, j ≤ e - 1 → digit α (s + j) = digit α s := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have := h (s + j) (by simp only [mem_Icc]; omega)
    rw [show s + (j + 1) = s + j + 1 by ring, ← this, ih (by omega)]

/-- Doubling: `a_{n+1} = ⌊2 {2^n α}⌋` and `{2^{n+1} α} = 2 {2^n α} - a_{n+1}`. -/
theorem fract_step (α : ℝ) (n : ℕ) :
    (digit α (n + 1) = 0 ∧ Int.fract ((2 : ℝ) ^ (n + 1) * α) = 2 * Int.fract ((2 : ℝ) ^ n * α)) ∨
    (digit α (n + 1) = 1 ∧
      Int.fract ((2 : ℝ) ^ (n + 1) * α) = 2 * Int.fract ((2 : ℝ) ^ n * α) - 1) := by
  set y := (2 : ℝ) ^ n * α
  set f := Int.fract y
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hy : (2 : ℝ) ^ (n + 1) * α = 2 * f + ((2 * ⌊y⌋ : ℤ) : ℝ) := by
    have := Int.floor_add_fract y
    push_cast
    rw [pow_succ]
    simp only [f, y] at this ⊢
    linarith
  unfold digit
  rw [hy, Int.floor_add_intCast, Int.fract_add_intCast]
  by_cases hh : f < 1 / 2
  · left
    have h0 : ⌊2 * f⌋ = 0 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [h0, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    exact ⟨by omega, rfl⟩
  · right
    push Not at hh
    have h1 : ⌊2 * f⌋ = 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hfr : Int.fract (2 * f) = 2 * f - 1 := by
      rw [Int.fract, h1]; push_cast; ring
    rw [h1, hfr]
    exact ⟨by omega, rfl⟩

/-- If every digit `a_μ`, `μ ≥ 1`, equals `c`, then `α` is an integer. -/
theorem int_of_const {α : ℝ} {c : ℤ} (h : ∀ μ, 1 ≤ μ → digit α μ = c) : ∃ z : ℤ, α = z := by
  rcases fract_step α 0 with ⟨h0, _⟩ | ⟨h0, _⟩
  · -- all digits 0: `{2^n α} = 2^n {α}`, bounded by 1
    have hc : c = 0 := by rw [← h 1 le_rfl]; simpa using h0
    have hx : ∀ n : ℕ, Int.fract ((2 : ℝ) ^ n * α) = 2 ^ n * Int.fract α := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rcases fract_step α n with ⟨_, h2⟩ | ⟨h1, _⟩
        · rw [h2, ih, pow_succ]; ring
        · rw [h (n + 1) (by omega)] at h1; omega
    refine ⟨⌊α⌋, ?_⟩
    by_contra hne
    have hpos : 0 < Int.fract α := by
      rcases (Int.fract_nonneg α).lt_or_eq with hp | hp
      · exact hp
      · exfalso; apply hne; rw [← Int.self_sub_floor] at hp; linarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / Int.fract α) (by norm_num : (1 : ℝ) < 2)
    have := Int.fract_lt_one ((2 : ℝ) ^ n * α)
    rw [hx n] at this
    rw [div_lt_iff₀ hpos] at hn
    linarith
  · -- all digits 1: `1 - {2^n α} = 2^n (1 - {α})`, bounded by 1
    exfalso
    have hc : c = 1 := by rw [← h 1 le_rfl]; simpa using h0
    have hx : ∀ n : ℕ, 1 - Int.fract ((2 : ℝ) ^ n * α) = 2 ^ n * (1 - Int.fract α) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rcases fract_step α n with ⟨h1, _⟩ | ⟨_, h2⟩
        · rw [h (n + 1) (by omega)] at h1; omega
        · rw [h2, pow_succ]; linarith
    have hpos : 0 < 1 - Int.fract α := by linarith [Int.fract_lt_one α]
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 - Int.fract α)) (by norm_num : (1 : ℝ) < 2)
    have := Int.fract_nonneg ((2 : ℝ) ^ n * α)
    have h2 := hx n
    rw [div_lt_iff₀ hpos] at hn
    linarith

/-- Every window `[s, s+e-2]`, `s ≥ 1`, holds a change, when `α ∉ ℤ` has period `e ≥ 2`. -/
theorem window_change {α : ℝ} {e : ℕ} (hα : ¬ ∃ z : ℤ, α = z)
    (hper : ∃ z : ℤ, ((2 : ℝ) ^ e - 1) * α = z) (he : 2 ≤ e) {s : ℕ} (hs : 1 ≤ s) :
    ∃ m ∈ Icc s (s + e - 2), digit α m ≠ digit α (m + 1) := by
  by_contra hno
  push Not at hno
  have hw := const_window hno he
  apply hα
  apply int_of_const (c := digit α s)
  intro μ hμ
  -- move μ up by s periods, then down into the window
  set μ' := μ + s * e with hμ'
  have h1 : digit α μ' = digit α μ := digit_periodic_mul hper hμ s
  have hge : s ≤ μ' := by
    have : s ≤ s * e := Nat.le_mul_of_pos_right s (by omega)
    omega
  set r := (μ' - s) % e
  set q := (μ' - s) / e
  have hdecomp : μ' = (s + r) + q * e := by
    have := Nat.mod_add_div (μ' - s) e
    simp only [r, q]
    rw [mul_comm] at this
    omega
  have hr : r < e := Nat.mod_lt _ (by omega)
  have h2 : digit α μ' = digit α (s + r) := by
    rw [hdecomp]; exact digit_periodic_mul hper (by omega) q
  rw [← h1, h2, hw r (by omega)]

/-- At least `⌊(L-1)/(e-1)⌋` changes in `[2, L]`. -/
theorem card_changes_ge {α : ℝ} {e L : ℕ} (hα : ¬ ∃ z : ℤ, α = z)
    (hper : ∃ z : ℤ, ((2 : ℝ) ^ e - 1) * α = z) (he : 2 ≤ e) :
    (L - 1) / (e - 1) ≤ #(changes α L) := by
  classical
  have hw : ∀ t : ℕ, ∃ m ∈ Icc (2 + t * (e - 1)) (2 + t * (e - 1) + e - 2),
      digit α m ≠ digit α (m + 1) := fun t => window_change hα hper he (by omega)
  choose f hf using hw
  rw [← card_range ((L - 1) / (e - 1))]
  apply card_le_card_of_injOn f
  · intro t ht
    simp only [coe_range, Set.mem_Iio] at ht
    have hft := (hf t).1
    simp only [mem_Icc] at hft
    simp only [changes, coe_filter, mem_Icc, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, ?_⟩, (hf t).2⟩
    have h1 : (t + 1) * (e - 1) ≤ (L - 1) / (e - 1) * (e - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (L - 1) / (e - 1) * (e - 1) ≤ L - 1 := Nat.div_mul_le_self _ _
    have h3 : (t + 1) * (e - 1) = t * (e - 1) + (e - 1) := by ring
    omega
  · intro t _ t' _ htt
    have ha := (hf t).1
    have hb := (hf t').1
    simp only [mem_Icc] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (t + 1) * (e - 1) ≤ t' * (e - 1) := Nat.mul_le_mul_right _ hlt
      have h3 : (t + 1) * (e - 1) = t * (e - 1) + (e - 1) := by ring
      omega
    · have : (t' + 1) * (e - 1) ≤ t * (e - 1) := Nat.mul_le_mul_right _ hlt
      have h3 : (t' + 1) * (e - 1) = t' * (e - 1) + (e - 1) := by ring
      omega

/-- **Gallagher 1975, Lemma 3, p.133, g = 2**, PROVED with `C = 1/16`: if `α ∉ ℤ`,
`(2^e - 1) α ∈ ℤ` and `2 ≤ e ≤ L`, then `|G(α)| < (1 - 1/(16 e)) L`. -/
theorem lemma3 {α : ℝ} {e L : ℕ} (hα : ¬ ∃ z : ℤ, α = z)
    (hper : ∃ z : ℤ, ((2 : ℝ) ^ e - 1) * α = z) (he : 2 ≤ e) (heL : e ≤ L) :
    ‖G L α‖ < (1 - 1 / (16 * e)) * L := by
  by_contra hcon
  push Not at hcon
  have h1 := lemma1 α (1 / (16 * e)) L hcon
  have h2 := card_changes_ge (L := L) hα hper he
  set W := (L - 1) / (e - 1)
  -- `L ≤ 2 W e`
  have hW1 : W * (e - 1) ≤ L - 1 := Nat.div_mul_le_self _ _
  have hW2 : L - 1 < (W + 1) * (e - 1) := by
    have := Nat.lt_div_mul_add (a := L - 1) (b := e - 1) (by omega)
    have h3 : (W + 1) * (e - 1) = W * (e - 1) + (e - 1) := by ring
    simp only [W] at h3 ⊢
    omega
  have hWpos : 1 ≤ W := by
    simp only [W]; exact (Nat.one_le_div_iff (by omega)).2 (by omega)
  have hLW : L ≤ 2 * W * e := by
    have h3 : (W + 1) * (e - 1) = W * (e - 1) + (e - 1) := by ring
    have h4 : (e - 1) ≤ W * (e - 1) := Nat.le_mul_of_pos_left _ hWpos
    have h5 : W * (e - 1) ≤ W * e := Nat.mul_le_mul_left _ (by omega)
    have h6 : 2 * W * e = W * e + W * e := by ring
    omega
  have hLWr : (L : ℝ) ≤ 2 * W * e := by exact_mod_cast hLW
  have hWr : (W : ℝ) ≤ #(changes α L) := by exact_mod_cast h2
  have hepos : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hWpos' : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have key : 4 * (1 / (16 * (e : ℝ))) * L = L / (4 * e) := by field_simp; ring
  rw [key] at h1
  have : (W : ℝ) ≤ L / (4 * e) := hWr.trans h1
  rw [le_div_iff₀ (by positivity)] at this
  nlinarith

/-- Vacuity: `α = 1/3`, `e = 2`, `L = 2` satisfy the hypotheses of `lemma3`. -/
theorem lemma3_instance : (¬ ∃ z : ℤ, (1 / 3 : ℝ) = z) ∧
    (∃ z : ℤ, ((2 : ℝ) ^ 2 - 1) * (1 / 3) = z) := by
  refine ⟨?_, ⟨1, by norm_num⟩⟩
  rintro ⟨z, hz⟩
  have h0 : (0 : ℝ) < z := by linarith
  have h1 : (z : ℝ) < 1 := by linarith
  have h0' : 0 < z := by exact_mod_cast h0
  have h1' : z < 1 := by exact_mod_cast h1
  omega

end LeanLab.Linnik.Gallagher1975Lemma1

