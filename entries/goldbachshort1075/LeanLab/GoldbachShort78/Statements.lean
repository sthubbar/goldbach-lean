module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Goldbach numbers in short intervals from two prime counts. The primes `p` of a window
`[x − 2Y, x − Y]` are compared with the `z ∈ [Y, 2Y]` such that `[z, z + H]` has no prime: when the
window holds more primes than there are such `z`, some `x − p` has a prime `q` within `H`, and
`p + q` lies in `[x, x + H]`.

AI wrote the Lean code, Claude. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.GoldbachShort78
open Real

/-- A Goldbach number: an even sum of two primes. -/
def IsGoldbachNumber (n : ℕ) : Prop := Even n ∧ IsGoldbachSum n

/-- The primes in `[x − 2Y, x − Y]`. -/
noncomputable def primeWindow (x Y : ℕ) : Finset ℕ :=
  (Finset.Icc (x - 2 * Y) (x - Y)).filter Nat.Prime

/-- The `z ∈ [Y, 2Y]` with no prime in `[z, z + H]`. -/
noncomputable def badSet (Y H : ℕ) : Finset ℕ :=
  (Finset.Icc Y (2 * Y)).filter (fun z => ∀ q ∈ Finset.Icc z (z + H), ¬ q.Prime)

/-- Count in all windows: for `x ≥ x₀` and `Y ≥ x^a` with `2Y + 3 ≤ x`, the window
`[x − 2Y, x − Y]` holds at least `c Y / log x` primes. -/
def WindowCount (a c x₀ : ℝ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∀ Y : ℕ, (x : ℝ) ^ a ≤ Y → 2 * Y + 3 ≤ x →
    c * Y / Real.log x ≤ (primeWindow x Y).card

/-- Count in almost all intervals: for `Y ≥ y₀` and `H ≥ Y^b`, at most `Y / log² Y` of the
`z ∈ [Y, 2Y]` have a prime free `[z, z + H]`. -/
def AlmostAllCount (b y₀ : ℝ) : Prop :=
  ∀ Y : ℕ, y₀ ≤ Y → ∀ H : ℕ, (Y : ℝ) ^ b ≤ H → ((badSet Y H).card : ℝ) ≤ Y / Real.log Y ^ 2

/-- The combinatorial step, proved with no cited input: if fewer `z ∈ [Y, 2Y]` have a prime free
`[z, z + H]` than there are primes in `[x − 2Y, x − Y]`, some `n ∈ [x, x + H]` is a Goldbach number. -/
theorem goldbach_of_counts {x Y H : ℕ} (hY : 3 ≤ Y) (hx : 2 * Y + 3 ≤ x)
    (hcount : (badSet Y H).card < (primeWindow x Y).card) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ n ≤ x + H := by
  by_contra hne
  push Not at hne
  have hmaps : ∀ p ∈ primeWindow x Y, x - p ∈ badSet Y H := by
    intro p hp
    simp only [primeWindow, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
    simp only [badSet, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro q hq hqp
    obtain ⟨hq1, hq2⟩ := hq
    have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
    have hqodd : Odd q := hqp.odd_of_ne_two (by omega)
    have hG : IsGoldbachNumber (p + q) := ⟨hpodd.add_odd hqodd, p, q, hpp, hqp, rfl⟩
    have := hne (p + q) hG (by omega)
    omega
  have hinj : Set.InjOn (fun p => x - p) (primeWindow x Y : Set ℕ) := by
    intro p hp p' hp' h
    simp only [Finset.coe_filter, Finset.mem_Icc, primeWindow, Set.mem_ofPred_eq] at hp hp'
    simp only at h
    omega
  have := Finset.card_le_card_of_injOn (fun p => x - p) hmaps hinj
  omega

/-- A Goldbach number in `[x, x + 3 x^{ab}]` from `WindowCount a c x₀` and `AlmostAllCount b y₀`,
with explicit side conditions that are true for large `x`. -/
theorem goldbach_short_b {a b c x₀ y₀ : ℝ} (ha : 0 < a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hW : WindowCount a c x₀) (hA : AlmostAllCount b y₀) {x : ℕ}
    (hx0 : x₀ ≤ x) (hxy : y₀ ≤ (x : ℝ) ^ a) (h3 : 3 ≤ (x : ℝ) ^ a)
    (hlog : 1 < c * a ^ 2 * Real.log x) (hsize : 2 * ⌈(x : ℝ) ^ a⌉₊ + 3 ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (a * b) := by
  set Y : ℕ := ⌈(x : ℝ) ^ a⌉₊ with hYdef
  set H : ℕ := ⌈(Y : ℝ) ^ b⌉₊ with hHdef
  have hxa_le : (x : ℝ) ^ a ≤ Y := Nat.le_ceil _
  have hYlt : (Y : ℝ) < (x : ℝ) ^ a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hY3 : 3 ≤ Y := by
    have : (3 : ℝ) ≤ Y := le_trans h3 hxa_le
    exact_mod_cast this
  have hYpos : (0 : ℝ) < Y := by linarith
  have hlogx : 0 < Real.log x := by
    by_contra hneg; push Not at hneg
    have : c * a ^ 2 * Real.log x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hxpos : (0 : ℝ) < x := by
    have : (x : ℝ) ≠ 0 := by intro h0; rw [h0, Real.log_zero] at hlogx; exact lt_irrefl _ hlogx
    positivity
  -- the two counts
  have hwin := hW x hx0 Y hxa_le hsize
  have hbad := hA Y (le_trans hxy hxa_le) H (Nat.le_ceil _)
  -- compare Y / log² Y < c Y / log x
  have hlogY : a * Real.log x ≤ Real.log Y := by
    rw [← Real.log_rpow hxpos]
    exact Real.log_le_log (by positivity) hxa_le
  have hal : 0 < a * Real.log x := mul_pos ha hlogx
  have hsq : (a * Real.log x) ^ 2 ≤ Real.log Y ^ 2 := pow_le_pow_left₀ hal.le hlogY 2
  have hkey : Real.log x < c * (a * Real.log x) ^ 2 := by
    have : c * (a * Real.log x) ^ 2 = (c * a ^ 2 * Real.log x) * Real.log x := by ring
    rw [this]; nlinarith
  have hlt : (Y : ℝ) / Real.log Y ^ 2 < c * Y / Real.log x := by
    have hLY : 0 < Real.log Y ^ 2 := lt_of_lt_of_le (by positivity) hsq
    rw [div_lt_div_iff₀ hLY hlogx]
    have : c * (a * Real.log x) ^ 2 ≤ c * Real.log Y ^ 2 := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith
  have hcount : (badSet Y H).card < (primeWindow x Y).card := by
    have : ((badSet Y H).card : ℝ) < (primeWindow x Y).card := by linarith
    exact_mod_cast this
  obtain ⟨n, hn, h1, h2⟩ := goldbach_of_counts hY3 hsize hcount
  refine ⟨n, hn, h1, ?_⟩
  -- H ≤ 3 x^{ab}
  have hx1 : (1 : ℝ) ≤ x := by
    by_contra hlt1; push Not at hlt1
    have : Real.log x < 0 := Real.log_neg hxpos hlt1
    linarith
  have hxab : (1 : ℝ) ≤ (x : ℝ) ^ (a * b) := Real.one_le_rpow hx1 (by positivity)
  have hH : (H : ℝ) < (Y : ℝ) ^ b + 1 := Nat.ceil_lt_add_one (by positivity)
  have hYb : (Y : ℝ) ^ b ≤ (2 * (x : ℝ) ^ a) ^ b :=
    Real.rpow_le_rpow hYpos.le (by linarith) hb0
  have h2b : (2 : ℝ) ^ b ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
    simpa using this
  have hsplit : (2 * (x : ℝ) ^ a) ^ b = (2 : ℝ) ^ b * (x : ℝ) ^ (a * b) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hxpos.le]
  have h2le : (2 * (x : ℝ) ^ a) ^ b ≤ 2 * (x : ℝ) ^ (a * b) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right h2b (by positivity)
  have : (n : ℝ) ≤ x + H := by exact_mod_cast h2
  linarith

end LeanLab.GoldbachShort78
