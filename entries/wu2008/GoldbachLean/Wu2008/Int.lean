module

public import GoldbachLean.Wu2008.Real

/-!
T1, unit U-1123, PC run 20261020T0003Z-10609. P0043 J. Wu, Chen's double sieve, Goldbach's
conjecture and the twin prime problem, 2, Acta Arith. 131, 2008, arXiv 0709.3764, Lemma 2.2, p. 371
of the journal version, with Υ₁₁ repaired to p₄ < N^{1/2−3κ₁} per F-0050, now for INTEGERS.

For an integer N > 1 and a squarefree integer 0 < a < N with every prime factor at least N^κ₁, the
terms Υ₂ to Υ₁₁ of Lemma 2.2 are written below as counts over the prime factors of a, with the
conditions exactly as products of primes against powers of N, and with the intended sieve sets:
"sifted by P(Np₁) at level p₂" for p₁ p₂ | a is `lowP`, every prime factor of a below p₂ is p₁;
Υ₉'s "every prime factor below (N/p₁p₂)^{1/2} is p₁ or p₂" is `N ≤ p₁ p₂ q²` or q = p₁ or q = p₂.
Any κ₁, κ₂ under Wu's hypotheses of Lemma 2.2, κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2, 3κ₁ − κ₂ ≤ 1/6,
as read on ar5iv 0709.3764 on 2026-10-20; Wu's own κ₁ = 1/13.27, κ₂ = 1/8.24 is `pointwise_wu`.
Υ₁ = 1 since a is sifted at N^κ₁.

Plain math twin, `pointwise_int`: 4·[Ω(a) ≤ 2] ≥ 3 + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁.
Proof: send each prime p | a to its real exponent log p / log N; this is strictly increasing and
turns every product condition into a linear one, so each count equals the count of
Wu2008Lemma22Real.lean, where the inequality is proved. Coprimality of a to N is not needed in
this pointwise form, since only prime factors of a are counted.
What this does not cover: a not squarefree, Wu's O(N^{1−κ₁}) term, and the summation over
A = {N − p}, which is linear once the inequality holds for each a.
KNOWN mathematics, Wu's lemma with its range fixed. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuInt
open Finset Real
open scoped ArithmeticFunction.Omega
open GoldbachLean.Wu2008.WuReal (e13)

@[expose] public noncomputable section
open scoped Classical

/-! ## The integer terms, Wu's conditions on primes -/

variable (N : ℕ) (a : ℕ) (k1 k2 : ℝ)


/-- `p₁ = e`, `p₂ = f`: every prime factor of `a` below `f` is `e`. -/
def lowP (e f : ℕ) : Prop := ∀ q ∈ a.primeFactors, f ≤ q ∨ q = e

def I2 (k1 k2 : ℝ) : ℤ := if ∀ p ∈ a.primeFactors, (N : ℝ) ^ k2 ≤ (p : ℝ) then 1 else 0
def I3 (k1 k2 : ℝ) : ℤ := #(a.primeFactors.filter (fun p : ℕ => (p : ℝ) < (N : ℝ) ^ e13))
def I4 (k1 k2 : ℝ) : ℤ := #(a.primeFactors.filter (fun p : ℕ => (p : ℝ) < (N : ℝ) ^ WuReal.em k1))
def I5 (k1 k2 : ℝ) : ℤ := #((a.primeFactors ×ˢ a.primeFactors).filter (fun t => t.1 < t.2 ∧ (t.2 : ℝ) < (N : ℝ) ^ k2))
def I6 (k1 k2 : ℝ) : ℤ := #((a.primeFactors ×ˢ a.primeFactors).filter (fun t => (N : ℝ) ^ k1 ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (N : ℝ) ^ k2 ∧
  (N : ℝ) ^ k2 ≤ (t.2 : ℝ) ∧ (t.2 : ℝ) < (N : ℝ) ^ WuReal.em k1))
def I7 (k1 k2 : ℝ) : ℤ := #((a.primeFactors ×ˢ a.primeFactors).filter (fun t => t.1 < t.2 ∧ (N : ℝ) ^ WuReal.em k1 ≤ (t.1 : ℝ) ∧
  t.1 * t.2 ^ 2 < N ∧ lowP a t.1 t.2))
def I8 (k1 k2 : ℝ) : ℤ := #((a.primeFactors ×ˢ a.primeFactors).filter (fun t => (t.1 : ℝ) < (N : ℝ) ^ e13 ∧ (N : ℝ) ^ e13 ≤ (t.2 : ℝ) ∧
  t.1 * t.2 ^ 2 < N ∧ lowP a t.1 t.2))
def I9 (k1 k2 : ℝ) : ℤ := #((a.primeFactors ×ˢ a.primeFactors).filter (fun t => (N : ℝ) ^ k2 ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (N : ℝ) ^ WuReal.em k1 ∧
  (N : ℝ) ^ WuReal.em k1 ≤ (t.2 : ℝ) ∧ t.1 * t.2 ^ 2 < N ∧
  ∀ q ∈ a.primeFactors, N ≤ t.1 * t.2 * q ^ 2 ∨ q = t.1 ∨ q = t.2))
def I10 (k1 k2 : ℝ) : ℤ := #((a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧
  t.2.2.1 < t.2.2.2 ∧ (t.2.2.2 : ℝ) < (N : ℝ) ^ k2 ∧ lowP a t.1 t.2.1))
/-- Υ₁₁ with the repaired range `p₄ < N^{1/2−3κ₁}`. -/
def I11 (k1 k2 : ℝ) : ℤ := #((a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧
  (t.2.2.1 : ℝ) < (N : ℝ) ^ k2 ∧ (N : ℝ) ^ k2 ≤ (t.2.2.2 : ℝ) ∧ (t.2.2.2 : ℝ) < (N : ℝ) ^ WuReal.em k1 ∧
  lowP a t.1 t.2.1))

def rhsI (k1 k2 : ℝ) : ℤ :=
  3 + I2 N a k1 k2 - I3 N a k1 k2 - I4 N a k1 k2 + I5 N a k1 k2 + I6 N a k1 k2 - 2 * I7 N a k1 k2 - I8 N a k1 k2 - I9 N a k1 k2 - I10 N a k1 k2
    - I11 N a k1 k2
def lhsI : ℤ := if Ω a ≤ 2 then 4 else 0

/-! ## Transfer lemmas -/

section transfer
variable {α β : Type*} [DecidableEq β]

lemma card_filter_image {s : Finset α} {f : α → β} (hf : Set.InjOn f s) {R : α → Prop}
    {Q : β → Prop} [DecidablePred R] [DecidablePred Q] (h : ∀ p ∈ s, R p ↔ Q (f p)) :
    #(s.filter R) = #((s.image f).filter Q) := by
  rw [filter_image, card_image_of_injOn (hf.mono (fun x hx => (mem_filter.1 hx).1))]
  congr 1
  exact filter_congr h

lemma card_filter_image2 {s : Finset α} {f : α → β} (hf : Set.InjOn f s) {R : α × α → Prop}
    {Q : β × β → Prop} [DecidablePred R] [DecidablePred Q]
    (h : ∀ p ∈ s, ∀ q ∈ s, R (p, q) ↔ Q (f p, f q)) :
    #((s ×ˢ s).filter R) = #(((s.image f) ×ˢ (s.image f)).filter Q) := by
  have e : ((s.image f) ×ˢ (s.image f)).filter Q =
      ((s ×ˢ s).filter R).image (fun t => (f t.1, f t.2)) := by
    ext ⟨u, v⟩
    simp only [mem_filter, mem_product, mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩, hQ⟩
      exact ⟨p, q, ⟨⟨hp, hq⟩, (h p hp q hq).2 hQ⟩, rfl, rfl⟩
    · rintro ⟨p, q, ⟨⟨hp, hq⟩, hR⟩, rfl, rfl⟩
      exact ⟨⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩, (h p hp q hq).1 hR⟩
  rw [e, card_image_of_injOn]
  rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' hh
  simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hpq hpq'
  simp only [Prod.mk.injEq] at hh
  exact Prod.ext (hf hpq.1.1 hpq'.1.1 hh.1) (hf hpq.1.2 hpq'.1.2 hh.2)

lemma card_filter_image4 {s : Finset α} {f : α → β} (hf : Set.InjOn f s)
    {R : α × α × α × α → Prop} {Q : β × β × β × β → Prop} [DecidablePred R] [DecidablePred Q]
    (h : ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, ∀ w ∈ s, R (p, q, r, w) ↔ Q (f p, f q, f r, f w)) :
    #((s ×ˢ s ×ˢ s ×ˢ s).filter R) =
      #(((s.image f) ×ˢ (s.image f) ×ˢ (s.image f) ×ˢ (s.image f)).filter Q) := by
  have e : ((s.image f) ×ˢ (s.image f) ×ˢ (s.image f) ×ˢ (s.image f)).filter Q =
      ((s ×ˢ s ×ˢ s ×ˢ s).filter R).image (fun t => (f t.1, f t.2.1, f t.2.2.1, f t.2.2.2)) := by
    ext ⟨u, v, x, y⟩
    simp only [mem_filter, mem_product, mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩, ⟨r, hr, rfl⟩, ⟨w, hw, rfl⟩⟩, hQ⟩
      exact ⟨p, q, r, w, ⟨⟨hp, hq, hr, hw⟩, (h p hp q hq r hr w hw).2 hQ⟩, rfl, rfl, rfl, rfl⟩
    · rintro ⟨p, q, r, w, ⟨⟨hp, hq, hr, hw⟩, hR⟩, rfl, rfl, rfl, rfl⟩
      exact ⟨⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩, ⟨r, hr, rfl⟩, ⟨w, hw, rfl⟩⟩,
        (h p hp q hq r hr w hw).1 hR⟩
  rw [e, card_image_of_injOn]
  rintro ⟨p, q, r, w⟩ hpq ⟨p', q', r', w'⟩ hpq' hh
  simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hpq hpq'
  simp only [Prod.mk.injEq] at hh
  obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hpq
  obtain ⟨⟨h1', h2', h3', h4'⟩, -⟩ := hpq'
  simp only [Prod.mk.injEq]
  exact ⟨hf h1 h1' hh.1, hf h2 h2' hh.2.1, hf h3 h3' hh.2.2.1, hf h4 h4' hh.2.2.2⟩

end transfer

/-! ## The exponent map -/

/-- The real exponent of `p` in base `N`. -/
def ex (p : ℕ) : ℝ := Real.log p / Real.log N

variable {N}

section expo
variable (hN : 1 < N)
include hN

lemma logN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)

lemma x_lt_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : ex N p < ex N q ↔ p < q := by
  unfold ex
  rw [div_lt_div_iff_of_pos_right (logN_pos hN), Real.log_lt_log_iff (by exact_mod_cast hp)
    (by exact_mod_cast hq), Nat.cast_lt]

lemma x_le_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : ex N p ≤ ex N q ↔ p ≤ q := by
  rw [← not_lt, x_lt_iff hN hq hp, not_lt]

lemma x_eq_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : ex N p = ex N q ↔ p = q := by
  rw [le_antisymm_iff, x_le_iff hN hp hq, x_le_iff hN hq hp, ← le_antisymm_iff]

lemma lt_rpow_iff {p : ℕ} (hp : 0 < p) (κ : ℝ) : (p : ℝ) < (N : ℝ) ^ κ ↔ ex N p < κ := by
  unfold ex
  rw [Real.lt_rpow_iff_log_lt (by exact_mod_cast hp) (by positivity),
    div_lt_iff₀ (logN_pos hN)]

lemma rpow_le_iff {p : ℕ} (hp : 0 < p) (κ : ℝ) : (N : ℝ) ^ κ ≤ (p : ℝ) ↔ κ ≤ ex N p := by
  rw [← not_lt, lt_rpow_iff hN hp, not_lt]

lemma mul_sq_lt_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    p * q ^ 2 < N ↔ ex N p + 2 * ex N q < 1 := by
  have hL := logN_pos hN
  have h0 : (0 : ℝ) < ((p * q ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hp (pow_pos hq 2)
  have hlog : Real.log ((p * q ^ 2 : ℕ) : ℝ) = Real.log p + 2 * Real.log q := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have he : ex N p + 2 * ex N q = (Real.log p + 2 * Real.log q) / Real.log N := by unfold ex; ring
  rw [← Nat.cast_lt (α := ℝ), ← Real.log_lt_log_iff h0 (by positivity), hlog, he, div_lt_one hL]

lemma le_mul_mul_sq_iff {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    N ≤ p * q * r ^ 2 ↔ 1 ≤ ex N p + ex N q + 2 * ex N r := by
  have hL := logN_pos hN
  have h0 : (0 : ℝ) < ((p * q * r ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hp hq) (pow_pos hr 2)
  have hlog : Real.log ((p * q * r ^ 2 : ℕ) : ℝ) = Real.log p + Real.log q + 2 * Real.log r := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast; ring
  have he : ex N p + ex N q + 2 * ex N r =
      (Real.log p + Real.log q + 2 * Real.log r) / Real.log N := by unfold ex; ring
  rw [← Nat.cast_le (α := ℝ), ← Real.log_le_log_iff (by positivity) h0, hlog, he, one_le_div hL]

lemma ex_injOn : Set.InjOn (ex N) {p : ℕ | 0 < p} := by
  intro p hp q hq h
  exact (x_eq_iff hN hp hq).1 h

end expo

/-! ## Each count equals the real-model count -/

lemma pos_of_mem {p : ℕ} (hp : p ∈ a.primeFactors) : 0 < p :=
  (Nat.prime_of_mem_primeFactors hp).pos

section counts
variable (hN : 1 < N)
include hN


lemma injP : Set.InjOn (ex N) (a.primeFactors : Set ℕ) :=
  (ex_injOn hN).mono (fun p hp => pos_of_mem a hp)

lemma lowP_iff {e f : ℕ} (he : 0 < e) (hf : 0 < f) :
    lowP a e f ↔ WuReal.low2 (a.primeFactors.image (ex N)) (ex N e) (ex N f) := by
  unfold lowP WuReal.low2
  rw [forall_mem_image]
  refine forall₂_congr (fun q hq => ?_)
  rw [x_le_iff hN hf (pos_of_mem a hq), x_eq_iff hN (pos_of_mem a hq) he]

lemma I2_eq : I2 N a k1 k2 = WuReal.U2 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I2 WuReal.U2
  congr 1
  rw [forall_mem_image]
  exact propext (forall₂_congr (fun p hp => rpow_le_iff hN (pos_of_mem a hp) _))

lemma I3_eq : I3 N a k1 k2 = WuReal.U3 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I3 WuReal.U3
  congr 1
  have := card_filter_image (injP a hN) (R := fun p : ℕ => (p : ℝ) < (N : ℝ) ^ e13)
    (Q := fun y => y < e13) (fun p hp => lt_rpow_iff hN (pos_of_mem a hp) e13)
  exact_mod_cast this

lemma I4_eq : I4 N a k1 k2 = WuReal.U4 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I4 WuReal.U4
  congr 1
  have := card_filter_image (injP a hN) (R := fun p : ℕ => (p : ℝ) < (N : ℝ) ^ WuReal.em k1)
    (Q := fun y => y < WuReal.em k1) (fun p hp => lt_rpow_iff hN (pos_of_mem a hp) (WuReal.em k1))
  exact_mod_cast this

lemma I5_eq : I5 N a k1 k2 = WuReal.U5 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I5 WuReal.U5
  congr 1
  refine card_filter_image2 (injP a hN) (fun p hp q hq => ?_)
  have hp' := pos_of_mem a hp; have hq' := pos_of_mem a hq
  rw [x_lt_iff hN hp' hq', lt_rpow_iff hN hq']

lemma I6_eq : I6 N a k1 k2 = WuReal.U6 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I6 WuReal.U6
  congr 1
  refine card_filter_image2 (injP a hN) (fun p hp q hq => ?_)
  have hp' := pos_of_mem a hp; have hq' := pos_of_mem a hq
  rw [rpow_le_iff hN hp', lt_rpow_iff hN hp', rpow_le_iff hN hq', lt_rpow_iff hN hq']

lemma I7_eq : I7 N a k1 k2 = WuReal.U7 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I7 WuReal.U7
  congr 1
  refine card_filter_image2 (injP a hN) (fun p hp q hq => ?_)
  have hp' := pos_of_mem a hp; have hq' := pos_of_mem a hq
  rw [x_lt_iff hN hp' hq', rpow_le_iff hN hp', mul_sq_lt_iff hN hp' hq', lowP_iff a hN hp' hq']

lemma I8_eq : I8 N a k1 k2 = WuReal.U8 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I8 WuReal.U8
  congr 1
  refine card_filter_image2 (injP a hN) (fun p hp q hq => ?_)
  have hp' := pos_of_mem a hp; have hq' := pos_of_mem a hq
  rw [lt_rpow_iff hN hp', rpow_le_iff hN hq', mul_sq_lt_iff hN hp' hq', lowP_iff a hN hp' hq']

lemma I9_eq : I9 N a k1 k2 = WuReal.U9 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I9 WuReal.U9
  congr 1
  refine card_filter_image2 (injP a hN) (fun p hp q hq => ?_)
  have hp' := pos_of_mem a hp; have hq' := pos_of_mem a hq
  rw [rpow_le_iff hN hp', lt_rpow_iff hN hp', rpow_le_iff hN hq', mul_sq_lt_iff hN hp' hq',
    forall_mem_image]
  refine and_congr_right' (and_congr_right' (and_congr_right' (and_congr_right'
    (forall₂_congr (fun r hr => ?_)))))
  have hr' := pos_of_mem a hr
  rw [le_mul_mul_sq_iff hN hp' hq' hr', x_eq_iff hN hr' hp', x_eq_iff hN hr' hq']

lemma I10_eq : I10 N a k1 k2 = WuReal.U10 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I10 WuReal.U10 WuReal.quads
  congr 1
  refine card_filter_image4 (injP a hN) (fun p hp q hq r hr w hw => ?_)
  have hp' := pos_of_mem a hp; have hq' := pos_of_mem a hq
  have hr' := pos_of_mem a hr; have hw' := pos_of_mem a hw
  rw [x_lt_iff hN hp' hq', x_lt_iff hN hq' hr', x_lt_iff hN hr' hw', lt_rpow_iff hN hw',
    lowP_iff a hN hp' hq']

lemma I11_eq : I11 N a k1 k2 = WuReal.U11 k1 k2 (a.primeFactors.image (ex N)) := by
  unfold I11 WuReal.U11 WuReal.quads
  congr 1
  refine card_filter_image4 (injP a hN) (fun p hp q hq r hr w hw => ?_)
  have hp' := pos_of_mem a hp; have hq' := pos_of_mem a hq
  have hr' := pos_of_mem a hr; have hw' := pos_of_mem a hw
  rw [x_lt_iff hN hp' hq', x_lt_iff hN hq' hr', lt_rpow_iff hN hr', rpow_le_iff hN hw',
    lt_rpow_iff hN hw', lowP_iff a hN hp' hq']

end counts

lemma cardFactors_of_squarefree {a : ℕ} (h : Squarefree a) (h0 : a ≠ 0) :
    Ω a = #a.primeFactors := by
  rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors,
    List.toFinset_card_of_nodup ((Nat.squarefree_iff_nodup_primeFactorsList h0).1 h)]

/-- **Wu 2008 Lemma 2.2, Υ₁₁ repaired, for one integer `a`, squarefree or not**, with
`ω(a) ≤ 2` on the left: every term depends only on the set of prime factors of `a`. -/
theorem pointwise_omega (hA : WuReal.Admissible k1 k2) (hN : 1 < N) (ha0 : 0 < a) (haN : a < N)
    (hk : ∀ p ∈ a.primeFactors, (N : ℝ) ^ k1 ≤ (p : ℝ)) :
    rhsI N a k1 k2 ≤ if #a.primeFactors ≤ 2 then 4 else 0 := by
  set d := a.primeFactors.image (ex N) with hd
  have hinj := injP a hN
  have hk' : ∀ e ∈ d, k1 ≤ e := by
    rw [hd, forall_mem_image]
    intro p hp
    exact (rpow_le_iff hN (pos_of_mem a hp) _).1 (hk p hp)
  have hs : ∑ e ∈ d, e < 1 := by
    rw [hd, sum_image hinj]
    have hL := logN_pos hN
    have hprod : ((∏ p ∈ a.primeFactors, p : ℕ) : ℝ) < N := by
      have := Nat.le_of_dvd ha0 (Nat.prod_primeFactors_dvd a)
      exact_mod_cast lt_of_le_of_lt this haN
    push_cast at hprod
    have hpos : ∀ p ∈ a.primeFactors, ((p : ℕ) : ℝ) ≠ 0 := fun p hp =>
      by exact_mod_cast (pos_of_mem a hp).ne'
    have hlog := Real.log_lt_log (prod_pos (fun p hp => by exact_mod_cast pos_of_mem a hp)) hprod
    rw [Real.log_prod hpos] at hlog
    unfold ex
    rw [← sum_div, div_lt_one hL]
    exact hlog
  have key := WuReal.pointwise k1 k2 hA d hk' hs
  have hcard : #d = #a.primeFactors := card_image_of_injOn hinj
  unfold rhsI
  unfold WuReal.rhs WuReal.lhs at key
  rw [I2_eq a k1 k2 hN, I3_eq a k1 k2 hN, I4_eq a k1 k2 hN, I5_eq a k1 k2 hN, I6_eq a k1 k2 hN, I7_eq a k1 k2 hN, I8_eq a k1 k2 hN,
    I9_eq a k1 k2 hN, I10_eq a k1 k2 hN, I11_eq a k1 k2 hN]
  rw [hcard] at key
  exact key

/-- **Wu 2008 Lemma 2.2, Υ₁₁ repaired, for one squarefree integer `a`.** -/
theorem pointwise_int (hA : WuReal.Admissible k1 k2) (hN : 1 < N) (ha : Squarefree a) (ha0 : 0 < a) (haN : a < N)
    (hk : ∀ p ∈ a.primeFactors, (N : ℝ) ^ k1 ≤ (p : ℝ)) :
    rhsI N a k1 k2 ≤ lhsI a := by
  have := pointwise_omega a k1 k2 hA hN ha0 haN hk
  unfold lhsI
  rwa [cardFactors_of_squarefree ha ha0.ne']

/-- Wu's own constants, κ₁ = 1/13.27, κ₂ = 1/8.24. -/
theorem pointwise_wu (hN : 1 < N) (ha : Squarefree a) (ha0 : 0 < a) (haN : a < N)
    (hk : ∀ p ∈ a.primeFactors, (N : ℝ) ^ WuReal.wk1 ≤ (p : ℝ)) :
    rhsI N a WuReal.wk1 WuReal.wk2 ≤ lhsI a :=
  pointwise_int a _ _ WuReal.wu_admissible hN ha ha0 haN hk

/-! ## Vacuity: the F-0050 shape as an actual integer -/

/-- `N = 2^100`, `a = 257 · 521 · 4099 · 33554467`, primes just above `2^8, 2^9, 2^12, 2^25`, the
exponents 0.08, 0.09, 0.12, 0.25 of Wu2008Lemma22Gap.lean. The hypotheses hold. -/
theorem vacuity :
    let N : ℕ := 2 ^ 100
    let a : ℕ := 257 * 521 * 4099 * 33554467
    1 < N ∧ Squarefree a ∧ 0 < a ∧ a < N ∧ ∀ p ∈ a.primeFactors, (N : ℝ) ^ WuReal.wk1 ≤ (p : ℝ) := by
  intro N a
  have p1 : Nat.Prime 257 := by norm_num
  have p2 : Nat.Prime 521 := by norm_num
  have p3 : Nat.Prime 4099 := by norm_num
  have p4 : Nat.Prime 33554467 := by norm_num
  have hfac : a.primeFactors = {257, 521, 4099, 33554467} := by
    show (257 * 521 * 4099 * 33554467).primeFactors = _
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num)
      (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), p1.primeFactors,
      p2.primeFactors, p3.primeFactors, p4.primeFactors]
    decide
  refine ⟨by norm_num [N], ?_, by norm_num [a], by norm_num [a, N], ?_⟩
  · show Squarefree (257 * 521 * 4099 * 33554467)
    rw [Nat.squarefree_mul_iff, Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
    exact ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, p1.squarefree, p2.squarefree⟩,
      p3.squarefree⟩, p4.squarefree⟩
  · have hb : (N : ℝ) ^ WuReal.wk1 ≤ 256 := by
      have e1 : ((N : ℕ) : ℝ) = (2 : ℝ) ^ ((100 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast [N]; ring
      rw [e1, ← Real.rpow_mul (by norm_num)]
      have : (2 : ℝ) ^ ((100 : ℕ) * WuReal.wk1 : ℝ) ≤ (2 : ℝ) ^ ((8 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by unfold WuReal.wk1; norm_num)
      rw [Real.rpow_natCast] at this
      linarith
    rw [hfac]
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    have h256 : (256 : ℝ) ≤ (p : ℝ) := by
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num
    exact hb.trans h256

end

end GoldbachLean.Wu2008.WuInt

