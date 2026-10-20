module

public import GoldbachLean.Wu2008.Sieve
public import GoldbachLean.Wu2008.Int

/-!
T1, unit U-1124, PC run 20261020T0003Z-10609. P0043 J. Wu, Acta Arith. 131, 2008, arXiv 0709.3764,
Lemma 2.2, inequality (2.2), in Wu's SUMMED form, with Υ₁₁ repaired to p₄ < N^{1/2−3κ₁}, F-0050:

  3Υ₁ + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁ ≤ 4 D₁₂ + 4 E,

for any finite set A of integers 0 < a < N coprime to N, as Wu's A = {N − p} is apart from p | N,
and any κ₁, κ₂ under Wu's hypotheses, `WuReal.Admissible`. The Υ are Wu's sieve sums as read on
ar5iv 0709.3764 on 2026-10-20, with S(A_d; P(D), y) = #{a ∈ A : d | a, no prime q < y with q ∤ D
divides a}, the lab's `WuSieve.S`, and the intended sieve sets: Υ₉ at P(Np₁p₂), Υ₁₀ and Υ₁₁ at P(Np₁);
Wu prints P(Np₁) and P(N), under which those sums vanish, see STATEMENTS.md U-5411.
D₁₂ = #{a ∈ A : Ω(a) ≤ 2}. E = #{a ∈ A : a sifted at N^κ₁, a not squarefree} is Wu's O(N^{1−κ₁}).
Wu's P(z) uses p ≤ z; we read p < z as the lab does for Lemma 2.1, a cosmetic boundary.
Proof: swap each sum with the sum over a, then for each a either a is not sifted at N^κ₁, when
every positive term is 0, or it is, when each inner count is the integer term of
Wu2008Lemma22Int.lean and `pointwise_omega` applies.
KNOWN mathematics, Wu's lemma with its range fixed. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuSum
open Finset
open scoped ArithmeticFunction.Omega
open GoldbachLean.Wu2008.WuSieve (Sifted S PS mem_PS S_eq_sum sifted_mono)
open GoldbachLean.Wu2008.WuInt
open GoldbachLean.Wu2008.WuReal (e13 em Admissible)

@[expose] public noncomputable section
open scoped Classical

/-! ## Index sets and Wu's sums -/

/-- Pairs of primes below `N`, both coprime to `N`, with condition `C`. -/
def P2 (N : ℕ) (C : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧ C q.1 q.2}

/-- Quadruples of primes below `N`, all coprime to `N`, with condition `C`. -/
def P4 (N : ℕ) (C : ℕ → ℕ → ℕ → ℕ → Prop) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N | q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
    q.2.2.2.Prime ∧ q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
    C q.1 q.2.1 q.2.2.1 q.2.2.2}

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)

local notation "Ny" => fun (κ : ℝ) => (N : ℝ) ^ κ

def Y1 : ℕ := S A 1 N ((N : ℝ) ^ k1)
def Y2 : ℕ := S A 1 N ((N : ℝ) ^ k2)
def Y3 : ℕ := ∑ p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ e13), S A p N ((N : ℝ) ^ k1)
def Y4 : ℕ := ∑ p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ em k1), S A p N ((N : ℝ) ^ k1)
def C5 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ (p₂ : ℝ) < (N : ℝ) ^ k2
def Y5 : ℕ := ∑ q ∈ P2 N (C5 N k1 k2), S A (q.1 * q.2) N ((N : ℝ) ^ k1)
def C6 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ k2 ∧
  (N : ℝ) ^ k2 ≤ p₂ ∧ (p₂ : ℝ) < (N : ℝ) ^ em k1
def Y6 : ℕ := ∑ q ∈ P2 N (C6 N k1 k2), S A (q.1 * q.2) N ((N : ℝ) ^ k1)
def C7 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ em k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₁ * p₂ ^ 2 < N
def Y7 : ℕ := ∑ q ∈ P2 N (C7 N k1), S A (q.1 * q.2) (N * q.1) q.2
def C8 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ e13 ∧
  (N : ℝ) ^ e13 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
def Y8 : ℕ := ∑ q ∈ P2 N (C8 N k1), S A (q.1 * q.2) (N * q.1) q.2
def C9 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k2 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ em k1 ∧
  (N : ℝ) ^ em k1 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
/-- Υ₉ with the intended P(Np₁p₂) at level (N/p₁p₂)^{1/2}. -/
def Y9 : ℕ := ∑ q ∈ P2 N (C9 N k1 k2),
  S A (q.1 * q.2) (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2)))
def C10 (p₁ p₂ p₃ p₄ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧
  (p₄ : ℝ) < (N : ℝ) ^ k2
def Y10 : ℕ := ∑ q ∈ P4 N (C10 N k1 k2),
  S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1
/-- Υ₁₁ with the repaired range `N^κ₂ ≤ p₄ < N^{1/2−3κ₁}`; Wu prints `p₄ < N^{1/2−2κ₁}/p₃`. -/
def C11 (p₁ p₂ p₃ p₄ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
  (p₃ : ℝ) < (N : ℝ) ^ k2 ∧ (N : ℝ) ^ k2 ≤ p₄ ∧ (p₄ : ℝ) < (N : ℝ) ^ em k1
def Y11 : ℕ := ∑ q ∈ P4 N (C11 N k1 k2),
  S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1

def D12 : ℕ := #{a ∈ A | Ω a ≤ 2}
def Esq : ℕ := #{a ∈ A | Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a}

/-! ## Pointwise bridges -/

section bridges
variable {N} {a : ℕ} (ha0 : 0 < a) (haN : a < N) (hcop : a.Coprime N)
include ha0 haN hcop

lemma mem_pf {p : ℕ} : p ∈ a.primeFactors ↔ p.Prime ∧ p ∣ a := by
  rw [Nat.mem_primeFactors]; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ha0.ne'⟩⟩

lemma pf_lt {p : ℕ} (hp : p ∈ a.primeFactors) : p < N :=
  lt_of_le_of_lt (Nat.le_of_dvd ha0 (Nat.dvd_of_mem_primeFactors hp)) haN

lemma pf_cop {p : ℕ} (hp : p ∈ a.primeFactors) : p.Coprime N :=
  Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hcop

lemma prime_dvd_not_dvd_N {q : ℕ} (hq : q.Prime) (hqa : q ∣ a) : ¬ q ∣ N := fun h =>
  hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hqa h)

/-- Sifted by `P(N)` at `y` means every prime factor is at least `y`. -/
lemma sifted_iff (y : ℝ) : Sifted N y a ↔ ∀ p ∈ a.primeFactors, y ≤ (p : ℝ) := by
  constructor
  · intro h p hp
    obtain ⟨hpr, hpa⟩ := (mem_pf ha0 haN hcop).1 hp
    by_contra hlt
    exact h p hpr (not_le.1 hlt) (prime_dvd_not_dvd_N ha0 haN hcop hpr hpa) hpa
  · intro h q hq hqy _ hqa
    exact absurd (h q ((mem_pf ha0 haN hcop).2 ⟨hq, hqa⟩)) (not_le.2 hqy)

/-- Sifted by `P(Np₁)` at `p₂` is `lowP`. -/
lemma sifted_lowP {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) :
    Sifted (N * p₁) p₂ a ↔ lowP a p₁ p₂ := by
  constructor
  · intro h q hq
    obtain ⟨hqp, hqa⟩ := (mem_pf ha0 haN hcop).1 hq
    by_contra hc
    push_neg at hc
    refine h q hqp (by exact_mod_cast hc.1) ?_ hqa
    intro hd
    rcases (Nat.Prime.dvd_mul hqp).1 hd with hd | hd
    · exact prime_dvd_not_dvd_N ha0 haN hcop hqp hqa hd
    · exact hc.2 ((Nat.prime_dvd_prime_iff_eq hqp hp₁).1 hd)
  · intro h q hq hqy hqD hqa
    rcases h q ((mem_pf ha0 haN hcop).2 ⟨hq, hqa⟩) with h1 | h1
    · exact absurd hqy (not_lt.2 (by exact_mod_cast h1))
    · exact hqD (h1 ▸ dvd_mul_left _ _)

/-- Sifted by `P(Np₁p₂)` at `(N/p₁p₂)^{1/2}` is Υ₉'s condition. -/
lemma sifted_nine {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    Sifted (N * p₁ * p₂) (Real.sqrt ((N : ℝ) / (p₁ * p₂))) a ↔
      ∀ q ∈ a.primeFactors, N ≤ p₁ * p₂ * q ^ 2 ∨ q = p₁ ∨ q = p₂ := by
  have hpos : (0 : ℝ) < (p₁ : ℝ) * p₂ := by
    have := hp₁.pos; have := hp₂.pos; positivity
  have key : ∀ q : ℕ, (q : ℝ) < Real.sqrt ((N : ℝ) / (p₁ * p₂)) ↔ p₁ * p₂ * q ^ 2 < N := by
    intro q
    rw [Real.lt_sqrt (by positivity), lt_div_iff₀ hpos, ← Nat.cast_lt (α := ℝ)]
    push_cast; constructor <;> intro h <;> linarith
  have hdvd : ∀ q : ℕ, q.Prime → q ∣ a → (q ∣ N * p₁ * p₂ ↔ q = p₁ ∨ q = p₂) := by
    intro q hq hqa
    constructor
    · intro hd
      rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
        · exact absurd hd (prime_dvd_not_dvd_N ha0 haN hcop hq hqa)
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp₁).1 hd)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp₂).1 hd)
    · rintro (rfl | rfl)
      · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      · exact dvd_mul_left _ _
  constructor
  · intro h q hq
    obtain ⟨hqp, hqa⟩ := (mem_pf ha0 haN hcop).1 hq
    by_contra hc
    push_neg at hc
    exact h q hqp ((key q).2 hc.1) (fun hd => by
      rcases (hdvd q hqp hqa).1 hd with h1 | h1
      · exact hc.2.1 h1
      · exact hc.2.2 h1) hqa
  · intro h q hq hqy hqD hqa
    rcases h q ((mem_pf ha0 haN hcop).2 ⟨hq, hqa⟩) with h1 | h1
    · exact absurd ((key q).1 hqy) (not_lt.2 h1)
    · exact hqD ((hdvd q hq hqa).2 h1)

/-- Generic pair bridge. -/
lemma pair_bridge (C : ℕ → ℕ → Prop) (T : ℕ → ℕ → Prop) (C' : ℕ × ℕ → Prop)
    (hdist : ∀ p₁ p₂, p₁.Prime → p₂.Prime → C p₁ p₂ → p₁ ≠ p₂)
    (hiff : ∀ p₁ ∈ a.primeFactors, ∀ p₂ ∈ a.primeFactors, (C p₁ p₂ ∧ T p₁ p₂ ↔ C' (p₁, p₂))) :
    #{q ∈ P2 N C | q.1 * q.2 ∣ a ∧ T q.1 q.2} = #{q ∈ a.primeFactors ×ˢ a.primeFactors | C' q} := by
  congr 1
  ext ⟨p₁, p₂⟩
  simp only [P2, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨⟨-, -⟩, h1, h2, -, -, hC⟩, hd, hT⟩
    have m1 := (mem_pf ha0 haN hcop).2 ⟨h1, dvd_trans (dvd_mul_right _ _) hd⟩
    have m2 := (mem_pf ha0 haN hcop).2 ⟨h2, dvd_trans (dvd_mul_left _ _) hd⟩
    exact ⟨⟨m1, m2⟩, (hiff p₁ m1 p₂ m2).1 ⟨hC, hT⟩⟩
  · rintro ⟨⟨m1, m2⟩, hC'⟩
    obtain ⟨hC, hT⟩ := (hiff p₁ m1 p₂ m2).2 hC'
    obtain ⟨h1, d1⟩ := (mem_pf ha0 haN hcop).1 m1
    obtain ⟨h2, d2⟩ := (mem_pf ha0 haN hcop).1 m2
    refine ⟨⟨⟨pf_lt ha0 haN hcop m1, pf_lt ha0 haN hcop m2⟩, h1, h2, pf_cop ha0 haN hcop m1,
      pf_cop ha0 haN hcop m2, hC⟩, ?_, hT⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes h1 h2).2 (hdist p₁ p₂ h1 h2 hC)) d1 d2

/-- Generic quadruple bridge, for increasing primes. -/
lemma quad_bridge (C : ℕ → ℕ → ℕ → ℕ → Prop) (T : ℕ → ℕ → Prop) (C' : ℕ × ℕ × ℕ × ℕ → Prop)
    (hinc : ∀ p₁ p₂ p₃ p₄, C p₁ p₂ p₃ p₄ → p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄)
    (hiff : ∀ p₁ ∈ a.primeFactors, ∀ p₂ ∈ a.primeFactors, ∀ p₃ ∈ a.primeFactors,
      ∀ p₄ ∈ a.primeFactors, (C p₁ p₂ p₃ p₄ ∧ T p₁ p₂ ↔ C' (p₁, p₂, p₃, p₄))) :
    #{q ∈ P4 N C | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧ T q.1 q.2.1} =
      #{q ∈ a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors | C' q} := by
  congr 1
  ext ⟨p₁, p₂, p₃, p₄⟩
  simp only [P4, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨-, h1, h2, h3, h4, -, -, -, -, hC⟩, hd, hT⟩
    have m1 := (mem_pf ha0 haN hcop).2 ⟨h1, dvd_trans (Dvd.intro (p₂ * p₃ * p₄) (by ring)) hd⟩
    have m2 := (mem_pf ha0 haN hcop).2 ⟨h2, dvd_trans (Dvd.intro (p₁ * p₃ * p₄) (by ring)) hd⟩
    have m3 := (mem_pf ha0 haN hcop).2 ⟨h3, dvd_trans (Dvd.intro (p₁ * p₂ * p₄) (by ring)) hd⟩
    have m4 := (mem_pf ha0 haN hcop).2 ⟨h4, dvd_trans (dvd_mul_left _ _) hd⟩
    exact ⟨⟨m1, m2, m3, m4⟩, (hiff p₁ m1 p₂ m2 p₃ m3 p₄ m4).1 ⟨hC, hT⟩⟩
  · rintro ⟨⟨m1, m2, m3, m4⟩, hC'⟩
    obtain ⟨hC, hT⟩ := (hiff p₁ m1 p₂ m2 p₃ m3 p₄ m4).2 hC'
    obtain ⟨h1, d1⟩ := (mem_pf ha0 haN hcop).1 m1
    obtain ⟨h2, d2⟩ := (mem_pf ha0 haN hcop).1 m2
    obtain ⟨h3, d3⟩ := (mem_pf ha0 haN hcop).1 m3
    obtain ⟨h4, d4⟩ := (mem_pf ha0 haN hcop).1 m4
    obtain ⟨i12, i23, i34⟩ := hinc _ _ _ _ hC
    have c : ∀ {x y : ℕ}, x.Prime → y.Prime → x < y → x.Coprime y :=
      fun hx hy hxy => (Nat.coprime_primes hx hy).2 hxy.ne
    refine ⟨⟨⟨pf_lt ha0 haN hcop m1, pf_lt ha0 haN hcop m2, pf_lt ha0 haN hcop m3,
      pf_lt ha0 haN hcop m4⟩, h1, h2, h3, h4, pf_cop ha0 haN hcop m1, pf_cop ha0 haN hcop m2,
      pf_cop ha0 haN hcop m3, pf_cop ha0 haN hcop m4, hC⟩, ?_, hT⟩
    have d12 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (c h1 h2 i12) d1 d2
    have d123 := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.mul_left (c h1 h3 (i12.trans i23)) (c h2 h3 i23)) d12 d3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.mul_left (Nat.Coprime.mul_left (c h1 h4 (i12.trans (i23.trans i34)))
        (c h2 h4 (i23.trans i34))) (c h3 h4 i34)) d123 d4

/-- Generic single-prime bridge. -/
lemma single_bridge (w z : ℝ) (hk : ∀ p ∈ a.primeFactors, w ≤ (p : ℝ)) (hs : Sifted N w a) :
    #{p ∈ PS N w z | p ∣ a ∧ Sifted N w a} = #(a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)) := by
  refine congrArg Finset.card ?_
  ext p
  simp only [mem_filter, mem_PS]
  constructor
  · rintro ⟨⟨hp, -, hz, -⟩, hd, -⟩
    exact ⟨(mem_pf ha0 haN hcop).2 ⟨hp, hd⟩, hz⟩
  · rintro ⟨m, hz⟩
    obtain ⟨hp, hd⟩ := (mem_pf ha0 haN hcop).1 m
    exact ⟨⟨hp, hk p m, hz, pf_cop ha0 haN hcop m⟩, hd, hs⟩

end bridges

/-! ## Swapping the sums -/

lemma swap1 {ι : Type*} (I : Finset ι) (e M : ι → ℕ) (y : ι → ℝ) :
    ∑ i ∈ I, S A (e i) (M i) (y i) = ∑ a ∈ A, #{i ∈ I | e i ∣ a ∧ Sifted (M i) (y i) a} := by
  simp only [S_eq_sum]
  rw [sum_comm]
  simp only [card_filter]

/-! ## The summed lemma -/

lemma D12_eq : (D12 A : ℤ) = ∑ a ∈ A, if Ω a ≤ 2 then (1 : ℤ) else 0 := by
  unfold D12; rw [card_filter]; push_cast; rfl

lemma Esq_eq : (Esq A N k1 : ℤ) =
    ∑ a ∈ A, if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0 := by
  unfold Esq; rw [card_filter]; push_cast; rfl

/-- The per-`a` inequality behind (2.2). -/
theorem per_a (hA : Admissible k1 k2) (hN : 1 < N) {a : ℕ} (ha0 : 0 < a) (haN : a < N)
    (hcop : a.Coprime N) :
    3 * (if 1 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a then (1 : ℤ) else 0)
      + (if 1 ∣ a ∧ Sifted N ((N : ℝ) ^ k2) a then (1 : ℤ) else 0)
      + #{q ∈ P2 N (C5 N k1 k2) | q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      + #{q ∈ P2 N (C6 N k1 k2) | q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      - #{p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ e13) | p ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      - #{p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ em k1) | p ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      - 2 * #{q ∈ P2 N (C7 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a}
      - #{q ∈ P2 N (C8 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a}
      - #{q ∈ P2 N (C9 N k1 k2) | q.1 * q.2 ∣ a ∧
          Sifted (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2))) a}
      - #{q ∈ P4 N (C10 N k1 k2) | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧
          Sifted (N * q.1) (q.2.1 : ℝ) a}
      - #{q ∈ P4 N (C11 N k1 k2) | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧
          Sifted (N * q.1) (q.2.1 : ℝ) a}
      ≤ 4 * (if Ω a ≤ 2 then (1 : ℤ) else 0)
        + 4 * (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) := by
  have hk12 : (N : ℝ) ^ k1 ≤ (N : ℝ) ^ k2 :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hA.2.1.le
  have n7 := Int.natCast_nonneg (#{q ∈ P2 N (C7 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a})
  have n8 := Int.natCast_nonneg (#{q ∈ P2 N (C8 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a})
  have n9 := Int.natCast_nonneg (#{q ∈ P2 N (C9 N k1 k2) | q.1 * q.2 ∣ a ∧
          Sifted (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2))) a})
  have n10 := Int.natCast_nonneg (#{q ∈ P4 N (C10 N k1 k2) | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧
          Sifted (N * q.1) (q.2.1 : ℝ) a})
  have n11 := Int.natCast_nonneg (#{q ∈ P4 N (C11 N k1 k2) | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧
          Sifted (N * q.1) (q.2.1 : ℝ) a})
  have hr : (0 : ℤ) ≤ 4 * (if Ω a ≤ 2 then (1 : ℤ) else 0)
      + 4 * (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) := by
    split_ifs <;> norm_num
  by_cases hs : Sifted N ((N : ℝ) ^ k1) a
  swap
  · -- not sifted at N^κ₁: every positive term vanishes
    have hs2 : ¬ Sifted N ((N : ℝ) ^ k2) a := fun h => hs (sifted_mono hk12 h)
    simp only [hs, hs2, and_false, filter_false, card_empty, if_false, false_and, Nat.cast_zero]
    have : (0 : ℤ) ≤ (if Ω a ≤ 2 then 1 else 0) := by split_ifs <;> norm_num
    linarith
  have hk := (sifted_iff ha0 haN hcop _).1 hs
  have hs2 : (if 1 ∣ a ∧ Sifted N ((N : ℝ) ^ k2) a then (1 : ℤ) else 0) = I2 N a k1 k2 := by
    unfold I2
    simp only [one_dvd, true_and, sifted_iff ha0 haN hcop]
  have e3 : #{p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ e13) | p ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      = I3 N a k1 k2 := by
    unfold I3; exact_mod_cast single_bridge ha0 haN hcop _ _ hk hs
  have e4 : #{p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ em k1) | p ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      = I4 N a k1 k2 := by
    unfold I4; exact_mod_cast single_bridge ha0 haN hcop _ _ hk hs
  have cl : ∀ {x y : ℕ} {t : ℝ}, (x : ℝ) < t → t ≤ (y : ℝ) → x ≠ y := by
    intro x y t h1 h2 h; subst h; linarith
  have e5 : #{q ∈ P2 N (C5 N k1 k2) | q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      = I5 N a k1 k2 := by
    unfold I5
    convert congrArg (Nat.cast : ℕ → ℤ) (pair_bridge ha0 haN hcop (C5 N k1 k2) (fun _ _ => Sifted N ((N : ℝ) ^ k1) a)
      (fun t => t.1 < t.2 ∧ (t.2 : ℝ) < (N : ℝ) ^ k2)
      (fun _ _ _ _ h => h.2.1.ne)
      (fun p₁ m₁ p₂ _ => ⟨fun h => ⟨h.1.2.1, h.1.2.2⟩, fun h => ⟨⟨hk p₁ m₁, h.1, h.2⟩, hs⟩⟩)) using 2
    congr 1
    ext x; simp only [mem_filter]
  have e6 : #{q ∈ P2 N (C6 N k1 k2) | q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}
      = I6 N a k1 k2 := by
    unfold I6
    convert congrArg (Nat.cast : ℕ → ℤ) (pair_bridge ha0 haN hcop (C6 N k1 k2) (fun _ _ => Sifted N ((N : ℝ) ^ k1) a)
      (fun t => (N : ℝ) ^ k1 ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (N : ℝ) ^ k2 ∧
        (N : ℝ) ^ k2 ≤ (t.2 : ℝ) ∧ (t.2 : ℝ) < (N : ℝ) ^ em k1)
      (fun _ _ _ _ h => cl h.2.1 h.2.2.1)
      (fun _ _ _ _ => ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩)) using 2
    congr 1
    ext x; simp only [mem_filter]
  have e7 : #{q ∈ P2 N (C7 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a}
      = I7 N a k1 k2 := by
    unfold I7
    convert congrArg (Nat.cast : ℕ → ℤ) (pair_bridge ha0 haN hcop (C7 N k1) (fun p₁ p₂ => Sifted (N * p₁) (p₂ : ℝ) a)
      (fun t => t.1 < t.2 ∧ (N : ℝ) ^ em k1 ≤ (t.1 : ℝ) ∧ t.1 * t.2 ^ 2 < N ∧ lowP a t.1 t.2)
      (fun _ _ _ _ h => h.2.1.ne)
      (fun p₁ m₁ p₂ _ => by
        rw [sifted_lowP ha0 haN hcop (Nat.prime_of_mem_primeFactors m₁)]
        unfold C7; tauto)) using 2
    congr 1
    ext x; simp only [mem_filter]
  have e8 : #{q ∈ P2 N (C8 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a}
      = I8 N a k1 k2 := by
    unfold I8
    convert congrArg (Nat.cast : ℕ → ℤ) (pair_bridge ha0 haN hcop (C8 N k1) (fun p₁ p₂ => Sifted (N * p₁) (p₂ : ℝ) a)
      (fun t => (t.1 : ℝ) < (N : ℝ) ^ e13 ∧ (N : ℝ) ^ e13 ≤ (t.2 : ℝ) ∧ t.1 * t.2 ^ 2 < N ∧
        lowP a t.1 t.2)
      (fun _ _ _ _ h => cl h.2.1 h.2.2.1)
      (fun p₁ m₁ p₂ _ => by
        rw [sifted_lowP ha0 haN hcop (Nat.prime_of_mem_primeFactors m₁)]
        unfold C8; have := hk p₁ m₁; tauto)) using 2
    congr 1
    ext x; simp only [mem_filter]
  have e9 : #{q ∈ P2 N (C9 N k1 k2) | q.1 * q.2 ∣ a ∧
          Sifted (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2))) a} = I9 N a k1 k2 := by
    unfold I9
    convert congrArg (Nat.cast : ℕ → ℤ) (pair_bridge ha0 haN hcop (C9 N k1 k2)
      (fun p₁ p₂ => Sifted (N * p₁ * p₂) (Real.sqrt ((N : ℝ) / (p₁ * p₂))) a)
      (fun t => (N : ℝ) ^ k2 ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (N : ℝ) ^ em k1 ∧
        (N : ℝ) ^ em k1 ≤ (t.2 : ℝ) ∧ t.1 * t.2 ^ 2 < N ∧
        ∀ q ∈ a.primeFactors, N ≤ t.1 * t.2 * q ^ 2 ∨ q = t.1 ∨ q = t.2)
      (fun _ _ _ _ h => cl h.2.1 h.2.2.1)
      (fun p₁ m₁ p₂ m₂ => by
        rw [sifted_nine ha0 haN hcop (Nat.prime_of_mem_primeFactors m₁)
          (Nat.prime_of_mem_primeFactors m₂)]
        unfold C9; tauto)) using 2
    congr 1
    ext x; simp only [mem_filter]
  have e10 : #{q ∈ P4 N (C10 N k1 k2) | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧
          Sifted (N * q.1) (q.2.1 : ℝ) a} = I10 N a k1 k2 := by
    unfold I10
    convert congrArg (Nat.cast : ℕ → ℤ) (quad_bridge ha0 haN hcop (C10 N k1 k2)
      (fun p₁ p₂ => Sifted (N * p₁) (p₂ : ℝ) a)
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2 ∧
        (t.2.2.2 : ℝ) < (N : ℝ) ^ k2 ∧ lowP a t.1 t.2.1)
      (fun _ _ _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)
      (fun p₁ m₁ p₂ _ p₃ _ p₄ _ => by
        rw [sifted_lowP ha0 haN hcop (Nat.prime_of_mem_primeFactors m₁)]
        unfold C10; have := hk p₁ m₁; tauto)) using 2
    congr 1
    ext x; simp only [mem_filter]
  have e11 : #{q ∈ P4 N (C11 N k1 k2) | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧
          Sifted (N * q.1) (q.2.1 : ℝ) a} = I11 N a k1 k2 := by
    unfold I11
    convert congrArg (Nat.cast : ℕ → ℤ) (quad_bridge ha0 haN hcop (C11 N k1 k2)
      (fun p₁ p₂ => Sifted (N * p₁) (p₂ : ℝ) a)
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ (t.2.2.1 : ℝ) < (N : ℝ) ^ k2 ∧
        (N : ℝ) ^ k2 ≤ (t.2.2.2 : ℝ) ∧ (t.2.2.2 : ℝ) < (N : ℝ) ^ em k1 ∧ lowP a t.1 t.2.1)
      (fun _ _ _ _ h => ⟨h.2.1, h.2.2.1, lt_of_le_of_ne (by
        have h1 := h.2.2.2.1; have h2 := h.2.2.2.2.1
        exact_mod_cast (lt_of_lt_of_le h1 h2).le) (cl h.2.2.2.1 h.2.2.2.2.1)⟩)
      (fun p₁ m₁ p₂ _ p₃ _ p₄ _ => by
        rw [sifted_lowP ha0 haN hcop (Nat.prime_of_mem_primeFactors m₁)]
        unfold C11; have := hk p₁ m₁; tauto)) using 2
    congr 1
    ext x; simp only [mem_filter]
  rw [if_pos ⟨one_dvd a, hs⟩, hs2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  have key := pointwise_omega a k1 k2 hA hN ha0 haN hk
  unfold rhsI at key
  have hw : (if #a.primeFactors ≤ 2 then (4 : ℤ) else 0) ≤ 4 * (if Ω a ≤ 2 then (1 : ℤ) else 0)
      + 4 * (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) := by
    by_cases hsq : Squarefree a
    · rw [show (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) = 0 from
        if_neg (fun h => h.2 hsq), cardFactors_of_squarefree hsq ha0.ne']
      split_ifs <;> norm_num
    · rw [show (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) = 1 from
        if_pos ⟨hs, hsq⟩]
      split_ifs <;> norm_num
  linarith

/-- **Wu 2008 Lemma 2.2, (2.2), summed, Υ₁₁ repaired.** -/
theorem lemma22_sum (hA : Admissible k1 k2) (hN : 1 < N)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 : ℤ) - Y3 A N k1 - Y4 A N k1
      - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2
      ≤ 4 * D12 A + 4 * Esq A N k1 := by
  rw [D12_eq, Esq_eq]
  unfold Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11
  rw [swap1 A (PS N _ _) (fun p => p) (fun _ => N) (fun _ => _),
    swap1 A (PS N _ (_ ^ em k1)) (fun p => p) (fun _ => N) (fun _ => _),
    swap1 A (P2 N (C5 N k1 k2)) (fun q => q.1 * q.2) (fun _ => N) (fun _ => _),
    swap1 A (P2 N (C6 N k1 k2)) (fun q => q.1 * q.2) (fun _ => N) (fun _ => _),
    swap1 A (P2 N (C7 N k1)) (fun q => q.1 * q.2) (fun q => N * q.1) (fun q => (q.2 : ℝ)),
    swap1 A (P2 N (C8 N k1)) (fun q => q.1 * q.2) (fun q => N * q.1) (fun q => (q.2 : ℝ)),
    swap1 A (P2 N (C9 N k1 k2)) (fun q => q.1 * q.2) (fun q => N * q.1 * q.2)
      (fun q => Real.sqrt ((N : ℝ) / (q.1 * q.2))),
    swap1 A (P4 N (C10 N k1 k2)) (fun q => q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (fun q => N * q.1)
      (fun q => (q.2.1 : ℝ)),
    swap1 A (P4 N (C11 N k1 k2)) (fun q => q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (fun q => N * q.1)
      (fun q => (q.2.1 : ℝ))]
  simp only [S_eq_sum]
  push_cast
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_le_sum fun a ha => ?_
  obtain ⟨ha0, haN, hcop⟩ := hAN a ha
  exact per_a N k1 k2 hA hN ha0 haN hcop

/-- Wu's constants κ₁ = 1/13.27, κ₂ = 1/8.24. -/
theorem lemma22_sum_wu (hN : 1 < N) (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (3 * Y1 A N WuReal.wk1 + Y2 A N WuReal.wk2 + Y5 A N WuReal.wk1 WuReal.wk2
      + Y6 A N WuReal.wk1 WuReal.wk2 : ℤ) - Y3 A N WuReal.wk1 - Y4 A N WuReal.wk1
      - 2 * Y7 A N WuReal.wk1 - Y8 A N WuReal.wk1 - Y9 A N WuReal.wk1 WuReal.wk2
      - Y10 A N WuReal.wk1 WuReal.wk2 - Y11 A N WuReal.wk1 WuReal.wk2
      ≤ 4 * D12 A + 4 * Esq A N WuReal.wk1 :=
  lemma22_sum A N _ _ WuReal.wu_admissible hN hAN

/-- Vacuity: the hypotheses hold for `A = {1, 3}`, `N = 4`, Wu's constants. -/
theorem vacuity_sum : Admissible WuReal.wk1 WuReal.wk2 ∧ 1 < 4 ∧
    ∀ a ∈ ({1, 3} : Finset ℕ), 0 < a ∧ a < 4 ∧ a.Coprime 4 :=
  ⟨WuReal.wu_admissible, by norm_num, by decide⟩

end

end GoldbachLean.Wu2008.WuSum

