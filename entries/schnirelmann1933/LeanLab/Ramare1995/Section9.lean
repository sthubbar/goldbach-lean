module

public import Mathlib
public import LeanLab.SchnirelmannConstant.Defs

/-!
Ramaré 1995, On Šnirel'man's constant, Ann. Sc. Norm. Pisa 22, 645-706, P0008.
Theorem 2 with the paper's constant, Theorem 9.1 of Deshouillers, and the Section 9
deduction of the large range of Theorem 1 from them.
Read 2026-10-17 from the numdam scan, pages 646 and 701 to 704, by eye from page images,
run 20261017T0803Z-2223.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Cited results are `def ... : Prop` hypotheses here, nothing is asserted without proof.
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace LeanLab.Ramare1995.Section9
open LeanLab LeanLab.SchnirelmannConstant

/-! ### Theorem 2, page 646 -/

/-- **Theorem 2**, page 646, as intended: for real `X ≥ exp 67`, at least `X/5` even
integers `N` in `]X, 2X]` are sums of two primes. The printed display counts every
`N ∈ ]X, 2X]` with `N = p₁ + p₂`; Section 2.3 says the count is of even integers and should
be about `X/2`, and Section 9 applies it to even `N` only. CITED. -/
def Theorem2 : Prop :=
  ∀ X : ℝ, exp 67 ≤ X →
    X / 5 ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ)

/-- Theorem 2 exactly as printed, odd `N = p + 2` included. -/
def Theorem2Printed : Prop :=
  ∀ X : ℝ, exp 67 ≤ X → X / 5 ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | IsGoldbachSum N} : ℝ)

/-- The intended form implies the printed form. -/
theorem theorem2Printed_of (h : Theorem2) : Theorem2Printed := by
  intro X hX
  refine (h X hX).trans ?_
  have hs : {N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} ⊆
      {N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | IsGoldbachSum N} := by
    intro N hN
    rw [mem_filter] at hN ⊢
    exact ⟨hN.1, hN.2.2⟩
  exact_mod_cast card_le_card hs

/-- The lab's earlier weak form, `X > exp 67` with an unnamed constant, follows. -/
theorem theorem2_weak_of (h : Theorem2) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, exp 67 < X →
      c * X ≤ (#{n ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | IsGoldbachSum n} : ℝ) :=
  ⟨1 / 5, by norm_num, fun X hX => by
    have := theorem2Printed_of h X hX.le
    linarith⟩

/-! ### Theorem 9.1, page 701 -/

/-- `A(n)`, the number of elements of `A` in `[1, n]`. -/
noncomputable def cnt (A : Set ℕ) (n : ℕ) : ℕ := #{a ∈ Icc 1 n | a ∈ A}

/-- `m` is a sum of at most `H` elements of `A`. -/
def SumOfAtMost (A : Set ℕ) (H m : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ H ∧ (∀ a ∈ l, a ∈ A) ∧ l.sum = m

/-- **Theorem 9.1**, page 701, an effective form of Ostmann's theorem due to Deshouillers.
`A` contains 0; real `σ`, integers `H, K, n₀` with
(a) `A(n) ≥ σ n + K(K+1)/2 · (H − 1)` for `n ≥ n₀`,
(b) `{0, …, K} ⊆ A` and `{n₀, …, n₀ + K} ⊆ A`,
(c) `(K + 1) H σ ≥ K + H`.
Then every integer `≥ H n₀` is a sum of at most `H` elements of `A`.
The lab adds `1 ≤ H`: for `H = 0` the printed statement is false, take `A = {0}`, `K = n₀ = 0`,
`σ = 0`, and `m = 1`. The paper's proof assumes `H ≥ 1` throughout. CITED. -/
def Theorem91 : Prop :=
  ∀ (A : Set ℕ) (σ : ℝ) (H K n₀ : ℕ), 1 ≤ H → 0 ∈ A →
    (∀ n, n₀ ≤ n → σ * n + (K * (K + 1) / 2 : ℝ) * ((H : ℝ) - 1) ≤ cnt A n) →
    (∀ i ≤ K, i ∈ A) → (∀ i ≤ K, n₀ + i ∈ A) →
    ((K : ℝ) + H ≤ (K + 1) * H * σ) →
    ∀ m, H * n₀ ≤ m → SumOfAtMost A H m

/-- The printed Theorem 9.1 without `1 ≤ H` is false. -/
theorem theorem91_printed_false :
    ¬ ∀ (A : Set ℕ) (σ : ℝ) (H K n₀ : ℕ), 0 ∈ A →
      (∀ n, n₀ ≤ n → σ * n + (K * (K + 1) / 2 : ℝ) * ((H : ℝ) - 1) ≤ cnt A n) →
      (∀ i ≤ K, i ∈ A) → (∀ i ≤ K, n₀ + i ∈ A) →
      ((K : ℝ) + H ≤ (K + 1) * H * σ) →
      ∀ m, H * n₀ ≤ m → SumOfAtMost A H m := by
  intro h
  obtain ⟨l, hl, -, hs⟩ := h {0} 0 0 0 0 rfl (fun n _ => by simp) (fun i hi => by simp; omega)
    (fun i hi => by simp; omega) (by norm_num) 1 (by norm_num)
  have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this
  simp at hs

/-! ### Section 9: the sequence `𝒜` and hypothesis (a) -/

/-- Section 9: `𝒜` is the set of `(g − 6)/2` with `g` a sum of two odd primes. For even
`g ≥ 6` a sum of two primes uses odd primes only, see `oddPrimes_of`, so `a ∈ 𝒜` iff
`2a + 6` is a sum of two primes. -/
def 𝒜 : Set ℕ := {a | IsGoldbachSum (2 * a + 6)}

/-- An even `g ≥ 6` that is a sum of two primes is a sum of two odd primes. -/
theorem oddPrimes_of {g : ℕ} (hg : Even g) (h6 : 6 ≤ g) (h : IsGoldbachSum g) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p + q = g := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  refine ⟨p, q, hp, hq, ?_, ?_, rfl⟩
  · rintro rfl
    have hev : Even q := by
      rcases hg with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have := (hq.even_iff).mp hev; omega
  · rintro rfl
    have hev : Even p := by
      rcases hg with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have := (hp.even_iff).mp hev; omega

/-- `2 n₀ = 1.002 · 10^30`, page 703. -/
def n₀ : ℕ := 501 * 10 ^ 27

lemma exp67_le : exp 67 ≤ 125250000000000000000000000000 := by
  have h := exp_one_lt_d9
  have e : exp 67 = exp 1 ^ 67 := by rw [← exp_nat_mul]; norm_num
  rw [e]
  calc exp 1 ^ 67 ≤ (2.7182818286 : ℝ) ^ 67 := pow_le_pow_left₀ (exp_pos 1).le h.le 67
    _ ≤ 125250000000000000000000000000 := by norm_num

/-- Page 703, `2 n₀ ≥ 8 exp 67`. -/
theorem two_n0_ge : 8 * exp 67 ≤ 2 * (n₀ : ℝ) := by
  have := exp67_le; simp only [n₀]; push_cast; linarith

/-- The counting function splits at `b / 2`. -/
lemma cnt_split (A : Set ℕ) (b : ℕ) :
    cnt A b = cnt A (b / 2) + #{a ∈ Ioc (b / 2) b | a ∈ A} := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · congr 1
    ext a; simp only [mem_filter, mem_union, mem_Icc, mem_Ioc]
    by_cases ha : a ∈ A
    · simp only [ha, and_true]; omega
    · simp [ha]
  · rw [disjoint_left]; intro a h1 h2
    simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2; omega

/-- One dyadic block of page 704: from Theorem 2 at `X = b + 3`, the block `]b/2, b]` holds at
least `(b + 3)/5 − 3` elements of `𝒜`. The paper subtracts 2; 3 is enough here. -/
lemma block (h2 : Theorem2) (b : ℕ) (hb : exp 67 ≤ (b : ℝ) + 3) :
    ((b : ℝ) + 3) / 5 ≤ (#{a ∈ Ioc (b / 2) b | a ∈ 𝒜} : ℝ) + 3 := by
  have h := h2 ((b : ℝ) + 3) hb
  have f1 : ⌊(b : ℝ) + 3⌋₊ = b + 3 := by exact_mod_cast Nat.floor_natCast (b + 3)
  have f2 : ⌊2 * ((b : ℝ) + 3)⌋₊ = 2 * b + 6 := by
    have : 2 * ((b : ℝ) + 3) = ((2 * b + 6 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.floor_natCast]
  rw [f1, f2] at h
  set S := {a ∈ Ioc (b / 2) b | a ∈ 𝒜}
  have hsub : {N ∈ Ioc (b + 3) (2 * b + 6) | Even N ∧ IsGoldbachSum N} ⊆
      S.image (fun a => 2 * a + 6) ∪ Ioc (b + 3) (b + 6) := by
    intro N hN
    simp only [mem_filter, mem_Ioc] at hN
    obtain ⟨⟨h1, h2'⟩, ⟨k, hk⟩, hg⟩ := hN
    rcases le_or_gt N (b + 6) with hle | hlt
    · exact mem_union_right _ (mem_Ioc.mpr ⟨h1, hle⟩)
    · apply mem_union_left
      refine mem_image.mpr ⟨k - 3, ?_, by omega⟩
      rw [mem_filter, mem_Ioc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      show IsGoldbachSum (2 * (k - 3) + 6)
      rwa [show 2 * (k - 3) + 6 = N by omega]
  have hc := card_le_card hsub
  have hu := card_union_le (S.image (fun a => 2 * a + 6)) (Ioc (b + 3) (b + 6))
  have hi := card_image_le (s := S) (f := fun a => 2 * a + 6)
  have h3 : #(Ioc (b + 3) (b + 6)) = 3 := by simp
  have : (#{N ∈ Ioc (b + 3) (2 * b + 6) | Even N ∧ IsGoldbachSum N} : ℝ) ≤ #S + 3 := by
    exact_mod_cast (by omega : #{N ∈ Ioc (b + 3) (2 * b + 6) | Even N ∧ IsGoldbachSum N} ≤ #S + 3)
  linarith

/-- The bottom block, from even Goldbach up to `2 · 10^10`, Granville, van de Lune and
te Riele [2]. -/
lemma bottom (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) (c : ℕ) (hc : 10 ^ 10 - 3 ≤ c) :
    10 ^ 10 - 3 ≤ cnt 𝒜 c := by
  unfold cnt
  have : Icc 1 (10 ^ 10 - 3) ⊆ {a ∈ Icc 1 c | a ∈ 𝒜} := by
    intro a ha
    simp only [mem_Icc] at ha
    rw [mem_filter, mem_Icc]
    exact ⟨⟨ha.1, by omega⟩, hG _ ⟨a + 3, by ring⟩ (by omega) (by omega)⟩
  have h := card_le_card this
  simpa using h

/-- **Hypothesis (a) of Theorem 9.1 for `𝒜`, page 704**, with `σ = 7/20`, `K = 39`, `H = 3`:
for `n ≥ n₀`, `𝒜(n) ≥ 7n/20 + 1560`. From Theorem 2 on three dyadic blocks and the bottom block
`[1, n/8]` from even Goldbach to `2 · 10^10`. The paper writes `A(Y/8) ≥ A(10^12 − 3) =
10^12 − 3` citing [2]; [2] reaches `2 · 10^10`, which gives `10^10 − 3`, and that is enough. -/
theorem hypA (h2 : Theorem2) (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) (n : ℕ) (hn : n₀ ≤ n) :
    (7 / 20 : ℝ) * n + (39 * (39 + 1) / 2 : ℝ) * ((3 : ℝ) - 1) ≤ cnt 𝒜 n := by
  have hE := exp67_le
  have hn' : (125250000000000000000000000000 : ℕ) ≤ n / 2 / 2 := by simp only [n₀] at hn; omega
  have hn8 : 10 ^ 10 - 3 ≤ n / 2 / 2 / 2 := by omega
  have hb : ∀ b : ℕ, n / 2 / 2 ≤ b → exp 67 ≤ (b : ℝ) + 3 := by
    intro b hb
    have : ((125250000000000000000000000000 : ℕ) : ℝ) ≤ b := by exact_mod_cast hn'.trans hb
    push_cast at this; linarith
  have b0 := block h2 n (hb n (by omega))
  have b1 := block h2 (n / 2) (hb _ (by omega))
  have b2 := block h2 (n / 2 / 2) (hb _ le_rfl)
  have s0 := cnt_split 𝒜 n
  have s1 := cnt_split 𝒜 (n / 2)
  have s2 := cnt_split 𝒜 (n / 2 / 2)
  have bot := bottom hG _ hn8
  have q1 : (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have q2 : ((n / 2 : ℕ) : ℝ) / 2 - 1 ≤ ((n / 2 / 2 : ℕ) : ℝ) := by
    have : n / 2 ≤ 2 * (n / 2 / 2) + 1 := by omega
    have : ((n / 2 : ℕ) : ℝ) ≤ 2 * ((n / 2 / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have r0 : (cnt 𝒜 n : ℝ) = cnt 𝒜 (n / 2) + #{a ∈ Ioc (n / 2) n | a ∈ 𝒜} := by
    exact_mod_cast s0
  have r1 : (cnt 𝒜 (n / 2) : ℝ) = cnt 𝒜 (n / 2 / 2) + #{a ∈ Ioc (n / 2 / 2) (n / 2) | a ∈ 𝒜} := by
    exact_mod_cast s1
  have r2 : (cnt 𝒜 (n / 2 / 2) : ℝ) =
      cnt 𝒜 (n / 2 / 2 / 2) + #{a ∈ Ioc (n / 2 / 2 / 2) (n / 2 / 2) | a ∈ 𝒜} := by
    exact_mod_cast s2
  have bot' : 9999999997 ≤ cnt 𝒜 (n / 2 / 2 / 2) := by simpa using bot
  have rb : (9999999997 : ℝ) ≤ cnt 𝒜 (n / 2 / 2 / 2) := by exact_mod_cast bot'
  linarith

/-- Hypothesis (b) for `𝒜`, first half: `{0, …, 39} ⊆ 𝒜`, from even Goldbach to 84. -/
theorem hypB_low (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) : ∀ i ≤ 39, i ∈ 𝒜 := by
  intro i hi
  exact hG _ ⟨i + 3, by ring⟩ (by omega) (by omega)

/-- Hypothesis (b) for `𝒜`, second half, `{n₀, …, n₀ + 39} ⊆ 𝒜`: the even numbers from
`2n₀ + 6` to `2n₀ + 84` are sums of two primes. Page 704: "a direct computation shows that
the assumption (b) holds". CITED. -/
def HypBHigh : Prop := ∀ i ≤ 39, IsGoldbachSum (2 * (n₀ + i) + 6)

/-- Hypothesis (c): `(K + 1) H σ ≥ K + H` with `K = 39`, `H = 3`, `σ = 7/20`; equality. -/
theorem hypC : ((39 : ℕ) : ℝ) + (3 : ℕ) ≤ ((39 : ℕ) + 1) * (3 : ℕ) * (7 / 20 : ℝ) := by norm_num

/-- Sums of elements of `𝒜` give sums of primes. -/
lemma atMost_of_list (l : List ℕ) (hl : ∀ a ∈ l, a ∈ 𝒜) :
    AtMostPrimes (2 * l.length) (2 * l.sum + 6 * l.length) := by
  induction l with
  | nil => simpa using AtMostPrimes.zero
  | cons a t ih =>
    have ha : IsGoldbachSum (2 * a + 6) := hl a (by simp)
    have ht := ih (fun x hx => hl x (by simp [hx]))
    have := (AtMostPrimes.of_goldbach ha).add ht
    simp only [List.length_cons, List.sum_cons]
    convert this using 1 <;> ring

lemma six_mul (j : ℕ) : AtMostPrimes (2 * j) (6 * j) := by
  induction j with
  | zero => simpa using AtMostPrimes.zero
  | succ j ih =>
    have h6 : AtMostPrimes 2 6 :=
      AtMostPrimes.of_goldbach ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
    have := h6.add ih
    convert this using 1 <;> ring

/-- **Section 9, page 704: the large range of Theorem 1.** From Theorem 2, Theorem 9.1, even
Goldbach up to `2 · 10^10`, and the direct computation of hypothesis (b), every even
`N ≥ 6 n₀ + 18`, about `3.006 · 10^30`, is a sum of at most 6 primes. The paper says
"larger than `6 n₀`"; Theorem 9.1 gives `m ≥ 3 n₀`, that is `N = 2m + 18 ≥ 6 n₀ + 18`.
The introduction's "larger than `10^30`", page 646, is not what Section 9 proves; the greedy
argument covers everything below. -/
theorem large_even_of (h2 : Theorem2) (h91 : Theorem91) (hG : EvenGoldbachUpTo (2 * 10 ^ 10))
    (hB : HypBHigh) : ∀ N : ℕ, Even N → 6 * n₀ + 18 ≤ N → AtMostPrimes 6 N := by
  intro N hN hle
  obtain ⟨k, hk⟩ := hN
  have h0 : (0 : ℕ) ∈ 𝒜 := ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
  obtain ⟨l, hl, hA, hs⟩ := h91 𝒜 (7 / 20) 3 39 n₀ (by norm_num) h0
    (fun n hn => hypA h2 hG n hn) (hypB_low hG) hB hypC (k - 9) (by omega)
  have h1 := atMost_of_list l hA
  have h2' := six_mul (3 - l.length)
  have := h1.add h2'
  rw [hs] at this
  have e : 2 * (k - 9) + 6 * l.length + 6 * (3 - l.length) = N := by
    have : l.length + (3 - l.length) = 3 := by omega
    omega
  rw [e] at this
  exact this.mono (by omega)

end LeanLab.Ramare1995.Section9
