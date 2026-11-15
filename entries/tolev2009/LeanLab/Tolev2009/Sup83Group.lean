module

public import LeanLab.Tolev2009.Sup83Heath

/-!
AI wrote this Lean code. Claude route burst 7, 2026-11-12.
Binary Goldbach is open.
Source: Tolev 1999 page 71 Lemma 4 and pages 82 to 83 displays 53 and 54.
Written proof: Heath Brown 1982 pages 1367 to 1368, displays 6 to 8 and the grouping
argument after display 8.
This file holds the generic machinery for Sup83Split.grouped_annular_decomposition:
the dyadic subdivision of each convolution variable, the splitting of a convolution
into a bilinear double sum, the support and coefficient bounds of grouped variables,
and the finite bookkeeping of block lists. The block sum blockSum below is the
definition Sup83Split.bilinear written with a general weight w; nothing here mentions
the Tolev objects themselves.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Sup83Group

/-- The weighted annular sum of a real arithmetic function f over x < n ≤ 2x, n ≤ N.
Tolev 1999 page 82 display 52 restricted to one shell, with a general complex weight. -/
noncomputable def annSum (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (f : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, if x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then (f n : ℂ) * w n else 0

/-- The bilinear block of Tolev 1999 page 83 displays 53 and 54 with a general weight w.
With w n = ee (α n) times the divisor weight this is Sup83Split.bilinear. -/
noncomputable def blockSum (w : ℕ → ℂ) (N : ℕ) (x M M₁ H H₁ : ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then a m * b l * w (m * l) else 0

/-- The restriction of g to the dyadic range clog 2 d = e, that is 2 ^ e / 2 < d ≤ 2 ^ e.
This is one factor of the dyadic subdivision in Heath Brown 1982 page 1367. -/
noncomputable def dy (g : ArithmeticFunction ℝ) (e : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if Nat.clog 2 d = e then g d else 0, by simp⟩

theorem dy_apply (g : ArithmeticFunction ℝ) (e d : ℕ) :
    dy g e d = if Nat.clog 2 d = e then g d else 0 := rfl

/-- Finite sums of arithmetic functions are evaluated pointwise. -/
theorem af_sum_apply {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, ArithmeticFunction.add_apply, ih]

/-- The dyadic pieces up to T recover g on 1 ≤ d ≤ 2 ^ T. -/
theorem sum_dy_apply (g : ArithmeticFunction ℝ) (T d : ℕ) (hd : d ≤ 2 ^ T) :
    (∑ e ∈ range (T + 1), dy g e) d = g d := by
  rw [af_sum_apply]
  simp only [dy_apply]
  rw [sum_ite_eq (range (T + 1)) (Nat.clog 2 d) (fun _ => g d)]
  have : Nat.clog 2 d ∈ range (T + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.clog_le_of_le_pow hd))
  simp [this]

/-- A dyadic piece is supported in 2 ^ e / 2 < d ≤ 2 ^ e. -/
theorem dy_support (g : ArithmeticFunction ℝ) (e d : ℕ) (h : dy g e d ≠ 0) :
    (2 : ℝ) ^ e / 2 < d ∧ (d : ℝ) ≤ 2 ^ e := by
  rw [dy_apply] at h
  by_cases he : Nat.clog 2 d = e
  · have hd0 : d ≠ 0 := by
      rintro rfl
      simp at h
    subst he
    refine ⟨?_, by exact_mod_cast Nat.le_pow_clog (by norm_num) d⟩
    by_cases h1 : d = 1
    · subst h1
      norm_num
    · have h1' : 1 < d := by omega
      have hp := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1'
      have hpos : 0 < Nat.clog 2 d := Nat.clog_pos (by norm_num) h1'
      have hcast : ((2 ^ (Nat.clog 2 d).pred : ℕ) : ℝ) < d := by exact_mod_cast hp
      have heq : (2 : ℝ) ^ Nat.clog 2 d / 2 = ((2 ^ (Nat.clog 2 d).pred : ℕ) : ℝ) := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hk]
        push_cast
        rw [pow_succ]
        simp
      rw [heq]
      exact hcast
  · simp [he] at h

/-- Values of a finite convolution at n depend only on the factor values at 1 ≤ d ≤ n. -/
theorem prod_apply_congr {ι : Type*} (s : Finset ι) (f g : ι → ArithmeticFunction ℝ) (n : ℕ)
    (h : ∀ i ∈ s, ∀ d, 1 ≤ d → d ≤ n → f i d = g i d) :
    (∏ i ∈ s, f i) n = (∏ i ∈ s, g i) n := by
  classical
  suffices H : ∀ m, m ≤ n → (∏ i ∈ s, f i) m = (∏ i ∈ s, g i) m from H n le_rfl
  induction s using Finset.induction_on with
  | empty => intro m _; simp
  | insert i s hi ih =>
    intro m hm
    rw [prod_insert hi, prod_insert hi, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply sum_congr rfl
    intro p hp
    have hpm := Nat.mem_divisorsAntidiagonal.mp hp
    have hm0 : m ≠ 0 := hpm.2
    have h1 : 1 ≤ p.1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hpm; omega)
    have h2 : 1 ≤ p.2 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hpm; omega)
    have hp1 : p.1 ≤ m := by
      rw [← hpm.1]; exact Nat.le_mul_of_pos_right _ h2
    have hp2 : p.2 ≤ m := by
      rw [← hpm.1]; exact Nat.le_mul_of_pos_left _ h1
    rw [h i (mem_insert_self _ _) p.1 h1 (hp1.trans hm),
      ih (fun j hj => h j (mem_insert_of_mem hj)) p.2 (hp2.trans hm)]

/-- The annular sum is additive over finite sums of arithmetic functions. -/
theorem annSum_sum {ι : Type*} (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (s : Finset ι)
    (F : ι → ArithmeticFunction ℝ) :
    annSum w N x (∑ i ∈ s, F i) = ∑ i ∈ s, annSum w N x (F i) := by
  unfold annSum
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [af_sum_apply]
  split_ifs
  · push_cast
    rw [sum_mul]
  · simp

/-- The annular sum only sees the values on the annulus. -/
theorem annSum_congr (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (f g : ArithmeticFunction ℝ)
    (h : ∀ n, 1 ≤ n → n ≤ N → x < (n : ℝ) → (n : ℝ) ≤ 2 * x → f n = g n) :
    annSum w N x f = annSum w N x g := by
  unfold annSum
  apply sum_congr rfl
  intro n hn
  have hn' := mem_Icc.mp hn
  split_ifs with hc
  · rw [h n hn'.1 hn'.2 hc.1 hc.2]
  · rfl

/-- Linearity of the annular sum in the coefficient. -/
theorem annSum_add (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (f g : ArithmeticFunction ℝ) :
    annSum w N x (f + g) = annSum w N x f + annSum w N x g := by
  unfold annSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  split_ifs
  · simp only [ArithmeticFunction.add_apply]
    push_cast
    ring
  · simp

theorem annSum_neg (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (f : ArithmeticFunction ℝ) :
    annSum w N x (-f) = -annSum w N x f := by
  unfold annSum
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro n _
  split_ifs
  · simp only [ArithmeticFunction.neg_apply]
    push_cast
    ring
  · simp

theorem annSum_three_mul (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (f : ArithmeticFunction ℝ) :
    annSum w N x (3 * f) = 3 * annSum w N x f := by
  have h : (3 : ArithmeticFunction ℝ) * f = f + f + f := by ring
  rw [h, annSum_add, annSum_add]
  ring

/-- A real Dirichlet convolution is bounded by the convolution of pointwise majorants. -/
theorem abs_convolution_le (f g F G : ArithmeticFunction ℝ)
    (hf : ∀ n, |f n| ≤ F n) (hg : ∀ n, |g n| ≤ G n) (n : ℕ) :
    |(f * g) n| ≤ (F * G) n := by
  simp only [ArithmeticFunction.mul_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p _
  rw [abs_mul]
  exact mul_le_mul (hf p.1) (hg p.2) (abs_nonneg _) ((abs_nonneg _).trans (hf p.1))

/-- Grouped variables with factor majorants beta times zeta have a convolution of
size at most the product of the beta times zeta to the number of factors.
This is the tau5 coefficient bound of Tolev 1999 page 71 Lemma 4. -/
theorem abs_prod_le {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (β : ι → ℝ)
    (hβ : ∀ i ∈ s, 0 ≤ β i)
    (hf : ∀ i ∈ s, ∀ d, |f i d| ≤ β i * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d)
    (n : ℕ) :
    |(∏ i ∈ s, f i) n| ≤
      (∏ i ∈ s, β i) * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ s.card) n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [prod_empty, card_empty, pow_zero, one_mul, ArithmeticFunction.one_apply]
    split_ifs <;> simp
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, card_insert_of_notMem hi, pow_succ',
      ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro p _
    rw [abs_mul]
    have hP := ih (fun j hj => hβ j (mem_insert_of_mem hj))
      (fun j hj => hf j (mem_insert_of_mem hj)) p.2
    have hF := hf i (mem_insert_self _ _) p.1
    calc |f i p.1| * |(∏ j ∈ s, f j) p.2| ≤
        (β i * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) p.1) *
          ((∏ j ∈ s, β j) * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ s.card) p.2) :=
          mul_le_mul hF hP (abs_nonneg _) ((abs_nonneg _).trans hF)
      _ = _ := by ring

/-- Real zeta powers are the casts of the natural ones. -/
theorem zeta_pow_cast (j n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ j) n =
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ j) n : ℝ) := by
  induction j generalizing n with
  | zero => simp [ArithmeticFunction.one_apply]
  | succ j ih =>
    rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    push_cast
    apply sum_congr rfl
    intro p _
    rw [ih]
    simp [ArithmeticFunction.natCoe_apply]

theorem zeta_pow_nonneg (j n : ℕ) :
    0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ j) n := by
  rw [zeta_pow_cast]; positivity

/-- Zeta powers increase with the exponent at every n. -/
theorem zeta_pow_le_succ (j n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ j) n ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j + 1)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [pow_succ', ArithmeticFunction.mul_apply]
  have hmem : ((1 : ℕ), n) ∈ n.divisorsAntidiagonal := by
    simp [Nat.mem_divisorsAntidiagonal, hn.ne']
  have := single_le_sum (f := fun p : ℕ × ℕ =>
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) p.1 *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ j) p.2)
    (fun p _ => mul_nonneg (by simp [ArithmeticFunction.zeta_apply]; split_ifs <;> norm_num)
      (zeta_pow_nonneg j p.2)) hmem
  simpa using this

theorem zeta_pow_mono {j k : ℕ} (hjk : j ≤ k) (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ j) n ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k) n := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (zeta_pow_le_succ _ n)

/-- The support of a convolution lies in the product of the factor support intervals. -/
theorem conv_support (f g : ArithmeticFunction ℝ) (P₁ R₁ P₂ R₂ : ℝ) (hP₁ : 0 ≤ P₁)
    (hP₂ : 0 ≤ P₂)
    (hf : ∀ a, f a ≠ 0 → P₁ < a ∧ (a : ℝ) ≤ R₁) (hg : ∀ b, g b ≠ 0 → P₂ < b ∧ (b : ℝ) ≤ R₂)
    (m : ℕ) (hm : (f * g) m ≠ 0) : P₁ * P₂ < m ∧ (m : ℝ) ≤ R₁ * R₂ := by
  rw [ArithmeticFunction.mul_apply] at hm
  obtain ⟨p, hp, hne⟩ := exists_ne_zero_of_sum_ne_zero hm
  have hpm := Nat.mem_divisorsAntidiagonal.mp hp
  have ha := hf p.1 (left_ne_zero_of_mul hne)
  have hb := hg p.2 (right_ne_zero_of_mul hne)
  have hmcast : (m : ℝ) = (p.1 : ℝ) * p.2 := by rw [← hpm.1]; push_cast; ring
  rw [hmcast]
  constructor
  · exact mul_lt_mul'' ha.1 hb.1 hP₁ hP₂
  · exact mul_le_mul ha.2 hb.2 (Nat.cast_nonneg _) ((hP₁.trans ha.1.le).trans ha.2)

/-- A nonempty grouped product of dyadic pieces lives in (P, 2 ^ card P]
with P the product of the lower endpoints.
Source: the ranges of the grouped variables in Heath Brown 1982 page 1368. -/
theorem prod_support {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ArithmeticFunction ℝ) (L : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i)
    (hf : ∀ i ∈ s, ∀ d, f i d ≠ 0 → L i < d ∧ (d : ℝ) ≤ 2 * L i)
    (m : ℕ) (hm : (∏ i ∈ s, f i) m ≠ 0) :
    (∏ i ∈ s, L i) < m ∧ (m : ℝ) ≤ 2 ^ s.card * ∏ i ∈ s, L i := by
  classical
  induction hs using Finset.Nonempty.cons_induction generalizing m with
  | singleton i =>
    simp only [prod_singleton, card_singleton, pow_one] at hm ⊢
    exact hf i (mem_singleton_self i) m hm
  | cons i s hi hs ih =>
    rw [prod_cons] at hm ⊢
    rw [card_cons, pow_succ]
    have hL' : ∀ j ∈ s, 0 < L j := fun j hj => hL j (mem_cons_of_mem hj)
    have hP : 0 ≤ ∏ j ∈ s, L j := prod_nonneg (fun j hj => (hL' j hj).le)
    have h := conv_support (f i) (∏ j ∈ s, f j) (L i) (2 * L i) (∏ j ∈ s, L j)
      (2 ^ s.card * ∏ j ∈ s, L j) (hL i (mem_cons_self _ _)).le hP
      (hf i (mem_cons_self _ _))
      (ih hL' (fun j hj => hf j (mem_cons_of_mem hj))) m hm
    refine ⟨h.1, h.2.trans_eq ?_⟩
    ring

/-- A convolution on the annulus becomes a double sum over its two factors.
This is the passage from display 52 to the bilinear form of display 53, Tolev 1999 page 83. -/
theorem annSum_mul (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (A B : ArithmeticFunction ℝ) :
    annSum w N x (A * B) =
      ∑ m ∈ Icc 1 N, ∑ l ∈ Icc 1 N,
        if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
          (A m : ℂ) * (B l : ℂ) * w (m * l) else 0 := by
  classical
  let G : ℕ × ℕ → ℂ := fun p =>
    if x < (p.1 * p.2 : ℕ) ∧ (p.1 * p.2 : ℕ) ≤ 2 * x ∧ p.1 * p.2 ≤ N then
      (A p.1 : ℂ) * (B p.2 : ℂ) * w (p.1 * p.2) else 0
  have hrhs : (∑ m ∈ Icc 1 N, ∑ l ∈ Icc 1 N,
        if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
          (A m : ℂ) * (B l : ℂ) * w (m * l) else 0) =
      ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N), G p := by
    rw [sum_filter, sum_product]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro l _
    by_cases h : m * l ≤ N
    · simp only [h, ite_true, G]
    · simp only [h, ite_false, G, and_false]
  rw [hrhs, ← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 N)]
  · unfold annSum
    apply sum_congr rfl
    intro n hn
    have hn' := mem_Icc.mp hn
    have hfib : ((Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
      constructor
      · rintro ⟨⟨⟨⟨ha, _⟩, _⟩, _⟩, he⟩
        exact ⟨he, by omega⟩
      · rintro ⟨he, _⟩
        have ha : 1 ≤ a := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at he; omega)
        have hb : 1 ≤ b := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at he; omega)
        have hab : a ≤ a * b := Nat.le_mul_of_pos_right _ hb
        have hba : b ≤ a * b := Nat.le_mul_of_pos_left _ ha
        refine ⟨⟨⟨⟨ha, by omega⟩, hb, by omega⟩, by omega⟩, he⟩
    rw [hfib, ArithmeticFunction.mul_apply]
    split_ifs with hc
    · push_cast
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
      simp only [G, he, hc, hn'.2, and_self, ite_true]
    · symm
      apply sum_eq_zero
      intro p hp
      have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
      simp only [G, he]
      rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
  · intro p hp
    have := mem_filter.mp hp
    have h1 := (mem_product.mp this.1)
    have ha := (mem_Icc.mp h1.1).1
    have hb := (mem_Icc.mp h1.2).1
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      this.2⟩

/-- Two finite index sets give the same sum when each contains every nonzero term of the other. -/
theorem sum_eq_of_nonzero_mem {M : Type*} [AddCommMonoid M] (X Y : Finset ℕ) (f : ℕ → M)
    (hXY : ∀ m ∈ X, f m ≠ 0 → m ∈ Y) (hYX : ∀ m ∈ Y, f m ≠ 0 → m ∈ X) :
    ∑ m ∈ X, f m = ∑ m ∈ Y, f m := by
  classical
  have h1 : ∑ m ∈ X ∩ Y, f m = ∑ m ∈ X, f m := by
    apply sum_subset inter_subset_left
    intro m hm hm'
    by_contra hne
    exact hm' (mem_inter.mpr ⟨hm, hXY m hm hne⟩)
  have h2 : ∑ m ∈ X ∩ Y, f m = ∑ m ∈ Y, f m := by
    apply sum_subset inter_subset_right
    intro m hm hm'
    by_contra hne
    exact hm' (mem_inter.mpr ⟨hYX m hm hne, hm⟩)
  rw [← h1, h2]

/-- A natural number lies in Ioc of the floors exactly when it lies in the real interval. -/
theorem mem_Ioc_floor (P R : ℝ) (hP : 0 ≤ P) (m : ℕ) :
    m ∈ Ioc ⌊P⌋₊ ⌊R⌋₊ ↔ P < m ∧ (m : ℝ) ≤ R := by
  rw [mem_Ioc, Nat.floor_lt hP]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hR : 0 ≤ R := by
      by_contra hR
      rw [Nat.floor_of_nonpos (le_of_not_ge hR)] at h2
      have : (0 : ℝ) < m := hP.trans_lt h1
      have : m = 0 := by omega
      simp_all
    exact (Nat.le_floor_iff hR).mp h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Nat.le_floor h2⟩

/-- The double sum restricted to the supports of the two grouped variables.
Source: the bilinear form of Tolev 1999 page 83 display 53. -/
theorem double_sum_restrict (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (A B : ArithmeticFunction ℝ)
    (P R Q S : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : ∀ m, A m ≠ 0 → P < m ∧ (m : ℝ) ≤ R) (hB : ∀ l, B l ≠ 0 → Q < l ∧ (l : ℝ) ≤ S) :
    (∑ m ∈ Icc 1 N, ∑ l ∈ Icc 1 N,
        if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
          (A m : ℂ) * (B l : ℂ) * w (m * l) else 0) =
      blockSum w N x P R Q S (fun m => (A m : ℂ)) (fun l => (B l : ℂ)) := by
  unfold blockSum
  have hterm : ∀ m l, (if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      (A m : ℂ) * (B l : ℂ) * w (m * l) else 0) ≠ 0 →
      A m ≠ 0 ∧ B l ≠ 0 ∧ m * l ≤ N := by
    intro m l h
    by_cases hc : x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N
    · rw [if_pos hc] at h
      refine ⟨fun h0 => h (by simp [h0]), fun h0 => h (by simp [h0]), hc.2.2⟩
    · rw [if_neg hc] at h
      exact absurd rfl h
  have hinner : ∀ m, (∑ l ∈ Icc 1 N, if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      (A m : ℂ) * (B l : ℂ) * w (m * l) else 0) =
      ∑ l ∈ Ioc ⌊Q⌋₊ ⌊S⌋₊, if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      (A m : ℂ) * (B l : ℂ) * w (m * l) else 0 := by
    intro m
    apply sum_eq_of_nonzero_mem
    · intro l _ hne
      obtain ⟨_, hBl, _⟩ := hterm m l hne
      exact (mem_Ioc_floor Q S hQ l).mpr (hB l hBl)
    · intro l hl hne
      obtain ⟨hAm, hBl, hle⟩ := hterm m l hne
      have hl1 : 1 ≤ l := Nat.pos_of_ne_zero (fun h0 => hBl (by simp [h0]))
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (fun h0 => hAm (by simp [h0]))
      have : l ≤ m * l := Nat.le_mul_of_pos_left _ hm1
      exact mem_Icc.mpr ⟨hl1, by omega⟩
  simp_rw [hinner]
  apply sum_eq_of_nonzero_mem
  · intro m _ hne
    obtain ⟨l, _, hl⟩ := exists_ne_zero_of_sum_ne_zero hne
    exact (mem_Ioc_floor P R hP m).mpr (hA m (hterm m l hl).1)
  · intro m _ hne
    obtain ⟨l, _, hl⟩ := exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨hAm, hBl, hle⟩ := hterm m l hl
    have hl1 : 1 ≤ l := Nat.pos_of_ne_zero (fun h0 => hBl (by simp [h0]))
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (fun h0 => hAm (by simp [h0]))
    have : m ≤ m * l := Nat.le_mul_of_pos_right _ hl1
    exact mem_Icc.mpr ⟨hm1, by omega⟩

/-- An interval (P, 2 ^ a P] is the union of a consecutive dyadic intervals.
Source: the dyadic subdivision of Heath Brown 1982 page 1367. -/
theorem sum_Ioc_dyadic {M : Type*} [AddCommMonoid M] (f : ℕ → M) (P : ℝ) (hP : 0 ≤ P)
    (a : ℕ) :
    ∑ m ∈ Ioc ⌊P⌋₊ ⌊2 ^ a * P⌋₊, f m =
      ∑ j ∈ range a, ∑ m ∈ Ioc ⌊2 ^ j * P⌋₊ ⌊2 ^ (j + 1) * P⌋₊, f m := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, ← ih]
    rw [sum_Ioc_consecutive]
    · exact Nat.floor_le_floor (le_mul_of_one_le_left hP (one_le_pow₀ (by norm_num)))
    · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.le_succ a)) hP)

/-- The block sum is additive in the first variable range under dyadic subdivision. -/
theorem blockSum_dyadic (w : ℕ → ℂ) (N : ℕ) (x P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (a b : ℕ) (α β : ℕ → ℂ) :
    blockSum w N x P (2 ^ a * P) Q (2 ^ b * Q) α β =
      ∑ j ∈ range a, ∑ j' ∈ range b,
        blockSum w N x (2 ^ j * P) (2 ^ (j + 1) * P) (2 ^ j' * Q) (2 ^ (j' + 1) * Q) α β := by
  unfold blockSum
  rw [sum_Ioc_dyadic _ P hP a]
  apply sum_congr rfl
  intro j _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [sum_Ioc_dyadic _ Q hQ b]

/-- Scalars pull out of the first coefficient of a block. -/
theorem blockSum_mul_left (w : ℕ → ℂ) (N : ℕ) (x M M₁ H H₁ : ℝ) (r : ℂ) (α β : ℕ → ℂ) :
    blockSum w N x M M₁ H H₁ (fun m => r * α m) β = r * blockSum w N x M M₁ H H₁ α β := by
  unfold blockSum
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rw [mul_sum]
  apply sum_congr rfl
  intro l _
  split_ifs <;> ring

theorem blockSum_mul_right (w : ℕ → ℂ) (N : ℕ) (x M M₁ H H₁ : ℝ) (r : ℂ) (α β : ℕ → ℂ) :
    blockSum w N x M M₁ H H₁ α (fun l => r * β l) = r * blockSum w N x M M₁ H H₁ α β := by
  unfold blockSum
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rw [mul_sum]
  apply sum_congr rfl
  intro l _
  split_ifs <;> ring

/-- Coefficients only matter on the block ranges. -/
theorem blockSum_congr (w : ℕ → ℂ) (N : ℕ) (x M M₁ H H₁ : ℝ) (α α' β β' : ℕ → ℂ)
    (hα : ∀ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, α m = α' m) (hβ : ∀ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, β l = β' l) :
    blockSum w N x M M₁ H H₁ α β = blockSum w N x M M₁ H H₁ α' β' := by
  unfold blockSum
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro l hl
  rw [hα m hm, hβ l hl]

/-- A block whose box misses the shell vanishes. Source: Tolev 1999 page 83 display 53,
the normalisation x / 4 ≤ M H ≤ 2 x of nonzero blocks. -/
theorem blockSum_eq_zero_of_scale (w : ℕ → ℂ) (N : ℕ) (x M M₁ H H₁ : ℝ) (α β : ℕ → ℂ)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hM₁ : M₁ ≤ 2 * M) (hH₁ : H₁ ≤ 2 * H)
    (h : ¬(x / 4 ≤ M * H ∧ M * H ≤ 2 * x)) :
    blockSum w N x M M₁ H H₁ α β = 0 := by
  unfold blockSum
  apply sum_eq_zero
  intro m hm
  apply sum_eq_zero
  intro l hl
  rw [mem_Ioc_floor M M₁ hM] at hm
  rw [mem_Ioc_floor H H₁ hH] at hl
  rw [if_neg]
  rintro ⟨h1, h2, _⟩
  have hml : ((m * l : ℕ) : ℝ) = (m : ℝ) * l := by push_cast; ring
  rw [hml] at h1 h2
  apply h
  constructor
  · have : (m : ℝ) * l ≤ (2 * M) * (2 * H) :=
      mul_le_mul (hm.2.trans hM₁) (hl.2.trans hH₁) (Nat.cast_nonneg _) (by linarith)
    linarith
  · have : M * H < (m : ℝ) * l := mul_lt_mul'' hm.1 hl.1 hM hH
    linarith

/-- The normalisation of one block in Tolev 1999 page 83 displays 53 and 54:
dyadic boxes, the shell scale x / 4 ≤ M H ≤ 2 x, the tau5 log N coefficient bound and
the Type I or Type II size condition on the second variable. -/
def BlockOK (N : ℕ) (x Cc : ℝ) (c : ℂ) (M M₁ H H₁ : ℝ) (a b : ℕ → ℂ) : Prop :=
  ‖c‖ ≤ Cc ∧ 0 < M ∧ M ≤ M₁ ∧ M₁ ≤ 2 * M ∧ 0 < H ∧ H ≤ H₁ ∧ H₁ ≤ 2 * H ∧
    x / 4 ≤ M * H ∧ M * H ≤ 2 * x ∧
    (∀ m, ‖a m‖ ≤ (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) m : ℝ) *
      Real.log N) ∧
    ((x ^ ((249 : ℝ) / 500) ≤ H ∧
        (b = (fun _ => 1) ∨ b = (fun l : ℕ => (Real.log l : ℂ)))) ∨
      (x ^ ((1 : ℝ) / 1000) ≤ H ∧ H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) ∧
        ∀ l, ‖b l‖ ≤ (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) l : ℝ) *
          Real.log N))

/-- S is a combination of at most n normalised blocks with coefficients at most Cc. -/
def Dec (w : ℕ → ℂ) (N : ℕ) (x Cc : ℝ) (n : ℕ) (S : ℂ) : Prop :=
  ∃ J : ℕ, J ≤ n ∧ ∃ (c : Fin J → ℂ) (M M₁ H H₁ : Fin J → ℝ) (a b : Fin J → ℕ → ℂ),
    S = ∑ j, c j * blockSum w N x (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
    ∀ j, BlockOK N x Cc (c j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)

theorem Dec_zero (w : ℕ → ℂ) (N : ℕ) (x Cc : ℝ) (n : ℕ) : Dec w N x Cc n 0 :=
  ⟨0, Nat.zero_le n, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    Fin.elim0, by simp, fun j => Fin.elim0 j⟩

theorem Dec_single (w : ℕ → ℂ) (N : ℕ) (x Cc : ℝ) (c : ℂ) (M M₁ H H₁ : ℝ) (a b : ℕ → ℂ)
    (h : BlockOK N x Cc c M M₁ H H₁ a b) :
    Dec w N x Cc 1 (c * blockSum w N x M M₁ H H₁ a b) :=
  ⟨1, le_rfl, fun _ => c, fun _ => M, fun _ => M₁, fun _ => H, fun _ => H₁, fun _ => a,
    fun _ => b, by simp, fun _ => h⟩

theorem Dec_mono {w : ℕ → ℂ} {N : ℕ} {x Cc Cc' : ℝ} {n n' : ℕ} {S : ℂ}
    (hn : n ≤ n') (hC : Cc ≤ Cc') (h : Dec w N x Cc n S) : Dec w N x Cc' n' S := by
  obtain ⟨J, hJ, c, M, M₁, H, H₁, a, b, hS, hb⟩ := h
  exact ⟨J, hJ.trans hn, c, M, M₁, H, H₁, a, b, hS, fun j => ⟨(hb j).1.trans hC, (hb j).2⟩⟩

theorem Dec_add {w : ℕ → ℂ} {N : ℕ} {x Cc : ℝ} {n n' : ℕ} {S S' : ℂ}
    (h : Dec w N x Cc n S) (h' : Dec w N x Cc n' S') : Dec w N x Cc (n + n') (S + S') := by
  obtain ⟨J, hJ, c, M, M₁, H, H₁, a, b, hS, hb⟩ := h
  obtain ⟨J', hJ', c', M', M₁', H', H₁', a', b', hS', hb'⟩ := h'
  refine ⟨J + J', by omega, Fin.append c c', Fin.append M M', Fin.append M₁ M₁',
    Fin.append H H', Fin.append H₁ H₁', Fin.append a a', Fin.append b b', ?_, ?_⟩
  · rw [Fin.sum_univ_add, hS, hS']
    simp only [Fin.append_left, Fin.append_right]
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; exact hb i
    · simp only [Fin.append_right]; exact hb' i

theorem Dec_sum {ι : Type*} {w : ℕ → ℂ} {N : ℕ} {x Cc : ℝ} {n : ℕ} (s : Finset ι)
    (S : ι → ℂ) (h : ∀ i ∈ s, Dec w N x Cc n (S i)) :
    Dec w N x Cc (s.card * n) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Dec_zero w N x Cc 0
  | insert i s hi ih =>
    rw [sum_insert hi, card_insert_of_notMem hi, Nat.succ_mul, add_comm (s.card * n) n]
    exact Dec_add (h i (mem_insert_self _ _)) (ih (fun j hj => h j (mem_insert_of_mem hj)))

theorem Dec_mul {w : ℕ → ℂ} {N : ℕ} {x Cc : ℝ} {n : ℕ} {S : ℂ} (r : ℂ)
    (h : Dec w N x Cc n S) : Dec w N x (‖r‖ * Cc) n (r * S) := by
  obtain ⟨J, hJ, c, M, M₁, H, H₁, a, b, hS, hb⟩ := h
  refine ⟨J, hJ, fun j => r * c j, M, M₁, H, H₁, a, b, ?_, fun j => ⟨?_, (hb j).2⟩⟩
  · rw [hS, mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb j).1 (norm_nonneg r)

/-- A product of dyadic variables split into a group sᶜ for m and a group s for l becomes
a double sum of dyadic blocks. Source: Heath Brown 1982 page 1368, the grouping into the
two variables of Tolev 1999 page 83 display 53. -/
theorem split_blocks {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℕ → ℂ) (N : ℕ) (x : ℝ)
    (F : ι → ArithmeticFunction ℝ) (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (hF : ∀ i d, F i d ≠ 0 → L i < d ∧ (d : ℝ) ≤ 2 * L i)
    (s : Finset ι) (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    annSum w N x (∏ i, F i) =
      ∑ j ∈ range sᶜ.card, ∑ j' ∈ range s.card,
        blockSum w N x (2 ^ j * ∏ i ∈ sᶜ, L i) (2 ^ (j + 1) * ∏ i ∈ sᶜ, L i)
          (2 ^ j' * ∏ i ∈ s, L i) (2 ^ (j' + 1) * ∏ i ∈ s, L i)
          (fun m => ((∏ i ∈ sᶜ, F i) m : ℂ)) (fun l => ((∏ i ∈ s, F i) l : ℂ)) := by
  have hP : 0 ≤ ∏ i ∈ sᶜ, L i := prod_nonneg (fun i _ => (hL i).le)
  have hQ : 0 ≤ ∏ i ∈ s, L i := prod_nonneg (fun i _ => (hL i).le)
  rw [← prod_compl_mul_prod s F, annSum_mul,
    double_sum_restrict w N x _ _ (∏ i ∈ sᶜ, L i) (2 ^ sᶜ.card * ∏ i ∈ sᶜ, L i)
      (∏ i ∈ s, L i) (2 ^ s.card * ∏ i ∈ s, L i) hP hQ
      (prod_support sᶜ hsc F L (fun i _ => hL i) (fun i _ => hF i))
      (prod_support s hs F L (fun i _ => hL i) (fun i _ => hF i)),
    blockSum_dyadic w N x _ _ hP hQ]

/-- A natural number in (2 ^ e / 2, 2 ^ e] has ceiling logarithm e. -/
theorem clog_of_mem (e l : ℕ) (h1 : (2 : ℝ) ^ e / 2 < l) (h2 : (l : ℝ) ≤ 2 ^ e) :
    Nat.clog 2 l = e := by
  have h2' : l ≤ 2 ^ e := by exact_mod_cast h2
  apply le_antisymm (Nat.clog_le_of_le_pow h2')
  rcases Nat.eq_zero_or_pos e with he | he
  · omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    have : (2 : ℝ) ^ (k + 1) / 2 = ((2 ^ k : ℕ) : ℝ) := by push_cast; rw [pow_succ]; ring
    rw [this] at h1
    have h1' : 2 ^ k < l := by exact_mod_cast h1
    exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr h1')

/-- The three kinds of convolution variable in Heath Brown's identity:
0 the truncated Moebius function, 1 the constant one, 2 the logarithm.
Source: Heath Brown 1982 page 1367 display 6, k equal to three. -/
noncomputable def kindFn (U : ℕ) (q : Fin 3) : ArithmeticFunction ℝ :=
  if q = 0 then LeanLab.HeathBrown1985.muLe U
  else if q = 1 then (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  else ArithmeticFunction.log

/-- Each dyadic variable is bounded by one, or by T log 2 for the logarithm, times zeta. -/
theorem kind_bound (U : ℕ) (q : Fin 3) (e T : ℕ) (he : e ≤ T) (d : ℕ) :
    |dy (kindFn U q) e d| ≤
      (if q = 2 then max 1 (T * Real.log 2) else 1) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d := by
  rw [dy_apply]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hz : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d = 1 := by
    simp [ArithmeticFunction.zeta_apply, hd.ne']
  rw [hz, mul_one]
  split_ifs with hc hq
  · subst hq
    simp only [kindFn, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_false, ArithmeticFunction.log_apply]
    have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    rw [abs_of_nonneg hlog0]
    apply le_max_of_le_right
    have hd2 : (d : ℝ) ≤ 2 ^ e := by
      rw [← hc]; exact_mod_cast Nat.le_pow_clog (by norm_num) d
    calc Real.log d ≤ Real.log ((2 : ℝ) ^ e) :=
          Real.log_le_log (by exact_mod_cast hd) hd2
      _ = e * Real.log 2 := by rw [Real.log_pow]
      _ ≤ T * Real.log 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast he) (Real.log_nonneg (by norm_num))
  · unfold kindFn
    split_ifs with h0 h1
    · simp only [LeanLab.HeathBrown1985.muLe]
      change |(if d ≤ U then (ArithmeticFunction.moebius d : ℝ) else 0)| ≤ 1
      split_ifs
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · simp
    · simp [ArithmeticFunction.zeta_apply, hd.ne']
    · exfalso
      fin_cases q <;> simp_all
  · simp
  · simp

/-- On its dyadic range a smooth variable is one or the logarithm. -/
theorem kind_on_range (U : ℕ) (q : Fin 3) (hq : q ≠ 0) (e l : ℕ) (hl : Nat.clog 2 l = e)
    (hl1 : 1 ≤ l) :
    (dy (kindFn U q) e l : ℂ) = if q = 1 then 1 else (Real.log l : ℂ) := by
  rw [dy_apply, if_pos hl]
  unfold kindFn
  rw [if_neg hq]
  split_ifs
  · simp [ArithmeticFunction.zeta_apply]; omega
  · simp [ArithmeticFunction.log_apply]

/-- The truncated Moebius variable vanishes on dyadic ranges above U. -/
theorem kind_mu_vanish (U e d : ℕ) (hU : (U : ℝ) ≤ (2 : ℝ) ^ e / 2) :
    dy (kindFn U 0) e d = 0 := by
  by_contra h
  have hs := dy_support _ e d h
  rw [dy_apply] at h
  unfold kindFn at h
  simp only [if_true] at h
  have hUd : U < d := by
    have : (U : ℝ) < d := hU.trans_lt hs.1
    exact_mod_cast this
  apply h
  split_ifs
  · simp [LeanLab.HeathBrown1985.muLe, show ¬d ≤ U by omega]
  · rfl

/-- With at most one logarithmic variable, the product of the variable majorants is at
most the larger of one and T log 2. -/
theorem prod_beta_le {k : ℕ} (κ : Fin k → Fin 3) (hκ : (univ.filter (fun i => κ i = 2)).card ≤ 1)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (s : Finset (Fin k)) :
    ∏ i ∈ s, (if κ i = 2 then Λ else 1) ≤ Λ := by
  classical
  rw [prod_ite, prod_const_one, mul_one, prod_const]
  have hc : (s.filter (fun i => κ i = 2)).card ≤ 1 :=
    (card_le_card (filter_subset_filter _ (subset_univ s))).trans hκ
  calc Λ ^ (s.filter (fun i => κ i = 2)).card ≤ Λ ^ 1 := pow_le_pow_right₀ hΛ hc
    _ = Λ := pow_one Λ

/-- The grouped coefficient bound of Tolev 1999 page 71 Lemma 4: a group of at most five
dyadic variables, one third of it, is bounded by tau5 times log N. -/
theorem group_coeff_bound {k : ℕ} (U T : ℕ) (κ : Fin k → Fin 3) (e : Fin k → ℕ)
    (he : ∀ i, e i ≤ T) (hκ : (univ.filter (fun i => κ i = 2)).card ≤ 1)
    (N : ℕ) (hT : max 1 (T * Real.log 2) ≤ 3 * Real.log N)
    (s : Finset (Fin k)) (hs : s.card ≤ 5) (m : ℕ) :
    ‖(1 / 3 : ℂ) * ((∏ i ∈ s, dy (kindFn U (κ i)) (e i)) m : ℂ)‖ ≤
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) m : ℝ) * Real.log N := by
  set Λ := max 1 (T * Real.log 2)
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hb := abs_prod_le s (fun i => dy (kindFn U (κ i)) (e i))
    (fun i => if κ i = 2 then Λ else 1) (fun i _ => by split_ifs <;> linarith)
    (fun i _ d => kind_bound U (κ i) (e i) T (he i) d) m
  have hp := prod_beta_le κ hκ Λ hΛ s
  have hz := zeta_pow_mono hs m
  rw [zeta_pow_cast 5 m] at hz
  have hz0 := zeta_pow_nonneg s.card m
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num
  have h1 : |(∏ i ∈ s, dy (kindFn U (κ i)) (e i)) m| ≤
      Λ * (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) m : ℝ) :=
    hb.trans (mul_le_mul hp hz hz0 (by linarith))
  have h0 : (0 : ℝ) ≤ (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) m : ℝ) :=
    Nat.cast_nonneg _
  nlinarith

theorem annSum_zero (w : ℕ → ℂ) (N : ℕ) (x : ℝ) : annSum w N x 0 = 0 := by
  unfold annSum
  simp

/-- Support of one dyadic variable in the half open form used by the blocks. -/
theorem dy_support' (g : ArithmeticFunction ℝ) (e d : ℕ) (h : dy g e d ≠ 0) :
    (2 : ℝ) ^ e / 2 < d ∧ (d : ℝ) ≤ 2 * ((2 : ℝ) ^ e / 2) := by
  have := dy_support g e d h
  exact ⟨this.1, by linarith [this.2]⟩

/-- Type I blocks, Tolev 1999 page 83 display 53 with H at least x to 249/500.
A smooth variable of size at least x to 249/500 is taken alone as l; the other
variables form m. Source: Heath Brown 1982 page 1368, the case of a long smooth factor. -/
theorem caseA_dec {k : ℕ} (hk2 : 2 ≤ k) (hk6 : k ≤ 6) (w : ℕ → ℂ) (N : ℕ) (x : ℝ)
    (U T : ℕ) (κ : Fin k → Fin 3) (e : Fin k → ℕ) (he : ∀ i, e i ≤ T)
    (hκ : (univ.filter (fun i => κ i = 2)).card ≤ 1)
    (hT : max 1 (T * Real.log 2) ≤ 3 * Real.log N)
    (i₀ : Fin k) (hi₀ : κ i₀ ≠ 0) (hz : x ^ ((249 : ℝ) / 500) ≤ (2 : ℝ) ^ e i₀ / 2) :
    Dec w N x 9 36 (annSum w N x (∏ i, dy (kindFn U (κ i)) (e i))) := by
  classical
  set L : Fin k → ℝ := fun i => (2 : ℝ) ^ e i / 2 with hLdef
  have hL : ∀ i, 0 < L i := fun i => by simp only [hLdef]; positivity
  have hs : ({i₀} : Finset (Fin k)).Nonempty := singleton_nonempty i₀
  have hcard : ({i₀}ᶜ : Finset (Fin k)).card = k - 1 := by
    rw [card_compl, card_singleton, Fintype.card_fin]
  have hsc : ({i₀}ᶜ : Finset (Fin k)).Nonempty := by
    rw [← card_pos, hcard]; omega
  rw [split_blocks w N x _ L hL (fun i d h => dy_support' _ _ d h) {i₀} hs hsc,
    card_singleton]
  refine Dec_mono ?hn le_rfl
    (Dec_sum (n := (range 1).card * 1) _ _ (fun j _ => Dec_sum (n := 1) _ _ (fun j' hj' => ?blk)))
  case hn => simp only [card_range, hcard]; omega
  case blk =>
  have hj'0 : j' = 0 := by simpa using hj'
  subst hj'0
  set P := ∏ i ∈ ({i₀}ᶜ : Finset (Fin k)), L i with hPdef
  have hP : 0 < P := prod_pos (fun i _ => hL i)
  simp only [prod_singleton, pow_zero, one_mul, zero_add, pow_one]
  by_cases hsc' : x / 4 ≤ 2 ^ j * P * L i₀ ∧ 2 ^ j * P * L i₀ ≤ 2 * x
  · let b : ℕ → ℂ := if κ i₀ = 1 then (fun _ => 1) else (fun l : ℕ => (Real.log l : ℂ))
    have hblk : blockSum w N x (2 ^ j * P) (2 ^ (j + 1) * P) (L i₀) (2 * L i₀)
        (fun m => ((∏ i ∈ ({i₀}ᶜ : Finset (Fin k)), dy (kindFn U (κ i)) (e i)) m : ℂ))
        (fun l => (dy (kindFn U (κ i₀)) (e i₀) l : ℂ)) =
        3 * blockSum w N x (2 ^ j * P) (2 ^ (j + 1) * P) (L i₀) (2 * L i₀)
          (fun m => (1 / 3 : ℂ) *
            ((∏ i ∈ ({i₀}ᶜ : Finset (Fin k)), dy (kindFn U (κ i)) (e i)) m : ℂ)) b := by
      rw [← blockSum_mul_left]
      apply blockSum_congr
      · intro m _; ring
      · intro l hl
        rw [mem_Ioc_floor _ _ (hL i₀).le] at hl
        have hl1 : 1 ≤ l := by
          have : (0 : ℝ) < l := (hL i₀).trans hl.1
          exact_mod_cast this
        rw [kind_on_range U (κ i₀) hi₀ (e i₀) l
          (clog_of_mem _ _ hl.1 (by simp only [hLdef] at hl; linarith [hl.2])) hl1]
        simp only [b]
        split_ifs <;> rfl
    rw [hblk]
    apply Dec_single
    refine ⟨by norm_num, by positivity, ?_, ?_, hL i₀, by linarith [hL i₀], le_rfl,
      by linarith [hsc'.1], by linarith [hsc'.2], ?_, Or.inl ⟨hz, ?_⟩⟩
    · have : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
      exact mul_le_mul_of_nonneg_right this hP.le
    · rw [pow_succ]; linarith
    · intro m
      exact group_coeff_bound U T κ e he hκ N hT _ (by rw [hcard]; omega) m
    · simp only [b]
      split_ifs
      · left; rfl
      · right; rfl
  · rw [blockSum_eq_zero_of_scale w N x _ _ _ _ _ _ (by positivity) (hL i₀).le
      (by rw [pow_succ]; linarith) le_rfl (by
        intro h; apply hsc'; constructor <;> linarith [h.1, h.2])]
    exact Dec_zero w N x 9 1

/-- Type II blocks, Tolev 1999 page 83 display 54 with x to 1/1000 ≤ H ≤ 2 ^ 30 x to 1/3.
When every variable is below x to 249/500 a subproduct lands in the middle range.
Source: Heath Brown 1982 page 1368, the grouping argument after display 8, with the
singleton adjustment of Sup83Heath.exists_subset_product_half_scale. -/
theorem caseB_dec {k : ℕ} (hk6 : k ≤ 6) (w : ℕ → ℂ) (N : ℕ) (x : ℝ)
    (hx : Real.exp 100000 ≤ x)
    (U T : ℕ) (κ : Fin k → Fin 3) (e : Fin k → ℕ) (he : ∀ i, e i ≤ T)
    (hκ : (univ.filter (fun i => κ i = 2)).card ≤ 1)
    (hT : max 1 (T * Real.log 2) ≤ 3 * Real.log N)
    (hall : ∀ i, (2 : ℝ) ^ e i / 2 ≤ x ^ ((249 : ℝ) / 500))
    (hprod : x / 64 < ∏ i, (2 : ℝ) ^ e i / 2 ∧ ∏ i, (2 : ℝ) ^ e i / 2 < 2 * x) :
    Dec w N x 9 36 (annSum w N x (∏ i, dy (kindFn U (κ i)) (e i))) := by
  classical
  set L : Fin k → ℝ := fun i => (2 : ℝ) ^ e i / 2 with hLdef
  have hL : ∀ i, 0 < L i := fun i => by simp only [hLdef]; positivity
  obtain ⟨p1, -, p3, -, -, -, -⟩ := Sup83Heath.source_parameters x hx
  obtain ⟨q1, q2, q3, q4⟩ := Sup83Heath.source_half_scale_parameters x hx
  set u := x ^ ((1 : ℝ) / 1000) with hu
  set z := x ^ ((249 : ℝ) / 500) with hzdef
  set V := (2 : ℝ) ^ 24 * x ^ ((1 : ℝ) / 3) with hV
  have hz1 : 16384 ≤ z := by nlinarith
  have hzx : z < x := by nlinarith
  have hx13 : 0 ≤ x ^ ((1 : ℝ) / 3) := by
    have : 0 ≤ x := by linarith [Real.exp_pos 100000]
    positivity
  have hhalf : ∀ i, (1 : ℝ) / 2 ≤ L i := by
    intro i
    simp only [hLdef]
    have := one_le_pow₀ (M₀ := ℝ) (n := e i) (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  obtain ⟨t, -, htu, htV⟩ := Sup83Heath.exists_subset_product_half_scale univ L u V z
    (by linarith) q1 q2 (fun i _ => ⟨hhalf i, hall i⟩)
    (by simp; omega) (by nlinarith [hprod.1]) (by nlinarith [hprod.2])
  have hs : t.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    subst h
    simp at htu
    linarith
  have hsc : tᶜ.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at h
    subst h
    have : 64 * V ≤ z := by
      simp only [hV]; nlinarith
    nlinarith [hprod.1]
  have hct : t.card + tᶜ.card = k := by
    rw [card_compl, Fintype.card_fin]; have := card_le_univ t; simp at this; omega
  have htc : 1 ≤ tᶜ.card := card_pos.mpr hsc
  have hts : 1 ≤ t.card := card_pos.mpr hs
  rw [split_blocks w N x _ L hL (fun i d h => dy_support' _ _ d h) t hs hsc]
  refine Dec_mono ?hn le_rfl
    (Dec_sum (n := (range t.card).card * 1) _ _
      (fun j _ => Dec_sum (n := 1) _ _ (fun j' hj' => ?blk)))
  case hn =>
    simp only [card_range, mul_one]
    calc tᶜ.card * t.card ≤ 6 * 6 :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 36 := by norm_num
  case blk =>
  have hj' : j' < t.card := mem_range.mp hj'
  set P := ∏ i ∈ tᶜ, L i with hPdef
  set Q := ∏ i ∈ t, L i with hQdef
  have hP : 0 < P := prod_pos (fun i _ => hL i)
  have hQ : 0 < Q := prod_pos (fun i _ => hL i)
  have h2j : (1 : ℝ) ≤ 2 ^ j' := one_le_pow₀ (by norm_num)
  have h2j' : (2 : ℝ) ^ j' ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
  by_cases hsc' : x / 4 ≤ 2 ^ j * P * (2 ^ j' * Q) ∧ 2 ^ j * P * (2 ^ j' * Q) ≤ 2 * x
  · have hblk : ∀ α β : ℕ → ℂ,
        blockSum w N x (2 ^ j * P) (2 ^ (j + 1) * P) (2 ^ j' * Q) (2 ^ (j' + 1) * Q) α β =
        9 * blockSum w N x (2 ^ j * P) (2 ^ (j + 1) * P) (2 ^ j' * Q) (2 ^ (j' + 1) * Q)
          (fun m => (1 / 3 : ℂ) * α m) (fun l => (1 / 3 : ℂ) * β l) := by
      intro α β
      rw [blockSum_mul_left, blockSum_mul_right]
      ring
    rw [hblk]
    apply Dec_single
    refine ⟨by norm_num, by positivity, ?_, ?_, by positivity, ?_, ?_,
      by linarith [hsc'.1], by linarith [hsc'.2], ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · have : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
      exact mul_le_mul_of_nonneg_right this hP.le
    · rw [pow_succ]; linarith
    · have : (2 : ℝ) ^ j' ≤ 2 ^ (j' + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ j')
      exact mul_le_mul_of_nonneg_right this hQ.le
    · rw [pow_succ]; linarith
    · intro m
      exact group_coeff_bound U T κ e he hκ N hT _ (by omega) m
    · nlinarith
    · have : 2 ^ j' * Q ≤ 2 ^ 4 * V := mul_le_mul h2j' htV hQ.le (by norm_num)
      simp only [hV] at this
      linarith
    · intro l
      exact group_coeff_bound U T κ e he hκ N hT _ (by omega) l
  · rw [blockSum_eq_zero_of_scale w N x _ _ _ _ _ _ (by positivity) (by positivity)
      (by rw [pow_succ]; linarith) (by rw [pow_succ]; linarith) (by
        intro h; apply hsc'; constructor <;> linarith [h.1, h.2])]
    exact Dec_zero w N x 9 1

/-- A truncated Moebius variable on a dyadic range above U kills the product. -/
theorem caseC1_zero {k : ℕ} (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (U : ℕ) (κ : Fin k → Fin 3)
    (e : Fin k → ℕ) (i : Fin k) (hi : κ i = 0) (hU : (U : ℝ) ≤ (2 : ℝ) ^ e i / 2) :
    annSum w N x (∏ i, dy (kindFn U (κ i)) (e i)) = 0 := by
  have h0 : dy (kindFn U (κ i)) (e i) = 0 := by
    ext d
    rw [hi, kind_mu_vanish U (e i) d hU]
    rfl
  rw [prod_eq_zero (mem_univ i) h0, annSum_zero]

/-- A dyadic box whose product misses (x / 64, 2 x) contributes nothing to the shell. -/
theorem caseC2_zero {k : ℕ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (w : ℕ → ℂ) (N : ℕ) (x : ℝ)
    (U : ℕ) (κ : Fin k → Fin 3) (e : Fin k → ℕ)
    (h : ¬(x / 64 < ∏ i, (2 : ℝ) ^ e i / 2 ∧ ∏ i, (2 : ℝ) ^ e i / 2 < 2 * x)) :
    annSum w N x (∏ i, dy (kindFn U (κ i)) (e i)) = 0 := by
  rw [annSum_congr w N x _ 0, annSum_zero]
  intro n _ _ hxn hn2
  by_contra hne
  have hk : (univ : Finset (Fin k)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  have hs := prod_support univ hk (fun i => dy (kindFn U (κ i)) (e i))
    (fun i => (2 : ℝ) ^ e i / 2) (fun i _ => by positivity)
    (fun i _ d hd => dy_support' _ _ d hd) n hne
  rw [card_univ, Fintype.card_fin] at hs
  have h64 : (2 : ℝ) ^ k ≤ 64 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hk6
      _ = 64 := by norm_num
  have hP0 : 0 ≤ ∏ i, (2 : ℝ) ^ e i / 2 := prod_nonneg (fun i _ => by positivity)
  apply h
  constructor
  · nlinarith [hs.2]
  · linarith [hs.1]

/-- One dyadic box of a Heath Brown term is a combination of at most 36 normalised blocks.
Source: Heath Brown 1982 page 1368 and Tolev 1999 page 71 Lemma 4. -/
theorem box_dec {k : ℕ} (hk2 : 2 ≤ k) (hk6 : k ≤ 6) (w : ℕ → ℂ) (N : ℕ) (x : ℝ)
    (hx : Real.exp 100000 ≤ x)
    (U T : ℕ) (hU : (U : ℝ) ≤ x ^ ((249 : ℝ) / 500))
    (κ : Fin k → Fin 3) (e : Fin k → ℕ) (he : ∀ i, e i ≤ T)
    (hκ : (univ.filter (fun i => κ i = 2)).card ≤ 1)
    (hT : max 1 (T * Real.log 2) ≤ 3 * Real.log N) :
    Dec w N x 9 36 (annSum w N x (∏ i, dy (kindFn U (κ i)) (e i))) := by
  classical
  by_cases hA : ∃ i, κ i ≠ 0 ∧ x ^ ((249 : ℝ) / 500) ≤ (2 : ℝ) ^ e i / 2
  · obtain ⟨i, hi, hz⟩ := hA
    exact caseA_dec hk2 hk6 w N x U T κ e he hκ hT i hi hz
  by_cases hC : ∃ i, κ i = 0 ∧ x ^ ((249 : ℝ) / 500) < (2 : ℝ) ^ e i / 2
  · obtain ⟨i, hi, hz⟩ := hC
    rw [caseC1_zero w N x U κ e i hi (hU.trans hz.le)]
    exact Dec_zero w N x 9 36
  have hall : ∀ i, (2 : ℝ) ^ e i / 2 ≤ x ^ ((249 : ℝ) / 500) := by
    intro i
    by_cases hi : κ i = 0
    · exact le_of_not_gt (fun h => hC ⟨i, hi, h⟩)
    · exact le_of_lt (lt_of_not_ge (fun h => hA ⟨i, hi, h⟩))
  by_cases hB : x / 64 < ∏ i, (2 : ℝ) ^ e i / 2 ∧ ∏ i, (2 : ℝ) ^ e i / 2 < 2 * x
  · exact caseB_dec hk6 w N x hx U T κ e he hκ hT hall hB
  · rw [caseC2_zero (by omega) hk6 w N x U κ e hB]
    exact Dec_zero w N x 9 36

/-- The number of dyadic ranges below 2 x is at most a constant times log N, and the
logarithmic variable is at most 3 log N on them. Source: the log N factors counted in
Heath Brown 1982 page 1367 and Tolev 1999 page 71 Lemma 4. -/
theorem clog_bounds (N : ℕ) (hN : 1 ≤ Real.log N) (x : ℝ) (hx1 : 1 ≤ x) (hxN : x ≤ N) :
    Nat.clog 2 ⌊2 * x⌋₊ * Real.log 2 ≤ Real.log 4 + Real.log N ∧
      max 1 (Nat.clog 2 ⌊2 * x⌋₊ * Real.log 2) ≤ 3 * Real.log N ∧
      ((Nat.clog 2 ⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ (3 + 1 / Real.log 2) * Real.log N := by
  set T := Nat.clog 2 ⌊2 * x⌋₊ with hTdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hn2 : 2 ≤ ⌊2 * x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hpow : (2 : ℝ) ^ T ≤ 4 * N := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0]; norm_num
      have : (1 : ℝ) ≤ N := by
        have := hx1.trans hxN; linarith
      linarith
    · have hp := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < ⌊2 * x⌋₊ by omega)
      rw [← hTdef] at hp
      have hp' : ((2 ^ T.pred : ℕ) : ℝ) < ⌊2 * x⌋₊ := by exact_mod_cast hp
      have hfl : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hj] at hp' ⊢
      simp only [Nat.pred_succ] at hp'
      push_cast at hp'
      rw [pow_succ]
      linarith
  have hN0 : (0 : ℝ) < N := by
    have := hx1.trans hxN; linarith
  have hlogT : T * Real.log 2 ≤ Real.log 4 + Real.log N := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) hN0.ne']
    exact Real.log_le_log (by positivity) hpow
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨hlogT, max_le (by linarith) (by linarith), ?_⟩
  push_cast
  have hT' : (T : ℝ) ≤ (Real.log 4 + Real.log N) / Real.log 2 := by
    rw [le_div_iff₀ hl2]; exact hlogT
  rw [hlog4, add_div, mul_div_assoc, div_self hl2.ne'] at hT'
  have : Real.log N / Real.log 2 = (1 / Real.log 2) * Real.log N := by ring
  rw [this] at hT'
  nlinarith

/-- One Heath Brown term with at most six variables and at most one logarithm is a
combination of at most 36 (T + 1) ^ k normalised blocks with coefficients at most 9.
Source: Heath Brown 1982 pages 1367 to 1368, Tolev 1999 page 71 Lemma 4. -/
theorem term_dec {k : ℕ} (hk2 : 2 ≤ k) (hk6 : k ≤ 6) (w : ℕ → ℂ) (N : ℕ) (x : ℝ)
    (hx : Real.exp 100000 ≤ x) (hxN : x ≤ N) (hN : 1 ≤ Real.log N)
    (U : ℕ) (hU : (U : ℝ) ≤ x ^ ((249 : ℝ) / 500))
    (κ : Fin k → Fin 3) (hκ : (univ.filter (fun i => κ i = 2)).card ≤ 1) :
    Dec w N x 9 (36 * (Nat.clog 2 ⌊2 * x⌋₊ + 1) ^ k)
      (annSum w N x (∏ i, kindFn U (κ i))) := by
  classical
  set T := Nat.clog 2 ⌊2 * x⌋₊ with hTdef
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp 100000; linarith
  have hT := (clog_bounds N hN x hx1 hxN).2.1
  rw [← hTdef] at hT
  have hsplit : annSum w N x (∏ i, kindFn U (κ i)) =
      annSum w N x (∏ i, ∑ e ∈ range (T + 1), dy (kindFn U (κ i)) e) := by
    apply annSum_congr
    intro n _ _ _ hn2
    apply prod_apply_congr
    intro i _ d _ hdn
    have hdT : d ≤ 2 ^ T := by
      have h1 : d ≤ ⌊2 * x⌋₊ := hdn.trans (Nat.le_floor hn2)
      exact h1.trans (Nat.le_pow_clog (by norm_num) _)
    exact (sum_dy_apply _ T d hdT).symm
  rw [hsplit, prod_univ_sum, annSum_sum]
  have hcard : (Fintype.piFinset (fun _ : Fin k => range (T + 1))).card = (T + 1) ^ k := by
    rw [Fintype.card_piFinset]; simp
  refine Dec_mono (n := (Fintype.piFinset (fun _ : Fin k => range (T + 1))).card * 36)
    (by rw [hcard, mul_comm]) le_rfl (Dec_sum _ _ (fun p hp => ?_))
  have he : ∀ i, p i ≤ T := by
    intro i
    have := Fintype.mem_piFinset.mp hp i
    exact Nat.lt_succ_iff.mp (mem_range.mp this)
  exact box_dec hk2 hk6 w N x hx U T hU κ p he hκ hT

theorem kindFn_zero (U : ℕ) : kindFn U 0 = LeanLab.HeathBrown1985.muLe U := by
  simp [kindFn]

theorem kindFn_one (U : ℕ) :
    kindFn U 1 = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  simp [kindFn]

theorem kindFn_two (U : ℕ) : kindFn U 2 = ArithmeticFunction.log := by
  simp [kindFn]

/-- The k equal to three Heath Brown polynomial as three products of kinds.
Source: Heath Brown 1982 page 1367 display 6. -/
theorem heathBrownPolynomial_eq (U : ℕ) :
    Sup83Heath.heathBrownPolynomial U =
      3 * (∏ i, kindFn U (![0, 2] i)) - 3 * (∏ i, kindFn U (![1, 0, 0, 2] i)) +
        ∏ i, kindFn U (![1, 1, 0, 0, 0, 2] i) := by
  simp only [Sup83Heath.heathBrownPolynomial, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, kindFn_zero, kindFn_one, kindFn_two]
  ring

/-- The whole Heath Brown polynomial on one shell is a combination of at most
108 (T + 1) ^ 6 normalised blocks with coefficients at most 27.
Source: Heath Brown 1982 pages 1367 to 1368, Tolev 1999 page 71 Lemma 4. -/
theorem hb_dec (w : ℕ → ℂ) (N : ℕ) (x : ℝ) (hx : Real.exp 100000 ≤ x) (hxN : x ≤ N)
    (hN : 1 ≤ Real.log N) :
    Dec w N x 27 (108 * (Nat.clog 2 ⌊2 * x⌋₊ + 1) ^ 6)
      (annSum w N x (Sup83Heath.heathBrownPolynomial ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊)) := by
  set U := ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊
  set T := Nat.clog 2 ⌊2 * x⌋₊
  have hx0 : 0 ≤ x := by linarith [Real.exp_pos 100000]
  have hU : (U : ℝ) ≤ x ^ ((249 : ℝ) / 500) := by
    obtain ⟨-, -, p3, -⟩ := Sup83Heath.source_parameters x hx
    have h1 : (U : ℝ) ≤ (2 * x) ^ ((1 : ℝ) / 3) := Nat.floor_le (by positivity)
    rw [Real.mul_rpow (by norm_num) hx0] at h1
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 ^ 30 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ 2 ^ 30 := by norm_num
    have h3 : 0 ≤ x ^ ((1 : ℝ) / 3) := by positivity
    nlinarith
  have hT1 : 1 ≤ T + 1 := by omega
  have D1 := term_dec (k := 2) (by norm_num) (by norm_num) w N x hx hxN hN U hU ![0, 2]
    (by decide)
  have D2 := term_dec (k := 4) (by norm_num) (by norm_num) w N x hx hxN hN U hU ![1, 0, 0, 2]
    (by decide)
  have D3 := term_dec (k := 6) (by norm_num) (by norm_num) w N x hx hxN hN U hU
    ![1, 1, 0, 0, 0, 2] (by decide)
  have hp2 : (T + 1) ^ 2 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_right hT1 (by norm_num)
  have hp4 : (T + 1) ^ 4 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_right hT1 (by norm_num)
  have heq : annSum w N x (Sup83Heath.heathBrownPolynomial U) =
      3 * annSum w N x (∏ i, kindFn U (![0, 2] i)) +
        (-3) * annSum w N x (∏ i, kindFn U (![1, 0, 0, 2] i)) +
        1 * annSum w N x (∏ i, kindFn U (![1, 1, 0, 0, 0, 2] i)) := by
    rw [heathBrownPolynomial_eq, sub_eq_add_neg, annSum_add, annSum_add, annSum_neg,
      annSum_three_mul, annSum_three_mul]
    ring
  rw [heq]
  have E1 := Dec_mul 3 D1
  have E2 := Dec_mul (-3) D2
  have E3 := Dec_mul 1 D3
  have h3 : ‖(3 : ℂ)‖ * 9 = 27 := by norm_num
  have h3' : ‖(-3 : ℂ)‖ * 9 = 27 := by norm_num
  have h1 : ‖(1 : ℂ)‖ * 9 ≤ 27 := by norm_num
  rw [h3] at E1
  rw [h3'] at E2
  have := Dec_add (Dec_add E1 E2) (Dec_mono le_rfl h1 E3)
  refine Dec_mono ?_ le_rfl this
  change 36 * (T + 1) ^ 2 + 36 * (T + 1) ^ 4 + 36 * (T + 1) ^ 6 ≤ 108 * (T + 1) ^ 6
  omega

/-- The grouped annular decomposition in block list form, with a general weight.
Source: Tolev 1999 page 71 Lemma 4 and page 83 displays 53 and 54, proved through
Heath Brown 1982 pages 1367 to 1368. -/
theorem grouped_blocks :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 3 ≤ X₀ ∧ ∀ N : ℕ, 1 ≤ Real.log N →
      ∀ x : ℝ, X₀ ≤ x → x ≤ N → ∀ w : ℕ → ℂ,
        ∃ n : ℕ, (n : ℝ) ≤ C * Real.log N ^ (6 : ℕ) ∧
          Dec w N x C n
            (annSum w N x (Sup83Heath.heathBrownPolynomial ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D := (3 + 1 / Real.log 2) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨27 + 108 * D ^ 6, Real.exp 100000, by positivity, ?_, ?_⟩
  · have := Real.add_one_le_exp 100000; linarith
  intro N hN x hx hxN w
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp 100000; linarith
  refine ⟨108 * (Nat.clog 2 ⌊2 * x⌋₊ + 1) ^ 6, ?_,
    Dec_mono le_rfl (by nlinarith [pow_nonneg hD0 6]) (hb_dec w N x hx hxN hN)⟩
  have hc := (clog_bounds N hN x hx1 hxN).2.2
  have hL0 : 0 ≤ Real.log N := by linarith
  have hp : (((Nat.clog 2 ⌊2 * x⌋₊ + 1 : ℕ) : ℝ)) ^ 6 ≤ (D * Real.log N) ^ 6 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hc 6
  push_cast at hp ⊢
  rw [mul_pow] at hp
  have h6 : 0 ≤ Real.log N ^ (6 : ℕ) := pow_nonneg hL0 6
  nlinarith [pow_nonneg hD0 6]

end LeanLab.Tolev2009.Sup83Group
