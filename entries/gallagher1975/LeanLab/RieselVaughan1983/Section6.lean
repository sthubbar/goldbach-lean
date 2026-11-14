module

public import LeanLab.RieselVaughan1983.Lemma7

/-!
P0032 Riesel-Vaughan 1983, Section 6, pages 58-59: the Cauchy-Schwarz count behind Lemma 8.
With `R(n)` the number of `p₁ + p₂ = n`, `3 ≤ p₁ ≤ u`, `3 ≤ p₂ ≤ x - u` primes, (6.1),
`(Σ R(n))² ≤ N(x) Σ R(n)²` and `Σ R(n)² = Σ R(n) + 2 ΣΣ_{p₁ < p₁'} #{…}`, so any bound
`#{p ≤ x : p, p + h prime} ≤ B·w(h)` gives `(Σ R)² ≤ N(x)(Σ R + 2 B T(u))`, which is
(6.3) with Lemma 5's `B = 8Cx/((log x)(A + log x))`.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.RieselVaughan1983
open LeanLab.SchnirelmannConstant

/-- The weight `Π_{p | h, p > 2} (p - 1)/(p - 2)` of Lemma 5 and (2.27). -/
noncomputable def wt (h : ℕ) : ℝ :=
  ∏ p ∈ h.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- (2.27): `T(u) = ΣΣ_{3 ≤ p₁ < p₂ ≤ u} Π_{p | p₂ - p₁, p > 2} (p - 1)/(p - 2)`. -/
noncomputable def Tu (u : ℕ) : ℝ :=
  ∑ a ∈ oddPrimes u, ∑ b ∈ (oddPrimes u).filter (a < ·), wt (b - a)

/-- The set counted by `N(x)` when `⌊x⌋ = n`. -/
noncomputable def Eset (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun k => Even k ∧ AtMostPrimes 2 k)

/-- The pairs `(p₁, p₂)` of (6.1). -/
def Pset (u n : ℕ) : Finset (ℕ × ℕ) := oddPrimes u ×ˢ oddPrimes (n - u)

lemma mem_oddPrimes {m p : ℕ} : p ∈ oddPrimes m ↔ 3 ≤ p ∧ p ≤ m ∧ p.Prime := by
  simp [oddPrimes, and_assoc]

lemma mem_Pset {u n : ℕ} {q : ℕ × ℕ} :
    q ∈ Pset u n ↔ q.1 ∈ oddPrimes u ∧ q.2 ∈ oddPrimes (n - u) := mem_product

lemma mem_Eset {n k : ℕ} : k ∈ Eset n ↔ (1 ≤ k ∧ k ≤ n) ∧ Even k ∧ AtMostPrimes 2 k := by
  unfold Eset; rw [mem_filter, mem_Icc]

lemma sum_mem_Eset {u n : ℕ} (hu : u ≤ n) {q : ℕ × ℕ} (hq : q ∈ Pset u n) :
    q.1 + q.2 ∈ Eset n := by
  rw [mem_Pset, mem_oddPrimes, mem_oddPrimes] at hq
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hq
  rw [mem_Eset]
  refine ⟨⟨by omega, by omega⟩, ?_, (AtMostPrimes.prime h3).add (AtMostPrimes.prime h6)⟩
  obtain ⟨a, ha⟩ := h3.odd_of_ne_two (by omega)
  obtain ⟨b, hb⟩ := h6.odd_of_ne_two (by omega)
  exact ⟨a + b + 1, by omega⟩

/-- `R(m)`, (6.1). -/
def Rn (u n m : ℕ) : ℕ := #((Pset u n).filter (fun q => q.1 + q.2 = m))

/-- The diagonal-free count: pairs of representations of the same number. -/
def Dset (u n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (Pset u n ×ˢ Pset u n).filter (fun z => z.1.1 + z.1.2 = z.2.1 + z.2.2)

lemma mem_Dset {u n : ℕ} {z : (ℕ × ℕ) × (ℕ × ℕ)} :
    z ∈ Dset u n ↔ (z.1 ∈ Pset u n ∧ z.2 ∈ Pset u n) ∧ z.1.1 + z.1.2 = z.2.1 + z.2.2 := by
  unfold Dset; rw [mem_filter, mem_product]

lemma sum_Rn (u n : ℕ) (hu : u ≤ n) : ∑ m ∈ Eset n, Rn u n m = #(Pset u n) :=
  (card_eq_sum_card_fiberwise (fun q hq => sum_mem_Eset hu hq)).symm

lemma sum_Rn_sq (u n : ℕ) (hu : u ≤ n) : ∑ m ∈ Eset n, Rn u n m ^ 2 = #(Dset u n) := by
  rw [card_eq_sum_card_fiberwise (f := fun z => z.1.1 + z.1.2) (t := Eset n)]
  · apply sum_congr rfl
    intro m _
    rw [Rn, sq, ← card_product]
    congr 1
    ext ⟨q, q'⟩
    simp only [mem_Dset, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨hq, hm⟩, hq', hm'⟩
      exact ⟨⟨⟨hq, hq'⟩, by omega⟩, hm⟩
    · rintro ⟨⟨⟨hq, hq'⟩, he⟩, hm⟩
      exact ⟨⟨hq, hm⟩, hq', by omega⟩
  · intro z hz
    rw [mem_coe, mem_Dset] at hz
    rw [mem_coe]
    exact sum_mem_Eset hu hz.1.1

/-- Cauchy's inequality, page 59: `(Σ R(n))² ≤ N(x) Σ R(n)²`. -/
lemma cauchy_R (u n : ℕ) (hu : u ≤ n) :
    ((#(Pset u n) : ℝ)) ^ 2 ≤ #(Eset n) * #(Dset u n) := by
  have h := sq_sum_le_card_mul_sum_sq (s := Eset n) (f := fun m => (Rn u n m : ℝ))
  have e1 : ∑ m ∈ Eset n, (Rn u n m : ℝ) = #(Pset u n) := by exact_mod_cast sum_Rn u n hu
  have e2 : ∑ m ∈ Eset n, (Rn u n m : ℝ) ^ 2 = #(Dset u n) := by exact_mod_cast sum_Rn_sq u n hu
  rw [e1, e2] at h
  exact h

/-- The triples `(p₁, p₁', p₂')` with `p₁ < p₁'` and `p₂' + (p₁' - p₁)` prime. -/
def Fset (u n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((oddPrimes u ×ˢ oddPrimes u) ×ˢ oddPrimes (n - u)).filter
    (fun t => t.1.1 < t.1.2 ∧ (t.2 + (t.1.2 - t.1.1)).Prime)

lemma mem_Fset {u n : ℕ} {t : (ℕ × ℕ) × ℕ} :
    t ∈ Fset u n ↔ ((t.1.1 ∈ oddPrimes u ∧ t.1.2 ∈ oddPrimes u) ∧ t.2 ∈ oddPrimes (n - u)) ∧
      t.1.1 < t.1.2 ∧ (t.2 + (t.1.2 - t.1.1)).Prime := by
  unfold Fset; rw [mem_filter, mem_product, mem_product]

/-- Page 59: `Σ R(n)² = Σ R(n) + 2 ΣΣ_{p₁ < p₁'} #{p₂' : p₂' + p₁' - p₁ prime}`, as `≤`. -/
lemma card_Dset_le (u n : ℕ) : #(Dset u n) ≤ #(Pset u n) + 2 * #(Fset u n) := by
  set D := Dset u n
  have hsplit : D ⊆ D.filter (fun z => z.1.1 = z.2.1) ∪ D.filter (fun z => z.1.1 < z.2.1) ∪
      D.filter (fun z => z.2.1 < z.1.1) := by
    intro z hz
    simp only [mem_union, mem_filter]
    rcases lt_trichotomy z.1.1 z.2.1 with h | h | h
    · exact Or.inl (Or.inr ⟨hz, h⟩)
    · exact Or.inl (Or.inl ⟨hz, h⟩)
    · exact Or.inr ⟨hz, h⟩
  have hdiag : #(D.filter (fun z => z.1.1 = z.2.1)) ≤ #(Pset u n) := by
    apply card_le_card_of_injOn (fun z => z.1)
    · intro z hz
      rw [mem_coe, mem_filter, mem_Dset] at hz
      exact hz.1.1.1
    · intro z hz w hw hzw
      rw [mem_coe, mem_filter, mem_Dset] at hz hw
      simp only at hzw
      obtain ⟨⟨_, hz1⟩, hz2⟩ := hz
      obtain ⟨⟨_, hw1⟩, hw2⟩ := hw
      have e1 : z.2.1 = w.2.1 := by rw [← hz2, ← hw2, hzw]
      have e2 : z.2.2 = w.2.2 := by
        have : z.1.1 + z.1.2 = w.1.1 + w.1.2 := by rw [hzw]
        omega
      exact Prod.ext hzw (Prod.ext e1 e2)
  have hlt : #(D.filter (fun z => z.1.1 < z.2.1)) ≤ #(Fset u n) := by
    apply card_le_card_of_injOn (fun z => ((z.1.1, z.2.1), z.2.2))
    · intro z hz
      rw [mem_coe, mem_filter, mem_Dset, mem_Pset, mem_Pset] at hz
      rw [mem_coe, mem_Fset]
      obtain ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, he⟩, hl⟩ := hz
      refine ⟨⟨⟨h1, h3⟩, h4⟩, hl, ?_⟩
      have : z.2.2 + (z.2.1 - z.1.1) = z.1.2 := by omega
      rw [this]
      exact (mem_oddPrimes.mp h2).2.2
    · intro z hz w hw hzw
      rw [mem_coe, mem_filter, mem_Dset] at hz hw
      simp only [Prod.mk.injEq] at hzw
      obtain ⟨⟨e1, e2⟩, e3⟩ := hzw
      obtain ⟨⟨_, hz1⟩, _⟩ := hz
      obtain ⟨⟨_, hw1⟩, _⟩ := hw
      have e4 : z.1.2 = w.1.2 := by omega
      exact Prod.ext (Prod.ext e1 e4) (Prod.ext e2 e3)
  have hgt : #(D.filter (fun z => z.2.1 < z.1.1)) = #(D.filter (fun z => z.1.1 < z.2.1)) := by
    apply card_bij (fun z _ => (z.2, z.1))
    · intro z hz
      rw [mem_filter, mem_Dset] at hz ⊢
      exact ⟨⟨⟨hz.1.1.2, hz.1.1.1⟩, hz.1.2.symm⟩, hz.2⟩
    · intro z _ w _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro w hw
      refine ⟨(w.2, w.1), ?_, rfl⟩
      rw [mem_filter, mem_Dset] at hw ⊢
      exact ⟨⟨⟨hw.1.1.2, hw.1.1.1⟩, hw.1.2.symm⟩, hw.2⟩
  have := card_le_card hsplit
  have := card_union_le (D.filter (fun z => z.1.1 = z.2.1) ∪ D.filter (fun z => z.1.1 < z.2.1))
    (D.filter (fun z => z.2.1 < z.1.1))
  have := card_union_le (D.filter (fun z => z.1.1 = z.2.1)) (D.filter (fun z => z.1.1 < z.2.1))
  omega

/-- `#F ≤ B·T(u)` from a Lemma 5 type bound for the shifts `h = p₁' - p₁`. -/
lemma card_Fset_le (u n : ℕ) (B : ℝ)
    (hB : ∀ h : ℕ, 0 < h → (#((Icc 1 n).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      B * wt h) :
    (#(Fset u n) : ℝ) ≤ B * Tu u := by
  -- fibre over the pair `(p₁, p₁')`
  have hfib := card_eq_sum_card_fiberwise (s := Fset u n) (t := (oddPrimes u ×ˢ oddPrimes u).filter
    (fun ab => ab.1 < ab.2)) (f := fun t => t.1) (by
      intro t ht
      rw [mem_coe, mem_Fset] at ht
      rw [mem_coe, mem_filter, mem_product]
      exact ⟨⟨ht.1.1.1, ht.1.1.2⟩, ht.2.1⟩)
  rw [hfib]
  push_cast
  have hfibre : ∀ ab ∈ (oddPrimes u ×ˢ oddPrimes u).filter (fun ab => ab.1 < ab.2),
      (#((Fset u n).filter (fun t => t.1 = ab)) : ℝ) ≤ B * wt (ab.2 - ab.1) := by
    intro ab hab
    simp only [mem_filter, mem_product] at hab
    refine le_trans ?_ (hB (ab.2 - ab.1) (by omega))
    have : #((Fset u n).filter (fun t => t.1 = ab)) ≤
        #((Icc 1 n).filter (fun p => p.Prime ∧ (p + (ab.2 - ab.1)).Prime)) := by
      apply card_le_card_of_injOn (fun t => t.2)
      · intro t ht
        rw [mem_coe, mem_filter, mem_Fset] at ht
        rw [mem_coe, mem_filter, mem_Icc]
        obtain ⟨⟨⟨⟨_, _⟩, h2⟩, _, h3⟩, rfl⟩ := ht
        obtain ⟨g1, g2, g3⟩ := mem_oddPrimes.mp h2
        dsimp only
        exact ⟨⟨by omega, by omega⟩, g3, h3⟩
      · intro t ht w hw h
        rw [mem_coe, mem_filter] at ht hw
        exact Prod.ext (ht.2.trans hw.2.symm) h
    exact_mod_cast this
  calc ∑ ab ∈ (oddPrimes u ×ˢ oddPrimes u).filter (fun ab => ab.1 < ab.2),
        (#((Fset u n).filter (fun t => t.1 = ab)) : ℝ)
      ≤ ∑ ab ∈ (oddPrimes u ×ˢ oddPrimes u).filter (fun ab => ab.1 < ab.2),
        B * wt (ab.2 - ab.1) := sum_le_sum hfibre
    _ = B * Tu u := by
      rw [← mul_sum, Tu, sum_filter, sum_product]
      congr 1
      apply sum_congr rfl
      intro a _
      rw [sum_filter]

/-- (6.3), page 59, in the form `(Σ R)² ≤ N(x)(Σ R + 2B T(u))`. -/
theorem eq63 (u n : ℕ) (hu : u ≤ n) (B : ℝ)
    (hB : ∀ h : ℕ, 0 < h → (#((Icc 1 n).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      B * wt h) :
    ((#(Pset u n) : ℝ)) ^ 2 ≤ #(Eset n) * (#(Pset u n) + 2 * (B * Tu u)) := by
  have h1 := cauchy_R u n hu
  have h2 : (#(Dset u n) : ℝ) ≤ #(Pset u n) + 2 * #(Fset u n) := by
    exact_mod_cast card_Dset_le u n
  have h3 := card_Fset_le u n B hB
  have hE : (0 : ℝ) ≤ #(Eset n) := Nat.cast_nonneg _
  calc ((#(Pset u n) : ℝ)) ^ 2 ≤ #(Eset n) * #(Dset u n) := h1
    _ ≤ #(Eset n) * (#(Pset u n) + 2 * (B * Tu u)) := by
      apply mul_le_mul_of_nonneg_left _ hE
      linarith

/-- Page 59, from (6.3) to `N(x) ≥ α²s²/(αs + βt)`: if `0 ≤ a ≤ Σ R` and `T(u) ≤ t`, then
`a² ≤ N(x)(a + 2Bt)`. The paper's chain `αs(αs - N) ≤ αs(ΣR - N) ≤ ΣR(ΣR - N)` needs
`ΣR ≥ N` for its second step; when `ΣR < N` the conclusion holds directly. -/
theorem key_ineq {P N a B T t : ℝ} (hP : P ^ 2 ≤ N * (P + 2 * (B * T))) (ha : 0 ≤ a)
    (haP : a ≤ P) (hN : 0 ≤ N) (hB : 0 ≤ B) (hT0 : 0 ≤ T) (hT : T ≤ t) :
    a ^ 2 ≤ N * (a + 2 * B * t) := by
  have hBT : B * T ≤ B * t := mul_le_mul_of_nonneg_left hT hB
  have hNBT : 0 ≤ N * (B * T) := mul_nonneg hN (mul_nonneg hB hT0)
  have hNB : N * (B * T) ≤ N * (B * t) := mul_le_mul_of_nonneg_left hBT hN
  by_cases haN : a ≤ N
  · -- `a² ≤ aN`
    have : a * a ≤ a * N := mul_le_mul_of_nonneg_left haN ha
    nlinarith
  · push Not at haN
    -- `a(a - N) ≤ P(P - N) ≤ 2NBT`, as `z(z - N)` increases for `z ≥ N/2`
    have : a * (a - N) ≤ P * (P - N) := by nlinarith
    nlinarith

end LeanLab.RieselVaughan1983
