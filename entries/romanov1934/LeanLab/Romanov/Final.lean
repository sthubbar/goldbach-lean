module

public import LeanLab.Romanov.Theorem

/-!
# Romanov's theorem, the assembly

Lab proof, unit U-5602, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics,
Romanov 1934. No cited input. Binary Goldbach is OPEN; this is the Linnik-Goldbach line, IDEAS
I-5052.

* `romanov_dyadic`: an absolute `c > 0` such that for every `L ≥ 2` at least `c · 2^(L+2)`
  numbers below `2^(L+2)` are of the form `p + 2^k`, `p` prime.
* `romanov`: an absolute `c > 0` such that for every `x ≥ 16` at least `c x` numbers below `x`
  are of the form `p + 2^k`: the numbers `p + 2^k` have positive lower density. PROVED.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset Real

lemma add_two_le_two_pow (L : ℕ) (hL : 2 ≤ L) : L + 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

/-- The dyadic form of Romanov's theorem. -/
theorem romanov_dyadic : ∃ c : ℝ, 0 < c ∧ ∀ L : ℕ, 2 ≤ L → ∃ I : Finset ℕ,
    (∀ n ∈ I, n < 2 ^ (L + 2) ∧ ∃ p k : ℕ, p.Prime ∧ n = p + 2 ^ k) ∧
    c * 2 ^ (L + 2) ≤ #I := by
  have hR := R₁_pos
  refine ⟨1 / (8 * (1 + 8 * R₁)), by positivity, fun L hL => ?_⟩
  set N := 2 ^ (L + 1) with hNdef
  set A := Nat.primesBelow (N + 1) with hAdef
  set P := Nat.primesBelow (2 ^ (L + 2)) with hPdef
  set T := A ×ˢ range L with hTdef
  refine ⟨T.image f, fun n hn => ?_, ?_⟩
  · rw [mem_image] at hn
    obtain ⟨⟨p, k⟩, hpk, rfl⟩ := hn
    rw [hTdef, mem_product, hAdef, Nat.mem_primesBelow, mem_range] at hpk
    obtain ⟨⟨hp, hpr⟩, hk⟩ := hpk
    refine ⟨?_, p, k, hpr, rfl⟩
    have h1 : 2 ^ k < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) hk
    have h2 : 2 ^ (L + 2) = 4 * 2 ^ L := by ring
    have h3 : N = 2 * 2 ^ L := by rw [hNdef]; ring
    simp only [f] at hp hk hpr ⊢
    omega
  · have hP : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
    have hA : ∀ p ∈ A, p < N + 1 ∧ p ∈ P := by
      intro p hp
      rw [hAdef, Nat.mem_primesBelow] at hp
      refine ⟨hp.1, ?_⟩
      rw [hPdef, Nat.mem_primesBelow]
      refine ⟨?_, hp.2⟩
      have h2 : 2 ^ (L + 2) = 4 * 2 ^ L := by ring
      have h3 : N = 2 * 2 ^ L := by rw [hNdef]; ring
      have h4 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      omega
    have hcs := card_sq_le T
    have hcoll := coll_le A P (N + 1) L hA
    have hQ := Q_le P hP L (by omega)
    have hT : #T = #A * L := by rw [hTdef, card_product, card_range]
    have hAc : #A = Nat.primeCounting N := by
      rw [hAdef, Nat.primesBelow_card_eq_primeCounting']; rfl
    -- the lower bound for `#T`
    have hNr : ((N : ℕ) : ℝ) = (2 : ℝ) ^ ((L : ℝ) + 1) := by
      rw [hNdef]; push_cast
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    have hpow : (L : ℝ) + 2 ≤ (2 : ℝ) ^ (L : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast add_two_le_two_pow L hL
    have hS := S_ge (L : ℝ) N (by exact_mod_cast hL) hNr hpow
    -- real bookkeeping
    set S : ℝ := (#T : ℝ) with hSdef
    set X : ℝ := (#(T.image f) : ℝ) with hXdef
    have hSeq : S = (Nat.primeCounting N : ℝ) * L := by
      rw [hSdef, hT, hAc]; push_cast; ring
    have hS4 : (N : ℝ) / 4 ≤ S := hSeq ▸ hS
    have hN0 : (0 : ℝ) < N := by rw [hNdef]; positivity
    have hS0 : 0 < S := by linarith
    have hE : (coll T : ℝ) ≤ S + 2 * (R₁ * N) := by
      have h1 : (coll T : ℝ) ≤ ((L * #A + 2 * ∑ k ∈ range L, ∑ k' ∈ range L,
          if k < k' then gap P (2 ^ k' - 2 ^ k) (N + 1) else 0 : ℕ) : ℝ) := by
        exact_mod_cast hcoll
      push_cast at h1
      have hQ' : ((∑ k ∈ range L, ∑ k' ∈ range L,
          if k < k' then gap P (2 ^ k' - 2 ^ k) (N + 1) else 0 : ℕ) : ℝ) ≤ R₁ * N := by
        have e : ((N : ℕ) : ℝ) = (2 : ℝ) ^ (L + 1) := by rw [hNdef]; push_cast; ring
        rw [e]; exact hQ
      push_cast at hQ'
      have : (L : ℝ) * #A = S := by rw [hSdef, hT]; push_cast; ring
      linarith
    have hcsr : S ^ 2 ≤ X * coll T := by
      rw [hSdef, hXdef]; exact_mod_cast hcs
    have hX0 : 0 ≤ X := Nat.cast_nonneg _
    have hmain : S ≤ X * (1 + 8 * R₁) := by
      have h1 : S ^ 2 ≤ X * (S + 2 * (R₁ * N)) :=
        le_trans hcsr (mul_le_mul_of_nonneg_left hE hX0)
      have h2 : X * (S + 2 * (R₁ * N)) ≤ X * (S * (1 + 8 * R₁)) := by
        apply mul_le_mul_of_nonneg_left _ hX0
        nlinarith
      have h3 : S * S ≤ S * (X * (1 + 8 * R₁)) := by nlinarith
      exact le_of_mul_le_mul_left h3 hS0
    have h22 : ((2 : ℝ) ^ (L + 2)) = 2 * N := by rw [hNdef]; push_cast; ring
    rw [h22]
    have hd : 0 < 1 + 8 * R₁ := by linarith
    calc 1 / (8 * (1 + 8 * R₁)) * (2 * (N : ℝ)) = (N / 4) / (1 + 8 * R₁) := by
          field_simp; ring
      _ ≤ S / (1 + 8 * R₁) := div_le_div_of_nonneg_right hS4 hd.le
      _ ≤ X := by rw [div_le_iff₀ hd]; exact hmain

/-- **Romanov's theorem**: the numbers `p + 2^k` have positive lower density. -/
theorem romanov : ∃ c : ℝ, 0 < c ∧ ∀ x : ℕ, 16 ≤ x → ∃ I : Finset ℕ,
    (∀ n ∈ I, n < x ∧ ∃ p k : ℕ, p.Prime ∧ n = p + 2 ^ k) ∧ c * x ≤ #I := by
  obtain ⟨c, hc, h⟩ := romanov_dyadic
  refine ⟨c / 2, by positivity, fun x hx => ?_⟩
  set j := Nat.log 2 x with hj
  have hx0 : x ≠ 0 := by omega
  have hj4 : 4 ≤ j := by
    rw [hj]
    exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hlo : 2 ^ j ≤ x := Nat.pow_log_le_self 2 hx0
  have hhi : x < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  obtain ⟨I, hI, hcard⟩ := h (j - 2) (by omega)
  have hj2 : j - 2 + 2 = j := by omega
  rw [hj2] at hI hcard
  refine ⟨I, fun n hn => ⟨lt_of_lt_of_le (hI n hn).1 hlo, (hI n hn).2⟩, ?_⟩
  have hhi' : (x : ℝ) < 2 * 2 ^ j := by
    have : x < 2 * 2 ^ j := by rw [pow_succ] at hhi; omega
    exact_mod_cast this
  nlinarith

end LeanLab.Romanov
