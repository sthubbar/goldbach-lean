module

public import Mathlib
public import LeanLab.PNTPort.LargeSieve.PrimeSieve

/-!
# The multiplicative large sieve

Lab proof, unit U-5000. AI wrote this file. Known mathematics, the Bombieri and Davenport
form, no cited input. Uses Mathlib's Gauss sums for primitive Dirichlet characters.

* `normSq_gaussSum_of_isPrimitive`: `‖τ(χ)‖² = q` for a primitive character mod `q`.
* `sum_chars_normSq`: `∑_χ ‖∑_x χ(x) S(x)‖² = φ(q) ∑_{x unit} ‖S(x)‖²`.
* `multiplicative_large_sieve`:
  `∑_{q ≤ Q} q/φ(q) ∑_{χ primitive mod q} ‖∑_{M<n≤M+N} a_n χ(n)‖² ≤ (N + 2Q²) ∑ ‖a_n‖²`.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

noncomputable instance (q : ℕ) :
    DecidablePred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) := Classical.decPred _

section ZModSums

variable {q : ℕ} [NeZero q]

lemma sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    ∑ x : ZMod q, f x = ∑ c ∈ range q, f (c : ZMod q) := by
  refine sum_nbij' (fun x => x.val) (fun c => (c : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro x _; rw [mem_range]; exact ZMod.val_lt x
  · intro c _; exact mem_coe.2 (mem_univ _)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro c hc; rw [mem_range] at hc; exact ZMod.val_natCast_of_lt hc
  · intro x _; rw [ZMod.natCast_zmod_val]

lemma stdAddChar_mul_natCast (n : ℤ) (c : ℕ) :
    ZMod.stdAddChar ((n : ZMod q) * (c : ZMod q)) = e (n * (c / q)) := by
  rw [show (n : ZMod q) * (c : ZMod q) = ((n * c : ℤ) : ZMod q) by push_cast; ring,
    ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

lemma norm_stdAddChar (z : ZMod q) : ‖ZMod.stdAddChar z‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma conj_stdAddChar (z : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_stdAddChar z)]

/-- `‖χ x‖² = 1` on units and `0` off them. -/
lemma normSq_char (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖χ x‖ ^ 2 = if IsUnit x then 1 else 0 := by
  split_ifs with hx
  · rw [show x = (hx.unit : ZMod q) from hx.unit_spec.symm, DirichletCharacter.unit_norm_eq_one]
    norm_num
  · rw [MulChar.map_nonunit _ hx, norm_zero]; norm_num

lemma sum_isUnit_eq_totient :
    ∑ x : ZMod q, (if IsUnit x then (1 : ℝ) else 0) = q.totient := by
  rw [sum_zmod_eq_sum_range, Nat.totient, ← sum_boole]
  push_cast
  apply sum_congr rfl
  intro c _
  by_cases h : Nat.Coprime c q
  · rw [if_pos ((ZMod.isUnit_iff_coprime c q).2 h), if_pos (Nat.coprime_comm.1 h)]
  · rw [if_neg (fun h' => h ((ZMod.isUnit_iff_coprime c q).1 h')),
      if_neg (fun h' => h (Nat.coprime_comm.1 h'))]

lemma sum_normSq_char (χ : DirichletCharacter ℂ q) :
    ∑ x : ZMod q, ‖χ x‖ ^ 2 = q.totient := by
  simp_rw [normSq_char]
  exact sum_isUnit_eq_totient

omit [NeZero q] in
lemma conj_char_of_isUnit (χ : DirichletCharacter ℂ q) {y : ZMod q} (hy : IsUnit y) :
    (starRingEnd ℂ) (χ y) = χ y⁻¹ := by
  have h1 : ‖χ y‖ = 1 := by
    rw [show y = (hy.unit : ZMod q) from hy.unit_spec.symm, DirichletCharacter.unit_norm_eq_one]
  rw [← Complex.inv_eq_conj h1]
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul, ZMod.mul_inv_of_unit y hy, map_one]

lemma conj_char_eq_inv (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    (starRingEnd ℂ) (χ n) = χ⁻¹ n := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases hn : IsUnit n
  · have h1 : ‖χ n‖ = 1 := by
      rw [show n = (hn.unit : ZMod q) from hn.unit_spec.symm,
        DirichletCharacter.unit_norm_eq_one]
    exact (Complex.inv_eq_conj h1).symm
  · rw [MulChar.map_nonunit _ hn, inv_zero, map_zero]

end ZModSums

section Gauss

variable {q : ℕ} [NeZero q]

/-- `‖τ(χ)‖² = q` for a primitive Dirichlet character. -/
theorem normSq_gaussSum_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = q := by
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  set τ := gaussSum χ ψ
  -- first count
  have h1 : ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 = ‖τ‖ ^ 2 * q.totient := by
    simp_rw [gaussSum_mulShift_of_isPrimitive ψ hχ, norm_mul, mul_pow]
    rw [← sum_mul, sum_normSq_char χ⁻¹, mul_comm]
  -- second count
  have h2 : ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 = q * q.totient := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [← Complex.ofReal_pow]
    unfold gaussSum
    simp_rw [ofReal_normSq_sum, AddChar.mulShift_apply]
    have hc : ∀ z, (starRingEnd ℂ) (ψ z) = ψ (-z) := fun z => conj_stdAddChar z
    have hexp : ∀ a x y : ZMod q, χ x * ψ (a * x) * (starRingEnd ℂ) (χ y * ψ (a * y)) =
        χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) := by
      intro a x y
      rw [(starRingEnd ℂ).map_mul, hc, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp_rw [hexp]
    rw [sum_comm]
    refine (sum_congr rfl (fun x _ => sum_comm)).trans ?_
    have hsum : ∀ x y : ZMod q, ∑ a : ZMod q, χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) =
        if x = y then (q : ℂ) * (χ x * (starRingEnd ℂ) (χ x)) else 0 := by
      intro x y
      rw [← mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
      by_cases hxy : x = y
      · rw [if_pos (sub_eq_zero.2 hxy), if_pos hxy, hxy]; ring
      · rw [if_neg (fun h => hxy (sub_eq_zero.1 h)), if_neg hxy, Nat.cast_zero, mul_zero]
    simp_rw [hsum, sum_ite_eq, mem_univ, if_true]
    rw [← mul_sum]
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [← Complex.ofReal_sum, sum_normSq_char]
    norm_cast
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have := h1.symm.trans h2
  exact mul_right_cancel₀ hφ.ne' this

/-- Orthogonality over all characters mod `q`. -/
theorem sum_chars_normSq (S : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ x : ZMod q, χ x * S x‖ ^ 2 =
      q.totient * ∑ x : ZMod q, (if IsUnit x then ‖S x‖ ^ 2 else 0) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.ofReal_pow, ofReal_normSq_sum]
  have horth : ∀ x y : ZMod q, ∑ χ : DirichletCharacter ℂ q,
      χ x * S x * (starRingEnd ℂ) (χ y * S y) =
      if x = y then (if IsUnit x then (q.totient : ℂ) * (S x * (starRingEnd ℂ) (S x)) else 0)
        else 0 := by
    intro x y
    by_cases hy : IsUnit y
    · have : ∀ χ : DirichletCharacter ℂ q, χ x * S x * (starRingEnd ℂ) (χ y * S y) =
          (χ y⁻¹ * χ x) * (S x * (starRingEnd ℂ) (S y)) := by
        intro χ; rw [map_mul, conj_char_of_isUnit χ hy]; ring
      simp_rw [this]
      rw [← sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hy x]
      by_cases hxy : y = x
      · subst hxy; rw [if_pos rfl, if_pos rfl, if_pos hy]
      · rw [if_neg hxy, if_neg (fun h => hxy h.symm), zero_mul]
    · have : (if x = y then (if IsUnit x then (q.totient : ℂ) * (S x * (starRingEnd ℂ) (S x))
          else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · exact absurd (h1 ▸ h2) hy
        · rfl
        · rfl
      rw [this]
      apply sum_eq_zero
      intro χ _
      rw [MulChar.map_nonunit _ hy, zero_mul, map_zero, mul_zero]
  rw [sum_comm]
  refine (sum_congr rfl (fun x _ => sum_comm)).trans ?_
  simp_rw [horth]
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  rw [sum_ite_eq]
  simp only [mem_univ, if_true]
  by_cases hx : IsUnit x
  · rw [if_pos hx, if_pos hx, Complex.mul_conj', Complex.ofReal_pow]
  · rw [if_neg hx, if_neg hx, Complex.ofReal_zero, mul_zero]

end Gauss

/-- The large sieve for one modulus, over primitive characters. -/
theorem prim_chars_le {q : ℕ} [NeZero q] (I : Finset ℤ) (a : ℤ → ℂ) :
    (q : ℝ) / q.totient * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => χ.IsPrimitive), ‖∑ n ∈ I, a n * χ n‖ ^ 2 ≤
      ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
        ‖∑ n ∈ I, (starRingEnd ℂ) (a n) * e (n * (c / q))‖ ^ 2 := by
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  set b : ℤ → ℂ := fun n => (starRingEnd ℂ) (a n)
  set S : ZMod q → ℂ := fun x => ∑ n ∈ I, b n * ψ ((n : ZMod q) * x)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  -- each primitive character
  have hprim : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      (q : ℝ) * ‖∑ n ∈ I, a n * χ n‖ ^ 2 = ‖∑ x : ZMod q, χ x * S x‖ ^ 2 := by
    intro χ hχ
    have hT : ∑ x : ZMod q, χ x * S x =
        (∑ n ∈ I, b n * χ⁻¹ (n : ZMod q)) * gaussSum χ ψ := by
      rw [sum_mul]
      simp_rw [mul_assoc, ← gaussSum_mulShift_of_isPrimitive ψ hχ]
      unfold gaussSum
      simp_rw [AddChar.mulShift_apply, S, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl; intro n _
      apply sum_congr rfl; intro x _
      ring
    have hb : ‖∑ n ∈ I, b n * χ⁻¹ (n : ZMod q)‖ = ‖∑ n ∈ I, a n * χ n‖ := by
      rw [← Complex.norm_conj, map_sum]
      congr 1
      apply sum_congr rfl; intro n _
      rw [map_mul, ← conj_char_eq_inv, Complex.conj_conj, Complex.conj_conj]
    rw [hT, norm_mul, mul_pow, normSq_gaussSum_of_isPrimitive hχ, hb, mul_comm]
  have h1 : (q : ℝ) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
      (fun χ => χ.IsPrimitive), ‖∑ n ∈ I, a n * χ n‖ ^ 2 ≤
      q.totient * ∑ x : ZMod q, (if IsUnit x then ‖S x‖ ^ 2 else 0) := by
    rw [mul_sum, ← sum_chars_normSq S]
    rw [sum_congr rfl (fun χ hχ => hprim χ (mem_filter.1 hχ).2)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have h2 : ∑ x : ZMod q, (if IsUnit x then ‖S x‖ ^ 2 else 0) =
      ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
        ‖∑ n ∈ I, b n * e (n * (c / q))‖ ^ 2 := by
    rw [sum_zmod_eq_sum_range, sum_filter]
    apply sum_congr rfl; intro c _
    by_cases h : c.Coprime q
    · rw [if_pos ((ZMod.isUnit_iff_coprime c q).2 h), if_pos h]
      simp only [S, stdAddChar_mul_natCast, ψ]
    · rw [if_neg (fun h' => h ((ZMod.isUnit_iff_coprime c q).1 h')), if_neg h]
  rw [h2] at h1
  rw [div_mul_eq_mul_div, div_le_iff₀ hφ, mul_comm _ (q.totient : ℝ)]
  exact h1

/-- **The multiplicative large sieve**, constant `N + 2Q²`. The modulus `k + 1` runs over
`1, …, Q`. -/
theorem multiplicative_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  set I := Ioc M (M + N)
  set b : ℤ → ℂ := fun n => (starRingEnd ℂ) (a n)
  set f : ℕ × ℕ → ℝ := fun p => ‖∑ n ∈ I, b n * e (n * fareyPt p)‖ ^ 2
  have h1 := sum_le_sum (fun k (_ : k ∈ range Q) => prim_chars_le (q := k + 1) I a)
  refine h1.trans ?_
  -- regroup the Farey sum by denominator
  have h2 : ∑ k ∈ range Q, ∑ c ∈ (range (k + 1)).filter (fun c => Nat.Coprime c (k + 1)),
      ‖∑ n ∈ I, (starRingEnd ℂ) (a n) * e (n * (c / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 =
      ∑ p ∈ farey Q, f p := by
    set T : Finset (ℕ × ℕ) := (range Q).biUnion (fun k =>
      ((range (k + 1)).filter (fun c => Nat.Coprime c (k + 1))).map
        ⟨fun c => (k + 1, c), fun c c' h => by simpa using h⟩) with hT
    have hTeq : T = farey Q := by
      ext ⟨q, c⟩
      rw [hT, mem_biUnion, mem_farey]
      constructor
      · rintro ⟨k, hk, hx⟩
        rw [mem_map] at hx
        obtain ⟨c', hc', h⟩ := hx
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (h : (k + 1, c') = (q, c))
        rw [mem_filter, mem_range] at hc'
        rw [mem_range] at hk
        exact ⟨by omega, by omega, hc'.1, hc'.2⟩
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨q - 1, by rw [mem_range]; omega, ?_⟩
        rw [mem_map]
        refine ⟨c, ?_, ?_⟩
        · rw [mem_filter, mem_range, show q - 1 + 1 = q by omega]; exact ⟨h3, h4⟩
        · show (q - 1 + 1, c) = (q, c)
          rw [show q - 1 + 1 = q by omega]
    rw [← hTeq, hT, sum_biUnion]
    · apply sum_congr rfl; intro k _
      rw [sum_map]
      apply sum_congr rfl; intro c _
      rfl
    · intro k _ k' _ hne
      refine disjoint_left.2 ?_
      intro x hx hx'
      rw [mem_map] at hx hx'
      obtain ⟨c, _, rfl⟩ := hx
      obtain ⟨c', _, h⟩ := hx'
      have : k' + 1 = k + 1 := congrArg Prod.fst h
      exact hne (by omega)
  rw [h2]
  have h3 := farey_large_sieve hQ b M N
  have h4 : ∑ n ∈ I, ‖b n‖ ^ 2 = ∑ n ∈ I, ‖a n‖ ^ 2 := by
    apply sum_congr rfl; intro n _; simp only [b, Complex.norm_conj]
  rw [h4] at h3
  exact h3

end LeanLab.PNTPort.LargeSieve
