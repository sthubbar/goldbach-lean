module

public import LeanLab.Grimmelt2019.GaussBounds
public import LeanLab.BhowmikGrimmelt2026.PrimeGauss443
public import LeanLab.Linnik1951.GaussBound376
public import LeanLab.Linnik1951.Decomp280b

/-!
P0093 page 156 Lemma 1. Bridges from natural residues to Gauss sums.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset

/-- Page 156 Lemma 1. The displayed reduced residue sum is the standard Gauss sum. -/
theorem residue_gauss_eq470 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c *
      Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)) =
      gaussSum χ ZMod.stdAddChar := by
  classical
  unfold gaussSum
  rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases h : Nat.Coprime c q
  · rw [ite_eq_left h]
    congr 1
    rw [show (c : ZMod q) = ((c : ℤ) : ZMod q) by push_cast; rfl,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  · have hz : χ (c : ZMod q) = 0 :=
      MulChar.map_nonunit χ (by simpa only [ZMod.isUnit_iff_coprime] using h)
    simp [h, hz]

/-- Page 156 Lemma 1. The residue Gauss bound includes imprimitive characters. -/
theorem residue_gauss_sq_le470 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c *
      Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 ≤ (q : ℝ) := by
  rw [residue_gauss_eq470]
  exact gauss_norm_sq_le376 χ

/-- Page 156 Lemma 1. The principal residue Gauss sum has squared norm at most one. -/
theorem residue_gauss_principal470 (q : ℕ) [NeZero q] :
    ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ((1 : DirichletCharacter ℂ q) c) *
      Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 ≤ 1 := by
  rw [residue_gauss_eq470, LeanLab.Grimmelt2019.MainTerm.gaussSum_principal]
  have hcast : (ArithmeticFunction.moebius q : ℂ) =
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have h := ArithmeticFunction.abs_moebius_le_one (n := q)
  have h' : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
  have h0 : 0 ≤ |((ArithmeticFunction.moebius q : ℤ) : ℝ)| := abs_nonneg _
  nlinarith

/-- Page 155 equation 2.3. Regroup the character prime series by reduced residue. -/
theorem character_coset_expansion470 (N q : ℕ) [NeZero q] (hN : 1 ≤ N)
    (z : ℝ) (χ : DirichletCharacter ℂ q) :
    characterPrime280 χ N z = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
  classical
  let s := (range q).filter (fun b => Nat.Coprime b q)
  let f : Nat.Primes → ℂ := fun p => (Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
    Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)
  have hs0 (b : ℕ) : Summable (fun p : Nat.Primes =>
      if (p : ℕ) % q = b then f p else 0) := by
    have h := (prime_fourier_summable111 N hN z).indicator
      {p : Nat.Primes | (p : ℕ) % q = b}
    convert h using 1
    ext p
    simp only [f, Set.indicator_apply, Set.mem_ofPred_eq, neg_div]
  have hs (b : ℕ) : Summable (fun p : Nat.Primes => χ b *
      (if (p : ℕ) % q = b then f p else 0)) :=
    (hs0 b).mul_left (χ b)
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun b _ => hs b)]
  unfold characterPrime280
  apply tsum_congr
  intro p
  change χ (p : ℕ) * _ * _ = ∑ b ∈ s, χ b * (if (p : ℕ) % q = b then f p else 0)
  have hmod : χ ((p : ℕ) % q : ℕ) = χ (p : ℕ) := by
    rw [ZMod.natCast_mod]
  have hcop : Nat.Coprime ((p : ℕ) % q) q ↔ Nat.Coprime (p : ℕ) q := by
    change Nat.gcd ((p : ℕ) % q) q = 1 ↔ Nat.gcd (p : ℕ) q = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm q (p : ℕ)]
  by_cases hc : Nat.Coprime (p : ℕ) q
  · have hm : (p : ℕ) % q ∈ s := by
      simp only [s, mem_filter, mem_range]
      exact ⟨Nat.mod_lt _ (NeZero.pos q), hcop.mpr hc⟩
    rw [Finset.sum_eq_single ((p : ℕ) % q)]
    · simp only [ite_true, hmod]
      dsimp [f]
      rw [neg_div, mul_assoc]
    · intro b hb hne
      rw [ite_eq_right (Ne.symm hne), mul_zero]
    · exact fun h => (h hm).elim
  · have hz : χ (p : ℕ) = 0 := MulChar.map_nonunit χ
        (fun hu => hc ((ZMod.isUnit_iff_coprime _ _).mp hu))
    rw [hz, zero_mul, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hne : (p : ℕ) % q ≠ b := by
      intro he
      have hb' : Nat.Coprime b q := (mem_filter.mp hb).2
      rw [← he] at hb'
      exact hc (hcop.mp hb')
    rw [ite_eq_right hne, mul_zero]

/-- Page 155 equation 2.3. The negative additive twist of an inverse character. -/
theorem inverse_gauss_twist470 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) :
    (∑ v : ZMod q, ZMod.stdAddChar (-(v * (u : ZMod q))) * χ⁻¹ v) =
      star (gaussSum χ ZMod.stdAddChar) * χ (u : ZMod q) := by
  have hg : (∑ v : ZMod q, ZMod.stdAddChar (-(v * (u : ZMod q))) * χ⁻¹ v) =
      gaussSum χ⁻¹ (ZMod.stdAddChar⁻¹.mulShift (u : ZMod q)) := by
    unfold gaussSum
    apply Finset.sum_congr rfl
    intro v _
    rw [AddChar.mulShift_apply, AddChar.inv_apply]
    rw [mul_comm v (u : ZMod q), mul_comm]
  rw [hg, gaussSum_mulShift_eq χ⁻¹ (ZMod.stdAddChar⁻¹) u, inv_inv]
  rw [show gaussSum χ⁻¹ (ZMod.stdAddChar⁻¹) = star (gaussSum χ ZMod.stdAddChar) from
    (star_gaussSum_eq χ ZMod.stdAddChar).symm]
  exact mul_comm _ _

/-- Page 160 character orthogonality. The restricted additive transform has exact Gauss energy. -/
theorem unit_transform_energy470 (q : ℕ) [NeZero q] (G : ZMod q → ℂ)
    (hG : ∀ b, ¬ IsUnit b → G b = 0) :
    (∑ a : ZMod q, if IsUnit a then
      ‖∑ b : ZMod q, ZMod.stdAddChar (-(b * a)) * G b‖ ^ 2 else 0) =
      1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * ‖∑ b : ZMod q, χ b * G b‖ ^ 2 := by
  classical
  let T : ZMod q → ℂ := fun a => ∑ b : ZMod q, ZMod.stdAddChar (-(b * a)) * G b
  have ht (χ : DirichletCharacter ℂ q) :
      (∑ a : ZMod q, χ⁻¹ a * T a) =
        star (gaussSum χ ZMod.stdAddChar) * ∑ b : ZMod q, χ b * G b := by
    simp only [T, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : IsUnit b
    · have he := inverse_gauss_twist470 q χ hb.unit
      rw [hb.unit_spec] at he
      calc
        (∑ a : ZMod q, χ⁻¹ a * (ZMod.stdAddChar (-(b * a)) * G b)) =
            (∑ a : ZMod q, ZMod.stdAddChar (-(a * b)) * χ⁻¹ a) * G b := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a _
              rw [mul_comm b a]
              ring
        _ = _ := by rw [he]; ring
    · simp [hG b hb]
  have hp := LeanLab.PNTPort.LargeSieve.sum_chars_normSq T
  have hs : (∑ χ : DirichletCharacter ℂ q, ‖∑ a : ZMod q, χ a * T a‖ ^ 2) =
      ∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * ‖∑ b : ZMod q, χ b * G b‖ ^ 2 := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, ‖∑ a : ZMod q, χ⁻¹ a * T a‖ ^ 2 :=
        (Equiv.sum_comp (Equiv.inv (DirichletCharacter ℂ q))
          (fun χ => ‖∑ a : ZMod q, χ a * T a‖ ^ 2)).symm
      _ = _ := by simp_rw [ht, norm_mul, norm_star, mul_pow]
  rw [hs] at hp
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  change _ = 1 / (q.totient : ℝ) * _
  rw [hp]
  field_simp
  rfl

/-- Page 155 equation 2.3. Natural representatives give the negative product phase. -/
theorem negative_unit_phase470 (q : ℕ) [NeZero q] (a b : ℕ) :
    ZMod.stdAddChar (-((b : ZMod q) * (a : ZMod q))) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) := by
  rw [show (-((b : ZMod q) * (a : ZMod q))) = ((-(b * a) : ℤ) : ZMod q) by push_cast; ring,
    ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- Page 160 character orthogonality. Exact finite energy for arbitrary reduced residue weights. -/
theorem residue_transform_energy470 (q : ℕ) [NeZero q] (w : ℕ → ℂ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * w b‖ ^ 2) =
      1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
        ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c *
          Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 *
        ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * w b‖ ^ 2 := by
  classical
  let G : ZMod q → ℂ := fun x => if IsUnit x then w x.val else 0
  have hG : ∀ x, ¬ IsUnit x → G x = 0 := by intro x hx; simp [G, hx]
  have hC (χ : DirichletCharacter ℂ q) : (∑ x : ZMod q, χ x * G x) =
      ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * w b := by
    rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    have hm := Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
    by_cases hc : Nat.Coprime b q <;> simp [G, ZMod.isUnit_iff_coprime, hc, hm]
  have hT (a : ℕ) : (∑ x : ZMod q, ZMod.stdAddChar (-(x * (a : ZMod q))) * G x) =
      ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * w b := by
    rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    have hm := Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
    by_cases hc : Nat.Coprime b q
    · simp [G, ZMod.isUnit_iff_coprime, hm, negative_unit_phase470]
    · simp [G, ZMod.isUnit_iff_coprime, hc]
  have h := unit_transform_energy470 q G hG
  rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range] at h
  simp_rw [ZMod.isUnit_iff_coprime, hT, hC, ← residue_gauss_eq470] at h
  simpa only [Finset.sum_filter] using h

/-- Page 156 Lemma 1. A prime already dividing the smaller level forces the lifted Gauss sum to zero. -/
theorem residue_gauss_prime_lift_zero470 {m : ℕ} [NeZero m] (p : ℕ) (hp : p.Prime)
    (hpm : p ∣ m) (χ : DirichletCharacter ℂ m) :
    (∑ c ∈ (range (m * p)).filter (fun c => Nat.Coprime c (m * p)),
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m p) χ) c *
      Complex.exp (((2 * Real.pi * ((c : ℝ) / ((m * p : ℕ) : ℝ))) : ℝ) * Complex.I)) = 0 := by
  letI : NeZero (m * p) := ⟨mul_ne_zero (NeZero.ne m) hp.ne_zero⟩
  have hn : ¬ Nat.Coprime p m := by
    intro hc
    have hd : p ∣ Nat.gcd p m := Nat.dvd_gcd (dvd_refl p) hpm
    rw [hc.gcd_eq_one] at hd
    exact hp.ne_one (Nat.dvd_one.mp hd)
  have hz : χ (p : ZMod m) = 0 := MulChar.map_nonunit χ
    (fun hu => hn ((ZMod.isUnit_iff_coprime p m).mp hu))
  rw [residue_gauss_eq470, LeanLab.BhowmikGrimmelt2026.gaussSum_lift_prime443 p hp χ,
    hz, neg_zero, zero_mul]

/-- Page 156 Lemma 1. A nonprincipal imprimitive character modulo nine can have zero Gauss sum. -/
theorem nonprincipal_zero_gauss_nine470 :
    ∃ χ : DirichletCharacter ℂ 9, χ ≠ 1 ∧
      (∑ c ∈ (range 9).filter (fun c => Nat.Coprime c 9), χ c *
        Complex.exp (((2 * Real.pi * ((c : ℝ) / (9 : ℝ))) : ℝ) * Complex.I)) = 0 := by
  obtain ⟨ψ, hψ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    ℂ (a := (2 : ZMod 3)) (by decide)
  have hn : ψ ≠ 1 := by
    intro he
    subst ψ
    exact hψ (MulChar.one_apply (by decide))
  let hd : 3 ∣ 9 := by decide
  refine ⟨DirichletCharacter.changeLevel hd ψ, ?_, ?_⟩
  · exact fun he => hn ((DirichletCharacter.changeLevel_eq_one_iff hd).mp he)
  · exact residue_gauss_prime_lift_zero470 3 (by decide) (dvd_refl 3) ψ

end LeanLab.Linnik1951
