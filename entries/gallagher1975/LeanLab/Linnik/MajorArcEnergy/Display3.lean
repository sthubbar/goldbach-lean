module

public import LeanLab.Linnik.MajorArcEnergy.Leaves13

/-!
Gallagher 1975 P0094 p.128, from the first display through display 3.
The major arc integral of |S|^2 e(n alpha) equals the sum of the pair sums J_n(chi, chi')
over primitive characters to conductors at most P, up to O(P^(5/2)).
Proved from the proved first character expansion hExpansion and Chebyshev's bound
for pi(N), along Gallagher's own derivation: (a) the disjoint arc decomposition,
(b) the per arc replacement of |S|^2 by |M|^2, (c) the sum over a and the reindexing of
characters mod q by their primitive characters, (d) the error sum.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries ramanujanSum)
open LeanLab.Linnik.U7204 (Sg)
open LeanLab.PNTPort.LargeSieve (e_add norm_e e_int)

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-! ### Characters, p.128 -/

/-- Gallagher 1975 p.128: a primitive character agrees with its own primitive character
at every integer. -/
theorem primitiveCharacter_apply_of_isPrimitive {m : ℕ} {χ : DirichletCharacter ℂ m}
    (hχ : χ.IsPrimitive) (a : ℤ) : χ.primitiveCharacter a = χ a := by
  by_cases ha : IsCoprime a m
  · exact DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ ha
  · have h1 : χ a = 0 := (DirichletCharacter.apply_eq_zero_iff χ a).mpr ha
    have h2 : χ.primitiveCharacter a = 0 := by
      rw [DirichletCharacter.apply_eq_zero_iff]
      rwa [show χ.conductor = m from hχ]
    rw [h1, h2]

/-- Gallagher 1975 p.128: A(chi*, beta) for chi = chi_q induced by a primitive chi is
A(chi, beta), since chi* = chi. -/
theorem primeAmplitude_induced {x : PChar} (hx : x.2.IsPrimitive) {q : ℕ} (hq : 1 ≤ q)
    (h : x.1 + 1 ∣ q) (N : ℕ) (β : ℝ) :
    primeAmplitude (induced x q).primitiveCharacter N β = primeAmplitude x.2 N β := by
  have : NeZero q := ⟨by omega⟩
  unfold primeAmplitude
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  have hind : induced x q = DirichletCharacter.changeLevel h x.2 := by
    unfold induced; simp only [h, ↓reduceDIte]
  have h1 := DirichletCharacter.primitiveCharacter_changeLevel_apply h x.2 (p : ℤ)
  have h2 := primitiveCharacter_apply_of_isPrimitive hx (p : ℤ)
  rw [hind]
  simpa only [Int.cast_natCast] using h1.trans h2

/-- Gallagher 1975 p.128: every character mod q is chi_q for a unique primitive chi of
conductor dividing q, which is the reindexing used to pass to display 3. Sums over the
family filtered by r dividing q equal sums over all characters mod q. -/
theorem sum_family_induced {P : ℝ} {q : ℕ} (hq1 : 1 ≤ q) (hqP : q ≤ ⌊P⌋₊)
    (h : PChar → ℂ) (g : DirichletCharacter ℂ q → ℂ)
    (hhg : ∀ x ∈ family P, x.1 + 1 ∣ q → h x = g (induced x q)) :
    ∑ x ∈ (family P).filter (fun x => x.1 + 1 ∣ q), h x =
      ∑ χ : DirichletCharacter ℂ q, g χ := by
  have : NeZero q := ⟨by omega⟩
  have hprim : ∀ x ∈ family P, x.2.IsPrimitive := by
    intro x hx
    unfold family at hx
    rw [Finset.mem_sigma] at hx
    exact (Finset.mem_filter.mp hx.2).2
  apply Finset.sum_bij (fun x _ => induced x q)
  · intro x _; exact Finset.mem_univ _
  · intro x hx y hy hxy
    rw [Finset.mem_filter] at hx hy
    have hcx := hprim x hx.1
    have hcy := hprim y hy.1
    obtain ⟨k, a⟩ := x
    obtain ⟨k', b⟩ := y
    simp only at hx hy hcx hcy hxy
    have hk : k + 1 = k' + 1 := by
      have e1 : (induced ⟨k, a⟩ q).conductor = k + 1 := by
        unfold induced; simp only [hx.2, ↓reduceDIte]
        rw [DirichletCharacter.conductor_changeLevel]; exact hcx
      have e2 : (induced ⟨k', b⟩ q).conductor = k' + 1 := by
        unfold induced; simp only [hy.2, ↓reduceDIte]
        rw [DirichletCharacter.conductor_changeLevel]; exact hcy
      rw [← e1, ← e2, hxy]
    have hkk : k = k' := by omega
    subst hkk
    unfold induced at hxy
    simp only [hx.2, ↓reduceDIte] at hxy
    rw [DirichletCharacter.changeLevel_injective hx.2 hxy]
  · intro χ _
    obtain ⟨k, hk⟩ : ∃ k, χ.conductor = k + 1 :=
      ⟨χ.conductor - 1, by have := χ.conductor_ne_zero; omega⟩
    have hft : χ.FactorsThrough (k + 1) := hk ▸ χ.factorsThrough_conductor
    obtain ⟨hd, χ₀, hχ₀⟩ := hft
    have hprim0 : χ₀.IsPrimitive := by
      have := DirichletCharacter.conductor_changeLevel χ₀ hd
      rw [← hχ₀, hk] at this
      exact this.symm
    have hkq : k + 1 ≤ q := Nat.le_of_dvd (by omega) hd
    refine ⟨⟨k, χ₀⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, hd⟩
      unfold family
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      exact ⟨show k < ⌊P⌋₊ by omega, Finset.mem_univ _, hprim0⟩
    · unfold induced
      simp only [hd, ↓reduceDIte]
      exact hχ₀.symm
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact hhg x hx.1 hx.2

/-- Gallagher 1975 p.128: the Gauss sum of the first display, written tau, as a sum over
residues 0 to q minus 1. -/
theorem gaussSum_eq_tau {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) :
    gaussSum ψ ZMod.stdAddChar = tau ψ := by
  unfold gaussSum tau cn
  symm
  apply Finset.sum_bij (fun (a : ℕ) _ => ((a : ℕ) : ZMod q))
  · intro a _; exact Finset.mem_univ _
  · intro a ha b hb hab
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] at this
  · intro z _
    exact ⟨z.val, Finset.mem_range.mpr z.val_lt, ZMod.natCast_zmod_val z⟩
  · intro a _
    congr 1
    have he := ZMod.stdAddChar_coe (N := q) (a : ℤ)
    simp only [Int.cast_natCast] at he
    rw [he]
    unfold LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring

/-- Gallagher 1975 p.128: summing conj chi(a) chi'(a) e(an/q) over reduced residues a
gives c_n(conj chi chi'). -/
theorem sum_units_eq_cn {q : ℕ} [NeZero q] (χ χ' : DirichletCharacter ℂ q) (n : ℤ) :
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        star (χ a) * χ' a * eL ((a : ℝ) * n / q) = cn (χ⁻¹ * χ') n := by
  unfold cn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  rw [MulChar.star_apply', MulChar.coeToFun_mul, Pi.mul_apply]
  split_ifs with h
  · rfl
  · have hu : ¬ IsUnit (a : ZMod q) := by
      rwa [ZMod.isUnit_iff_coprime]
    rw [MulChar.map_nonunit χ' hu, mul_zero, zero_mul]

/-! ### The main term M on an arc and the sum over a, p.128 -/

/-- Gallagher 1975 p.128 first display: the main term
M = phi(q)^(-1) sum over chi mod q of chi(a) tau(conj chi) A(chi*, beta). -/
noncomputable def arcMain (N q : ℕ) [NeZero q] (a : ℕ) (β : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
    χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β

/-- Gallagher 1975 p.128: e is continuous. -/
theorem continuous_eL : Continuous eL := by
  unfold LeanLab.PNTPort.LargeSieve.e; fun_prop

/-- Gallagher 1975 p.128: M is continuous in beta. -/
theorem continuous_arcMain (N q : ℕ) [NeZero q] (a : ℕ) : Continuous (arcMain N q a) := by
  unfold arcMain
  exact continuous_const.mul (continuous_finsetSum _ fun χ _ =>
    continuous_const.mul (continuous_primeAmplitude _ N))

/-- Gallagher 1975 p.128, second display expanded: for one a,
|M|^2 e(n(a/q + beta)) as a double sum over chi, chi'. -/
theorem normSq_arcMain_expand {q : ℕ} [NeZero q] (N : ℕ) (n : ℤ) (a : ℕ) (β : ℝ) :
    ((‖arcMain N q a β‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β)) =
      ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
        (1 / (q.totient : ℂ) ^ 2) * (star (χ a) * χ' a * eL ((a : ℝ) * n / q)) *
          (star (gaussSum χ⁻¹ ZMod.stdAddChar) * gaussSum χ'⁻¹ ZMod.stdAddChar *
            (star (primeAmplitude χ.primitiveCharacter N β) *
              primeAmplitude χ'.primitiveCharacter N β * eL ((n : ℝ) * β))) := by
  have hn : ((‖arcMain N q a β‖ ^ 2 : ℝ) : ℂ) = star (arcMain N q a β) * arcMain N q a β := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  have he : eL ((n : ℝ) * ((a : ℝ) / q + β)) = eL ((a : ℝ) * n / q) * eL ((n : ℝ) * β) := by
    rw [← e_add]; congr 1; ring
  have hφ : star ((q.totient : ℂ)⁻¹) = (q.totient : ℂ)⁻¹ := by simp
  rw [hn, he]
  unfold arcMain
  rw [star_mul', hφ, star_sum]
  rw [show ∀ (A B c d : ℂ), (c * A) * (c * B) * d = (c * c * d) * (A * B) from
    fun _ _ _ _ => by ring]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ' _ => ?_
  simp only [star_mul']
  ring

/-- Gallagher 1975 p.128, passing from the second display to the third: summing
|M|^2 e(n(a/q + beta)) over reduced residues a gives
phi(q)^(-2) times the sum over chi, chi' of c_n(conj chi chi') conj tau(conj chi)
tau(conj chi') conj A(chi*, beta) A(chi'*, beta) e(n beta). -/
theorem sum_units_normSq_arcMain {q : ℕ} [NeZero q] (N : ℕ) (n : ℤ) (β : ℝ) :
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ((‖arcMain N q a β‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β)) =
      ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
        (1 / (q.totient : ℂ) ^ 2) * (cn (χ⁻¹ * χ') n * star (tau χ⁻¹) * tau χ'⁻¹) *
          (star (primeAmplitude χ.primitiveCharacter N β) *
            primeAmplitude χ'.primitiveCharacter N β * eL ((n : ℝ) * β)) := by
  simp only [normSq_arcMain_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun χ' _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_units_eq_cn, gaussSum_eq_tau, gaussSum_eq_tau]
  ring

/-- Gallagher 1975 p.128: the pair sums of display 3, summed over the family, regrouped by
the modulus q: J_n(chi, chi') summed over chi, chi' equals the sum over q at most P of the
sum over chi, chi' in the family with conductors dividing q. -/
theorem sum_pairSum_regroup (N : ℕ) (P : ℝ) (n : ℤ) :
    ∑ x ∈ family P, ∑ y ∈ family P, pairSum N P n x y =
      ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ x ∈ (family P).filter (fun x => x.1 + 1 ∣ q),
        ∑ y ∈ (family P).filter (fun y => y.1 + 1 ∣ q),
          (1 / (q.totient : ℂ) ^ 2) * pairCoeff n q x y * arcIntegral N P n q x y := by
  unfold pairSum pairModuli
  simp only [Finset.sum_filter, Nat.lcm_dvd_iff, ite_and]
  calc _ = ∑ x ∈ family P, ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ y ∈ family P,
        (if x.1 + 1 ∣ q then if y.1 + 1 ∣ q then
          (1 / (q.totient : ℂ) ^ 2) * pairCoeff n q x y * arcIntegral N P n q x y else 0
          else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ x ∈ family P, ∑ y ∈ family P,
        (if x.1 + 1 ∣ q then if y.1 + 1 ∣ q then
          (1 / (q.totient : ℂ) ^ 2) * pairCoeff n q x y * arcIntegral N P n q x y else 0
          else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp

/-- Gallagher 1975 p.128, display 3 main term on one modulus q: the q part of the pair sums
equals the sum over reduced residues a of the integral over |beta| at most P/(qN) of
|M|^2 e(n(a/q + beta)). This is step (iii) of the derivation: the sum over a and the
reindexing of characters mod q by the primitive characters inducing them. -/
theorem pair_q_part_eq {N : ℕ} {P : ℝ} (n : ℤ) {q : ℕ} [NeZero q] (hq : q ∈ Icc 1 ⌊P⌋₊) :
    ∑ x ∈ (family P).filter (fun x => x.1 + 1 ∣ q),
        ∑ y ∈ (family P).filter (fun y => y.1 + 1 ∣ q),
          (1 / (q.totient : ℂ) ^ 2) * pairCoeff n q x y * arcIntegral N P n q x y =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ β in Set.Icc (-(P / (q * N))) (P / (q * N)),
          ((‖arcMain N q a β‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β)) := by
  rw [Finset.mem_Icc] at hq
  have hprim : ∀ x ∈ family P, x.2.IsPrimitive := by
    intro x hx
    unfold family at hx
    rw [Finset.mem_sigma] at hx
    exact (Finset.mem_filter.mp hx.2).2
  set s := Set.Icc (-(P / (q * N))) (P / (q * N)) with hs
  let G : DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℂ := fun χ χ' =>
    (1 / (q.totient : ℂ) ^ 2) * (cn (χ⁻¹ * χ') n * star (tau χ⁻¹) * tau χ'⁻¹) *
      ∫ β in s, star (primeAmplitude χ.primitiveCharacter N β) *
        primeAmplitude χ'.primitiveCharacter N β * eL ((n : ℝ) * β)
  have hL : ∑ x ∈ (family P).filter (fun x => x.1 + 1 ∣ q),
        ∑ y ∈ (family P).filter (fun y => y.1 + 1 ∣ q),
          (1 / (q.totient : ℂ) ^ 2) * pairCoeff n q x y * arcIntegral N P n q x y =
      ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q, G χ χ' := by
    apply sum_family_induced hq.1 hq.2
    intro x hx hxq
    apply sum_family_induced hq.1 hq.2
    intro y hy hyq
    simp only [G]
    unfold pairCoeff arcIntegral
    congr 1
    congr 1
    funext β
    rw [primeAmplitude_induced (hprim x hx) hq.1 hxq,
      primeAmplitude_induced (hprim y hy) hq.1 hyq]
  rw [hL]
  have hcA : ∀ χ χ' : DirichletCharacter ℂ q, Continuous fun β : ℝ =>
      star (primeAmplitude χ.primitiveCharacter N β) *
        primeAmplitude χ'.primitiveCharacter N β * eL ((n : ℝ) * β) := by
    intro χ χ'
    exact ((continuous_star.comp (continuous_primeAmplitude _ N)).mul
      (continuous_primeAmplitude _ N)).mul (continuous_eL.comp (continuous_const.mul continuous_id))
  have hcM : ∀ a : ℕ, Continuous fun β : ℝ =>
      ((‖arcMain N q a β‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β)) := by
    intro a
    exact (Complex.continuous_ofReal.comp ((continuous_arcMain N q a).norm.pow 2)).mul
      (continuous_eL.comp (continuous_const.mul (continuous_const.add continuous_id)))
  rw [← integral_finsetSum _ (fun a _ => (hcM a).integrableOn_Icc)]
  simp only [sum_units_normSq_arcMain]
  rw [integral_finsetSum _ (fun χ _ => integrable_finsetSum _ fun χ' _ =>
    ((hcA χ χ').integrableOn_Icc).const_mul _)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [integral_finsetSum _ (fun χ' _ => ((hcA χ χ').integrableOn_Icc).const_mul _)]
  refine Finset.sum_congr rfl fun χ' _ => ?_
  simp only [G]
  rw [integral_const_mul]

/-! ### The arc decomposition, p.128 -/

/-- Gallagher 1975 p.128: reduced fractions a/q, a'/q' with q, q' at least 1 that are
equal have q = q' and a = a'. -/
theorem reduced_frac_inj {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (h : Nat.Coprime a q)
    (h' : Nat.Coprime a' q') (heq : (a : ℝ) / q = a' / q') : q = q' ∧ a = a' := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq0' : (q' : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff hq0 hq0'] at heq
  have hn : a * q' = a' * q := by exact_mod_cast heq
  have h1 : q ∣ q' := by
    have hd : q ∣ q' * a := ⟨a', by rw [mul_comm q' a, hn, mul_comm]⟩
    exact (Nat.Coprime.symm h).dvd_of_dvd_mul_right hd
  have h2 : q' ∣ q := by
    have hd : q' ∣ q * a' := ⟨a, by rw [mul_comm q a', ← hn, mul_comm]⟩
    exact (Nat.Coprime.symm h').dvd_of_dvd_mul_right hd
  have hqq : q = q' := Nat.dvd_antisymm h1 h2
  subst hqq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) hn⟩

/-- Gallagher 1975 p.128: translating an arc of half width delta about c to the origin. -/
theorem integral_Icc_translate (f : ℝ → ℂ) (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ x in Set.Icc (c - δ) (c + δ), f x = ∫ β in Set.Icc (-δ) δ, f (c + β) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_left f c]
  rw [sub_eq_add_neg]

/-- Gallagher 1975 p.128: for 2 P^2 < N the major arcs M(a, q), q at most P, a prime to q,
are disjoint, and with the two half arcs at 0 and 1 joined by periodicity the integral
over the major arcs is the sum over q at most P and reduced residues a of the integral
over |beta| at most P/(qN) of the integrand at a/q + beta. Step (i) of the derivation of
display 3. -/
theorem integral_majorArcs_eq {N : ℕ} {P : ℝ} (hP1 : 1 ≤ P) (hPN : 2 * P ^ 2 < N)
    (f : ℝ → ℂ) (hf : Continuous f) (hper : ∀ x, f (x + 1) = f x) :
    ∫ α in majorArcs N P, f α =
      ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ β in Set.Icc (-(P / (q * N))) (P / (q * N)), f ((a : ℝ) / q + β) := by
  have hP0 : 0 < P := by linarith
  have hN : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hPN
  have hPN' : P ≤ N := by nlinarith
  let T : Finset (Σ _ : ℕ, ℕ) :=
    (Icc 1 ⌊P⌋₊).sigma (fun q => (range (q + 1)).filter (fun a => Nat.Coprime a q))
  let arc : (Σ _ : ℕ, ℕ) → Set ℝ := fun i =>
    Set.Icc ((i.2 : ℝ) / i.1 - P / (i.1 * N)) ((i.2 : ℝ) / i.1 + P / (i.1 * N)) ∩
      Set.Icc 0 1
  have hU : majorArcs N P = ⋃ i ∈ T, arc i := by
    ext α
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_iUnion, T, arc, Finset.mem_sigma,
      Finset.mem_Icc, Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff, Set.mem_Icc,
      exists_prop, Sigma.exists]
    constructor
    · rintro ⟨hα, q, hq1, hqP, a, haq, hcop, habs⟩
      rw [abs_sub_le_iff] at habs
      refine ⟨q, a, ⟨⟨hq1, Nat.le_floor hqP⟩, by omega, hcop⟩, ⟨by linarith, by linarith⟩, hα⟩
    · rintro ⟨q, a, ⟨⟨hq1, hqP⟩, haq, hcop⟩, ⟨h1, h2⟩, hα⟩
      refine ⟨hα, q, hq1, ?_, a, by omega, hcop, ?_⟩
      · exact le_trans (by exact_mod_cast hqP) (Nat.floor_le hP0.le)
      · rw [abs_sub_le_iff]; constructor <;> linarith
  have hmeas : ∀ i ∈ T, MeasurableSet (arc i) :=
    fun i _ => measurableSet_Icc.inter measurableSet_Icc
  have hdisj : Set.Pairwise (↑T) (Function.onFun Disjoint arc) := by
    rintro ⟨q, a⟩ hi ⟨q', a'⟩ hj hij
    rw [Finset.mem_coe] at hi hj
    simp only [T, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_range] at hi hj
    rw [Function.onFun, Set.disjoint_left]
    intro α hα hα'
    simp only [arc, Set.mem_inter_iff, Set.mem_Icc] at hα hα'
    have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hi.1.2) (Nat.floor_le hP0.le)
    have hqP' : (q' : ℝ) ≤ P := le_trans (by exact_mod_cast hj.1.2) (Nat.floor_le hP0.le)
    have hne : (a : ℝ) / q ≠ a' / q' := by
      intro heq
      obtain ⟨rfl, rfl⟩ := reduced_frac_inj hi.1.1 hj.1.1 hi.2.2 hj.2.2 heq
      exact hij rfl
    exact LeanLab.Linnik.Decomp1532b.majorArcs_disjoint (α := α) hP0 hPN hi.1.1 hj.1.1 hqP hqP' hne
      (abs_sub_le_iff.mpr ⟨by linarith [hα.1.2], by linarith [hα.1.1]⟩)
      (abs_sub_le_iff.mpr ⟨by linarith [hα'.1.2], by linarith [hα'.1.1]⟩)
  have hint : ∀ i ∈ T, IntegrableOn f (arc i) :=
    fun i _ => hf.integrableOn_Icc.mono_set Set.inter_subset_right
  rw [hU, integral_biUnion_finset T hmeas hdisj hint, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_Icc] at hq
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq.1
  have hδ0 : 0 ≤ P / (q * N) := by positivity
  have hδq : P / (q * N) * q ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  by_cases hq1 : q = 1
  · subst hq1
    have hs2 : (range (1 + 1)).filter (fun a => Nat.Coprime a 1) = {0, 1} := by decide
    have hs1 : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
    rw [hs2, hs1, Finset.sum_pair (by norm_num), Finset.sum_singleton]
    simp only [arc, Nat.cast_one, one_mul, div_one, Nat.cast_zero, zero_add, zero_sub]
    have hδ1 : P / N ≤ 1 := by rw [div_le_one hN]; exact hPN'
    have hδ0' : 0 ≤ P / N := by positivity
    rw [Set.Icc_inter_Icc, Set.Icc_inter_Icc, max_eq_right (by linarith),
      min_eq_left hδ1, max_eq_left (by linarith), min_eq_right (by linarith)]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδ0',
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals (a := -(P / N)) (b := 0) (c := P / N)
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    have hshift : ∫ x in (-(P / N))..0, f x = ∫ x in (1 - P / N)..1, f x := by
      have := intervalIntegral.integral_comp_add_right f (a := -(P / N)) (b := 0) 1
      simp only [hper] at this
      rw [this]; congr 1 <;> ring
    rw [hshift, add_comm]
  · have hq2 : 2 ≤ q := by omega
    have hfil : (range (q + 1)).filter (fun a => Nat.Coprime a q) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact h
        · subst h; exact absurd (by simpa using h2) hq1
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    rw [hfil]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter, Finset.mem_range] at ha
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; exact absurd (Nat.coprime_zero_left _ |>.mp ha.2) hq1
      · exact h
    have hqpos : (0 : ℝ) < q := by positivity
    have hlo : (1 : ℝ) / q ≤ (a : ℝ) / q :=
      div_le_div_of_nonneg_right (by exact_mod_cast ha1) hqpos.le
    have hhi : (a : ℝ) / q ≤ ((q : ℝ) - 1) / q :=
      div_le_div_of_nonneg_right (by
        have : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha.1
        linarith) hqpos.le
    have hδ' : P / (q * N) ≤ 1 / q := by
      rw [le_div_iff₀ hqpos]; linarith
    have hsub : Set.Icc ((a : ℝ) / q - P / (q * N)) ((a : ℝ) / q + P / (q * N)) ⊆
        Set.Icc 0 1 := by
      apply Set.Icc_subset_Icc
      · linarith
      · have : ((q : ℝ) - 1) / q = 1 - 1 / q := by field_simp
        linarith
    simp only [arc]
    rw [Set.inter_eq_left.mpr hsub, integral_Icc_translate f _ hδ0]

/-! ### The replacement of |S|^2 by |M|^2 on one arc, p.128 -/

/-- Gallagher 1975 p.128: if S = M + O(E) then |S|^2 = |M|^2 + O(E(2|S| + E)). -/
theorem abs_normSq_sub_le (z w : ℂ) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ ‖z - w‖ * (2 * ‖z‖ + ‖z - w‖) := by
  have h1 : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_norm_sub_norm_le z w
  have h2 : ‖w‖ ≤ ‖z‖ + ‖z - w‖ := by
    have := norm_sub_norm_le w z
    rw [norm_sub_rev] at this
    linarith
  rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ + ‖w‖)]
  exact mul_le_mul h1 (by linarith) (by positivity) (norm_nonneg _)

/-- Gallagher 1975 p.127: |S(alpha)| is at most pi(N). -/
theorem norm_Sg_le_primeCounting (N : ℕ) (α : ℝ) : ‖Sg N α‖ ≤ Nat.primeCounting N := by
  unfold Sg LeanLab.Linnik.LiLiuLemma43.SA
  calc _ ≤ ∑ p ∈ LeanLab.Linnik.U7204.primesLe N,
        ‖(1 : ℂ) * LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * α)‖ := norm_sum_le _ _
    _ = (LeanLab.Linnik.U7204.primesLe N).card := by simp [norm_e]
    _ = Nat.primeCounting N := by
        rw [show LeanLab.Linnik.U7204.primesLe N = Nat.primesLE N from rfl,
          Nat.primesLE_card_eq_primeCounting]

/-- Gallagher 1975 p.128, step (ii) of the derivation of display 3 on one arc: if on the arc
|S(a/q + beta)| is at most B and S differs from the main term M by at most E, then the arc
integrals of |S|^2 e(n alpha) and of |M|^2 e(n alpha) differ by at most E(2B + E) times the
arc length 2 delta. -/
theorem arc_replacement_bound {q : ℕ} [NeZero q] (N : ℕ) (n : ℤ) (a : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) {E B : ℝ} (hS : ∀ β, ‖Sg N ((a : ℝ) / q + β)‖ ≤ B)
    (hE : ∀ β, ‖Sg N ((a : ℝ) / q + β) - arcMain N q a β‖ ≤ E) (hE0 : 0 ≤ E) :
    ‖(∫ β in Set.Icc (-δ) δ,
        ((‖Sg N ((a : ℝ) / q + β)‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β))) -
      ∫ β in Set.Icc (-δ) δ,
        ((‖arcMain N q a β‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β))‖ ≤
      E * (2 * B + E) * (2 * δ) := by
  have he : Continuous fun β : ℝ => eL ((n : ℝ) * ((a : ℝ) / q + β)) :=
    continuous_eL.comp (continuous_const.mul (continuous_const.add continuous_id))
  have hc1 : Continuous fun β : ℝ =>
      ((‖Sg N ((a : ℝ) / q + β)‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β)) :=
    (Complex.continuous_ofReal.comp (((LeanLab.Linnik.U7206.continuous_Sg N).comp
      (continuous_const.add continuous_id)).norm.pow 2)).mul he
  have hc2 : Continuous fun β : ℝ =>
      ((‖arcMain N q a β‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * ((a : ℝ) / q + β)) :=
    (Complex.continuous_ofReal.comp ((continuous_arcMain N q a).norm.pow 2)).mul he
  rw [← integral_sub hc1.integrableOn_Icc hc2.integrableOn_Icc]
  refine (norm_setIntegral_le_of_norm_le_const (C := E * (2 * B + E)) measure_Icc_lt_top
    fun β _ => ?_).trans ?_
  · rw [← sub_mul, norm_mul, norm_e, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    refine (abs_normSq_sub_le _ _).trans ?_
    exact mul_le_mul (hE β) (by linarith [hS β, hE β]) (by positivity) hE0
  · rw [Real.volume_real_Icc_of_le (by linarith)]
    apply le_of_eq; ring

/-! ### The error sum, p.128 -/

/-- Gallagher 1975 p.128, step (d): summing the per arc error C q^(1/2) log 2q times
(2 pi(N) + C q^(1/2) log 2q) over arcs of length 2P/(qN), over phi(q) values of a and
q at most P, gives O(P^(5/2)) once log 2P pi(N) is O(N) and P^3 is at most N. -/
theorem error_sum_numeric {C c₀ P N L B : ℝ} (hC : 0 < C) (hN : 0 < N)
    (hP1 : 1 ≤ P) (hL0 : 0 ≤ L) (hLP : L ≤ 2 * P) (hLB : L * B ≤ 2 * c₀ * N)
    (hP3 : P ^ 3 ≤ N) :
    P * ((C * Real.sqrt P * L) * (2 * B + C * Real.sqrt P * L)) * (2 * P / N) ≤
      8 * C * (c₀ + C) * (P ^ 2 * Real.sqrt P) := by
  set s := Real.sqrt P with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg P
  have hsP : s ≤ P := by
    rw [hs, Real.sqrt_le_left (by linarith)]; nlinarith
  have hL2 : L ^ 2 ≤ 4 * P ^ 2 := by nlinarith
  have key : 2 * (L * B) + C * s * L ^ 2 ≤ 4 * (c₀ + C) * N := by
    have h1 : C * s * L ^ 2 ≤ C * P * (4 * P ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsP hC.le) hL2 (by positivity) (by positivity)
    nlinarith
  have hrw : P * ((C * s * L) * (2 * B + C * s * L)) * (2 * P / N) =
      (2 * C * P ^ 2 * s) * (2 * (L * B) + C * s * L ^ 2) / N := by
    field_simp
  rw [hrw, div_le_iff₀ hN]
  have hA : 0 ≤ 2 * C * P ^ 2 * s := by positivity
  calc (2 * C * P ^ 2 * s) * (2 * (L * B) + C * s * L ^ 2)
      ≤ (2 * C * P ^ 2 * s) * (4 * (c₀ + C) * N) := mul_le_mul_of_nonneg_left key hA
    _ = _ := by ring

/-! ### Display 3 -/

/-- Gallagher 1975 p.128 display 3, proved from the first character expansion hExpansion
along Gallagher's own derivation, steps (i) to (iii) and the error sum, with Chebyshev's
bound pi(N) at most (log 4 + 1) N/log N for S(alpha) at most a constant times N/log N.
The statement is exactly that of `major_arc_pair_expansion` in Leaves13.lean. -/
theorem major_arc_pair_expansion_of_steps
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ,
        ‖(∫ α in majorArcs N ((N : ℝ) ^ θ),
            ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) -
          ∑ x ∈ family ((N : ℝ) ^ θ), ∑ y ∈ family ((N : ℝ) ^ θ),
            pairSum N ((N : ℝ) ^ θ) n x y‖ ≤ K * ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) := by
  obtain ⟨C, hC, hexp⟩ := hExpansion
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  set c₀ : ℝ := Real.log 4 + 1 with hc₀
  have hc₀0 : 0 ≤ c₀ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  refine ⟨8 * C * (c₀ + C), 1 / 4, by positivity, by norm_num, ?_⟩
  intro θ hθ hθ4
  refine ⟨max ⌈x₀⌉₊ 5, ?_⟩
  intro N hN n
  have hN5 : (5 : ℝ) ≤ N := by
    have : 5 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : x₀ ≤ N := by
    have : ⌈x₀⌉₊ ≤ N := le_trans (le_max_left _ _) hN
    exact le_trans (Nat.le_ceil x₀) (by exact_mod_cast this)
  set P : ℝ := (N : ℝ) ^ θ with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 hθ.le
  have hP0 : 0 < P := by linarith
  have hPpow : ∀ k : ℕ, θ * k ≤ 1 → P ^ k ≤ (N : ℝ) ^ (θ * k) := by
    intro k _
    rw [hPdef, Real.rpow_mul (by linarith), Real.rpow_natCast]
  have hP3 : P ^ 3 ≤ N := by
    refine (hPpow 3 (by push_cast; linarith)).trans ?_
    calc (N : ℝ) ^ (θ * ((3 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = N := Real.rpow_one _
  have hP2 : P ^ 2 ≤ Real.sqrt N := by
    refine (hPpow 2 (by push_cast; linarith)).trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hPN : 2 * P ^ 2 < N := by
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have hs2 : 2 < Real.sqrt N := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    nlinarith
  have hPleN : P ≤ N := by nlinarith
  have hpi : (Nat.primeCounting N : ℝ) ≤ c₀ * N / Real.log N := by
    have := hx₀ N hx
    rwa [Nat.floor_natCast] at this
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  set L : ℝ := Real.log (2 * P) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLP : L ≤ 2 * P := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * P by linarith)
    linarith
  have hL2 : L ≤ 2 * Real.log N := by
    calc L ≤ Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  set B : ℝ := (Nat.primeCounting N : ℝ) with hBdef
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hLB : L * B ≤ 2 * c₀ * N := by
    calc L * B ≤ (2 * Real.log N) * (c₀ * N / Real.log N) :=
          mul_le_mul hL2 hpi hB0 (by positivity)
      _ = 2 * c₀ * N := by field_simp
  set E : ℝ := C * Real.sqrt P * L with hEdef
  have hE0 : 0 ≤ E := by positivity
  -- step (i): the arc decomposition
  set f : ℝ → ℂ := fun α => ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * eL ((n : ℝ) * α) with hfdef
  have hf : Continuous f :=
    (Complex.continuous_ofReal.comp ((LeanLab.Linnik.U7206.continuous_Sg N).norm.pow 2)).mul
      (continuous_eL.comp (continuous_const.mul continuous_id))
  have hper : ∀ x, f (x + 1) = f x := by
    intro x
    simp only [hfdef]
    have hS : Sg N (x + 1) = Sg N x := by
      simpa only [Sg] using LeanLab.Linnik.LiLiuLemma43Int.SA_periodic
        (LeanLab.Linnik.U7204.primesLe N) (fun _ => 1) x
    rw [hS, mul_add, mul_one, e_add, e_int, mul_one]
  rw [integral_majorArcs_eq hP1 hPN f hf hper, sum_pairSum_regroup, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  -- steps (ii) and (iii) on each modulus q
  have hq_bound : ∀ q ∈ Icc 1 ⌊P⌋₊,
      ‖(∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ β in Set.Icc (-(P / (q * N))) (P / (q * N)), f ((a : ℝ) / q + β)) -
        ∑ x ∈ (family P).filter (fun x => x.1 + 1 ∣ q),
          ∑ y ∈ (family P).filter (fun y => y.1 + 1 ∣ q),
            (1 / (q.totient : ℂ) ^ 2) * pairCoeff n q x y * arcIntegral N P n q x y‖ ≤
        E * (2 * B + E) * (2 * P / N) := by
    intro q hq
    have hq' := Finset.mem_Icc.mp hq
    have : NeZero q := ⟨by omega⟩
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq'.1
    have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hq'.2) (Nat.floor_le hP0.le)
    rw [pair_q_part_eq n hq, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hδ0 : 0 ≤ P / (q * N) := by positivity
    have hEq : C * Real.sqrt q * Real.log (2 * q) ≤ E := by
      have h1 : Real.sqrt q ≤ Real.sqrt P := Real.sqrt_le_sqrt hqP
      have h2 : Real.log (2 * q) ≤ L := Real.log_le_log (by linarith) (by linarith)
      have h3 : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC.le) h2 h3 (by positivity)
    calc ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖_ - _‖
        ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            E * (2 * B + E) * (2 * (P / (q * N))) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_filter, Finset.mem_range] at ha
          exact arc_replacement_bound N n a hδ0
            (fun β => norm_Sg_le_primeCounting N _)
            (fun β => (hexp N q a ha.2 ha.1.le β).trans hEq) hE0
      _ = ((range q).filter (fun a => Nat.Coprime a q)).card *
            (E * (2 * B + E) * (2 * (P / (q * N)))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q : ℝ) * (E * (2 * B + E) * (2 * (P / (q * N)))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := Finset.card_filter_le (range q) (fun a => Nat.Coprime a q)
          rw [Finset.card_range] at this
          exact_mod_cast this
      _ = E * (2 * B + E) * (2 * P / N) := by
          field_simp
  -- step (d): the error sum
  calc ∑ q ∈ Icc 1 ⌊P⌋₊, ‖_‖ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, E * (2 * B + E) * (2 * P / N) :=
        Finset.sum_le_sum hq_bound
    _ = (⌊P⌋₊ : ℝ) * (E * (2 * B + E) * (2 * P / N)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; congr 2
    _ ≤ P * (E * (2 * B + E) * (2 * P / N)) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hP0.le) (by positivity)
    _ = P * ((C * Real.sqrt P * L) * (2 * B + C * Real.sqrt P * L)) * (2 * P / N) := by
        rw [hEdef]; ring
    _ ≤ 8 * C * (c₀ + C) * (P ^ 2 * Real.sqrt P) :=
        error_sum_numeric hC hN0 hP1 hL0 hLP hLB hP3
    _ = 8 * C * (c₀ + C) * P ^ (5 / 2 : ℝ) := by
        congr 1
        rw [show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hP0,
          Real.rpow_natCast, Real.sqrt_eq_rpow]

end LeanLab.Linnik.MajorArcEnergy

