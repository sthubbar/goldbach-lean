module

public import Mathlib

/-!
P0032 Riesel-Vaughan 1983, Lemma 13, pages 64 to 66, displays (8.16) to (8.18): the Gauss sum
of an imprimitive character. Unit U-6701, CLOUD 20261020T1816Z-cloud48. AI-written Lean code,
Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Davenport, Multiplicative Number Theory, chapter 9: if χ mod q is induced by the primitive
χ* mod q* and q/q* is squarefree and prime to q*, then τ(χ) = μ(q/q*) χ*(q/q*) τ(χ*), so
|τ(χ)|² = q*. Here τ(χ) is Mathlib's `gaussSum χ stdAddChar`, with e(a/q) the standard
additive character of `ZMod q`.

Route: |τ(χ*)|² = q* for primitive χ* from Mathlib's Fourier inversion `ZMod.dft_dft` and
`IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`; the CRT parametrisation
(x, y) ↦ x n₂ + y n₁ of ZMod (n₁ n₂) factors τ(χ) as χ*(n₂) τ(χ*) c_{n₂}(1); the Ramanujan sum
c_m(1) = μ(m) for squarefree m by multiplicativity and c_p(1) = −1.

What is here, all PROVED unconditional:
* `norm_sq_gaussSum_of_isPrimitive`: |τ(χ)|² = q for primitive χ mod q.
* `gaussSum_changeLevel_mul`: τ of a character induced from level n₁ to n₁ n₂, (n₁, n₂) = 1,
  is χ₁(n₂) τ(χ₁) c_{n₂}(1).
* `ram_squarefree`: c_m(1) = μ(m) for squarefree m.
* `gaussSum_eq_moebius_mul`: τ(χ) = μ(q/q*) χ*(q/q*) τ(χ*), Davenport chapter 9.
* `norm_sq_gaussSum_eq_conductor`, `norm_sq_gaussSum_changeLevel`: |τ(χ)|² = q*.
* `inv_mul_gaussSum_eq`, `card_mul_norm_sq_charSum_eq`: for primitive χ mod r,
  r |Σ_{p∈P} χ(p)|² = |Σ_a χ(a) Σ_{p∈P} e(ap/r)|², the bridge from `Delta.Spsi` to additive sums.
* `sum_norm_sq_twist`: Σ_{χ mod r} |Σ_a χ(a) f(a)|² = φ(r) Σ_{(a, r) = 1} |f(a)|².
* `card_mul_sum_primitive_le`: r Σ*_{χ mod r} |Σ_{p∈P} χ(p)|² ≤ φ(r) Σ_{(a, r) = 1} |Σ_{p∈P} e(ap/r)|²,
  the passage from the paper's Σ*|S_k(χ)|² to the additive sums of a large sieve.
* `totient_mul_sum_additive_eq`: the page 65 identity, for P prime to r,
  φ(r) Σ_{(a, r) = 1} |Σ_{p∈P} e(ap/r)|² = Σ_{χ mod r} |τ(χ)|² |Σ_{p∈P} χ(p)|².
KNOWN mathematics.
-/

@[expose] public section

open ZMod AddChar DirichletCharacter Finset

noncomputable section
namespace LeanLab.RieselVaughan1983.GaussImprim

/-! ### Primitive characters -/

section Primitive

variable {N : ℕ} [NeZero N]

theorem gauss_mul_inv_gauss {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = χ (-1) * N := by
  have h := congrFun (dft_dft (N := N) (fun j => χ j)) 1
  have h1 : (𝓕 (fun j => χ j) : ZMod N → ℂ) = fun k => χ⁻¹ (-k) * gaussSum χ stdAddChar := by
    funext k; exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  rw [h1] at h
  have h2 : (fun k : ZMod N => χ⁻¹ (-k) * gaussSum χ stdAddChar) =
      fun k => gaussSum χ stdAddChar * (fun j => (χ⁻¹ : DirichletCharacter ℂ N) j) (-k) := by
    funext k; ring
  rw [h2, dft_const_mul, dft_comp_neg] at h
  simp only at h
  rw [fourierTransform_eq_gaussSum_mulShift, neg_neg, mulShift_one] at h
  rw [h, smul_eq_mul, mul_comm]

theorem gauss_star {χ : DirichletCharacter ℂ N} :
    star (gaussSum χ stdAddChar) = χ (-1) * gaussSum χ⁻¹ stdAddChar := by
  rw [star_gaussSum_eq]
  have : (stdAddChar : AddChar (ZMod N) ℂ)⁻¹ = stdAddChar.mulShift ((-1 : (ZMod N)ˣ) : ZMod N) := by
    ext x; simp [mulShift_apply, AddChar.inv_apply]
  rw [this, gaussSum_mulShift_eq]
  simp

theorem norm_sq_gaussSum_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = N := by
  have hm : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]; simp
  have key : gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = N := by
    rw [gauss_star, ← mul_assoc, mul_comm _ (χ (-1)), mul_assoc, gauss_mul_inv_gauss hχ,
      ← mul_assoc, hm, one_mul]
  have : ((‖gaussSum χ stdAddChar‖ ^ 2 : ℝ) : ℂ) = (N : ℂ) := by
    rw [← key, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast this

end Primitive

/-! ### The CRT factorisation and the Ramanujan sum -/

section CRT

/-- The CRT parametrisation `(x, y) ↦ x n₂ + y n₁` of `ZMod (n₁ n₂)`. -/
def crt (n1 n2 : ℕ) (p : ZMod n1 × ZMod n2) : ZMod (n1 * n2) :=
  ((p.1.val * n2 + p.2.val * n1 : ℕ) : ZMod (n1 * n2))

variable {n1 n2 : ℕ} [NeZero n1] [NeZero n2]

lemma cast_crt_left (p : ZMod n1 × ZMod n2) :
    ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1) (crt n1 n2 p) = p.1 * n2 := by
  simp only [crt, Nat.cast_add, Nat.cast_mul, map_add, map_mul, map_natCast, ZMod.natCast_self,
    mul_zero, add_zero, natCast_zmod_val]

lemma cast_crt_right (p : ZMod n1 × ZMod n2) :
    ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2) (crt n1 n2 p) = p.2 * n1 := by
  simp only [crt, Nat.cast_add, Nat.cast_mul, map_add, map_mul, map_natCast, ZMod.natCast_self,
    mul_zero, zero_add, natCast_zmod_val]

lemma std_crt (p : ZMod n1 × ZMod n2) :
    stdAddChar (crt n1 n2 p) = stdAddChar p.1 * stdAddChar p.2 := by
  simp only [crt, stdAddChar_apply, toCircle_natCast]
  conv_rhs => rw [← natCast_zmod_val p.1, ← natCast_zmod_val p.2, toCircle_natCast,
    toCircle_natCast]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  have h1 : (n1 : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n1
  have h2 : (n2 : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n2
  field_simp

lemma crt_bijective (h : n1.Coprime n2) : Function.Bijective (crt n1 n2) := by
  have : NeZero (n1 * n2) := ⟨Nat.mul_ne_zero (NeZero.ne n1) (NeZero.ne n2)⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun p p' hp => ?_, by simp [ZMod.card]⟩
  have u2 : IsUnit (n2 : ZMod n1) := (ZMod.isUnit_iff_coprime n2 n1).mpr h.symm
  have u1 : IsUnit (n1 : ZMod n2) := (ZMod.isUnit_iff_coprime n1 n2).mpr h
  have e1 := congrArg (ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1)) hp
  have e2 := congrArg (ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2)) hp
  rw [cast_crt_left, cast_crt_left] at e1
  rw [cast_crt_right, cast_crt_right] at e2
  exact Prod.ext (u2.mul_left_inj.mp e1) (u1.mul_left_inj.mp e2)


lemma changeLevel_apply_split (χ1 : DirichletCharacter ℂ n1)
    (a : ZMod (n1 * n2)) :
    changeLevel (Dvd.intro n2 rfl) χ1 a =
      χ1 (ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1) a) *
        (1 : DirichletCharacter ℂ n2) (ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2) a) := by
  have : NeZero (n1 * n2) := ⟨Nat.mul_ne_zero (NeZero.ne n1) (NeZero.ne n2)⟩
  by_cases ha : IsUnit a
  · have e := changeLevel_eq_cast_of_dvd χ1 (Dvd.intro n2 rfl) ha.unit
    rw [ha.unit_spec] at e
    rw [e, MulChar.one_apply (ha.map _), mul_one, ZMod.castHom_apply]
  · rw [MulChar.map_nonunit _ ha]
    have hv : a = ((a.val : ℕ) : ZMod (n1 * n2)) := (natCast_zmod_val a).symm
    by_cases u1 : IsUnit (ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1) a)
    · by_cases u2 : IsUnit (ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2) a)
      · exfalso; apply ha
        rw [hv, map_natCast] at u1 u2
        rw [hv, ZMod.isUnit_iff_coprime]
        exact Nat.Coprime.mul_right ((ZMod.isUnit_iff_coprime _ _).mp u1)
          ((ZMod.isUnit_iff_coprime _ _).mp u2)
      · rw [MulChar.map_nonunit _ u2, mul_zero]
    · rw [MulChar.map_nonunit _ u1, zero_mul]

/-- Gauss sums over `ZMod (n₁ n₂)` factor through the CRT, for `χ` induced from level `n₁`. -/
theorem gaussSum_changeLevel_mul (h : n1.Coprime n2) (χ1 : DirichletCharacter ℂ n1) :
    haveI : NeZero (n1 * n2) := ⟨Nat.mul_ne_zero (NeZero.ne n1) (NeZero.ne n2)⟩
    gaussSum (changeLevel (Dvd.intro n2 rfl) χ1) (stdAddChar (N := n1 * n2)) =
      χ1 n2 * gaussSum χ1 stdAddChar *
        gaussSum (1 : DirichletCharacter ℂ n2) stdAddChar := by
  have : NeZero (n1 * n2) := ⟨Nat.mul_ne_zero (NeZero.ne n1) (NeZero.ne n2)⟩
  have u1 : IsUnit (n1 : ZMod n2) := (ZMod.isUnit_iff_coprime n1 n2).mpr h
  unfold gaussSum
  rw [← Fintype.sum_bijective _ (crt_bijective h) _ _ (fun _ => rfl), Fintype.sum_prod_type,
    mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [changeLevel_apply_split, cast_crt_left, cast_crt_right, std_crt, map_mul, map_mul,
    MulChar.one_apply u1]
  simp only
  ring


omit [NeZero n1] [NeZero n2] in
lemma std_ne_one {p : ℕ} [NeZero p] (hp : 1 < p) : (stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
  intro h
  have e : stdAddChar (1 : ZMod p) = stdAddChar (0 : ZMod p) := by
    rw [h, AddChar.one_apply, AddChar.one_apply]
  have h10 : (1 : ZMod p) = 0 := injective_stdAddChar e
  have : Fact (1 < p) := ⟨hp⟩
  exact one_ne_zero h10

open scoped ArithmeticFunction.Moebius in
/-- The Ramanujan sum `c_m(1) = Σ_{a mod m, (a, m) = 1} e(a/m)`, as a function of `m`. -/
noncomputable def ram (m : ℕ) : ℂ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    gaussSum (1 : DirichletCharacter ℂ m) stdAddChar

omit [NeZero n1] [NeZero n2] in
lemma ram_eq (m : ℕ) [NeZero m] : ram m = gaussSum (1 : DirichletCharacter ℂ m) stdAddChar := by
  rw [ram, dif_neg (NeZero.ne m)]

omit [NeZero n1] [NeZero n2] in
lemma ram_one : ram 1 = 1 := by
  rw [ram_eq, gaussSum, Fintype.sum_unique]
  generalize (default : ZMod 1) = x
  obtain rfl : x = 0 := Subsingleton.elim _ _
  rw [MulChar.one_apply (isUnit_of_subsingleton _), AddChar.map_zero_eq_one, one_mul]

omit [NeZero n1] [NeZero n2] in
lemma ram_prime {p : ℕ} (hp : p.Prime) : ram p = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [ram_eq, gaussSum]
  have key : ∀ a : ZMod p, (1 : DirichletCharacter ℂ p) a * stdAddChar a =
      stdAddChar a - (if a = 0 then 1 else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha; rw [MulChar.map_nonunit _ not_isUnit_zero]; simp
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr ha), if_neg ha]; ring
  simp_rw [key]
  rw [Finset.sum_sub_distrib, AddChar.sum_eq_zero_of_ne_one (std_ne_one hp.one_lt),
    Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun _ => (1 : ℂ))]
  simp

omit [NeZero n1] [NeZero n2] in
lemma ram_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.Coprime b) :
    ram (a * b) = ram a * ram b := by
  have : NeZero a := ⟨ha⟩
  have : NeZero b := ⟨hb⟩
  have : NeZero (a * b) := ⟨Nat.mul_ne_zero ha hb⟩
  rw [ram_eq, ram_eq, ram_eq, ← changeLevel_one (R := ℂ) (Dvd.intro b rfl),
    gaussSum_changeLevel_mul h,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime b a).mpr h.symm), one_mul]

open scoped ArithmeticFunction.Moebius in
omit [NeZero n1] [NeZero n2] in
/-- `c_m(1) = μ(m)` for squarefree `m`. -/
theorem ram_squarefree (m : ℕ) (hm : Squarefree m) : ram m = μ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hm0 : m ≠ 0 := hm.ne_zero
  by_cases h1 : m = 1
  · subst h1; simp [ram_one]
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  obtain ⟨k, hk⟩ := Nat.minFac_dvd m
  rw [← hpdef] at hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hm0 hk
  have hpk : ¬ p ∣ k := by
    rintro ⟨j, rfl⟩
    have := hm p ⟨j, by rw [hk]; ring⟩
    exact hp.not_isUnit (Nat.isUnit_iff.mpr (Nat.isUnit_iff.mp this))
  have hcop : p.Coprime k := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpk
  have hklt : k < m := by
    rw [hk]; have := hp.two_le
    have : 0 < k := Nat.pos_of_ne_zero hk0
    nlinarith
  have hksq : Squarefree k := Squarefree.of_mul_right (hk ▸ hm)
  rw [hk, ram_mul hp.ne_zero hk0 hcop, ram_prime hp, ih k hklt hksq,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast; ring


end CRT

/-! ### The imprimitive Gauss sum, Davenport chapter 9 -/

open scoped ArithmeticFunction.Moebius

/-- The conductor of a character of nonzero level is nonzero. -/
instance conductor_neZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

/-- For `q = n₁ n₂` with `(n₁, n₂) = 1` and `n₂` squarefree, the Gauss sum of a character
induced from `χ₁ mod n₁` is `μ(n₂) χ₁(n₂) τ(χ₁)`. -/
theorem gaussSum_changeLevel_eq {q n1 n2 : ℕ} [NeZero q] [NeZero n1] (hq : q = n1 * n2)
    (hcop : n1.Coprime n2) (hsq : Squarefree n2) (χ1 : DirichletCharacter ℂ n1) (hd : n1 ∣ q) :
    gaussSum (changeLevel hd χ1) (stdAddChar (N := q)) =
      (μ n2 : ℂ) * χ1 n2 * gaussSum χ1 stdAddChar := by
  have : NeZero n2 := ⟨hsq.ne_zero⟩
  subst hq
  rw [gaussSum_changeLevel_mul hcop, ← ram_eq, ram_squarefree n2 hsq]
  ring

/-- **The Gauss sum of an imprimitive character**, Davenport chapter 9: if `χ mod q` has
conductor `q*` and `q/q*` is squarefree and prime to `q*`, then
`τ(χ) = μ(q/q*) χ*(q/q*) τ(χ*)`, with `χ*` the primitive character inducing `χ`. -/
theorem gaussSum_eq_moebius_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hsq : Squarefree (q / χ.conductor)) (hcop : χ.conductor.Coprime (q / χ.conductor)) :
    gaussSum χ stdAddChar =
      (μ (q / χ.conductor) : ℂ) * χ.primitiveCharacter (q / χ.conductor) *
        gaussSum χ.primitiveCharacter stdAddChar := by
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  exact gaussSum_changeLevel_eq (Nat.mul_div_cancel' χ.conductor_dvd_level).symm hcop hsq _ _

/-- **`|τ(χ)|² = q*`** under the hypotheses of (8.16) to (8.18): `q/q*` squarefree and prime
to `q*`. -/
theorem norm_sq_gaussSum_eq_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hsq : Squarefree (q / χ.conductor)) (hcop : χ.conductor.Coprime (q / χ.conductor)) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = χ.conductor := by
  rw [gaussSum_eq_moebius_mul χ hsq hcop, norm_mul, norm_mul, mul_pow, mul_pow,
    norm_sq_gaussSum_of_isPrimitive χ.primitiveCharacter_isPrimitive]
  have hu : IsUnit ((q / χ.conductor : ℕ) : ZMod χ.conductor) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcop.symm
  have h1 : ‖χ.primitiveCharacter ((q / χ.conductor : ℕ) : ZMod χ.conductor)‖ = 1 := by
    have := χ.primitiveCharacter.unit_norm_eq_one hu.unit
    rwa [hu.unit_spec] at this
  have h2 : ‖((μ (q / χ.conductor) : ℤ) : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs,
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq, Int.cast_one]
  rw [h1, h2]; ring

/-- The same for a character presented as `changeLevel` of a primitive `χ₁ mod q₁`. -/
theorem norm_sq_gaussSum_changeLevel {q q1 : ℕ} [NeZero q] [NeZero q1]
    {χ1 : DirichletCharacter ℂ q1} (hχ1 : χ1.IsPrimitive) (hd : q1 ∣ q)
    (hsq : Squarefree (q / q1)) (hcop : q1.Coprime (q / q1)) :
    ‖gaussSum (changeLevel hd χ1) (stdAddChar (N := q))‖ ^ 2 = q1 := by
  rw [gaussSum_changeLevel_eq (Nat.mul_div_cancel' hd).symm hcop hsq χ1 hd, norm_mul, norm_mul,
    mul_pow, mul_pow, norm_sq_gaussSum_of_isPrimitive hχ1]
  have hu : IsUnit ((q / q1 : ℕ) : ZMod q1) := (ZMod.isUnit_iff_coprime _ _).mpr hcop.symm
  have h1 : ‖χ1 ((q / q1 : ℕ) : ZMod q1)‖ = 1 := by
    have := χ1.unit_norm_eq_one hu.unit
    rwa [hu.unit_spec] at this
  have h2 : ‖((μ (q / q1) : ℤ) : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs,
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq, Int.cast_one]
  rw [h1, h2]; ring

/-! ### Bridge to the character sums `S_k(χ)` of (8.17), (8.18) -/

/-- For primitive `χ mod r`, `χ̄(n) τ(χ) = Σ_a χ(a) e(an/r)`. -/
theorem inv_mul_gaussSum_eq {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (n : ZMod r) :
    χ⁻¹ n * gaussSum χ stdAddChar = ∑ a, χ a * stdAddChar (a * n) := by
  rw [← gaussSum_mulShift_of_isPrimitive _ hχ, gaussSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mulShift_apply, mul_comm n a]

/-- **Bridge**: for primitive `χ mod r` and a finite set `P`, with `S(χ) = Σ_{p ∈ P} χ(p)`,
`r |S(χ)|² = |Σ_a χ(a) Σ_{p ∈ P} e(ap/r)|²`. The lab's `Delta.Spsi y k χ` is by definition
`Σ_{p ∈ Xi.Pset y k} χ p`, so this is the step from `|S_k(χ)|²` to the additive sums. -/
theorem card_mul_norm_sq_charSum_eq {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (P : Finset ℕ) :
    (r : ℝ) * ‖∑ p ∈ P, χ (p : ZMod r)‖ ^ 2 =
      ‖∑ a, χ a * ∑ p ∈ P, stdAddChar (a * (p : ZMod r))‖ ^ 2 := by
  have e : ∑ a, χ a * ∑ p ∈ P, stdAddChar (a * (p : ZMod r)) =
      gaussSum χ stdAddChar * star (∑ p ∈ P, χ (p : ZMod r)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MulChar.star_apply', mul_comm, inv_mul_gaussSum_eq hχ]
  rw [e, norm_mul, mul_pow, norm_sq_gaussSum_of_isPrimitive hχ, norm_star]

/-! ### Character Parseval and the step to additive sums -/

section Parseval

variable {r : ℕ} [NeZero r]

/-- `conj χ(b) = χ(b⁻¹)` for a unit `b`. -/
lemma star_apply_unit (χ : DirichletCharacter ℂ r) {b : ZMod r} (hb : IsUnit b) :
    star (χ b) = χ b⁻¹ := by
  rw [Complex.star_def]
  have hn : ‖χ b‖ = 1 := by
    have := χ.unit_norm_eq_one hb.unit
    simpa using this
  have hmul : χ b⁻¹ * χ b = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit b hb, map_one]
  have hinv : χ b⁻¹ = (χ b)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  rw [hinv, Complex.inv_def]
  have hns : Complex.normSq (χ b) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn]; norm_num
  rw [hns]; simp

/-- **Character Parseval**: `Σ_{χ mod r} |Σ_a χ(a) f(a)|² = φ(r) Σ_{a unit} |f(a)|²`. -/
theorem sum_norm_sq_twist (f : ZMod r → ℂ) :
    ∑ χ : DirichletCharacter ℂ r, ‖∑ a, χ a * f a‖ ^ 2 =
      (r.totient : ℝ) * ∑ a ∈ univ.filter IsUnit, ‖f a‖ ^ 2 := by
  set U := (univ : Finset (ZMod r)).filter IsUnit
  have hU : ∀ χ : DirichletCharacter ℂ r, ∑ a, χ a * f a = ∑ a ∈ U, χ a * f a := by
    intro χ
    rw [Finset.sum_filter_of_ne]
    intro a _ ha
    by_contra hu
    exact ha (by rw [MulChar.map_nonunit _ hu, zero_mul])
  have key : ∀ χ : DirichletCharacter ℂ r, ((‖∑ a, χ a * f a‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ U ×ˢ U, f q.1 * star (f q.2) * (χ q.2⁻¹ * χ q.1) := by
    intro χ
    have hz : ((‖∑ a ∈ U, χ a * f a‖ ^ 2 : ℝ) : ℂ) =
        (∑ a ∈ U, χ a * f a) * star (∑ a ∈ U, χ a * f a) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hU, hz, star_sum, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [star_mul, star_apply_unit χ (Finset.mem_filter.1 (Finset.mem_product.1 hq).2).2]
    ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [key]
  rw [Finset.sum_comm]
  have h2 : ∀ q ∈ U ×ˢ U, ∑ χ : DirichletCharacter ℂ r, f q.1 * star (f q.2) * (χ q.2⁻¹ * χ q.1) =
      if q.2 = q.1 then (r.totient : ℂ) * ((‖f q.1‖ ^ 2 : ℝ) : ℂ) else 0 := by
    intro q hq
    rw [← Finset.mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      (Finset.mem_filter.1 (Finset.mem_product.1 hq).2).2]
    split_ifs with h
    · rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    · ring
  rw [Finset.sum_congr rfl h2, Finset.sum_product, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_ite_eq' U a]
  simp only [ha, ↓reduceIte]
  push_cast; ring

/-- **The step to the additive large sieve**: for a finite set `P` and `r ≥ 1`,
`r Σ*_{χ mod r} |Σ_{p ∈ P} χ(p)|² ≤ φ(r) Σ_{(a, r) = 1} |Σ_{p ∈ P} e(ap/r)|²`, with `Σ*` over
primitive characters. With `P = Xi.Pset y k` the left side is `r · Lemma13Red.Qr y k r`. -/
theorem card_mul_sum_primitive_le (P : Finset ℕ) :
    (r : ℝ) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.conductor = r),
        ‖∑ p ∈ P, χ (p : ZMod r)‖ ^ 2 ≤
      (r.totient : ℝ) *
        ∑ a ∈ (univ : Finset (ZMod r)).filter IsUnit,
          ‖∑ p ∈ P, stdAddChar (a * (p : ZMod r))‖ ^ 2 := by
  rw [Finset.mul_sum, ← sum_norm_sq_twist]
  calc ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.conductor = r),
        (r : ℝ) * ‖∑ p ∈ P, χ (p : ZMod r)‖ ^ 2
      = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.conductor = r),
          ‖∑ a, χ a * ∑ p ∈ P, stdAddChar (a * (p : ZMod r))‖ ^ 2 :=
        Finset.sum_congr rfl fun χ hχ =>
          card_mul_norm_sq_charSum_eq (Finset.mem_filter.1 hχ).2 P
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)

/-- **The paper's identity on page 65**: if every `p ∈ P` is prime to `r`, then
`φ(r) Σ_{(a, r) = 1} |Σ_{p ∈ P} e(ap/r)|² = Σ_{χ mod r} |τ(χ)|² |Σ_{p ∈ P} χ(p)|²`,
over all characters, primitive or not. -/
theorem totient_mul_sum_additive_eq (P : Finset ℕ) (hP : ∀ p ∈ P, IsUnit (p : ZMod r)) :
    (r.totient : ℝ) *
        ∑ a ∈ (univ : Finset (ZMod r)).filter IsUnit,
          ‖∑ p ∈ P, stdAddChar (a * (p : ZMod r))‖ ^ 2 =
      ∑ χ : DirichletCharacter ℂ r,
        ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ p ∈ P, χ (p : ZMod r)‖ ^ 2 := by
  rw [← sum_norm_sq_twist]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have e : ∑ a, χ a * ∑ p ∈ P, stdAddChar (a * (p : ZMod r)) =
      gaussSum χ stdAddChar * star (∑ p ∈ P, χ (p : ZMod r)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hu := hP p hp
    have := gaussSum_mulShift_eq χ stdAddChar hu.unit
    rw [hu.unit_spec, gaussSum] at this
    rw [MulChar.star_apply', mul_comm (gaussSum χ stdAddChar), ← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mulShift_apply, mul_comm (p : ZMod r) a]
  rw [e, norm_mul, mul_pow, norm_star]

end Parseval

end LeanLab.RieselVaughan1983.GaussImprim
