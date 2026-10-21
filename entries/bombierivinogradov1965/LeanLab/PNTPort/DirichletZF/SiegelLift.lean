module

public import LeanLab.PNTPort.DirichletZF.SiegelSigns
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Moving characters to a common modulus

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input. Bookkeeping for
the all-moduli form of Siegel's theorem.

* `chi8`: the real character mod `8` from Mathlib's `ZMod.χ₈`, non-principal, `chi8² = 1`;
* `lift_sq`, `lift_ne_one`, `L_lift`: `changeLevel` keeps a character real and non-principal,
  and `L(s, ψ') = L(s, ψ) E(s)` with `E(s) = ∏_{p | M} (1 - ψ(p) p^{-s})`;
* `prod_one_sub_inv_ge`: `∏_{p ∈ S} (1 - 1/p) ≥ 1/(|S| + 1)` for a finite set of integers `≥ 2`;
* `card_primeFactors_le_log`: `ω(M) log 2 ≤ log M`;
* `norm_Efac_one_le`: for `χ` mod `N` and `M = A N`, `‖E(1)‖ ≤ 2^{A+1}`;
* `norm_Efac_one_ge`: `‖E(1)‖ ≥ 1/(ω(M) + 1)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Finset

/-- The real character mod `8`, `χ₈` with values in `ℂ`. -/
noncomputable def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

lemma chi8_sq : chi8 ^ 2 = 1 := ((ZMod.isQuadratic_χ₈).comp _).sq_eq_one

lemma chi8_ne_one : chi8 ≠ 1 := by
  have u3 : IsUnit ((3 : ℕ) : ZMod 8) := by decide
  have e1 : chi8 (3 : ℕ) = -1 := by
    show (ZMod.χ₈ (3 : ℕ) : ℂ) = -1
    rw [ZMod.χ₈_nat_eq_if_mod_eight]; norm_num
  intro h
  rw [h, MulChar.one_apply u3] at e1
  norm_num at e1

variable {d M : ℕ}

lemma lift_sq [NeZero M] (h : d ∣ M) {ψ : DirichletCharacter ℂ d} (h2 : ψ ^ 2 = 1) :
    (DirichletCharacter.changeLevel h ψ) ^ 2 = 1 := by
  rw [← map_pow, h2, map_one]

lemma lift_ne_one [NeZero M] (h : d ∣ M) {ψ : DirichletCharacter ℂ d} (hψ : ψ ≠ 1) :
    DirichletCharacter.changeLevel h ψ ≠ 1 := fun e ↦
  hψ ((DirichletCharacter.changeLevel_eq_one_iff h).mp e)

/-- The Euler factor at the primes of `M`. -/
noncomputable def Efac (ψ : DirichletCharacter ℂ d) (M : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ M.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))

lemma L_lift [NeZero d] [NeZero M] (h : d ∣ M) {ψ : DirichletCharacter ℂ d} (hψ : ψ ≠ 1)
    (s : ℂ) : DirichletCharacter.LFunction (DirichletCharacter.changeLevel h ψ) s =
      DirichletCharacter.LFunction ψ s * Efac ψ M s :=
  DirichletCharacter.LFunction_changeLevel h ψ (Or.inl hψ)

lemma factor_one (ψ : DirichletCharacter ℂ d) (p : ℕ) :
    (1 - ψ p * (p : ℂ) ^ (-(1 : ℂ))) = 1 - ψ p / p := by
  rw [Complex.cpow_neg_one, div_eq_mul_inv]

lemma norm_factor_le (ψ : DirichletCharacter ℂ d) {p : ℕ} (hp : p.Prime) :
    ‖1 - ψ p / (p : ℂ)‖ ≤ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc ‖1 - ψ p / (p : ℂ)‖ ≤ 1 + ‖ψ p / (p : ℂ)‖ := by
        have := norm_sub_le (1 : ℂ) (ψ p / p); rwa [norm_one] at this
    _ ≤ 2 := by
        rw [norm_div, Complex.norm_natCast]
        have := ψ.norm_le_one p
        have : ‖ψ p‖ / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith

lemma norm_factor_ge (ψ : DirichletCharacter ℂ d) {p : ℕ} (hp : p.Prime) :
    1 - 1 / (p : ℝ) ≤ ‖1 - ψ p / (p : ℂ)‖ := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have := norm_sub_norm_le (1 : ℂ) (ψ p / p)
  rw [norm_one, norm_div, Complex.norm_natCast] at this
  have h1 : ‖ψ p‖ / p ≤ 1 / p := div_le_div_of_nonneg_right (ψ.norm_le_one p) (by linarith)
  linarith

lemma prod_one_sub_inv_ge (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : 2 ≤ a := hS a (mem_insert_self a s)
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp ↦ hS p (mem_insert_of_mem hp)
    have hna : a ∉ s := fun h ↦ lt_irrefl a (hlt a h)
    rw [prod_insert hna, card_insert_of_notMem hna]
    have ih := ih hs
    have hsub : s ⊆ Ico 2 a := fun x hx ↦ mem_Ico.mpr ⟨hs x hx, hlt x hx⟩
    have hcard : s.card ≤ a - 2 := by
      have := card_le_card hsub; simpa using this
    have hk : (s.card : ℝ) + 2 ≤ a := by
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    have ha0 : (0 : ℝ) < a := by linarith
    have hfac : 0 ≤ 1 - 1 / (a : ℝ) := by
      rw [sub_nonneg, div_le_one ha0]; linarith
    push_cast
    calc 1 / ((s.card : ℝ) + 1 + 1) ≤ (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) := by
          rw [div_le_iff₀ (by positivity)]
          field_simp
          nlinarith
      _ ≤ (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left ih hfac

lemma card_primeFactors_le_log (M : ℕ) [NeZero M] :
    (M.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log M := by
  have h1 : 2 ^ M.primeFactors.card ≤ ∏ p ∈ M.primeFactors, p :=
    pow_card_le_prod _ _ _ fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ M.primeFactors, p ≤ M :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.prod_primeFactors_dvd M)
  have h3 : ((2 : ℝ) ^ M.primeFactors.card) ≤ M := by exact_mod_cast h1.trans h2
  have := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at this

/-- For `χ` mod `N` and `M = A N`, the extra factor at `1` is at most `2^{A+1}`. -/
lemma norm_Efac_one_le {N A : ℕ} [NeZero N] [NeZero A] (χ : DirichletCharacter ℂ N) :
    ‖Efac χ (A * N) 1‖ ≤ 2 ^ (A + 1) := by
  classical
  unfold Efac
  rw [norm_prod]
  simp_rw [factor_one]
  rw [← prod_filter_mul_prod_filter_not (A * N).primeFactors (fun p ↦ p ∣ N)]
  have h1 : ∏ p ∈ (A * N).primeFactors with p ∣ N, ‖1 - χ p / (p : ℂ)‖ = 1 := by
    refine prod_eq_one fun p hp ↦ ?_
    rw [mem_filter] at hp
    have hnu : ¬ IsUnit ((p : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime]
      intro hc
      have hp' := Nat.prime_of_mem_primeFactors hp.1
      exact hp'.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hp.2)
    rw [χ.map_nonunit hnu, zero_div, sub_zero, norm_one]
  rw [h1, one_mul]
  have hsub : (A * N).primeFactors.filter (fun p ↦ ¬ p ∣ N) ⊆ range (A + 1) := by
    intro p hp
    rw [mem_filter] at hp
    have hp' := Nat.prime_of_mem_primeFactors hp.1
    have hdvd := Nat.dvd_of_mem_primeFactors hp.1
    have hA : p ∣ A := ((Nat.Prime.dvd_mul hp').mp hdvd).resolve_right hp.2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne A)) hA))
  calc ∏ p ∈ (A * N).primeFactors with ¬ p ∣ N, ‖1 - χ p / (p : ℂ)‖
      ≤ ∏ _p ∈ (A * N).primeFactors.filter (fun p ↦ ¬ p ∣ N), (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          (fun p hp ↦ norm_factor_le χ (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1))
    _ = 2 ^ ((A * N).primeFactors.filter (fun p ↦ ¬ p ∣ N)).card := by rw [prod_const]
    _ ≤ 2 ^ (A + 1) := by
        have := card_le_card hsub
        rw [card_range] at this
        exact pow_le_pow_right₀ (by norm_num) this

lemma norm_Efac_one_ge (ψ : DirichletCharacter ℂ d) (M : ℕ) :
    1 / ((M.primeFactors.card : ℝ) + 1) ≤ ‖Efac ψ M 1‖ := by
  unfold Efac
  rw [norm_prod]
  simp_rw [factor_one]
  calc 1 / ((M.primeFactors.card : ℝ) + 1) ≤ ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ)) :=
        prod_one_sub_inv_ge _ fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ ∏ p ∈ M.primeFactors, ‖1 - ψ p / (p : ℂ)‖ := by
        refine Finset.prod_le_prod₀ (fun p hp ↦ ?_) (fun p hp ↦
          norm_factor_ge ψ (Nat.prime_of_mem_primeFactors hp))
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        rw [sub_nonneg, div_le_one (by linarith)]; linarith

lemma Efac_one_ne_zero (ψ : DirichletCharacter ℂ d) (M : ℕ) : Efac ψ M 1 ≠ 0 := by
  intro h
  have := norm_Efac_one_ge ψ M
  rw [h, norm_zero] at this
  have : 0 < 1 / ((M.primeFactors.card : ℝ) + 1) := by positivity
  linarith

end LeanLab.PNTPort.DirichletZF

