module

public import Mathlib
public import LeanLab.RieselVaughan1983.Lemma12Sum

/-!
P0032 Riesel-Vaughan 1983, (2.25) and (2.26): odd partial sums below A₁₀ and A₁₁.
Unit U-1194, PC run 20261020T0703Z-22071. AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN.

* `odd_sum_le_prod`: for `h ≥ 0`, `Σ_{r ≤ D, r odd} μ(r)² Π_{p ∣ r} h(p) ≤ Π_{2 < p ≤ D} (1 + h(p))`,
  by expanding the product over subsets of primes and the injection `r ↦ primeFactors r` on odd
  squarefree `r`.
* `A10`, `A11`: the Euler products `Π_{p > 2} (1 + 1/(p(p − 1)))` and `Π_{p > 2} (1 + g(p)/p)`,
  defined as the supremum of the partial products, bounded by `exp 1` and `exp 4`.
* `odd_sum_A10`: `Σ_{r ≤ B, r odd} μ(r)²/(r φ(r)) ≤ A₁₀` for every `B`, the input below `A₁₀`
  that `Lemma10Sum.lean` leaves open.
* `odd_sum_A11`: `Σ_{r ≤ D, r odd} g(r)/r ≤ A₁₁` for every `D`, the input below `A₁₁` that
  `Lemma12Sum.lean` leaves open.
The numerical values A₁₀ = 1.2957310 and A₁₁ = 1.7724311 are checked in Python, not in Lean.
KNOWN mathematics.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.OddSums

/-- The odd primes up to `D`. -/
def S (D : ℕ) : Finset ℕ := (Icc 3 D).filter Nat.Prime

lemma primeFactors_subset_S {r D : ℕ} (hr : r ∈ Icc 1 D) (ho : Odd r) :
    r.primeFactors ∈ (S D).powerset := by
  rw [mem_powerset]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  simp only [mem_Icc] at hr
  simp only [S, mem_filter, mem_Icc]
  refine ⟨⟨?_, (Nat.le_of_dvd (by omega) hpd).trans hr.2⟩, hpp⟩
  rcases hpp.eq_two_or_odd' with h2 | hodd
  · subst h2; exact absurd (even_iff_two_dvd.2 hpd) (Nat.not_even_iff_odd.2 ho)
  · have := hpp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · have : p = 2 := by omega
      subst this; exact absurd hodd (by decide)
    · exact h

/-- The generic bound: odd squarefree sums below the Euler product. -/
theorem odd_sum_le_prod (h : ℕ → ℝ) (hh : ∀ p, 0 ≤ h p) (D : ℕ) :
    ∑ r ∈ (Icc 1 D).filter Odd, ((μ r : ℝ)) ^ 2 * ∏ p ∈ r.primeFactors, h p ≤
      ∏ p ∈ S D, (1 + h p) := by
  rw [prod_one_add]
  set R := (Icc 1 D).filter Odd
  have hsplit : ∑ r ∈ R, ((μ r : ℝ)) ^ 2 * ∏ p ∈ r.primeFactors, h p =
      ∑ r ∈ R.filter Squarefree, ∏ p ∈ r.primeFactors, h p := by
    rw [show (∑ r ∈ R.filter Squarefree, ∏ p ∈ r.primeFactors, h p) =
        ∑ r ∈ R, if Squarefree r then ∏ p ∈ r.primeFactors, h p else 0 from sum_filter _ _]
    apply sum_congr rfl
    intro r _
    split_ifs with hs
    · have : ((μ r : ℝ)) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hs
      rw [this, one_mul]
    · rw [moebius_eq_zero_of_not_squarefree hs]; simp
  rw [hsplit]
  have hinj : Set.InjOn (fun r : ℕ => r.primeFactors) (R.filter Squarefree : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_setOf_eq] at ha hb
    have ea := Nat.prod_primeFactors_of_squarefree ha.2
    have eb := Nat.prod_primeFactors_of_squarefree hb.2
    simp only at hab
    rw [← ea, ← eb, hab]
  rw [← sum_image (f := fun T => ∏ p ∈ T, h p) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro T hT
    rw [mem_image] at hT
    obtain ⟨r, hrR, rfl⟩ := hT
    have h1 := (mem_filter.1 hrR).1
    have h2 := mem_filter.1 h1
    exact primeFactors_subset_S h2.1 h2.2
  · intro T _ _
    exact prod_nonneg fun p _ => hh p

/-- Partial Euler products are bounded by `exp` of the sum of the local terms. -/
lemma prod_le_exp (h : ℕ → ℝ) (hh : ∀ p, 0 ≤ h p) (s : Finset ℕ) :
    ∏ p ∈ s, (1 + h p) ≤ Real.exp (∑ p ∈ s, h p) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun p _ => by linarith [hh p])
    (fun p _ => by linarith [Real.add_one_le_exp (h p)])

/-- The telescoping bound `Σ_{2 ≤ n ≤ B} 1/(n(n − 1)) ≤ 1`. -/
lemma sum_inv_mul_pred_le (B : ℕ) :
    ∑ n ∈ Icc 2 B, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 - 1 / (max B 1 : ℕ) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rcases Nat.eq_zero_or_pos B with hB | hB
    · subst hB; simp
    · rw [sum_Icc_succ_top (by omega)]
      have hmax : (max B 1 : ℕ) = B := by omega
      have hmax' : (max (B + 1) 1 : ℕ) = B + 1 := by omega
      rw [hmax] at ih; rw [hmax']
      have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
      push_cast
      have hB0 : (B : ℝ) ≠ 0 := by positivity
      have hB1 : (B : ℝ) + 1 ≠ 0 := by positivity
      have : (1 : ℝ) / (((B : ℝ) + 1) * ((B : ℝ) + 1 - 1)) = 1 / B - 1 / (B + 1) := by
        rw [show (B : ℝ) + 1 - 1 = B by ring, div_sub_div _ _ hB0 hB1,
          div_eq_div_iff (mul_ne_zero hB1 hB0) (mul_ne_zero hB0 hB1)]
        ring
      rw [this]; linarith

lemma S_sub_Icc (D : ℕ) : S D ⊆ Icc 2 D := by
  intro p hp; simp only [S, mem_filter, mem_Icc] at hp ⊢; omega

/-- A generic bound for `Σ_{p ∈ S D} h(p)` when `h(p) ≤ c/(p(p − 1))`. -/
lemma sum_S_le (h : ℕ → ℝ) (hh : ∀ p, 0 ≤ h p) (c : ℝ) (hc : 0 ≤ c)
    (hle : ∀ p, 3 ≤ p → h p ≤ c * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) (D : ℕ) :
    ∑ p ∈ S D, h p ≤ c := by
  have h1 : ∑ p ∈ S D, h p ≤ ∑ p ∈ S D, c * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    apply sum_le_sum; intro p hp
    simp only [S, mem_filter, mem_Icc] at hp
    exact hle p hp.1.1
  have hnn : ∀ n ∈ Icc 2 D, 0 ≤ c * (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
    intro n hn; simp only [mem_Icc] at hn
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    apply mul_nonneg hc; apply div_nonneg zero_le_one; nlinarith
  have h2 := sum_le_sum_of_subset_of_nonneg (S_sub_Icc D) (fun n hn _ => hnn n hn)
  have h2' : ∑ n ∈ Icc 2 D, c * (1 / ((n : ℝ) * ((n : ℝ) - 1)))
      = c * ∑ n ∈ Icc 2 D, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by rw [mul_sum]
  have h3 := sum_inv_mul_pred_le D
  have h4 : (0 : ℝ) ≤ 1 / ((max D 1 : ℕ) : ℝ) := by positivity
  have h5 : c * ∑ n ∈ Icc 2 D, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ c * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  linarith

/-- The Euler product as the supremum of its partial products. -/
def Aprod (h : ℕ → ℝ) : ℝ := ⨆ D : ℕ, ∏ p ∈ S D, (1 + h p)

lemma bdd (h : ℕ → ℝ) (hh : ∀ p, 0 ≤ h p) (c : ℝ) (hc : 0 ≤ c)
    (hle : ∀ p, 3 ≤ p → h p ≤ c * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) :
    BddAbove (Set.range fun D : ℕ => ∏ p ∈ S D, (1 + h p)) := by
  refine ⟨Real.exp c, ?_⟩
  rintro _ ⟨D, rfl⟩
  exact (prod_le_exp h hh (S D)).trans (Real.exp_le_exp.2 (sum_S_le h hh c hc hle D))

lemma Aprod_le (h : ℕ → ℝ) (hh : ∀ p, 0 ≤ h p) (c : ℝ) (hc : 0 ≤ c)
    (hle : ∀ p, 3 ≤ p → h p ≤ c * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) :
    Aprod h ≤ Real.exp c := by
  apply ciSup_le
  intro D
  exact (prod_le_exp h hh (S D)).trans (Real.exp_le_exp.2 (sum_S_le h hh c hc hle D))

/-! ### A₁₀ -/

def h10 (p : ℕ) : ℝ := 1 / ((p : ℝ) * ((p : ℝ) - 1))

lemma h10_nonneg (p : ℕ) : 0 ≤ h10 p := by
  unfold h10
  rcases Nat.eq_zero_or_pos p with h | h
  · subst h; simp
  · have : (1 : ℝ) ≤ p := by exact_mod_cast h
    apply div_nonneg zero_le_one; nlinarith

/-- `A₁₀ = Π_{p > 2} (1 + 1/(p(p − 1)))`, the paper's (2.25). -/
def A10 : ℝ := Aprod h10

theorem A10_le : A10 ≤ Real.exp 1 :=
  Aprod_le h10 h10_nonneg 1 zero_le_one (fun p _ => by rw [one_mul]; exact le_refl _)

/-- For squarefree `r`, `1/(r φ(r)) = Π_{p ∣ r} 1/(p(p − 1))`. -/
lemma inv_mul_totient_eq {r : ℕ} (hs : Squarefree r) :
    (1 : ℝ) / ((r : ℝ) * (r.totient : ℝ)) = ∏ p ∈ r.primeFactors, h10 p := by
  have hr0 : r ≠ 0 := hs.ne_zero
  have er := Nat.prod_primeFactors_of_squarefree hs
  have key := Nat.totient_mul_prod_primeFactors r
  rw [er] at key
  have hphi : r.totient = ∏ p ∈ r.primeFactors, (p - 1) := by
    have hr : 0 < r := Nat.pos_of_ne_zero hr0
    exact Nat.eq_of_mul_eq_mul_right hr (by rw [key, mul_comm])
  have hr' : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← er]
    push_cast; rfl
  have hphi' : (r.totient : ℝ) = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
    rw [hphi]; push_cast
    apply prod_congr rfl; intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  rw [hr', hphi', ← prod_mul_distrib, one_div, ← prod_inv_distrib]
  apply prod_congr rfl; intro p _; unfold h10; rw [one_div]

/-- (2.25) input: every odd partial sum is at most `A₁₀`. -/
theorem odd_sum_A10 (B : ℕ) :
    ∑ r ∈ (Icc 1 B).filter Odd, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ)) ≤ A10 := by
  have hterm : ∀ r, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ)) =
      ((μ r : ℝ)) ^ 2 * ∏ p ∈ r.primeFactors, h10 p := by
    intro r
    by_cases hs : Squarefree r
    · rw [← inv_mul_totient_eq hs]; ring
    · rw [moebius_eq_zero_of_not_squarefree hs]; simp
  simp_rw [hterm]
  refine (odd_sum_le_prod h10 h10_nonneg B).trans ?_
  exact le_ciSup (bdd h10 h10_nonneg 1 zero_le_one (fun p _ => by rw [one_mul]; exact le_refl _)) B

/-! ### A₁₁ -/

def h11 (p : ℕ) : ℝ := L12.gp p / p

lemma h11_nonneg (p : ℕ) : 0 ≤ h11 p := by
  unfold h11 L12.gp
  rcases Nat.lt_or_ge p 2 with h | h
  · interval_cases p <;> simp
  · have : (2 : ℝ) ≤ p := by exact_mod_cast h
    apply div_nonneg _ (by linarith)
    apply div_nonneg (by linarith) (by positivity)

lemma h11_le (p : ℕ) (hp : 3 ≤ p) : h11 p ≤ 4 * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  unfold h11 L12.gp
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < (p : ℝ) * ((p : ℝ) - 1) := by positivity
  nlinarith

/-- `A₁₁ = Π_{p > 2} (1 + g(p)/p)`, the paper's (2.26). -/
def A11 : ℝ := Aprod h11

theorem A11_le : A11 ≤ Real.exp 4 :=
  Aprod_le h11 h11_nonneg 4 (by norm_num) h11_le

/-- (2.26) input: every odd partial sum of `g(r)/r` is at most `A₁₁`. -/
theorem odd_sum_A11 (D : ℕ) :
    ∑ r ∈ (Icc 1 D).filter Odd, L12.gfun r / r ≤ A11 := by
  have hterm : ∀ r ∈ (Icc 1 D).filter Odd, L12.gfun r / r =
      ((μ r : ℝ)) ^ 2 * ∏ p ∈ r.primeFactors, h11 p := by
    intro r hr
    have ho : Odd r := (mem_filter.1 hr).2
    unfold L12.gfun
    rw [if_pos ho]
    by_cases hs : Squarefree r
    · have er := Nat.prod_primeFactors_of_squarefree hs
      have hr' : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
        conv_lhs => rw [← er]
        push_cast; rfl
      rw [hr', mul_div_assoc, ← prod_div_distrib]
      rfl
    · rw [moebius_eq_zero_of_not_squarefree hs]; simp
  rw [sum_congr rfl hterm]
  refine (odd_sum_le_prod h11 h11_nonneg D).trans ?_
  exact le_ciSup (bdd h11 h11_nonneg 4 (by norm_num) h11_le) D

/-- Vacuity: the first partial product, `S 3 = {3}`, gives `A₁₀ ≥ 1 + 1/6`. -/
theorem A10_ge : 1 + 1 / 6 ≤ A10 := by
  have h := le_ciSup (bdd h10 h10_nonneg 1 zero_le_one (fun p _ => by rw [one_mul]; exact le_refl _)) 3
  have hS : S 3 = {3} := by decide
  have h3 : h10 3 = 1 / 6 := by unfold h10; norm_num
  simp only [hS, prod_singleton, h3] at h
  unfold A10 Aprod
  exact h

end LeanLab.RieselVaughan1983.OddSums
