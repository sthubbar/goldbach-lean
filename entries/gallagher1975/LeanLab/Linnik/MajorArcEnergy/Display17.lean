module

public import LeanLab.Linnik.MajorArcEnergy.Display7
public import LeanLab.Linnik.MajorArcEnergy.Leaves1517

/-!
Gallagher 1975 P0094 pp.131 and 132, display 17 with its printed proof.
`exceptional_weight_bound_of_cited` proves the statement of `exceptional_weight_bound`
from the CITED-LEFT leaf `induced_cn_bound`, display 5, and the helpers of Display7.lean.
It never uses `exceptional_weight_bound` itself.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a

/-! ### The principal character, p.131 -/

/-- Gallagher 1975 p.131 proof of display 17: the character 1 induces the principal
character 1_q to every modulus q. -/
theorem induced_one (q : ℕ) : induced one q = 1 := by
  unfold induced one
  split_ifs <;> simp

/-! ### One modulus q, pp.131 and 132 -/

/-- Gallagher 1975 p.131 proof of display 17: the factor r/(phi(r) phi(r_n)) in front of
the sum over s, with r_n = r/(r, n). When the q term is nonzero, r_n = r and this is the
printed r/phi^2(r). -/
noncomputable def excFactor (r N : ℕ) : ℝ :=
  (r : ℝ) / ((r.totient : ℝ) * (r / Nat.gcd r N).totient)

theorem excFactor_nonneg (r N : ℕ) : 0 ≤ excFactor r N := by
  unfold excFactor; positivity

/-- Gallagher 1975 pp.131 and 132 proof of display 17, one term: if the q coefficient z has
|z| at most r phi(q)/phi(q_n), and vanishes unless q = r s with s squarefree and prime to r,
then the q term of C_n is at most r/(phi(r) phi(r_n)) times mu^2(s)/(phi(s) phi(s_n)). -/
theorem exc_term_le {q r N : ℕ} (hq : 1 ≤ q) (hr : r ∣ q) (z : ℂ)
    (hn : ‖z‖ ≤ (r : ℝ) * q.totient / (q / Nat.gcd q N).totient)
    (hz : z ≠ 0 → Squarefree (q / r) ∧ Nat.Coprime (q / r) r) :
    1 / (q.totient : ℝ) ^ 2 * ‖z‖ ≤
      if Squarefree (q / r) ∧ Nat.Coprime (q / r) r then
        excFactor r N * eulerTerm N (q / r) else 0 := by
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr hq
  by_cases h0 : z = 0
  · rw [h0, norm_zero, mul_zero]
    split_ifs
    · exact mul_nonneg (excFactor_nonneg _ _) (eulerTerm_nonneg _ _)
    · exact le_rfl
  obtain ⟨hsq, hcop⟩ := hz h0
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hsq, hcop⟩)]
  obtain ⟨s, rfl⟩ := hr
  rw [Nat.mul_div_cancel_left _ hr0] at hcop hsq ⊢
  have hs0 : 0 < s := Nat.pos_of_ne_zero hsq.ne_zero
  obtain ⟨-, h2, h3⟩ := split_q (m := r) (N := N) hcop
  rw [h3, h2] at hn
  rw [h2]
  have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr0
  have hφs : (0 : ℝ) < s.totient := by exact_mod_cast Nat.totient_pos.mpr hs0
  have hrn : 0 < r / Nat.gcd r N :=
    Nat.div_pos (Nat.gcd_le_left _ hr0) (Nat.gcd_pos_of_pos_left _ hr0)
  have hsn : 0 < s / Nat.gcd s N :=
    Nat.div_pos (Nat.gcd_le_left _ hs0) (Nat.gcd_pos_of_pos_left _ hs0)
  have hφrn : (0 : ℝ) < (r / Nat.gcd r N).totient := by exact_mod_cast Nat.totient_pos.mpr hrn
  have hφsn : (0 : ℝ) < (s / Nat.gcd s N).totient := by exact_mod_cast Nat.totient_pos.mpr hsn
  push_cast at hn ⊢
  calc 1 / ((r.totient : ℝ) * s.totient) ^ 2 * ‖z‖
      ≤ 1 / ((r.totient : ℝ) * s.totient) ^ 2 *
          ((r : ℝ) * (r.totient * s.totient) /
            ((r / Nat.gcd r N).totient * (s / Nat.gcd s N).totient)) := by gcongr
    _ = excFactor r N * eulerTerm N s := by
        unfold excFactor eulerTerm
        field_simp

/-! ### Summing over q = r s, p.131 -/

/-- Gallagher 1975 p.131 proof of display 17: summing the q terms over q = r s, the weight
C_n is at most r/(phi(r) phi(r_n)) times the sum over squarefree s prime to r of
mu^2(s)/(phi(s) phi(s_n)); here s runs up to P, a finite part of Gallagher's sum. -/
theorem weight_le_exc (P : ℝ) (n : ℤ) {x y : PChar} {r : ℕ} (hr : 0 < r)
    (hm : Nat.lcm (x.1 + 1) (y.1 + 1) = r)
    (hterm : ∀ q ∈ pairModuli P x y, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖ ≤
      if Squarefree (q / r) ∧ Nat.Coprime (q / r) r then
        excFactor r n.natAbs * eulerTerm n.natAbs (q / r) else 0) :
    pairWeight P n x y ≤ excFactor r n.natAbs *
      ∑ s ∈ (Icc 1 ⌊P⌋₊).filter (fun s => Squarefree s ∧ Nat.Coprime s r),
        eulerTerm n.natAbs s := by
  set H : ℕ → ℝ := fun s => if Squarefree s ∧ Nat.Coprime s r then
    excFactor r n.natAbs * eulerTerm n.natAbs s else 0 with hH
  have hH0 : ∀ s, 0 ≤ H s := by
    intro s
    simp only [hH]
    split_ifs
    · exact mul_nonneg (excFactor_nonneg _ _) (eulerTerm_nonneg _ _)
    · exact le_rfl
  have hdvd : ∀ q ∈ pairModuli P x y, r ∣ q := fun q hq => hm ▸ (Finset.mem_filter.mp hq).2
  unfold pairWeight
  calc ∑ q ∈ pairModuli P x y, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖
      ≤ ∑ q ∈ pairModuli P x y, H (q / r) :=
        Finset.sum_le_sum fun q hq => hterm q hq
    _ = ∑ s ∈ (pairModuli P x y).image (fun q => q / r), H s := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        simp only at hab
        rw [← Nat.div_mul_cancel (hdvd a ha), ← Nat.div_mul_cancel (hdvd b hb), hab]
    _ ≤ ∑ s ∈ Icc 1 ⌊P⌋₊, H s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          rw [Finset.mem_image] at hs
          obtain ⟨q, hq, rfl⟩ := hs
          have hrq := hdvd q hq
          have hq' := Finset.mem_filter.mp hq
          rw [Finset.mem_Icc] at hq' ⊢
          obtain ⟨⟨hq1, hqP⟩, -⟩ := hq'
          refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hrq) hr, ?_⟩
          exact (Nat.div_le_self _ _).trans hqP
        · intro s _ _
          exact hH0 s
    _ = excFactor r n.natAbs * ∑ s ∈ (Icc 1 ⌊P⌋₊).filter (fun s => Squarefree s ∧
          Nat.Coprime s r), eulerTerm n.natAbs s := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        simp only [hH]
        split_ifs
        · rfl
        · rw [mul_zero]

/-! ### The factor bound, p.132 -/

/-- Gallagher 1975 p.132 proof of display 17, an arithmetic step: phi(a b) is at most
a phi(b), since b/phi(b) is at most a b/phi(a b). -/
theorem totient_mul_le_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((a * b).totient : ℝ) ≤ a * b.totient := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h1 : (b : ℝ) / b.totient ≤ ((a * b : ℕ) : ℝ) / (a * b).totient := by
    rw [ratio_eq_prod hb, ratio_eq_prod hab]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
      (Nat.primeFactors_mono (dvd_mul_left b a) hab)
    · intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
    · intro p hp _
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
  have hφb : (0 : ℝ) < b.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)
  have hφab : (0 : ℝ) < (a * b).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hab)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  rw [div_le_div_iff₀ hφb hφab] at h1
  push_cast at h1
  have : (b : ℝ) * (a * b).totient ≤ b * (a * b.totient) := by linarith
  exact le_of_mul_le_mul_left this hb0

/-- Gallagher 1975 p.132 proof of display 17, the last inequality: with g = (r, n),
r/(phi(r) phi(r_n)) times the product over p dividing n and not r of 1 + 1/(p - 1) is at
most r phi(g)/phi^2(r) times n/phi(n). This uses phi(r) at most g phi(r_n) and
g/phi(g) times that product equal to n/phi(n). -/
theorem excFactor_mul_le {r N : ℕ} (hr : 0 < r) (hN : N ≠ 0) :
    excFactor r N * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ r), (1 + ((p : ℝ) - 1)⁻¹) ≤
      (r : ℝ) * (Nat.gcd r N).totient / (r.totient : ℝ) ^ 2 * ((N : ℝ) / N.totient) := by
  set g := Nat.gcd r N with hgdef
  set k := r / g with hkdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hr
  have hrk : r = g * k := (Nat.mul_div_cancel' (Nat.gcd_dvd_left r N)).symm
  have hk : 1 ≤ k := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_left r N)) hg0
  have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr
  have hφk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hφg : (0 : ℝ) < g.totient := by exact_mod_cast Nat.totient_pos.mpr hg0
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hg0' : (0 : ℝ) < g := by exact_mod_cast hg0
  have hle : (r.totient : ℝ) ≤ g * k.totient := by
    rw [hrk]; exact totient_mul_le_mul hg0.ne' (by omega)
  have hgpf : g.primeFactors = N.primeFactors.filter (fun p => p ∣ r) := by
    rw [hgdef, Nat.primeFactors_gcd hr.ne' hN]
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpm, -⟩, hpN⟩
      exact ⟨hpN, hpm⟩
    · rintro ⟨hpN, hpm⟩
      exact ⟨⟨hpN.1, hpm, hr.ne'⟩, hpN⟩
  set PP := ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ r), (1 + ((p : ℝ) - 1)⁻¹) with hPP
  have hprod : ((g : ℝ) / g.totient) * PP = (N : ℝ) / N.totient := by
    rw [hPP, ratio_eq_prod hg0.ne', ratio_eq_prod hN, hgpf,
      Finset.prod_filter_mul_prod_filter_not]
  have hP0 : 0 ≤ PP := by
    apply Finset.prod_nonneg
    intro p hp
    have : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
    have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    linarith
  have hfac : excFactor r N ≤ (r : ℝ) * g / (r.totient : ℝ) ^ 2 := by
    unfold excFactor
    rw [← hgdef, ← hkdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (r : ℝ) * r.totient * r.totient ≤ (r : ℝ) * r.totient * (g * k.totient) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    nlinarith
  calc excFactor r N * PP ≤ (r : ℝ) * g / (r.totient : ℝ) ^ 2 * PP :=
        mul_le_mul_of_nonneg_right hfac hP0
    _ = (r : ℝ) * g.totient / (r.totient : ℝ) ^ 2 * ((g : ℝ) / g.totient * PP) := by
        field_simp
    _ = _ := by rw [hprod]

/-- Gallagher 1975 p.131 proof of display 17, assembly for one weight: if every q term
satisfies the bound of `exc_term_le`, then C_n is at most
4 n/phi(n) r phi((n, r))/phi^2(r), via the Euler product of Display7.lean. -/
theorem weight_le_final (P : ℝ) (n : ℤ) (hn : n ≠ 0) {x y : PChar} {r : ℕ} (hr : 0 < r)
    (hm : Nat.lcm (x.1 + 1) (y.1 + 1) = r)
    (hterm : ∀ q ∈ pairModuli P x y, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖ ≤
      if Squarefree (q / r) ∧ Nat.Coprime (q / r) r then
        excFactor r n.natAbs * eulerTerm n.natAbs (q / r) else 0) :
    pairWeight P n x y ≤ 4 * totientWeight n * exceptionalWeight r n := by
  have hN : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have h1 := weight_le_exc P n hr hm hterm
  have h2 := euler_sum_le_prod (N := n.natAbs) (m := r) ⌊P⌋₊
  have h3 := euler_prod_le (m := r) hN ⌊P⌋₊
  have h4 := excFactor_mul_le hr hN
  have hA := excFactor_nonneg r n.natAbs
  unfold totientWeight exceptionalWeight
  calc pairWeight P n x y
      ≤ excFactor r n.natAbs * (4 * ∏ p ∈ n.natAbs.primeFactors.filter (fun p => ¬ p ∣ r),
          (1 + ((p : ℝ) - 1)⁻¹)) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hA)
    _ = 4 * (excFactor r n.natAbs * ∏ p ∈ n.natAbs.primeFactors.filter (fun p => ¬ p ∣ r),
          (1 + ((p : ℝ) - 1)⁻¹)) := by ring
    _ ≤ 4 * ((r : ℝ) * (Nat.gcd r n.natAbs).totient / (r.totient : ℝ) ^ 2 *
          ((n.natAbs : ℝ) / n.natAbs.totient)) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = _ := by ring

/-! ### The three weights, pp.131 and 132 -/

/-- Gallagher 1975 p.131 proof of display 17, C_n(chi~, 1): the q coefficient is
c_n(conj chi~_q) conj tau(conj chi~_q) tau(1_q), bounded by display 5 and display 6. -/
theorem term_x_one (P : ℝ) (n : ℤ) {x : PChar} (hx : x.2.IsPrimitive) :
    ∀ q ∈ pairModuli P x one, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x one‖ ≤
      if Squarefree (q / (x.1 + 1)) ∧ Nat.Coprime (q / (x.1 + 1)) (x.1 + 1) then
        excFactor (x.1 + 1) n.natAbs * eulerTerm n.natAbs (q / (x.1 + 1)) else 0 := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq'.1).1
  have hrq : x.1 + 1 ∣ q := (Nat.dvd_lcm_left _ _).trans hq'.2
  have : NeZero q := ⟨by omega⟩
  apply exc_term_le hq1 hrq
  · unfold pairCoeff
    rw [induced_one, inv_one, mul_one, norm_mul, norm_mul, norm_star]
    have hC := (induced_cn_bound hq1 (induced x q)⁻¹ n).1
    have hT := (tau_bound hq1 (induced x q)⁻¹).1
    have hT1 := (tau_bound hq1 (1 : DirichletCharacter ℂ q)).1
    rw [conductor_induced_inv hx hq1 hrq] at hC hT
    rw [DirichletCharacter.conductor_one] at hT1
    simp only [Nat.cast_one, Real.sqrt_one] at hT1
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (x.1 + 1))
    calc ‖cn (induced x q)⁻¹ n‖ * ‖tau (induced x q)⁻¹‖ * ‖tau (1 : DirichletCharacter ℂ q)‖
        ≤ (Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * q.totient / (q / Nat.gcd q n.natAbs).totient) *
            Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * 1 := by gcongr
      _ = _ := by
        generalize Real.sqrt ((x.1 + 1 : ℕ) : ℝ) = t at hs ⊢
        rw [← hs]; ring
  · intro hz
    unfold pairCoeff at hz
    rw [induced_one, inv_one, mul_one] at hz
    have ht : tau (induced x q)⁻¹ ≠ 0 := fun h => hz (by rw [h]; simp)
    have h := (tau_bound hq1 (induced x q)⁻¹).2 ht
    rw [conductor_induced_inv hx hq1 hrq] at h
    exact ⟨h.2.1, h.2.2⟩

/-- Gallagher 1975 p.131 proof of display 17, C_n(1, chi~), treated in the same way as
C_n(chi~, 1): the q coefficient is c_n(chi~_q) conj tau(1_q) tau(conj chi~_q). -/
theorem term_one_x (P : ℝ) (n : ℤ) {x : PChar} (hx : x.2.IsPrimitive) :
    ∀ q ∈ pairModuli P one x, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q one x‖ ≤
      if Squarefree (q / (x.1 + 1)) ∧ Nat.Coprime (q / (x.1 + 1)) (x.1 + 1) then
        excFactor (x.1 + 1) n.natAbs * eulerTerm n.natAbs (q / (x.1 + 1)) else 0 := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq'.1).1
  have hrq : x.1 + 1 ∣ q := (Nat.dvd_lcm_right _ _).trans hq'.2
  have : NeZero q := ⟨by omega⟩
  apply exc_term_le hq1 hrq
  · unfold pairCoeff
    rw [induced_one, inv_one, one_mul, norm_mul, norm_mul, norm_star]
    have hC := (induced_cn_bound hq1 (induced x q) n).1
    have hT := (tau_bound hq1 (induced x q)⁻¹).1
    have hT1 := (tau_bound hq1 (1 : DirichletCharacter ℂ q)).1
    rw [conductor_induced hx hq1 hrq] at hC
    rw [conductor_induced_inv hx hq1 hrq] at hT
    rw [DirichletCharacter.conductor_one] at hT1
    simp only [Nat.cast_one, Real.sqrt_one] at hT1
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (x.1 + 1))
    calc ‖cn (induced x q) n‖ * ‖tau (1 : DirichletCharacter ℂ q)‖ * ‖tau (induced x q)⁻¹‖
        ≤ (Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * q.totient / (q / Nat.gcd q n.natAbs).totient) *
            1 * Real.sqrt ((x.1 + 1 : ℕ) : ℝ) := by gcongr
      _ = _ := by
        generalize Real.sqrt ((x.1 + 1 : ℕ) : ℝ) = t at hs ⊢
        rw [← hs]; ring
  · intro hz
    unfold pairCoeff at hz
    rw [induced_one, inv_one, one_mul] at hz
    have ht : tau (induced x q)⁻¹ ≠ 0 := fun h => hz (by rw [h]; simp)
    have h := (tau_bound hq1 (induced x q)⁻¹).2 ht
    rw [conductor_induced_inv hx hq1 hrq] at h
    exact ⟨h.2.1, h.2.2⟩

/-- Gallagher 1975 p.132 proof of display 17, C_n(chi~, chi~): the q coefficient is
|tau(conj chi~_q)|^2 c_q(n), with c_q(n) = c_n(1_q) bounded by display 5 for the principal
character and |tau|^2 at most r by display 6. -/
theorem term_x_x (P : ℝ) (n : ℤ) {x : PChar} (hx : x.2.IsPrimitive) :
    ∀ q ∈ pairModuli P x x, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x x‖ ≤
      if Squarefree (q / (x.1 + 1)) ∧ Nat.Coprime (q / (x.1 + 1)) (x.1 + 1) then
        excFactor (x.1 + 1) n.natAbs * eulerTerm n.natAbs (q / (x.1 + 1)) else 0 := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq'.1).1
  have hrq : x.1 + 1 ∣ q := (Nat.dvd_lcm_left _ _).trans hq'.2
  have : NeZero q := ⟨by omega⟩
  apply exc_term_le hq1 hrq
  · unfold pairCoeff
    rw [MulChar.inv_mul, norm_mul, norm_mul, norm_star]
    have hC := (induced_cn_bound hq1 (1 : DirichletCharacter ℂ q) n).1
    have hT := (tau_bound hq1 (induced x q)⁻¹).1
    rw [conductor_induced_inv hx hq1 hrq] at hT
    rw [DirichletCharacter.conductor_one] at hC
    simp only [Nat.cast_one, Real.sqrt_one, one_mul] at hC
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (x.1 + 1))
    calc ‖cn (1 : DirichletCharacter ℂ q) n‖ * ‖tau (induced x q)⁻¹‖ * ‖tau (induced x q)⁻¹‖
        ≤ ((q.totient : ℝ) / (q / Nat.gcd q n.natAbs).totient) *
            Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * Real.sqrt ((x.1 + 1 : ℕ) : ℝ) := by gcongr
      _ = _ := by rw [mul_assoc, hs, mul_comm, mul_div_assoc]
  · intro hz
    unfold pairCoeff at hz
    have ht : tau (induced x q)⁻¹ ≠ 0 := fun h => hz (by rw [h]; simp)
    have h := (tau_bound hq1 (induced x q)⁻¹).2 ht
    rw [conductor_induced_inv hx hq1 hrq] at h
    exact ⟨h.2.1, h.2.2⟩

/-! ### Display 17 -/

/-- Gallagher 1975 p.131 display 17, proved by the printed argument on pp.131 and 132 from
display 5, the CITED-LEFT leaf `induced_cn_bound`: C_n(chi~, 1) + C_n(1, chi~) + C_n(chi~, chi~)
is at most 12 n/phi(n) r phi((n, r))/phi^2(r) for every primitive chi~ to conductor r,
uniformly in P. Same statement as `exceptional_weight_bound`. -/
theorem exceptional_weight_bound_of_cited :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ) (x : PChar), n ≠ 0 → x.2.IsPrimitive →
      pairWeight P n x one + pairWeight P n one x + pairWeight P n x x ≤
        K * totientWeight n * exceptionalWeight (x.1 + 1) n := by
  refine ⟨12, by norm_num, ?_⟩
  intro P n x hn hx
  have hr : 0 < x.1 + 1 := by omega
  have hone : one.1 = 0 := rfl
  have h1 := weight_le_final P n hn hr (by rw [hone, Nat.lcm_one_right]) (term_x_one P n hx)
  have h2 := weight_le_final P n hn hr (by rw [hone, Nat.lcm_one_left]) (term_one_x P n hx)
  have h3 := weight_le_final P n hn hr (Nat.lcm_self _) (term_x_x P n hx)
  linarith

end LeanLab.Linnik.MajorArcEnergy

