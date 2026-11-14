module

public import LeanLab.Linnik.MajorArcEnergy.Leaves13

/-!
Gallagher 1975 P0094 p.129, display 7 with its printed Proof of (7).
`pair_weight_bound_of_cited` proves the statement of `pair_weight_bound` from the
CITED-LEFT leaf `induced_cn_bound`, display 5, which at n = 1 also gives display 6.
It never uses `pair_weight_bound` itself.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset
open scoped Classical
open LeanLab.Linnik.Decomp466a

/-! ### Conductors of the induced characters, p.129 Proof of (7) -/

/-- Gallagher 1975 p.128: chi_q is chi lifted to modulus q when the conductor divides q. -/
theorem induced_eq_changeLevel {x : PChar} {q : ℕ} (h : x.1 + 1 ∣ q) :
    induced x q = DirichletCharacter.changeLevel h x.2 := by
  unfold induced
  simp only [h, ↓reduceDIte]

/-- Gallagher 1975 p.129 Proof of (7): for primitive chi to conductor r dividing q,
the induced character chi_q has conductor r. -/
theorem conductor_induced {x : PChar} (hx : x.2.IsPrimitive) {q : ℕ} (hq : 1 ≤ q)
    (h : x.1 + 1 ∣ q) : (induced x q).conductor = x.1 + 1 := by
  have : NeZero q := ⟨by omega⟩
  rw [induced_eq_changeLevel h, DirichletCharacter.conductor_changeLevel]
  exact hx

/-- Gallagher 1975 p.129 Proof of (7): conj chi_q also has conductor r. -/
theorem conductor_induced_inv {x : PChar} (hx : x.2.IsPrimitive) {q : ℕ} (hq : 1 ≤ q)
    (h : x.1 + 1 ∣ q) : (induced x q)⁻¹.conductor = x.1 + 1 := by
  rw [DirichletCharacter.conductor_inv, conductor_induced hx hq h]

/-- Gallagher 1975 p.129 Proof of (7): the conductor r'' of conj chi_q chi'_q,
which is the conductor of conj chi_m chi'_m, divides m = [r, r']. -/
theorem conductor_pair_dvd {x y : PChar} (hx : x.2.IsPrimitive) (hy : y.2.IsPrimitive)
    {q : ℕ} (hq : 1 ≤ q) (hm : Nat.lcm (x.1 + 1) (y.1 + 1) ∣ q) :
    ((induced x q)⁻¹ * induced y q).conductor ∣ Nat.lcm (x.1 + 1) (y.1 + 1) := by
  have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (induced x q)⁻¹ (induced y q)
  rwa [conductor_induced_inv hx hq ((Nat.dvd_lcm_left _ _).trans hm),
    conductor_induced hy hq ((Nat.dvd_lcm_right _ _).trans hm)] at h

/-- Gallagher 1975 p.129 display 6, the case n = 1 of display 5: |tau(chi_q)| is at most
r^(1/2), and tau(chi_q) vanishes unless q = r s with s squarefree and prime to r. -/
theorem tau_bound {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    ‖tau χ‖ ≤ Real.sqrt χ.conductor ∧
      (tau χ ≠ 0 → χ.conductor ∣ q ∧ Squarefree (q / χ.conductor) ∧
        Nat.Coprime (q / χ.conductor) χ.conductor) := by
  have h := induced_cn_bound hq χ 1
  simp only [Int.natAbs_one, Nat.gcd_one_right, Nat.div_one] at h
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  refine ⟨?_, h.2⟩
  have h1 := h.1
  rw [mul_div_assoc, div_self hφ.ne', mul_one] at h1
  exact h1

/-! ### One modulus q, p.129 Proof of (7) -/

/-- Gallagher 1975 p.129 Proof of (7), one term of C_n: with m = [r, r'] and q_n = q/(q, n),
the q term of C_n vanishes unless q/m is squarefree and prime to m, and it is at most
m (m, q_n)^(1/2)/(phi(q) phi(q_n)). This uses display 5 for conj chi_q chi'_q, display 6 for
conj chi_q and conj chi'_q, r r' = (r, r') m, and r'' dividing both m and q_n. -/
theorem pair_term_le {P : ℝ} {n : ℤ} {x y : PChar} (hx : x.2.IsPrimitive)
    (hy : y.2.IsPrimitive) {q : ℕ} (hq : q ∈ pairModuli P x y) :
    1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖ ≤
      if Squarefree (q / Nat.lcm (x.1 + 1) (y.1 + 1)) ∧
          Nat.Coprime (q / Nat.lcm (x.1 + 1) (y.1 + 1)) (Nat.lcm (x.1 + 1) (y.1 + 1)) then
        (Nat.lcm (x.1 + 1) (y.1 + 1) : ℝ) *
            Real.sqrt (Nat.gcd (Nat.lcm (x.1 + 1) (y.1 + 1)) (q / Nat.gcd q n.natAbs)) /
          ((q.totient : ℝ) * (q / Nat.gcd q n.natAbs).totient)
      else 0 := by
  set r := x.1 + 1 with hr
  set r' := y.1 + 1 with hr'
  set m := Nat.lcm r r' with hmdef
  set qn := q / Nat.gcd q n.natAbs with hqn
  unfold pairModuli at hq
  rw [Finset.mem_filter, Finset.mem_Icc] at hq
  obtain ⟨⟨hq1, -⟩, hmq⟩ := hq
  have hφq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq1
  have hqn_pos : 0 < qn := Nat.div_pos (Nat.gcd_le_left _ hq1) (Nat.gcd_pos_of_pos_left _ hq1)
  have hφqn : (0 : ℝ) < qn.totient := by exact_mod_cast Nat.totient_pos.mpr hqn_pos
  have hm_pos : 0 < m := Nat.lcm_pos (by omega) (by omega)
  by_cases hz : pairCoeff n q x y = 0
  · rw [hz, norm_zero, mul_zero]
    split_ifs
    · positivity
    · exact le_rfl
  have hz' := hz
  unfold pairCoeff at hz'
  have hc : cn ((induced x q)⁻¹ * induced y q) n ≠ 0 := fun h => hz' (by rw [h]; ring)
  have ht1 : tau (induced x q)⁻¹ ≠ 0 := fun h => hz' (by rw [h]; simp)
  have ht2 : tau (induced y q)⁻¹ ≠ 0 := fun h => hz' (by rw [h]; ring)
  have hrq : r ∣ q := (Nat.dvd_lcm_left _ _).trans hmq
  have hr'q : r' ∣ q := (Nat.dvd_lcm_right _ _).trans hmq
  obtain ⟨hT1, hS1⟩ := tau_bound hq1 (induced x q)⁻¹
  obtain ⟨hT2, hS2⟩ := tau_bound hq1 (induced y q)⁻¹
  rw [conductor_induced_inv hx hq1 hrq] at hT1 hS1
  rw [conductor_induced_inv hy hq1 hr'q] at hT2 hS2
  obtain ⟨-, hsq1, hco1⟩ := hS1 ht1
  obtain ⟨-, hsq2, hco2⟩ := hS2 ht2
  obtain ⟨hC, hCS⟩ := induced_cn_bound hq1 ((induced x q)⁻¹ * induced y q) n
  obtain ⟨hr''qn, -, -⟩ := hCS hc
  have hr''m := conductor_pair_dvd hx hy hq1 hmq
  set r'' := ((induced x q)⁻¹ * induced y q).conductor with hr''
  obtain ⟨s, hs⟩ := hmq
  obtain ⟨u, hu⟩ : r ∣ m := Nat.dvd_lcm_left _ _
  obtain ⟨u', hu'⟩ : r' ∣ m := Nat.dvd_lcm_right _ _
  have hqm : q / m = s := by rw [hs]; exact Nat.mul_div_cancel_left _ hm_pos
  have hqr : q / r = u * s := by
    have hq' : q = r * (u * s) := by rw [← mul_assoc, ← hu]; exact hs
    rw [hq']; exact Nat.mul_div_cancel_left _ (by omega)
  have hqr' : q / r' = u' * s := by
    have hq' : q = r' * (u' * s) := by rw [← mul_assoc, ← hu']; exact hs
    rw [hq']; exact Nat.mul_div_cancel_left _ (by omega)
  rw [hqr] at hsq1 hco1
  rw [hqr'] at hsq2 hco2
  have hsqf : Squarefree s := Squarefree.squarefree_of_dvd (dvd_mul_left s u) hsq1
  have hcop : Nat.Coprime s m := by
    have h1 : Nat.Coprime s r := Nat.Coprime.coprime_dvd_left (dvd_mul_left s u) hco1
    have h2 : Nat.Coprime s r' := Nat.Coprime.coprime_dvd_left (dvd_mul_left s u') hco2
    exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul r r') (Nat.Coprime.mul_right h1 h2)
  rw [hqm]
  split_ifs with hcond
  swap
  · exact absurd ⟨hsqf, hcop⟩ hcond
  have hnorm : ‖pairCoeff n q x y‖ ≤
      (Real.sqrt r'' * q.totient / qn.totient) * Real.sqrt r * Real.sqrt r' := by
    unfold pairCoeff
    rw [norm_mul, norm_mul, norm_star]
    have h1 : ‖tau (induced x q)⁻¹‖ ≤ Real.sqrt r := by exact_mod_cast hT1
    have h2 : ‖tau (induced y q)⁻¹‖ ≤ Real.sqrt r' := by exact_mod_cast hT2
    gcongr
  have hg_pos : 0 < Nat.gcd m qn := Nat.gcd_pos_of_pos_left _ hm_pos
  have hprod : Real.sqrt r'' * Real.sqrt r * Real.sqrt r' ≤
      m * Real.sqrt (Nat.gcd m qn) := by
    have hr''g : r'' ≤ Nat.gcd m qn := Nat.le_of_dvd hg_pos (Nat.dvd_gcd hr''m hr''qn)
    have hgr : Nat.gcd r r' ≤ m := Nat.le_of_dvd hm_pos ((Nat.gcd_dvd_left _ _).trans
      (Nat.dvd_lcm_left _ _))
    have hrr : r * r' = Nat.gcd r r' * m := (Nat.gcd_mul_lcm r r').symm
    have hkey : (r'' : ℝ) * r * r' ≤ (m : ℝ) ^ 2 * Nat.gcd m qn := by
      have : (r'' : ℝ) * (Nat.gcd r r' * m) ≤ Nat.gcd m qn * (m * m) := by
        have a1 : (r'' : ℝ) ≤ Nat.gcd m qn := by exact_mod_cast hr''g
        have a2 : (Nat.gcd r r' : ℝ) * m ≤ m * m := by
          have : (Nat.gcd r r' : ℝ) ≤ m := by exact_mod_cast hgr
          nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        exact mul_le_mul a1 a2 (by positivity) (by positivity)
      have hrr' : (r : ℝ) * r' = Nat.gcd r r' * m := by exact_mod_cast hrr
      nlinarith
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    calc Real.sqrt (r'' * r * r') ≤ Real.sqrt ((m : ℝ) ^ 2 * Nat.gcd m qn) :=
          Real.sqrt_le_sqrt hkey
      _ = m * Real.sqrt (Nat.gcd m qn) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖
      ≤ 1 / (q.totient : ℝ) ^ 2 *
          ((Real.sqrt r'' * q.totient / qn.totient) * Real.sqrt r * Real.sqrt r') := by
        gcongr
    _ = (Real.sqrt r'' * Real.sqrt r * Real.sqrt r') / (q.totient * qn.totient) := by
        field_simp
    _ ≤ m * Real.sqrt (Nat.gcd m qn) / (q.totient * qn.totient) := by gcongr

/-! ### Writing q = m s, p.129 Proof of (7) -/

/-- Gallagher 1975 p.129 Proof of (7): for q = m s with s prime to m, writing k_n = k/(k, n),
one has (m, q_n) = m_n, phi(q) = phi(m) phi(s) and phi(q_n) = phi(m_n) phi(s_n). -/
theorem split_q {m s N : ℕ} (hcop : Nat.Coprime s m) :
    Nat.gcd m (m * s / Nat.gcd (m * s) N) = m / Nat.gcd m N ∧
      (m * s).totient = m.totient * s.totient ∧
      (m * s / Nat.gcd (m * s) N).totient =
        (m / Nat.gcd m N).totient * (s / Nat.gcd s N).totient := by
  have hg : Nat.gcd (m * s) N = Nat.gcd m N * Nat.gcd s N := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul N hcop.symm, Nat.gcd_comm N m, Nat.gcd_comm N s]
  have hdiv : m * s / Nat.gcd (m * s) N = (m / Nat.gcd m N) * (s / Nat.gcd s N) := by
    rw [hg, Nat.div_mul_div_comm (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)]
  have hsd : s / Nat.gcd s N ∣ s := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hmd : m / Nat.gcd m N ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hc1 : Nat.Coprime (s / Nat.gcd s N) m := Nat.Coprime.coprime_dvd_left hsd hcop
  have hc2 : Nat.Coprime (m / Nat.gcd m N) (s / Nat.gcd s N) :=
    Nat.Coprime.coprime_dvd_left hmd hc1.symm
  refine ⟨?_, Nat.totient_mul hcop.symm, ?_⟩
  · rw [hdiv, Nat.Coprime.gcd_mul_right_cancel_right _ hc1]
    exact Nat.gcd_eq_right hmd
  · rw [hdiv, Nat.totient_mul hc2]

/-- Gallagher 1975 p.129 Proof of (7): the factor m m_n^(1/2)/(phi(m) phi(m_n)) in front
of the sum over s, with m_n = m/(m, n). -/
noncomputable def pairFactor (m N : ℕ) : ℝ :=
  (m : ℝ) * Real.sqrt (m / Nat.gcd m N : ℕ) / ((m.totient : ℝ) * (m / Nat.gcd m N).totient)

/-- Gallagher 1975 p.129 Proof of (7): the summand mu^2(s)/(phi(s) phi(s_n)), taken on
squarefree s, with s_n = s/(s, n). -/
noncomputable def eulerTerm (N s : ℕ) : ℝ :=
  1 / ((s.totient : ℝ) * (s / Nat.gcd s N).totient)

/-- Gallagher 1975 p.129 Proof of (7): the q term of C_n is at most
m m_n^(1/2)/(phi(m) phi(m_n)) times 1/(phi(s) phi(s_n)), with s = q/m squarefree and prime
to m, and vanishes otherwise. -/
theorem pair_term_le_split {P : ℝ} {n : ℤ} {x y : PChar} (hx : x.2.IsPrimitive)
    (hy : y.2.IsPrimitive) {q : ℕ} (hq : q ∈ pairModuli P x y) :
    1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖ ≤
      if Squarefree (q / Nat.lcm (x.1 + 1) (y.1 + 1)) ∧
          Nat.Coprime (q / Nat.lcm (x.1 + 1) (y.1 + 1)) (Nat.lcm (x.1 + 1) (y.1 + 1)) then
        pairFactor (Nat.lcm (x.1 + 1) (y.1 + 1)) n.natAbs *
          eulerTerm n.natAbs (q / Nat.lcm (x.1 + 1) (y.1 + 1))
      else 0 := by
  have h := pair_term_le (n := n) hx hy hq
  have hmq : Nat.lcm (x.1 + 1) (y.1 + 1) ∣ q := (Finset.mem_filter.mp hq).2
  set m := Nat.lcm (x.1 + 1) (y.1 + 1) with hmdef
  have hm_pos : 0 < m := Nat.lcm_pos (by omega) (by omega)
  obtain ⟨s, rfl⟩ := hmq
  rw [Nat.mul_div_cancel_left _ hm_pos] at h ⊢
  split_ifs at h ⊢ with hc
  · obtain ⟨h1, h2, h3⟩ := split_q (N := n.natAbs) hc.2
    rw [h1, h3] at h
    rw [h2] at h ⊢
    refine h.trans (le_of_eq ?_)
    unfold pairFactor eulerTerm
    push_cast
    ring
  · exact h

theorem pairFactor_nonneg (m N : ℕ) : 0 ≤ pairFactor m N := by
  unfold pairFactor; positivity

theorem eulerTerm_nonneg (N s : ℕ) : 0 ≤ eulerTerm N s := by
  unfold eulerTerm; positivity

/-- Gallagher 1975 p.129 Proof of (7): summing the q terms over q = m s gives
C_n(chi, chi') at most m m_n^(1/2)/(phi(m) phi(m_n)) times the sum over squarefree s prime
to m of mu^2(s)/(phi(s) phi(s_n)); here s runs up to P, a finite part of Gallagher's sum. -/
theorem pairWeight_le_split (P : ℝ) (n : ℤ) {x y : PChar} (hx : x.2.IsPrimitive)
    (hy : y.2.IsPrimitive) :
    pairWeight P n x y ≤ pairFactor (Nat.lcm (x.1 + 1) (y.1 + 1)) n.natAbs *
      ∑ s ∈ (Icc 1 ⌊P⌋₊).filter (fun s => Squarefree s ∧
          Nat.Coprime s (Nat.lcm (x.1 + 1) (y.1 + 1))), eulerTerm n.natAbs s := by
  set m := Nat.lcm (x.1 + 1) (y.1 + 1) with hmdef
  have hm_pos : 0 < m := Nat.lcm_pos (by omega) (by omega)
  set H : ℕ → ℝ := fun s => if Squarefree s ∧ Nat.Coprime s m then
    pairFactor m n.natAbs * eulerTerm n.natAbs s else 0 with hH
  have hH0 : ∀ s, 0 ≤ H s := by
    intro s
    simp only [hH]
    split_ifs
    · exact mul_nonneg (pairFactor_nonneg _ _) (eulerTerm_nonneg _ _)
    · exact le_rfl
  unfold pairWeight
  calc ∑ q ∈ pairModuli P x y, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖
      ≤ ∑ q ∈ pairModuli P x y, H (q / m) :=
        Finset.sum_le_sum fun q hq => pair_term_le_split hx hy hq
    _ = ∑ s ∈ (pairModuli P x y).image (fun q => q / m), H s := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        have ha' : m ∣ a := (Finset.mem_filter.mp ha).2
        have hb' : m ∣ b := (Finset.mem_filter.mp hb).2
        simp only at hab
        rw [← Nat.div_mul_cancel ha', ← Nat.div_mul_cancel hb', hab]
    _ ≤ ∑ s ∈ Icc 1 ⌊P⌋₊, H s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          rw [Finset.mem_image] at hs
          obtain ⟨q, hq, rfl⟩ := hs
          have hq' := Finset.mem_filter.mp hq
          rw [Finset.mem_Icc] at hq' ⊢
          obtain ⟨⟨hq1, hqP⟩, hmq⟩ := hq'
          refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hmq) hm_pos, ?_⟩
          exact (Nat.div_le_self _ _).trans hqP
        · intro s _ _
          exact hH0 s
    _ = pairFactor m n.natAbs * ∑ s ∈ (Icc 1 ⌊P⌋₊).filter (fun s => Squarefree s ∧
          Nat.Coprime s m), eulerTerm n.natAbs s := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        simp only [hH]
        split_ifs
        · rfl
        · rw [mul_zero]

/-! ### The Euler product and the factor bound, p.129 Proof of (7) -/

/-- Gallagher 1975 p.129 Proof of (7), the Euler product bound: the product over k from 2
to X of 1 + 1/(k - 1)^2, which dominates the product over p not dividing mn of
1 + 1/(p - 1)^2, is at most 4. Telescoping with 1 + 1/j^2 at most j^2/(j^2 - 1). -/
theorem tele_le (X : ℕ) :
    ∏ k ∈ Icc 2 X, (1 + ((k : ℝ) - 1)⁻¹ * ((k : ℝ) - 1)⁻¹) ≤ 4 := by
  have key : ∀ X : ℕ, 2 ≤ X →
      ∏ k ∈ Icc 2 X, (1 + ((k : ℝ) - 1)⁻¹ * ((k : ℝ) - 1)⁻¹) ≤ 4 * ((X : ℝ) - 1) / X := by
    intro X hX
    induction X, hX using Nat.le_induction with
    | base => norm_num
    | succ X hX ih =>
      rw [Finset.prod_Icc_succ_top (by omega)]
      have hX' : (2 : ℝ) ≤ X := by exact_mod_cast hX
      push_cast
      have e : ((X : ℝ) + 1 - 1) = X := by ring
      rw [e]
      have hpos : 0 ≤ 1 + (X : ℝ)⁻¹ * (X : ℝ)⁻¹ := by positivity
      calc (∏ k ∈ Icc 2 X, (1 + ((k : ℝ) - 1)⁻¹ * ((k : ℝ) - 1)⁻¹)) *
            (1 + (X : ℝ)⁻¹ * (X : ℝ)⁻¹)
          ≤ 4 * ((X : ℝ) - 1) / X * (1 + (X : ℝ)⁻¹ * (X : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_right ih hpos
        _ ≤ 4 * (X : ℝ) / ((X : ℝ) + 1) := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            have hX0 : (0 : ℝ) < X := by linarith
            field_simp
            nlinarith [sq_nonneg ((X : ℝ)), mul_pos hX0 hX0]
  by_cases hX : 2 ≤ X
  · refine (key X hX).trans ?_
    have hX' : (2 : ℝ) ≤ X := by exact_mod_cast hX
    rw [div_le_iff₀ (by linarith)]
    linarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    norm_num

/-- Gallagher 1975 p.129 Proof of (7): for squarefree s, phi(s) is the product of p - 1
over the primes p dividing s. -/
theorem totient_squarefree_real {s : ℕ} (hs : Squarefree s) :
    (s.totient : ℝ) = ∏ p ∈ s.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors s
  rw [Nat.prod_primeFactors_of_squarefree hs, mul_comm s] at h
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs.ne_zero
  have h2 : s.totient = ∏ p ∈ s.primeFactors, (p - 1) := Nat.eq_of_mul_eq_mul_right hs0 h
  rw [h2, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

/-- Gallagher 1975 p.129 Proof of (7): for squarefree s, the primes dividing
s_n = s/(s, n) are the primes dividing s and not n. -/
theorem primeFactors_div_gcd {s : ℕ} (hs : Squarefree s) (N : ℕ) :
    (s / Nat.gcd s N).primeFactors = s.primeFactors.filter (fun p => ¬ p ∣ N) := by
  have hs0 : s ≠ 0 := hs.ne_zero
  have hgd : Nat.gcd s N ∣ s := Nat.gcd_dvd_left _ _
  have hst : s = Nat.gcd s N * (s / Nat.gcd s N) := (Nat.mul_div_cancel' hgd).symm
  have ht0 : s / Nat.gcd s N ≠ 0 := by
    intro h; rw [h, mul_zero] at hst; exact hs0 hst
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpt, -⟩
    refine ⟨⟨hp, hpt.trans (Nat.div_dvd_of_dvd hgd), hs0⟩, fun hpN => ?_⟩
    have hpg : p ∣ Nat.gcd s N := Nat.dvd_gcd (hpt.trans (Nat.div_dvd_of_dvd hgd)) hpN
    have : p * p ∣ s := by rw [hst]; exact Nat.mul_dvd_mul hpg hpt
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) p hp this
  · rintro ⟨⟨hp, hps, -⟩, hpN⟩
    refine ⟨hp, ?_, ht0⟩
    rw [hst] at hps
    rcases (Nat.Prime.dvd_mul hp).mp hps with h | h
    · exact absurd (h.trans (Nat.gcd_dvd_right _ _)) hpN
    · exact h


/-- Gallagher 1975 p.129 Proof of (7): for squarefree s, mu^2(s)/(phi(s) phi(s_n)) is the
product over p dividing s of 1/(p - 1) times 1 if p divides n and 1/(p - 1) otherwise. -/
theorem eulerTerm_eq_prod {s : ℕ} (hs : Squarefree s) (N : ℕ) :
    eulerTerm N s = ∏ p ∈ s.primeFactors,
      ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹) := by
  have ht : Squarefree (s / Nat.gcd s N) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)) hs
  unfold eulerTerm
  rw [totient_squarefree_real hs, totient_squarefree_real ht, primeFactors_div_gcd hs N,
    Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib, one_div, mul_inv]

/-- Gallagher 1975 p.129 Proof of (7), "The sum is" the Euler product: the sum over squarefree
s at most X prime to m of mu^2(s)/(phi(s) phi(s_n)) is at most the product over primes p at
most X not dividing m of 1 + 1/(p - 1)^2 when p does not divide n and 1 + 1/(p - 1) when it
does. -/
theorem euler_sum_le_prod {N m : ℕ} (X : ℕ) :
    ∑ s ∈ (Icc 1 X).filter (fun s => Squarefree s ∧ Nat.Coprime s m), eulerTerm N s ≤
      ∏ p ∈ (Icc 1 X).filter Nat.Prime, (1 + (if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹))) := by
  set f : ℕ → ℝ := fun p => if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹) with hf
  have hf0 : ∀ p, Nat.Prime p → 0 ≤ f p := by
    intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    simp only [hf]
    split_ifs <;> first | exact le_rfl | (apply mul_nonneg <;> positivity)
  set S := (Icc 1 X).filter (fun s => Squarefree s ∧ Nat.Coprime s m) with hS
  set T := (Icc 1 X).filter Nat.Prime with hT
  have h1 : ∀ s ∈ S, eulerTerm N s = ∏ p ∈ s.primeFactors, f p := by
    intro s hs
    obtain ⟨-, hsq, hcop⟩ := Finset.mem_filter.mp hs
    rw [eulerTerm_eq_prod hsq N]
    apply Finset.prod_congr rfl
    intro p hp
    have hpm : ¬ p ∣ m := by
      intro hpm
      have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
      have := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hps hpm : p ∣ 1)
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' this
    simp only [hf, hpm, ↓reduceIte]
  calc ∑ s ∈ S, eulerTerm N s = ∑ s ∈ S, ∏ p ∈ s.primeFactors, f p := Finset.sum_congr rfl h1
    _ = ∑ t ∈ S.image Nat.primeFactors, ∏ p ∈ t, f p := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2.1
        have hb' := (Finset.mem_filter.mp hb).2.1
        rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb']
        rw [hab]
    _ ≤ ∑ t ∈ T.powerset, ∏ p ∈ t, f p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          rw [Finset.mem_image] at ht
          obtain ⟨s, hs, rfl⟩ := ht
          rw [Finset.mem_powerset]
          intro p hp
          have hsX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1)
          have hpp := Nat.prime_of_mem_primeFactors hp
          rw [hT, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hpp.one_le, (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans
            hsX.2⟩, hpp⟩
        · intro t ht _
          apply Finset.prod_nonneg
          intro p hp
          exact hf0 p (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).2
    _ = ∏ p ∈ T, (1 + f p) := (Finset.prod_one_add T).symm

/-- Gallagher 1975 p.129 Proof of (7): the Euler product is at most 4 times the product over
p dividing n and not m of 1 + 1/(p - 1), since the product of 1 + 1/(p - 1)^2 is bounded. -/
theorem euler_prod_le {N m : ℕ} (hN : N ≠ 0) (X : ℕ) :
    ∏ p ∈ (Icc 1 X).filter Nat.Prime, (1 + (if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹))) ≤
      4 * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) := by
  set T := (Icc 1 X).filter Nat.Prime with hT
  set a : ℕ → ℝ := fun p => 1 + ((p : ℝ) - 1)⁻¹ * ((p : ℝ) - 1)⁻¹ with ha
  set b : ℕ → ℝ := fun p => if p ∣ N ∧ ¬ p ∣ m then 1 + ((p : ℝ) - 1)⁻¹ else 1 with hb
  have hv : ∀ p ∈ T, 0 ≤ ((p : ℝ) - 1)⁻¹ := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    exact inv_nonneg.mpr (by linarith)
  have hstep : ∏ p ∈ T, (1 + (if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹))) ≤ ∏ p ∈ T, (a p * b p) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have := hv p hp
      split_ifs <;> positivity
    · intro p hp
      have v0 := hv p hp
      set v := ((p : ℝ) - 1)⁻¹
      simp only [ha, hb]
      by_cases hpm : p ∣ m
      · simp only [hpm, ↓reduceIte, not_true_eq_false, and_false, add_zero, mul_one]
        nlinarith [mul_nonneg v0 v0]
      · by_cases hpN : p ∣ N
        · simp only [hpm, hpN, ↓reduceIte, not_false_eq_true, and_self, mul_one]
          nlinarith [mul_nonneg (mul_nonneg v0 v0) v0, mul_nonneg v0 v0]
        · simp only [hpm, hpN, ↓reduceIte, false_and, mul_one]
          exact le_rfl
  have hA : ∏ p ∈ T, a p ≤ 4 := by
    refine le_trans ?_ (tele_le X)
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      rw [hT, Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, hp.1.2⟩
    · intro p hp
      have := hv p hp
      positivity
    · intro p _ _
      simp only [ha]
      nlinarith [mul_self_nonneg ((p : ℝ) - 1)⁻¹]
  have hB : ∏ p ∈ T, b p ≤ ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m),
      (1 + ((p : ℝ) - 1)⁻¹) := by
    simp only [hb]
    rw [← Finset.prod_filter]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      rw [Nat.mem_primeFactors]
      exact ⟨⟨(Finset.mem_filter.mp hp.1).2, hp.2.1, hN⟩, hp.2.2⟩
    · intro p hp
      have := hv p (Finset.mem_filter.mp hp).1
      positivity
    · intro p hp _
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
      have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
  have hA0 : 0 ≤ ∏ p ∈ T, a p := Finset.prod_nonneg fun p hp => by
    have := hv p hp
    positivity
  have hB0 : 0 ≤ ∏ p ∈ T, b p := Finset.prod_nonneg fun p hp => by
    have := hv p hp
    simp only [hb]
    split_ifs <;> positivity
  calc _ ≤ ∏ p ∈ T, (a p * b p) := hstep
    _ = (∏ p ∈ T, a p) * ∏ p ∈ T, b p := Finset.prod_mul_distrib
    _ ≤ 4 * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) :=
        mul_le_mul hA hB hB0 (by norm_num)

/-- Gallagher 1975 p.129 Proof of (7), the factor bound, an arithmetic step: for a finite set
of primes, the product of p^3 is at most w times the product of (p - 1)^4, with w equal to
8 if 2 is in the set times 2 if 3 is in the set. -/
theorem prime_prod_cube_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, p ^ 3 ≤ ((if 2 ∈ S then 8 else 1) * (if 3 ∈ S then 2 else 1)) *
      ∏ p ∈ S, (p - 1) ^ 4 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self _ _)
    have ih' := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS]
    set A := ∏ p ∈ S, p ^ 3
    set B := ∏ p ∈ S, (p - 1) ^ 4
    by_cases h2 : p = 2
    · subst h2
      have h3 : (3 ∈ insert 2 S) ↔ 3 ∈ S := by simp
      simp only [Finset.mem_insert_self, ↓reduceIte, h3]
      simp only [hpS, ↓reduceIte, one_mul] at ih'
      norm_num
      split_ifs at ih' ⊢ <;> omega
    · by_cases h3 : p = 3
      · subst h3
        have h2' : (2 ∈ insert 3 S) ↔ 2 ∈ S := by simp
        simp only [Finset.mem_insert_self, ↓reduceIte, h2']
        simp only [hpS, ↓reduceIte, mul_one] at ih'
        norm_num
        split_ifs at ih' ⊢ <;> omega
      · have h2' : (2 ∈ insert p S) ↔ 2 ∈ S := by simp [Ne.symm h2]
        have h3' : (3 ∈ insert p S) ↔ 3 ∈ S := by simp [Ne.symm h3]
        simp only [h2', h3']
        set w := (if 2 ∈ S then 8 else 1) * (if 3 ∈ S then 2 else 1)
        have hp5 : 5 ≤ p := by
          have := hp.two_le
          have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
          omega
        have key : p ^ 3 ≤ (p - 1) ^ 4 := by
          obtain ⟨j, rfl⟩ : ∃ j, p = j + 5 := ⟨p - 5, by omega⟩
          rw [show j + 5 - 1 = j + 4 by omega]
          ring_nf
          nlinarith [sq_nonneg j, Nat.zero_le j]
        calc p ^ 3 * A ≤ (p - 1) ^ 4 * (w * B) := Nat.mul_le_mul key ih'
          _ = w * ((p - 1) ^ 4 * B) := by ring

/-- Gallagher 1975 p.129 Proof of (7), the factor bound: k^3 is at most 16 phi(k)^4. -/
theorem cube_le_totient_pow (k : ℕ) (hk : 1 ≤ k) : k ^ 3 ≤ 16 * k.totient ^ 4 := by
  set R := ∏ p ∈ k.primeFactors, p
  set Q := ∏ p ∈ k.primeFactors, (p - 1)
  have hφ : k.totient * R = k * Q := Nat.totient_mul_prod_primeFactors k
  have hRk : R ≤ k := Nat.le_of_dvd hk (Nat.prod_primeFactors_dvd k)
  have hR0 : 0 < R := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hRQ : R ^ 3 ≤ 16 * Q ^ 4 := by
    have h := prime_prod_cube_le k.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [Finset.prod_pow, Finset.prod_pow] at h
    refine h.trans (Nat.mul_le_mul_right _ ?_)
    split_ifs <;> norm_num
  apply Nat.le_of_mul_le_mul_right (c := R ^ 4) _ (by positivity)
  calc k ^ 3 * R ^ 4 = k ^ 3 * R * R ^ 3 := by ring
    _ ≤ k ^ 3 * k * (16 * Q ^ 4) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hRk) hRQ
    _ = 16 * (k * Q) ^ 4 := by ring
    _ = 16 * k.totient ^ 4 * R ^ 4 := by rw [← hφ]; ring

/-- Gallagher 1975 p.129 Proof of (7), the factor bound: k^(3/2) is at most 4 phi(k)^2,
which bounds m_n^(3/2)/phi^2(m_n). -/
theorem mul_sqrt_le_totient_sq (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * Real.sqrt k ≤ 4 * (k.totient : ℝ) ^ 2 := by
  have h := cube_le_totient_pow k hk
  have h' : (k : ℝ) ^ 3 ≤ 16 * (k.totient : ℝ) ^ 4 := by exact_mod_cast h
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)]
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith

/-- Gallagher 1975 p.129 Proof of (7), last line: k/phi(k) is the product over p dividing k
of 1 + 1/(p - 1). -/
theorem ratio_eq_prod {k : ℕ} (hk : k ≠ 0) :
    (k : ℝ) / k.totient = ∏ p ∈ k.primeFactors, (1 + ((p : ℝ) - 1)⁻¹) := by
  have hφ : (k.totient : ℝ) * ∏ p ∈ k.primeFactors, (p : ℝ) =
      k * ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    have := Nat.totient_mul_prod_primeFactors k
    have h2 : ((k.totient * ∏ p ∈ k.primeFactors, p : ℕ) : ℝ) =
        ((k * ∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [this]
    push_cast at h2
    rw [h2]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hpos : ∀ p ∈ k.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hQ : (0 : ℝ) < ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  have hφ0 : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk)
  have e : ∏ p ∈ k.primeFactors, (1 + ((p : ℝ) - 1)⁻¹) =
      ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have := hpos p hp
    field_simp
    ring
  rw [e, Finset.prod_div_distrib, div_eq_div_iff hφ0.ne' hQ.ne']
  linarith [hφ]

/-- Gallagher 1975 p.129 Proof of (7): the factors preceding the sum are at most
(m, n)/phi((m, n)) times m_n^(3/2)/phi^2(m_n), hence at most 4 (m, n)/phi((m, n)), and
together with the product over p dividing n and not m this gives 4 n/phi(n). -/
theorem pairFactor_mul_le {m N : ℕ} (hm : 0 < m) (hN : N ≠ 0) :
    pairFactor m N * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) ≤
      4 * ((N : ℝ) / N.totient) := by
  set g := Nat.gcd m N with hgdef
  set k := m / g with hkdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hmk : m = k * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left m N)).symm
  have hk : 1 ≤ k := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m N)) hg0
  have hsup : k.totient * g.totient ≤ m.totient := by
    rw [hmk]; exact Nat.totient_super_multiplicative k g
  have hφk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hφg : (0 : ℝ) < g.totient := by exact_mod_cast Nat.totient_pos.mpr hg0
  have hsup' : (k.totient : ℝ) * g.totient ≤ m.totient := by exact_mod_cast hsup
  have hpf : pairFactor m N ≤ 4 * ((g : ℝ) / g.totient) := by
    unfold pairFactor
    rw [← hgdef, ← hkdef]
    have hmR : (m : ℝ) = k * g := by exact_mod_cast hmk
    have hF := mul_sqrt_le_totient_sq k hk
    calc (m : ℝ) * Real.sqrt k / (m.totient * k.totient)
        ≤ (m : ℝ) * Real.sqrt k / ((k.totient * g.totient) * k.totient) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hsup' hφk.le
      _ = ((k : ℝ) * Real.sqrt k / (k.totient : ℝ) ^ 2) * ((g : ℝ) / g.totient) := by
          rw [hmR]; field_simp
      _ ≤ 4 * ((g : ℝ) / g.totient) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_iff₀ (by positivity)]
          exact hF
  have hgpf : g.primeFactors = N.primeFactors.filter (fun p => p ∣ m) := by
    rw [hgdef, Nat.primeFactors_gcd hm.ne' hN]
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpm, -⟩, hpN⟩
      exact ⟨hpN, hpm⟩
    · rintro ⟨hpN, hpm⟩
      exact ⟨⟨hpN.1, hpm, hm.ne'⟩, hpN⟩
  have hprod : ((g : ℝ) / g.totient) *
      ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) =
      (N : ℝ) / N.totient := by
    rw [ratio_eq_prod hg0.ne', ratio_eq_prod hN, hgpf,
      Finset.prod_filter_mul_prod_filter_not]
  have hP0 : 0 ≤ ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) := by
    apply Finset.prod_nonneg
    intro p hp
    have : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
    have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    linarith
  calc pairFactor m N * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹)
      ≤ 4 * ((g : ℝ) / g.totient) *
          ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) :=
        mul_le_mul_of_nonneg_right hpf hP0
    _ = 4 * ((N : ℝ) / N.totient) := by rw [mul_assoc, hprod]

/-! ### Display 7 -/

/-- Gallagher 1975 p.129 display 7, proved by the printed Proof of (7) from display 5,
the CITED-LEFT leaf `induced_cn_bound`: C_n(chi, chi') is at most 16 n/phi(n), uniformly in
the primitive characters chi, chi' and in P. Same statement as `pair_weight_bound`. -/
theorem pair_weight_bound_of_cited :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ) (x y : PChar), n ≠ 0 →
      x.2.IsPrimitive → y.2.IsPrimitive → pairWeight P n x y ≤ K * totientWeight n := by
  refine ⟨16, by norm_num, ?_⟩
  intro P n x y hn hx hy
  set m := Nat.lcm (x.1 + 1) (y.1 + 1) with hmdef
  have hm_pos : 0 < m := Nat.lcm_pos (by omega) (by omega)
  have hN : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have h1 := pairWeight_le_split P n hx hy
  have h2 := euler_sum_le_prod (N := n.natAbs) (m := m) ⌊P⌋₊
  have h3 := euler_prod_le (m := m) hN ⌊P⌋₊
  have h4 := pairFactor_mul_le hm_pos hN
  have hA := pairFactor_nonneg m n.natAbs
  unfold totientWeight
  calc pairWeight P n x y
      ≤ pairFactor m n.natAbs * (4 * ∏ p ∈ n.natAbs.primeFactors.filter (fun p => ¬ p ∣ m),
          (1 + ((p : ℝ) - 1)⁻¹)) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hA)
    _ = 4 * (pairFactor m n.natAbs * ∏ p ∈ n.natAbs.primeFactors.filter (fun p => ¬ p ∣ m),
          (1 + ((p : ℝ) - 1)⁻¹)) := by ring
    _ ≤ 4 * (4 * ((n.natAbs : ℝ) / n.natAbs.totient)) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 16 * ((n.natAbs : ℝ) / n.natAbs.totient) := by ring

end LeanLab.Linnik.MajorArcEnergy

