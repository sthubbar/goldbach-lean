module

public import Mathlib
public import LeanLab.PNTPort.LargeSieve.Parseval
public import LeanLab.HeathBrown1985.Elementary

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

The arithmetic side of the large spectrum bound: the Ramanujan sum majorant

  `G(m) = Σ_{q ≤ T squarefree} φ(q)⁻¹ Σ_{(a, q) = 1} e(-ma/q)`

satisfies `|G(m)| ≤ T`, and `|G(m)| ≤ e S(T) 3^{ω_T(m)}` with `S(T) = Σ_{n ≤ T} 1/φ(n)` and
`ω_T(m)` the number of primes `p ≤ T` dividing `m`; and the eighth moment over `1 ≤ m < L` is
at most `L exp(6560 Σ_{p ≤ T} 1/p)`. Also the Cauchy-Schwarz chain
`(Σ g p²)^8 ≤ (Σ g^8) |I| k^4 (Σ p²)^6` for `0 ≤ p ≤ k`.

Known mathematics, no cited input. AI-written Lean code, Claude, 2026-10-23. Checked only by
the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open LeanLab.PNTPort.LargeSieve
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.DensityGoldbach.U1502

/-- Squarefree moduli up to `T`. -/
def Qs (T : ℕ) : Finset ℕ := (Icc 1 T).filter Squarefree

/-- Reduced residues mod `q`. -/
def Us (q : ℕ) : Finset ℕ := (range q).filter (Nat.Coprime q)

lemma card_Us (q : ℕ) : (Us q).card = Nat.totient q := by
  unfold Us; rw [Nat.totient]

/-- The index set of all Farey shifts `a/q`, `q ≤ T` squarefree. -/
def Fs (T : ℕ) : Finset (Σ _ : ℕ, ℕ) := (Qs T).sigma Us

/-- Weight `1/φ(q)` of the shift `a/q`. -/
def wF (j : Σ _ : ℕ, ℕ) : ℝ := 1 / (Nat.totient j.1 : ℝ)

/-- The shift `a/q`. -/
def bF (j : Σ _ : ℕ, ℕ) : ℝ := (j.2 : ℝ) / j.1

lemma wF_nonneg (j : Σ _ : ℕ, ℕ) : 0 ≤ wF j := by unfold wF; positivity

/-! ### Möbius and the Ramanujan sum bound -/

lemma sum_moebius_divisors' (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← h]
  simp

/-- `|Σ_{a < q, (a, q) = 1} e(ka/q)| ≤ Σ_{d ∣ q, d ∣ k} d`. -/
theorem ram_bound {q : ℕ} (hq : 1 ≤ q) (k : ℤ) :
    ‖∑ a ∈ Us q, e (k * a / q)‖ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℤ) ∣ k), (d : ℝ) := by
  unfold Us
  rw [sum_filter]
  have step1 : ∀ a ∈ range q, (if Nat.Coprime q a then e (k * a / q) else 0) =
      ∑ d ∈ (Nat.gcd q a).divisors, (μ d : ℂ) * e (k * a / q) := by
    intro a _
    rw [← sum_mul, sum_moebius_divisors']
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl step1]
  rw [sum_comm' (t' := q.divisors) (s' := fun d => (range q).filter (fun a => d ∣ a))]
  · have step2 : ∀ d ∈ q.divisors, ∑ a ∈ (range q).filter (fun a => d ∣ a),
        (μ d : ℂ) * e (k * a / q) =
        (μ d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ k then ((q / d : ℕ) : ℂ) else 0) := by
      intro d hd
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0
      rw [← mul_sum, ← sum_e_mul_div k hqd]
      congr 1
      refine sum_nbij' (fun a => a / d) (fun s => d * s) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rw [mem_filter, mem_range] at ha
        rw [mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq ha.1
      · intro s hs
        rw [mem_range] at hs
        rw [mem_filter, mem_range]
        refine ⟨?_, dvd_mul_right d s⟩
        have := Nat.mul_lt_mul_of_pos_left hs hd0
        rwa [Nat.mul_div_cancel' hdq] at this
      · intro a ha
        rw [mem_filter] at ha
        exact Nat.mul_div_cancel' ha.2
      · intro s _; exact Nat.mul_div_cancel_left s hd0
      · intro a ha
        rw [mem_filter] at ha
        obtain ⟨s, rfl⟩ := ha.2
        rw [Nat.mul_div_cancel_left s hd0, Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
        congr 1
        push_cast
        field_simp
    rw [sum_congr rfl step2]
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ d ∈ q.divisors, ‖(μ d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ k then
        ((q / d : ℕ) : ℂ) else 0)‖ ≤ (if ((q / d : ℕ) : ℤ) ∣ k then ((q / d : ℕ) : ℝ) else 0) := by
      intro d _
      rw [norm_mul]
      have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      split_ifs
      · rw [Complex.norm_natCast]
        calc ‖(μ d : ℂ)‖ * ((q / d : ℕ) : ℝ) ≤ 1 * ((q / d : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg _)
          _ = _ := one_mul _
      · simp
    refine (sum_le_sum hpt).trans (le_of_eq ?_)
    rw [← sum_filter]
    refine sum_nbij' (fun d => q / d) (fun d => q / d) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.div_dvd_of_dvd hd.1.1, by omega⟩, hd.2⟩
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd hd.1.1, by omega⟩, ?_⟩
      rw [Nat.div_div_self hd.1.1 (by omega)]; exact hd.2
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 (by omega)
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 (by omega)
    · intro d _; rfl
  · intro a d
    simp only [mem_range, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨ha, hd, _⟩
      exact ⟨⟨ha, (Nat.dvd_gcd_iff.1 hd).2⟩, (Nat.dvd_gcd_iff.1 hd).1, by omega⟩
    · rintro ⟨⟨ha, hda⟩, hdq, _⟩
      exact ⟨ha, Nat.dvd_gcd hdq hda, (Nat.gcd_pos_of_pos_left a (by omega)).ne'⟩

/-! ### The majorant `G` -/

/-- `G(t) = Σ_{q ≤ T sqfree} Σ_{(a, q) = 1} φ(q)⁻¹ e(-t a/q)`, as a sum over `Fs T`. -/
def GT (T : ℕ) (t : ℤ) : ℂ := ∑ j ∈ Fs T, (wF j : ℂ) * e (-((t : ℝ) * bF j))

lemma GT_eq (T : ℕ) (t : ℤ) :
    GT T t = ∑ q ∈ Qs T, (1 / (Nat.totient q : ℂ)) * ∑ a ∈ Us q, e ((-t : ℤ) * a / q) := by
  unfold GT Fs
  rw [sum_sigma]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  unfold wF bF
  push_cast
  congr 2
  ring

lemma mem_Qs {T q : ℕ} : q ∈ Qs T ↔ (1 ≤ q ∧ q ≤ T) ∧ Squarefree q := by
  unfold Qs; rw [mem_filter, mem_Icc]

/-- Trivial bound `|G(t)| ≤ T`. -/
theorem GT_le_T (T : ℕ) (t : ℤ) : ‖GT T t‖ ≤ T := by
  rw [GT_eq]
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ q ∈ Qs T, ‖(1 / (Nat.totient q : ℂ)) * ∑ a ∈ Us q, e ((-t : ℤ) * a / q)‖ ≤ 1 := by
    intro q hq
    rw [mem_Qs] at hq
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
    rw [norm_mul]
    have h1 : ‖∑ a ∈ Us q, e ((-t : ℤ) * a / q)‖ ≤ Nat.totient q := by
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_e, sum_const, card_Us, nsmul_eq_mul, mul_one, le_refl]
    have h2 : ‖(1 / (Nat.totient q : ℂ))‖ = 1 / (Nat.totient q : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_natCast]
    rw [h2]
    calc 1 / (Nat.totient q : ℝ) * ‖∑ a ∈ Us q, e ((-t : ℤ) * a / q)‖
        ≤ 1 / (Nat.totient q : ℝ) * Nat.totient q := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp
  refine (sum_le_sum hpt).trans ?_
  rw [sum_const, nsmul_eq_mul, mul_one]
  have : (Qs T).card ≤ T := by
    unfold Qs
    exact (card_filter_le _ _).trans (by simp)
  exact_mod_cast this

/-- `Σ_{q ≤ Q, d ∣ q} 1/φ(q) ≤ φ(d)⁻¹ Σ_{m ≤ Q} 1/φ(m)` (as in PNTPort.BV.Assembly). -/
theorem sum_dvd_inv_totient_le' {d : ℕ} (hd : 1 ≤ d) (Q : ℕ) :
    ∑ q ∈ (Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / q.totient ≤
      (1 / d.totient) * ∑ m ∈ Icc 1 Q, (1 : ℝ) / m.totient := by
  have hsub : (Icc 1 Q).filter (fun q => d ∣ q) ⊆ (Icc 1 Q).image (fun m => d * m) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hq
    rw [mem_image]
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at h1
      · exact h
    exact ⟨m, mem_Icc.2 ⟨hm, le_trans (Nat.le_mul_of_pos_left m (by omega)) h2⟩, rfl⟩
  have hinj : Set.InjOn (fun m => d * m) (Icc 1 Q : Finset ℕ) := by
    intro m _ m' _ h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  calc ∑ q ∈ (Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / q.totient
      ≤ ∑ q ∈ (Icc 1 Q).image (fun m => d * m), (1 : ℝ) / q.totient :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ m ∈ Icc 1 Q, (1 : ℝ) / (d * m).totient := sum_image hinj
    _ ≤ ∑ m ∈ Icc 1 Q, (1 / d.totient) * ((1 : ℝ) / m.totient) := by
        apply sum_le_sum
        intro m hm
        rw [mem_Icc] at hm
        have hdφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
        have hmφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
        have hsm : ((d.totient * m.totient : ℕ) : ℝ) ≤ (d * m).totient := by
          exact_mod_cast Nat.totient_super_multiplicative d m
        push_cast at hsm
        rw [div_mul_div_comm, one_mul]
        exact one_div_le_one_div_of_le (by positivity) hsm
    _ = (1 / d.totient) * ∑ m ∈ Icc 1 Q, (1 : ℝ) / m.totient := by rw [mul_sum]

/-- `S(T) = Σ_{n ≤ T} 1/φ(n)`. -/
def ST (T : ℕ) : ℝ := ∑ m ∈ Icc 1 T, (1 : ℝ) / m.totient

lemma ST_nonneg (T : ℕ) : 0 ≤ ST T := sum_nonneg fun _ _ => by positivity

/-- The primes `p ≤ T` dividing `m`. -/
def Bset (T m : ℕ) : Finset ℕ := (Icc 1 T).filter (fun p => p.Prime ∧ p ∣ m)

/-- The primes `p ≤ T`. -/
def PT (T : ℕ) : Finset ℕ := (Icc 1 T).filter Nat.Prime

lemma two_pow_ge (n : ℕ) : (1 : ℝ) + n ≤ 2 ^ n := by
  have : 1 + n ≤ 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; omega
  exact_mod_cast this

/-- `Σ_{d ≤ T sqfree, d ∣ m} d/φ(d) ≤ e 3^{ω_T(m)}`. -/
theorem sum_div_totient_le (T m : ℕ) :
    ∑ d ∈ (Icc 1 T).filter (fun d => Squarefree d ∧ d ∣ m), (d : ℝ) / d.totient ≤
      Real.exp 1 * 3 ^ (Bset T m).card := by
  set D := (Icc 1 T).filter (fun d => Squarefree d ∧ d ∣ m)
  have h1 : ∀ d ∈ D, (d : ℝ) / d.totient ≤ Real.exp 1 * 2 ^ d.primeFactors.card := by
    intro d hd
    simp only [D, mem_filter, mem_Icc] at hd
    refine (LeanLab.HeathBrown1985.div_totient_le d hd.1.1).trans ?_
    exact mul_le_mul_of_nonneg_left (two_pow_ge _) (Real.exp_pos 1).le
  have hinj : Set.InjOn (fun d : ℕ => d.primeFactors) (D : Set ℕ) := by
    intro a ha b hb hab
    simp only [D, coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    rw [← Nat.prod_primeFactors_of_squarefree ha.2.1, ← Nat.prod_primeFactors_of_squarefree hb.2.1,
      hab]
  have hsub : D.image (fun d : ℕ => d.primeFactors) ⊆ (Bset T m).powerset := by
    intro A hA
    rw [mem_image] at hA
    obtain ⟨d, hd, rfl⟩ := hA
    simp only [D, mem_filter, mem_Icc] at hd
    rw [mem_powerset]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    simp only [Bset, mem_filter, mem_Icc]
    exact ⟨⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpd).trans hd.1.2⟩, hpp,
      hpd.trans hd.2.2⟩
  calc ∑ d ∈ D, (d : ℝ) / d.totient ≤ ∑ d ∈ D, Real.exp 1 * 2 ^ d.primeFactors.card :=
        sum_le_sum h1
    _ = Real.exp 1 * ∑ A ∈ D.image (fun d : ℕ => d.primeFactors), (2 : ℝ) ^ A.card := by
        rw [sum_image hinj, mul_sum]
    _ ≤ Real.exp 1 * ∑ A ∈ (Bset T m).powerset, (2 : ℝ) ^ A.card := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = Real.exp 1 * 3 ^ (Bset T m).card := by
        congr 1
        have := sum_pow_mul_eq_add_pow (2 : ℝ) 1 (Bset T m)
        simp only [one_pow, mul_one] at this
        rw [this]; norm_num

/-- **Divisor bound for `G`**: `|G(m)| ≤ e S(T) 3^{ω_T(m)}`. -/
theorem GT_le_omega (T m : ℕ) : ‖GT T m‖ ≤ ST T * (Real.exp 1 * 3 ^ (Bset T m).card) := by
  rw [GT_eq]
  refine (norm_sum_le _ _).trans ?_
  -- termwise Ramanujan bound
  have hpt : ∀ q ∈ Qs T, ‖(1 / (Nat.totient q : ℂ)) * ∑ a ∈ Us q, e ((-(m : ℤ) : ℤ) * a / q)‖ ≤
      ∑ d ∈ q.divisors.filter (fun d => d ∣ m), (d : ℝ) * (1 / (Nat.totient q : ℝ)) := by
    intro q hq
    rw [mem_Qs] at hq
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have hr := ram_bound hq.1.1 (-(m : ℤ))
    have e1 : q.divisors.filter (fun d : ℕ => (d : ℤ) ∣ -(m : ℤ)) =
        q.divisors.filter (fun d => d ∣ m) := by
      apply filter_congr; intro d _
      rw [Int.dvd_neg]; exact_mod_cast Iff.rfl
    rw [e1] at hr
    rw [← sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hr (by positivity)
  refine (sum_le_sum hpt).trans ?_
  -- swap the sums
  set D := (Icc 1 T).filter (fun d => Squarefree d ∧ d ∣ m)
  have hswap : ∑ q ∈ Qs T, ∑ d ∈ q.divisors.filter (fun d => d ∣ m),
      (d : ℝ) * (1 / (Nat.totient q : ℝ)) =
      ∑ d ∈ D, ∑ q ∈ (Qs T).filter (fun q => d ∣ q), (d : ℝ) * (1 / (Nat.totient q : ℝ)) := by
    apply sum_comm'
    intro q d
    simp only [D, mem_filter, Nat.mem_divisors, mem_Qs, mem_Icc]
    constructor
    · rintro ⟨hq, ⟨hdq, _⟩, hdm⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdq (by omega)
      exact ⟨⟨hq, hdq⟩, ⟨hd1, (Nat.le_of_dvd (by omega) hdq).trans hq.1.2⟩,
        hq.2.squarefree_of_dvd hdq, hdm⟩
    · rintro ⟨⟨hq, hdq⟩, _, _, hdm⟩
      exact ⟨hq, ⟨hdq, by omega⟩, hdm⟩
  rw [hswap]
  have hd : ∀ d ∈ D, ∑ q ∈ (Qs T).filter (fun q => d ∣ q), (d : ℝ) * (1 / (Nat.totient q : ℝ)) ≤
      ST T * ((d : ℝ) / d.totient) := by
    intro d hdD
    simp only [D, mem_filter, mem_Icc] at hdD
    rw [← mul_sum]
    have hsub : (Qs T).filter (fun q => d ∣ q) ⊆ (Icc 1 T).filter (fun q => d ∣ q) := by
      intro q hq
      simp only [mem_filter, mem_Qs, mem_Icc] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩
    have h1 : ∑ q ∈ (Qs T).filter (fun q => d ∣ q), (1 / (Nat.totient q : ℝ)) ≤
        (1 / d.totient) * ST T :=
      (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
        (sum_dvd_inv_totient_le' hdD.1.1 T)
    calc (d : ℝ) * ∑ q ∈ (Qs T).filter (fun q => d ∣ q), (1 / (Nat.totient q : ℝ))
        ≤ (d : ℝ) * ((1 / d.totient) * ST T) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = ST T * ((d : ℝ) / d.totient) := by ring
  calc ∑ d ∈ D, ∑ q ∈ (Qs T).filter (fun q => d ∣ q), (d : ℝ) * (1 / (Nat.totient q : ℝ))
      ≤ ∑ d ∈ D, ST T * ((d : ℝ) / d.totient) := sum_le_sum hd
    _ = ST T * ∑ d ∈ D, (d : ℝ) / d.totient := by rw [mul_sum]
    _ ≤ ST T * (Real.exp 1 * 3 ^ (Bset T m).card) :=
        mul_le_mul_of_nonneg_left (sum_div_totient_le T m) (ST_nonneg T)

/-! ### The eighth moment -/

lemma card_dvd_Ico_le (L d : ℕ) (_hd : 1 ≤ d) :
    (((Ico 1 L).filter (fun m => d ∣ m)).card : ℝ) ≤ (L : ℝ) / d := by
  have hsub : (Ico 1 L).filter (fun m => d ∣ m) ⊆ (Ioc 0 L).filter (fun m => d ∣ m) := by
    intro m hm
    simp only [mem_filter, mem_Ico, mem_Ioc] at hm ⊢
    exact ⟨⟨by omega, by omega⟩, hm.2⟩
  have h1 := card_le_card hsub
  rw [Nat.Ioc_filter_dvd_card_eq_div] at h1
  calc (((Ico 1 L).filter (fun m => d ∣ m)).card : ℝ) ≤ ((L / d : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (L : ℝ) / d := Nat.cast_div_le

lemma Bset_sub_PT (T m : ℕ) : Bset T m ⊆ PT T := by
  intro p hp
  simp only [Bset, PT, mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- **Eighth moment**: `Σ_{1 ≤ m < L} (3^{ω_T(m)})^8 ≤ L exp(6560 Σ_{p ≤ T} 1/p)`. -/
theorem moment8 (T L : ℕ) :
    ∑ m ∈ Ico 1 L, ((3 : ℝ) ^ (Bset T m).card) ^ 8 ≤
      L * Real.exp (6560 * ∑ p ∈ PT T, (1 : ℝ) / p) := by
  set f : Finset ℕ → ℝ := fun A => (6560 : ℝ) ^ A.card
  have hexp : ∀ m, ((3 : ℝ) ^ (Bset T m).card) ^ 8 =
      ∑ A ∈ (PT T).powerset, if A ⊆ Bset T m then f A else 0 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, show (3 : ℝ) ^ 8 = 6560 + 1 by norm_num]
    rw [← sum_pow_mul_eq_add_pow (6560 : ℝ) 1 (Bset T m)]
    simp only [one_pow, mul_one]
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext A
    simp only [mem_powerset, mem_filter]
    constructor
    · intro h; exact ⟨h.trans (Bset_sub_PT T m), h⟩
    · intro h; exact h.2
  simp_rw [hexp]
  rw [sum_comm]
  have hA : ∀ A ∈ (PT T).powerset,
      ∑ m ∈ Ico 1 L, (if A ⊆ Bset T m then f A else 0) ≤ L * ∏ p ∈ A, ((6560 : ℝ) / p) := by
    intro A hAP
    rw [mem_powerset] at hAP
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hprime : ∀ p ∈ A, p.Prime := fun p hp => by
      have := hAP hp; simp only [PT, mem_filter] at this; exact this.2
    set d := ∏ p ∈ A, p
    have hd1 : 1 ≤ d := by
      apply Nat.one_le_iff_ne_zero.2
      rw [Finset.prod_ne_zero_iff]; intro p hp; exact (hprime p hp).ne_zero
    have hsub : (Ico 1 L).filter (fun m => A ⊆ Bset T m) ⊆ (Ico 1 L).filter (fun m => d ∣ m) := by
      intro m hm
      simp only [mem_filter] at hm ⊢
      refine ⟨hm.1, ?_⟩
      apply Finset.prod_primes_dvd
      · intro p hp; exact (hprime p hp).prime
      · intro p hp
        have := hm.2 hp
        simp only [Bset, mem_filter] at this
        exact this.2.2
    have hc : (((Ico 1 L).filter (fun m => A ⊆ Bset T m)).card : ℝ) ≤ (L : ℝ) / d :=
      le_trans (by exact_mod_cast card_le_card hsub) (card_dvd_Ico_le L d hd1)
    have hf0 : 0 ≤ f A := by simp only [f]; positivity
    have he : (L : ℝ) / d * f A = L * ∏ p ∈ A, ((6560 : ℝ) / p) := by
      simp only [f, d]
      rw [prod_div_distrib, prod_const]
      push_cast
      ring
    calc (((Ico 1 L).filter (fun m => A ⊆ Bset T m)).card : ℝ) * f A ≤ (L : ℝ) / d * f A :=
          mul_le_mul_of_nonneg_right hc hf0
      _ = _ := he
  calc ∑ A ∈ (PT T).powerset, ∑ m ∈ Ico 1 L, (if A ⊆ Bset T m then f A else 0)
      ≤ ∑ A ∈ (PT T).powerset, L * ∏ p ∈ A, ((6560 : ℝ) / p) := sum_le_sum hA
    _ = L * ∏ p ∈ PT T, ((6560 : ℝ) / p + 1) := by
        rw [← mul_sum, prod_add]
        simp only [prod_const_one, mul_one]
    _ ≤ L * ∏ p ∈ PT T, Real.exp ((6560 : ℝ) / p) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply prod_le_prod₀
        · intro p _; positivity
        · intro p _; have := Real.add_one_le_exp ((6560 : ℝ) / p); linarith
    _ = L * Real.exp (6560 * ∑ p ∈ PT T, (1 : ℝ) / p) := by
        rw [← Real.exp_sum, mul_sum]
        congr 2
        refine sum_congr rfl fun p _ => ?_
        ring

/-! ### The Cauchy-Schwarz chain -/

/-- `(Σ g p²)^8 ≤ (Σ g^8) |I| k^4 (Σ p²)^6` for `g ≥ 0` and `0 ≤ p ≤ k`. -/
theorem cs_chain {ι : Type*} (I : Finset ι) (g p : ι → ℝ) (hg : ∀ i ∈ I, 0 ≤ g i)
    (hp : ∀ i ∈ I, 0 ≤ p i) (k : ℝ) (hpk : ∀ i ∈ I, p i ≤ k) :
    (∑ i ∈ I, g i * p i ^ 2) ^ 8 ≤
      (∑ i ∈ I, g i ^ 8) * I.card * k ^ 4 * (∑ i ∈ I, p i ^ 2) ^ 6 := by
  set X := ∑ i ∈ I, g i * p i ^ 2
  set Y := ∑ i ∈ I, g i ^ 2 * p i ^ 2
  set Z := ∑ i ∈ I, g i ^ 4
  set P2 := ∑ i ∈ I, p i ^ 2
  set P4 := ∑ i ∈ I, p i ^ 4
  set S8 := ∑ i ∈ I, g i ^ 8
  have hX0 : 0 ≤ X := sum_nonneg fun i hi => mul_nonneg (hg i hi) (sq_nonneg _)
  have hY0 : 0 ≤ Y := sum_nonneg fun i _ => by positivity
  have hZ0 : 0 ≤ Z := sum_nonneg fun i _ => by positivity
  have hP2 : 0 ≤ P2 := sum_nonneg fun i _ => by positivity
  have hP4 : 0 ≤ P4 := sum_nonneg fun i _ => by positivity
  have h1 : X ^ 2 ≤ Y * P2 := by
    have := sum_mul_sq_le_sq_mul_sq I (fun i => g i * p i) p
    have e1 : ∑ i ∈ I, g i * p i * p i = X := sum_congr rfl fun i _ => by ring
    have e2 : ∑ i ∈ I, (g i * p i) ^ 2 = Y := sum_congr rfl fun i _ => by ring
    rw [e1, e2] at this; exact this
  have h2 : Y ^ 2 ≤ Z * P4 := by
    have := sum_mul_sq_le_sq_mul_sq I (fun i => g i ^ 2) (fun i => p i ^ 2)
    have e2 : ∑ i ∈ I, (g i ^ 2) ^ 2 = Z := sum_congr rfl fun i _ => by ring
    have e3 : ∑ i ∈ I, (p i ^ 2) ^ 2 = P4 := sum_congr rfl fun i _ => by ring
    rw [e2, e3] at this; exact this
  have h3 : Z ^ 2 ≤ S8 * I.card := by
    have := sum_mul_sq_le_sq_mul_sq I (fun i => g i ^ 4) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul] at this
    have e2 : ∑ i ∈ I, (g i ^ 4) ^ 2 = S8 := sum_congr rfl fun i _ => by ring
    rw [e2] at this; linarith
  have h4 : P4 ≤ k ^ 2 * P2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hk2 : p i ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (hp i hi) (hpk i hi) 2
    have : p i ^ 4 = p i ^ 2 * p i ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hk2 (sq_nonneg _)
  have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
  calc X ^ 8 = (X ^ 2) ^ 4 := by ring
    _ ≤ (Y * P2) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
    _ = (Y ^ 2) ^ 2 * P2 ^ 4 := by ring
    _ ≤ (Z * P4) ^ 2 * P2 ^ 4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) h2 2
    _ = Z ^ 2 * P4 ^ 2 * P2 ^ 4 := by ring
    _ ≤ (S8 * I.card) * (k ^ 2 * P2) ^ 2 * P2 ^ 4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul h3 (pow_le_pow_left₀ hP4 h4 2) (by positivity) (by positivity)
    _ = S8 * I.card * k ^ 4 * P2 ^ 6 := by ring

end LeanLab.DensityGoldbach.U1502
