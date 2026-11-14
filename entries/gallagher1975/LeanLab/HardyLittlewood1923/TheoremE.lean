module

public import LeanLab.HardyLittlewood1923.Count4
public import LeanLab.HardyLittlewood1923.APSums
public import LeanLab.HardyLittlewood1923.EulerE

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5707, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III, Theorem E, (3.63) and (3.64), p. 31

`theoremE : theoremE_stmt`: for even `n → ∞`,
`N̄₄(n) = (1 + o(1)) (1/3) C₄ n³/(log n)⁴ ∏_{p ∣ n, p odd} (p-1)(p²-3p+3)/((p-2)(p²-2p+2))`,
and `theoremE_four`: every large even number is a sum of four odd primes.
Hardy and Littlewood assume Hypothesis R; here there is no hypothesis. The route is not theirs:
`N̄₄(n) = Σ_{p odd prime} N̄₃(n - p)` (`Count4`), Theorem D for each `N̄₃(n - p)` with `n - p`
large (`TheoremD`, from the lab's unconditional circle method), the divisor expansion
`Pi3 m = Σ_{d ∣ m squarefree} g d` truncated at `d ≤ D` with a tail `≤ 3/(z - 1)` uniform in `m`
(`sqf_tail`), prime sums `Σ_{p ≡ n (d)} (n - p)²` in progressions (`APSums.ap_sum_sq`, from
Siegel-Walfisz) and the average of the singular series (`EulerE.euler_avg_tendsto`).
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923
namespace ThmE

open Real Finset Filter Topology

attribute [local instance] Classical.propDecidable

theorem Pi3_bounds (m : ℕ) : 0 ≤ Pi3 m ∧ Pi3 m ≤ 1 := by
  unfold Pi3
  have hf : ∀ p ∈ m.primeFactors, 0 ≤ ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) ^ 2 - 3 * p + 3) ∧
      ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) ^ 2 - 3 * p + 3) ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hd : 0 < (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
    constructor
    · apply div_nonneg _ hd.le; nlinarith
    · rw [div_le_one hd]; nlinarith
  exact ⟨prod_nonneg fun p hp => (hf p hp).1,
    prod_le_one₀ (fun p hp => (hf p hp).1) fun p hp => (hf p hp).2⟩

/-- `x_ℓ = 1/(ℓ² - 3ℓ + 3) = |g ℓ|`. -/
noncomputable def xf (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 3 * l + 3)

theorem xf_nonneg (l : ℕ) : 0 ≤ xf l := by
  unfold xf
  apply div_nonneg zero_le_one
  have : (0 : ℝ) ≤ ((l : ℝ) - 3 / 2) ^ 2 := sq_nonneg _
  nlinarith

theorem xf_le_tele (l : ℕ) (hl : 3 ≤ l) : xf l ≤ 1 / ((l : ℝ) - 2) - 1 / ((l : ℝ) - 1) := by
  have h3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  rw [xf, div_sub_div _ _ (by linarith) (by linarith),
    div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

theorem abs_g_prod (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    |g (∏ p ∈ t, p)| = ∏ l ∈ t, xf l := by
  unfold g; rw [Nat.primeFactors_prod ht, abs_prod]
  refine prod_congr rfl fun l hl => ?_
  have hp2 : (2 : ℝ) ≤ l := by exact_mod_cast (ht l hl).two_le
  have hd : 0 < (l : ℝ) ^ 2 - 3 * l + 3 := by nlinarith
  rw [xf, abs_div, abs_neg, abs_one, abs_of_pos hd]

theorem sum_xf_le (A : Finset ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (hA : ∀ p ∈ A, Q + 1 ≤ p) :
    ∑ l ∈ A, xf l ≤ 1 / ((Q : ℝ) - 1) :=
  (sum_le_sum fun l hl => xf_le_tele l (by have := hA l hl; omega)).trans (tele_set_le A hQ hA)

theorem prod_one_add_sub_one_le (B : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ i ∈ B, 0 ≤ x i) :
    ∏ i ∈ B, (1 + x i) - 1 ≤ (∑ i ∈ B, x i) * ∏ i ∈ B, (1 + x i) := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have hxa := hx a (mem_insert_self a B)
    have ih' := ih fun i hi => hx i (mem_insert_of_mem hi)
    have hP : 1 ≤ ∏ i ∈ B, (1 + x i) :=
      one_le_prod₀ fun i hi => by linarith [hx i (mem_insert_of_mem hi)]
    have hS : 0 ≤ ∑ i ∈ B, x i := sum_nonneg fun i hi => hx i (mem_insert_of_mem hi)
    set P := ∏ i ∈ B, (1 + x i)
    set S := ∑ i ∈ B, x i
    have h1 : 0 ≤ (x a + S) * x a * P := by positivity
    nlinarith

/-- The squarefree divisors `d > D ≥ z!` of an odd `m` carry `Σ |g d| ≤ 3/(z - 1)`. -/
theorem sqf_tail (m : ℕ) (hm : Odd m) (z D : ℕ) (hz : 2 ≤ z) (hD : z.factorial ≤ D) :
    ∑ d ∈ m.divisors.filter Squarefree, (if D < d then |g d| else 0) ≤ 3 / ((z : ℝ) - 1) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.sum_divisors_filter_squarefree hm0]
  have e : (UniqueFactorizationMonoid.normalizedFactors m).toFinset = m.primeFactors := by
    rw [Nat.factors_eq]; rfl
  rw [e]
  set A := m.primeFactors with hAdef
  have hAp : ∀ p ∈ A, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hA3 : ∀ p ∈ A, 3 ≤ p := fun p hp =>
    three_le_of_odd_prime (hAp p hp) (Odd.of_dvd_nat hm (Nat.dvd_of_mem_primeFactors hp))
  set Az := A.filter (· ≤ z) with hAz
  have hAzA : Az ⊆ A := filter_subset _ _
  have step1 : ∀ t ∈ A.powerset, (if D < t.val.prod then |g t.val.prod| else 0) ≤
      (if t ⊆ Az then 0 else ∏ l ∈ t, xf l) := by
    intro t ht
    rw [mem_powerset] at ht
    have htp : t.val.prod = ∏ a ∈ t, a := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [htp]
    have habs := abs_g_prod t (fun p hp => hAp p (ht hp))
    have hxnn : 0 ≤ ∏ l ∈ t, xf l := prod_nonneg fun l _ => xf_nonneg l
    split_ifs with h1 h2 h2
    · exfalso
      have hdvd : ∏ a ∈ t, a ∣ ∏ x ∈ Ico 1 (z + 1), x := by
        apply Finset.prod_dvd_prod_of_subset
        intro a ha
        have h := h2 ha
        rw [hAz, mem_filter] at h
        have := (hAp a (ht ha)).two_le
        rw [mem_Ico]; omega
      rw [Finset.prod_Ico_id_eq_factorial] at hdvd
      have := Nat.le_of_dvd (Nat.factorial_pos z) hdvd
      omega
    · rw [habs]
    · exact le_refl 0
    · exact hxnn
  refine (sum_le_sum step1).trans ?_
  have hsplit : ∑ t ∈ A.powerset, (if t ⊆ Az then 0 else ∏ l ∈ t, xf l) =
      ∏ l ∈ A, (1 + xf l) - ∏ l ∈ Az, (1 + xf l) := by
    rw [prod_one_add, prod_one_add]
    have : ∑ t ∈ A.powerset, (∏ l ∈ t, xf l) =
        ∑ t ∈ A.powerset, (if t ⊆ Az then 0 else ∏ l ∈ t, xf l) +
        ∑ t ∈ A.powerset, (if t ⊆ Az then ∏ l ∈ t, xf l else 0) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun t _ => ?_; split_ifs <;> simp
    have hf : A.powerset.filter (fun t => t ⊆ Az) = Az.powerset := by
      ext t; simp only [mem_filter, mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans hAzA, h⟩⟩
    rw [this, ← Finset.sum_filter, hf]; ring
  rw [hsplit]
  rw [← prod_filter_mul_prod_filter_not A (fun l => l ≤ z)]
  set Pz := ∏ l ∈ A.filter (fun l => l ≤ z), (1 + xf l)
  set Pb := ∏ l ∈ A.filter (fun l => ¬ l ≤ z), (1 + xf l)
  have hPz : 0 ≤ Pz := prod_nonneg fun l _ => by linarith [xf_nonneg l]
  have hb := prod_one_add_sub_one_le (A.filter (fun l => ¬ l ≤ z)) xf (fun i _ => xf_nonneg i)
  have hSb : ∑ l ∈ A.filter (fun l => ¬ l ≤ z), xf l ≤ 1 / ((z : ℝ) - 1) := by
    apply sum_xf_le _ hz
    intro p hp; rw [mem_filter] at hp; omega
  have hAll : Pz * Pb ≤ 3 := by
    have hPP : Pz * Pb = ∏ l ∈ A, (1 + xf l) := prod_filter_mul_prod_filter_not _ _ _
    rw [hPP]
    have h1 := (prod_le_exp_sum (S := A) (fun l => 1 + xf l) xf
      (fun i _ => ⟨by linarith [xf_nonneg i], le_refl _⟩)).2
    have h2 : ∑ l ∈ A, xf l ≤ 1 := by
      have := sum_xf_le A (le_refl 2) (fun p hp => by have := hA3 p hp; omega)
      norm_num at this; linarith
    have h3 : Real.exp (∑ l ∈ A, xf l) ≤ Real.exp 1 := Real.exp_le_exp.mpr h2
    have h4 := Real.exp_one_lt_d9
    linarith
  have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by
    have : (2 : ℝ) ≤ z := by exact_mod_cast hz
    linarith
  have hSb0 : 0 ≤ ∑ l ∈ A.filter (fun l => ¬ l ≤ z), xf l := sum_nonneg fun l _ => xf_nonneg l
  have hPb0 : 0 ≤ Pb := prod_nonneg fun l _ => by linarith [xf_nonneg l]
  calc Pz * Pb - Pz = Pz * (Pb - 1) := by ring
    _ ≤ Pz * ((∑ l ∈ A.filter (fun l => ¬ l ≤ z), xf l) * Pb) :=
        mul_le_mul_of_nonneg_left hb hPz
    _ = (∑ l ∈ A.filter (fun l => ¬ l ≤ z), xf l) * (Pz * Pb) := by ring
    _ ≤ (1 / ((z : ℝ) - 1)) * 3 := mul_le_mul hSb hAll (by positivity) (by positivity)
    _ = 3 / ((z : ℝ) - 1) := by ring

/-- The truncated divisor expansion of `Pi3`. -/
theorem pi3_trunc (m : ℕ) (hm : Odd m) (z D : ℕ) (hz : 2 ≤ z) (hD : z.factorial ≤ D) :
    |Pi3 m - ∑ d ∈ (Icc 1 D).filter (fun d => Squarefree d ∧ Odd d),
      (if d ∣ m then g d else 0)| ≤ 3 / ((z : ℝ) - 1) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Pi3_eq_sum m hm]
  have h1 : ∑ d ∈ m.divisors.filter Squarefree, g d =
      ∑ d ∈ m.divisors.filter Squarefree, (if D < d then g d else 0) +
      ∑ d ∈ m.divisors.filter Squarefree, (if D < d then 0 else g d) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun d _ => ?_; split_ifs <;> simp
  have h2 : ∑ d ∈ m.divisors.filter Squarefree, (if D < d then 0 else g d) =
      ∑ d ∈ (Icc 1 D).filter (fun d => Squarefree d ∧ Odd d), (if d ∣ m then g d else 0) := by
    rw [sum_ite, sum_ite]; simp only [sum_const_zero, zero_add, add_zero]
    apply sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_Icc]
    constructor
    · rintro ⟨⟨⟨hdm, -⟩, hsq⟩, hle⟩
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdm (Nat.pos_of_ne_zero hm0), by omega⟩, hsq,
        Odd.of_dvd_nat hm hdm⟩, hdm⟩
    · rintro ⟨⟨⟨_, hle⟩, hsq, _⟩, hdm⟩
      exact ⟨⟨⟨hdm, hm0⟩, hsq⟩, by omega⟩
  rw [h1, h2, add_sub_cancel_right]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (sqf_tail m hm z D hz hD)
  refine sum_le_sum fun d _ => ?_
  split_ifs <;> simp

end ThmE
end LeanLab.HardyLittlewood1923

namespace LeanLab.HardyLittlewood1923
namespace ThmE

open Real Finset Filter Topology

attribute [local instance] Classical.propDecidable

theorem grow (k : ℕ) (T : ℝ) (hT : 0 < T) : ∀ᶠ n : ℕ in atTop, T ≤ (n : ℝ) / Real.log n ^ k := by
  have hb := (isLittleO_pow_log_id_atTop (n := k)).bound (show (0 : ℝ) < 1 / T by positivity)
  have hb' : ∀ᶠ n : ℕ in atTop, ‖Real.log (n : ℝ) ^ k‖ ≤ 1 / T * ‖((n : ℝ))‖ :=
    tendsto_natCast_atTop_atTop.eventually hb
  filter_upwards [hb', eventually_ge_atTop 3] with n hn h3
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < Real.log n := Real.log_pos hn1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hL k),
    abs_of_pos (by linarith : (0 : ℝ) < n)] at hn
  rw [le_div_iff₀ (pow_pos hL k)]
  have := mul_le_mul_of_nonneg_left hn hT.le
  rw [show T * (1 / T * (n : ℝ)) = n by field_simp] at this
  linarith

theorem loglog (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.log (Real.log n) ≤ c * Real.log n := by
  have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < c / 2 by positivity)
  have hLt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb' : ∀ᶠ n : ℕ in atTop, ‖Real.log (Real.log n)‖ ≤ c / 2 * ‖Real.log n‖ :=
    hLt.eventually hb
  filter_upwards [hb', hLt.eventually_ge_atTop 1] with n hn h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log n)] at hn
  have := le_abs_self (Real.log (Real.log n))
  linarith

theorem mem_oddPrimesLE {n p : ℕ} : p ∈ oddPrimesLE n ↔ p ≤ n ∧ p.Prime ∧ Odd p := by
  simp [oddPrimesLE]

theorem sq_le_n2 {n p : ℕ} (h : p ≤ n) : (((n - p : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
  have : ((n - p : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n p
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2

/-- `A_d(n) = Σ_{p odd prime ≤ n, d ∣ n - p} (n - p)²`. -/
noncomputable def Ad (d n : ℕ) : ℝ :=
  ∑ p ∈ (oddPrimesLE n).filter (fun p => d ∣ n - p), (((n - p : ℕ) : ℝ)) ^ 2

theorem Ad_nonneg (d n : ℕ) : 0 ≤ Ad d n := sum_nonneg fun _ _ => sq_nonneg _

theorem Ad_compare (d n : ℕ) (hn : 1 ≤ n) :
    Ad d n ≤ ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d), ((n : ℝ) - p) ^ 2 ∧
    ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d), ((n : ℝ) - p) ^ 2 ≤
      Ad d n + (n : ℝ) ^ 2 := by
  set T := (range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)
  set O := (oddPrimesLE n).filter (fun p => d ∣ n - p)
  have hOT : O ⊆ T := by
    intro p hp
    simp only [O, T, mem_filter, mem_oddPrimesLE, mem_range] at hp ⊢
    obtain ⟨⟨hpn, hp, _⟩, hdvd⟩ := hp
    exact ⟨by omega, hp, (Nat.modEq_iff_dvd' hpn).mpr hdvd⟩
  have hAd : Ad d n = ∑ p ∈ O, ((n : ℝ) - p) ^ 2 := by
    unfold Ad; refine sum_congr rfl fun p hp => ?_
    simp only [O, mem_filter, mem_oddPrimesLE] at hp
    rw [Nat.cast_sub hp.1.1]
  rw [hAd]
  constructor
  · exact sum_le_sum_of_subset_of_nonneg hOT (fun _ _ _ => sq_nonneg _)
  · have hTO : T ⊆ insert 2 O := by
      intro p hp
      simp only [O, T, mem_filter, mem_oddPrimesLE, mem_range, mem_insert] at hp ⊢
      obtain ⟨hpn, hp, hmod⟩ := hp
      by_cases h2 : p = 2
      · left; exact h2
      · right
        exact ⟨⟨by omega, hp, hp.odd_of_ne_two h2⟩, (Nat.modEq_iff_dvd' (by omega)).mp hmod⟩
    refine (sum_le_sum_of_subset_of_nonneg hTO (fun _ _ _ => sq_nonneg _)).trans ?_
    have h2 : ((n : ℝ) - 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    by_cases hm : 2 ∈ O
    · rw [insert_eq_of_mem hm]; linarith [sq_nonneg (n : ℝ)]
    · rw [sum_insert hm]; push_cast; linarith

theorem Ad_noncop (d n : ℕ) (h : ¬ Nat.Coprime d n) : Ad d n ≤ (n : ℝ) ^ 2 := by
  obtain ⟨l, hl, hld, hln⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have key : ∀ p ∈ (oddPrimesLE n).filter (fun p => d ∣ n - p), p = l := by
    intro p hp
    simp only [mem_filter, mem_oddPrimesLE] at hp
    obtain ⟨⟨hpn, hp, _⟩, hdvd⟩ := hp
    have h1 : l ∣ n - p := hld.trans hdvd
    have h2 : l ∣ p := by
      have := Nat.dvd_sub hln h1
      rwa [Nat.sub_sub_self hpn] at this
    exact ((Nat.prime_dvd_prime_iff_eq hl hp).mp h2).symm
  have hcard : ((oddPrimesLE n).filter (fun p => d ∣ n - p)).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    rw [key a ha, key b hb]
  unfold Ad
  calc _ ≤ ∑ p ∈ (oddPrimesLE n).filter (fun p => d ∣ n - p), (n : ℝ) ^ 2 :=
        sum_le_sum fun p hp => sq_le_n2 (mem_oddPrimesLE.mp (mem_filter.mp hp).1).1
    _ = ((oddPrimesLE n).filter (fun p => d ∣ n - p)).card * (n : ℝ) ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * (n : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact_mod_cast hcard
    _ = (n : ℝ) ^ 2 := one_mul _

/-- `S(n) = Σ_{p odd prime ≤ n} (n - p)² Pi3(n - p)`. -/
noncomputable def Sfun (n : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesLE n, (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p)

theorem swap (n D : ℕ) :
    ∑ p ∈ oddPrimesLE n, (((n - p : ℕ) : ℝ)) ^ 2 *
      (∑ d ∈ (Icc 1 D).filter (fun d => Squarefree d ∧ Odd d), if d ∣ n - p then g d else 0) =
    ∑ d ∈ (Icc 1 D).filter (fun d => Squarefree d ∧ Odd d), g d * Ad d n := by
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  unfold Ad
  rw [mul_sum, sum_filter]
  refine sum_congr rfl fun p _ => ?_
  split_ifs <;> ring

theorem Wbound : ∀ᶠ n : ℕ in atTop,
    ∑ p ∈ oddPrimesLE n, (((n - p : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) ^ 3 / Real.log n := by
  obtain ⟨n₀, h⟩ := ap_sum_sq 1 le_rfl (2 / 3) (by norm_num)
  filter_upwards [eventually_ge_atTop (max n₀ 2)] with n hn
  have hL : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have h1 := (abs_le.mp (h n (le_of_max_le_left hn) 0 (Nat.coprime_one_right 0))).2
  rw [Nat.totient_one] at h1
  have hsub : ∑ p ∈ oddPrimesLE n, (((n - p : ℕ) : ℝ)) ^ 2 ≤
      ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % 1 = 0 % 1), ((n : ℝ) - p) ^ 2 := by
    calc _ = ∑ p ∈ oddPrimesLE n, ((n : ℝ) - p) ^ 2 := by
          refine sum_congr rfl fun p hp => ?_
          rw [Nat.cast_sub (mem_oddPrimesLE.mp hp).1]
      _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
          intro p hp
          simp only [oddPrimesLE, mem_filter, mem_range] at hp ⊢
          exact ⟨hp.1, hp.2.1, by simp [Nat.mod_one]⟩
  have : (n : ℝ) ^ 3 / (3 * ((1 : ℕ) : ℝ) * Real.log n) + 2 / 3 * (n : ℝ) ^ 3 / Real.log n =
      (n : ℝ) ^ 3 / Real.log n := by
    field_simp; ring
  linarith

/-- The singular-series average: `S(n) = (C₄/C₃) Pi4(n) n³/(3 log n) + o(n³/log n)`. -/
theorem S_asymp (θ : ℝ) (hθ : 0 < θ) : ∀ᶠ n : ℕ in atTop, Even n →
    |Sfun n - C4 * Pi4 n * (n : ℝ) ^ 3 / (3 * C3 * Real.log n)| ≤ θ * ((n : ℝ) ^ 3 / Real.log n) := by
  have hC3 := C3_pos
  obtain ⟨z, hz2, hzθ⟩ : ∃ z : ℕ, 2 ≤ z ∧ 3 / ((z : ℝ) - 1) ≤ θ / 4 := by
    refine ⟨⌈12 / θ⌉₊ + 2, by omega, ?_⟩
    have h1 : 12 / θ ≤ (⌈12 / θ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : 12 ≤ (⌈12 / θ⌉₊ : ℝ) * θ := (div_le_iff₀ hθ).mp h1
    push_cast
    have h0 : (0 : ℝ) ≤ ⌈12 / θ⌉₊ := Nat.cast_nonneg _
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨D₀, hE⟩ := euler_avg_tendsto (3 / 4 * θ * C3) (by positivity)
  set D := max D₀ z.factorial with hDdef
  set F := (Icc 1 D).filter (fun d => Squarefree d ∧ Odd d) with hF
  set ε₁ := θ / (4 * ((D : ℝ) + 1)) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  have hAP : ∀ᶠ n : ℕ in atTop, ∀ d ∈ F, Nat.Coprime d n →
      |Ad d n - (n : ℝ) ^ 3 / (3 * (Nat.totient d : ℝ) * Real.log n)| ≤
        ε₁ * (n : ℝ) ^ 3 / Real.log n + (n : ℝ) ^ 2 := by
    rw [eventually_all_finset]
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp (mem_filter.mp hd).1).1
    obtain ⟨n₀, h⟩ := ap_sum_sq d hd1 ε₁ hε₁
    filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn hcop
    have h1 := h n (le_of_max_le_left hn) n hcop.symm
    have h2 := Ad_compare d n (le_of_max_le_right hn)
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h2.1, h2.2, h1.1, h1.2]
  filter_upwards [hAP, Wbound, grow 1 (8 * ((D : ℝ) + 1) / θ) (by positivity),
    eventually_ge_atTop 2] with n hAPn hW hg hn2 heven
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmodd : ∀ p ∈ oddPrimesLE n, Odd (n - p) := fun p hp => by
    obtain ⟨hpn, -, hpo⟩ := mem_oddPrimesLE.mp hp
    exact Nat.Even.sub_odd hpn heven hpo
  -- step 1: truncate the divisor expansion
  have htail : |Sfun n - ∑ p ∈ oddPrimesLE n, (((n - p : ℕ) : ℝ)) ^ 2 *
      (∑ d ∈ F, if d ∣ n - p then g d else 0)| ≤ θ / 4 * ((n : ℝ) ^ 3 / Real.log n) := by
    unfold Sfun
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ oddPrimesLE n, |(((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) -
          (((n - p : ℕ) : ℝ)) ^ 2 * (∑ d ∈ F, if d ∣ n - p then g d else 0)|
        ≤ ∑ p ∈ oddPrimesLE n, (((n - p : ℕ) : ℝ)) ^ 2 * (θ / 4) := by
          refine sum_le_sum fun p hp => ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left ((pi3_trunc (n - p) (hmodd p hp) z D hz2
            (le_max_right _ _)).trans hzθ) (sq_nonneg _)
      _ = (∑ p ∈ oddPrimesLE n, (((n - p : ℕ) : ℝ)) ^ 2) * (θ / 4) := by rw [sum_mul]
      _ ≤ ((n : ℝ) ^ 3 / Real.log n) * (θ / 4) := mul_le_mul_of_nonneg_right hW (by positivity)
      _ = θ / 4 * ((n : ℝ) ^ 3 / Real.log n) := by ring
  rw [swap n D] at htail
  -- step 2: the progressions
  set E := ∑ d ∈ F.filter (fun d => Nat.Coprime d n), g d / (Nat.totient d : ℝ) with hEdef
  have hcardF : (F.card : ℝ) ≤ D + 1 := by
    have : F.card ≤ D + 1 := (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hmain : |∑ d ∈ F, g d * Ad d n - (n : ℝ) ^ 3 / (3 * Real.log n) * E| ≤
      ((D : ℝ) + 1) * (ε₁ * (n : ℝ) ^ 3 / Real.log n + (n : ℝ) ^ 2) := by
    rw [hEdef, mul_sum, sum_filter (fun d => Nat.Coprime d n), ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hper : ∀ d ∈ F, |g d * Ad d n - (if Nat.Coprime d n then
        (n : ℝ) ^ 3 / (3 * Real.log n) * (g d / (Nat.totient d : ℝ)) else 0)| ≤
        ε₁ * (n : ℝ) ^ 3 / Real.log n + (n : ℝ) ^ 2 := by
      intro d hd
      obtain ⟨hdI, hsq, hodd⟩ := mem_filter.mp hd
      have hd1 : 1 ≤ d := (mem_Icc.mp hdI).1
      have hg1 : |g d| ≤ 1 := by
        refine (abs_g_le d hsq hodd).trans ?_
        rw [div_le_one (by exact_mod_cast hd1)]; exact_mod_cast hd1
      have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd1
      have hB : 0 ≤ ε₁ * (n : ℝ) ^ 3 / Real.log n := by positivity
      split_ifs with hcop
      · have := hAPn d hd hcop
        have e : g d * Ad d n - (n : ℝ) ^ 3 / (3 * Real.log n) * (g d / (Nat.totient d : ℝ)) =
            g d * (Ad d n - (n : ℝ) ^ 3 / (3 * (Nat.totient d : ℝ) * Real.log n)) := by
          field_simp
        rw [e, abs_mul]
        calc |g d| * |Ad d n - (n : ℝ) ^ 3 / (3 * (Nat.totient d : ℝ) * Real.log n)|
            ≤ 1 * (ε₁ * (n : ℝ) ^ 3 / Real.log n + (n : ℝ) ^ 2) :=
              mul_le_mul hg1 this (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      · rw [sub_zero, abs_mul, abs_of_nonneg (Ad_nonneg d n)]
        have := Ad_noncop d n hcop
        calc |g d| * Ad d n ≤ 1 * (n : ℝ) ^ 2 :=
              mul_le_mul hg1 this (Ad_nonneg d n) zero_le_one
          _ ≤ _ := by linarith
    refine (sum_le_sum hper).trans ?_
    rw [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcardF (by positivity)
  -- step 3: the Euler product
  have hEn := hE D n (le_max_left _ _) heven (by omega)
  have hFE : (Icc 1 D).filter (fun d => Squarefree d ∧ Odd d ∧ Nat.Coprime d n) =
      F.filter (fun d => Nat.Coprime d n) := by
    rw [hF, filter_filter]; simp only [and_assoc]
  rw [hFE, ← hEdef] at hEn
  have heul : |(n : ℝ) ^ 3 / (3 * Real.log n) * E - C4 * Pi4 n * (n : ℝ) ^ 3 / (3 * C3 * Real.log n)|
      ≤ θ / 4 * ((n : ℝ) ^ 3 / Real.log n) := by
    have e : (n : ℝ) ^ 3 / (3 * Real.log n) * E - C4 * Pi4 n * (n : ℝ) ^ 3 / (3 * C3 * Real.log n)
        = (n : ℝ) ^ 3 / (3 * C3 * Real.log n) * (C3 * E - C4 * Pi4 n) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    calc (n : ℝ) ^ 3 / (3 * C3 * Real.log n) * |C3 * E - C4 * Pi4 n|
        ≤ (n : ℝ) ^ 3 / (3 * C3 * Real.log n) * (3 / 4 * θ * C3) :=
          mul_le_mul_of_nonneg_left hEn (by positivity)
      _ = θ / 4 * ((n : ℝ) ^ 3 / Real.log n) := by field_simp
  -- step 4: sizes
  have hDn : ((D : ℝ) + 1) * (n : ℝ) ^ 2 ≤ θ / 8 * ((n : ℝ) ^ 3 / Real.log n) := by
    rw [pow_one, div_le_div_iff₀ hθ hL] at hg
    rw [show θ / 8 * ((n : ℝ) ^ 3 / Real.log n) = θ * (n : ℝ) ^ 3 / (8 * Real.log n) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hg (sq_nonneg (n : ℝ))]
  have hε : ((D : ℝ) + 1) * (ε₁ * (n : ℝ) ^ 3 / Real.log n + (n : ℝ) ^ 2) =
      θ / 4 * ((n : ℝ) ^ 3 / Real.log n) + ((D : ℝ) + 1) * (n : ℝ) ^ 2 := by
    rw [hε₁def]; field_simp
  rw [hε] at hmain
  rw [abs_le] at htail hmain heul ⊢
  constructor <;> nlinarith [htail.1, htail.2, hmain.1, hmain.2, heul.1, heul.2]

end ThmE
end LeanLab.HardyLittlewood1923

namespace LeanLab.HardyLittlewood1923
namespace ThmE

open Real Finset Filter Topology

attribute [local instance] Classical.propDecidable

theorem N3bar_le_sq (m : ℕ) : (N3bar m : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
  have : N3bar m ≤ (m + 1) ^ 2 := by
    unfold N3bar
    refine (card_filter_le _ _).trans ?_
    rw [card_product, card_range, sq]
  exact_mod_cast this

/-- One term `N̄₃(m)` with `log m` replaced by `L`. -/
theorem good_term (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (m₀ : ℕ)
    (hD : ∀ m, Odd m → m₀ ≤ m → |(N3bar m : ℝ) - C3 * (m : ℝ) ^ 2 / Real.log m ^ 3 * Pi3 m| ≤
      δ * (C3 * (m : ℝ) ^ 2 / Real.log m ^ 3 * Pi3 m))
    (m : ℕ) (hm : Odd m) (hm0 : m₀ ≤ m) (L : ℝ) (hl0 : 0 < Real.log m) (hlL : Real.log m ≤ L)
    (hLl : L ^ 3 ≤ (1 + δ) * Real.log m ^ 3) :
    |(N3bar m : ℝ) - C3 * (m : ℝ) ^ 2 * Pi3 m / L ^ 3| ≤ 3 * δ * (C3 * (m : ℝ) ^ 2 / L ^ 3) := by
  have hC3 := C3_pos
  have hP := Pi3_bounds m
  have hL0 : 0 < L := by linarith
  have hK : 0 ≤ C3 * (m : ℝ) ^ 2 * Pi3 m := by have := hP.1; positivity
  have h := hD m hm hm0
  have hX : C3 * (m : ℝ) ^ 2 / Real.log m ^ 3 * Pi3 m =
      C3 * (m : ℝ) ^ 2 * Pi3 m / Real.log m ^ 3 := by ring
  rw [hX] at h
  set K := C3 * (m : ℝ) ^ 2 * Pi3 m with hKdef
  set ℓ := Real.log m with hℓ
  set X := K / ℓ ^ 3 with hXdef
  set Y := K / L ^ 3 with hYdef
  set W := C3 * (m : ℝ) ^ 2 / L ^ 3 with hWdef
  have hY0 : 0 ≤ Y := by positivity
  have hYX : Y ≤ X := div_le_div_of_nonneg_left hK (pow_pos hl0 3) (pow_le_pow_left₀ hl0.le hlL 3)
  have hXY : X ≤ (1 + δ) * Y := by
    rw [hXdef, div_le_iff₀ (pow_pos hl0 3)]
    have e : Y * L ^ 3 = K := div_mul_cancel₀ _ (by positivity)
    have := mul_le_mul_of_nonneg_left hLl hY0
    nlinarith
  have hYW : Y ≤ W := by
    rw [hYdef, hWdef]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [hKdef]
    have : 0 ≤ C3 * (m : ℝ) ^ 2 := by positivity
    nlinarith [hP.2]
  have a1 : δ * X ≤ δ * ((1 + δ) * Y) := mul_le_mul_of_nonneg_left hXY hδ.le
  have a2 : (1 - δ) * Y ≤ (1 - δ) * X := mul_le_mul_of_nonneg_left hYX (by linarith)
  have a3 : δ * δ * Y ≤ δ * Y := mul_le_mul_of_nonneg_right (by nlinarith) hY0
  have a4 : δ * Y ≤ δ * W := mul_le_mul_of_nonneg_left hYW hδ.le
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

/-- `N̄₄(n) = (C₃/log³ n) S(n) + o(n³/log⁴ n)`. -/
theorem N4_vs_S (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, Even n →
    |(N4bar n : ℝ) - C3 * Sfun n / Real.log n ^ 3| ≤ δ * ((n : ℝ) ^ 3 / Real.log n ^ 4) := by
  have hC3 := C3_pos
  set δ' := min (δ / (6 * C3)) 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'2 : δ' ≤ δ / (6 * C3) := min_le_left _ _
  obtain ⟨m₀, hD⟩ := theoremD δ' hδ'0
  filter_upwards [Wbound, grow 2 (max (m₀ : ℝ) 2) (by positivity), loglog (δ' / 12) (by positivity),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (16 * (1 + C3) / δ + 1), eventually_ge_atTop 2] with n hW hg hll hLbig hn2 heven
  simp only [Function.comp] at hLbig
  set L := Real.log n with hLdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc0 : 0 ≤ 16 * (1 + C3) / δ := by positivity
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL2 : 16 * (1 + C3) ≤ δ * L ^ 2 := by
    have h1 : 16 * (1 + C3) / δ ≤ L ^ 2 := by nlinarith
    rw [div_le_iff₀ hδ] at h1; linarith
  set B := ⌈(n : ℝ) / L ^ 2⌉₊ with hBdef
  have hq0 : 0 ≤ (n : ℝ) / L ^ 2 := by positivity
  have hB1 : (n : ℝ) / L ^ 2 ≤ B := Nat.le_ceil _
  have hB2 : (B : ℝ) < (n : ℝ) / L ^ 2 + 1 := Nat.ceil_lt_add_one hq0
  have hq2 : 2 ≤ (n : ℝ) / L ^ 2 := (le_max_right _ _).trans hg
  have hqm : (m₀ : ℝ) ≤ (n : ℝ) / L ^ 2 := (le_max_left _ _).trans hg
  have hB2' : (B : ℝ) ≤ 2 * ((n : ℝ) / L ^ 2) := by linarith
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  -- the decomposition
  have hsum : (N4bar n : ℝ) - C3 * Sfun n / L ^ 3 = ∑ p ∈ oddPrimesLE n,
      ((N3bar (n - p) : ℝ) - C3 * (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) / L ^ 3) := by
    rw [N4bar_eq_sum, Nat.cast_sum, Sfun, mul_sum, sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    ring
  rw [hsum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← sum_filter_add_sum_filter_not (oddPrimesLE n) (fun p => B ≤ n - p)]
  -- good terms
  have hgood : ∑ p ∈ (oddPrimesLE n).filter (fun p => B ≤ n - p),
      |(N3bar (n - p) : ℝ) - C3 * (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) / L ^ 3| ≤
      δ / 2 * ((n : ℝ) ^ 3 / L ^ 4) := by
    have hper : ∀ p ∈ (oddPrimesLE n).filter (fun p => B ≤ n - p),
        |(N3bar (n - p) : ℝ) - C3 * (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) / L ^ 3| ≤
        3 * δ' * C3 / L ^ 3 * (((n - p : ℕ) : ℝ)) ^ 2 := by
      intro p hp
      obtain ⟨hpQ, hBp⟩ := mem_filter.mp hp
      obtain ⟨hpn, -, hpo⟩ := mem_oddPrimesLE.mp hpQ
      have hmo : Odd (n - p) := Nat.Even.sub_odd hpn heven hpo
      have hmB : (n : ℝ) / L ^ 2 ≤ ((n - p : ℕ) : ℝ) := hB1.trans (by exact_mod_cast hBp)
      have hm2 : (2 : ℝ) ≤ ((n - p : ℕ) : ℝ) := hq2.trans hmB
      have hmm0 : m₀ ≤ n - p := by exact_mod_cast hqm.trans hmB
      have hmpos : (0 : ℝ) < ((n - p : ℕ) : ℝ) := by linarith
      have hl0 : 0 < Real.log ((n - p : ℕ) : ℝ) := Real.log_pos (by linarith)
      have hlL : Real.log ((n - p : ℕ) : ℝ) ≤ L :=
        Real.log_le_log hmpos (by exact_mod_cast Nat.sub_le n p)
      have hlow : (1 - δ' / 12) * L ≤ Real.log ((n - p : ℕ) : ℝ) := by
        have h1 : Real.log ((n : ℝ) / L ^ 2) ≤ Real.log ((n - p : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) hmB
        rw [Real.log_div hn0.ne' (by positivity), Real.log_pow] at h1
        push_cast at h1
        linarith
      have hLl : L ^ 3 ≤ (1 + δ') * Real.log ((n - p : ℕ) : ℝ) ^ 3 := by
        have hu : 0 ≤ (1 - δ' / 12) * L := mul_nonneg (by linarith) hL0.le
        have h1 := pow_le_pow_left₀ hu hlow 3
        have hb0 : 0 ≤ (δ' / 12) ^ 2 * (3 - δ' / 12) :=
          mul_nonneg (sq_nonneg _) (by linarith)
        have hbe : (1 - δ' / 12) ^ 3 = 1 - δ' / 4 + (δ' / 12) ^ 2 * (3 - δ' / 12) := by ring
        have hb : 1 - δ' / 4 ≤ (1 - δ' / 12) ^ 3 := by linarith
        have hb2 := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ 1 + δ')
        have hdd : δ' * δ' ≤ δ' * 1 := mul_le_mul_of_nonneg_left hδ'1 hδ'0.le
        have h2 : 1 ≤ (1 + δ') * (1 - δ' / 12) ^ 3 := by linarith
        have h3 : 0 ≤ L ^ 3 := by positivity
        calc L ^ 3 ≤ (1 + δ') * (1 - δ' / 12) ^ 3 * L ^ 3 := le_mul_of_one_le_left h3 h2
          _ = (1 + δ') * ((1 - δ' / 12) * L) ^ 3 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by linarith)
      have := good_term δ' hδ'0 hδ'1 m₀ hD (n - p) hmo hmm0 L hl0 hlL hLl
      calc _ ≤ 3 * δ' * (C3 * (((n - p : ℕ) : ℝ)) ^ 2 / L ^ 3) := this
        _ = _ := by ring
    refine (sum_le_sum hper).trans ?_
    rw [← mul_sum]
    have hsub : ∑ p ∈ (oddPrimesLE n).filter (fun p => B ≤ n - p), (((n - p : ℕ) : ℝ)) ^ 2 ≤
        (n : ℝ) ^ 3 / L :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)).trans hW
    have hc : 0 ≤ 3 * δ' * C3 / L ^ 3 := by positivity
    calc 3 * δ' * C3 / L ^ 3 * ∑ p ∈ (oddPrimesLE n).filter (fun p => B ≤ n - p),
          (((n - p : ℕ) : ℝ)) ^ 2
        ≤ 3 * δ' * C3 / L ^ 3 * ((n : ℝ) ^ 3 / L) := mul_le_mul_of_nonneg_left hsub hc
      _ = 3 * δ' * C3 * ((n : ℝ) ^ 3 / L ^ 4) := by field_simp
      _ ≤ δ / 2 * ((n : ℝ) ^ 3 / L ^ 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := mul_le_mul_of_nonneg_left hδ'2 (by positivity : (0 : ℝ) ≤ 3 * C3)
          rw [show 3 * C3 * (δ / (6 * C3)) = δ / 2 by field_simp; ring] at this
          linarith
  -- bad terms
  have hbad : ∑ p ∈ (oddPrimesLE n).filter (fun p => ¬ B ≤ n - p),
      |(N3bar (n - p) : ℝ) - C3 * (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) / L ^ 3| ≤
      δ / 2 * ((n : ℝ) ^ 3 / L ^ 4) := by
    have hper : ∀ p ∈ (oddPrimesLE n).filter (fun p => ¬ B ≤ n - p),
        |(N3bar (n - p) : ℝ) - C3 * (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) / L ^ 3| ≤
        (1 + C3) * (B : ℝ) ^ 2 := by
      intro p hp
      have hlt : n - p < B := by have := (mem_filter.mp hp).2; omega
      have hm1 : ((n - p : ℕ) : ℝ) + 1 ≤ B := by exact_mod_cast hlt
      have hm0 : (0 : ℝ) ≤ ((n - p : ℕ) : ℝ) := Nat.cast_nonneg _
      have hN := N3bar_le_sq (n - p)
      have hN0 : (0 : ℝ) ≤ N3bar (n - p) := Nat.cast_nonneg _
      have hP := Pi3_bounds (n - p)
      have hY0 : 0 ≤ C3 * (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) / L ^ 3 := by
        have := hP.1; positivity
      have hY1 : C3 * (((n - p : ℕ) : ℝ)) ^ 2 * Pi3 (n - p) / L ^ 3 ≤
          C3 * (((n - p : ℕ) : ℝ)) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
        have : 0 ≤ C3 * (((n - p : ℕ) : ℝ)) ^ 2 := by positivity
        have e1 := mul_le_mul_of_nonneg_left hP.2 this
        have e2 := mul_le_mul_of_nonneg_left hL3 this
        linarith
      have hsq : (((n - p : ℕ) : ℝ) + 1) ^ 2 ≤ (B : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hm1 2
      have hsq' : (((n - p : ℕ) : ℝ)) ^ 2 ≤ (B : ℝ) ^ 2 :=
        pow_le_pow_left₀ hm0 (by linarith) 2
      have hC3B := mul_le_mul_of_nonneg_left hsq' hC3.le
      have hB2 : 0 ≤ C3 * (B : ℝ) ^ 2 := by positivity
      rw [abs_le]
      constructor <;> linarith
    refine (sum_le_sum hper).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hcard : ((oddPrimesLE n).filter (fun p => ¬ B ≤ n - p)).card ≤ B := by
      have := card_le_card_of_injOn (fun p => n - p) (t := range B)
        (s := (oddPrimesLE n).filter (fun p => ¬ B ≤ n - p)) (fun p hp => by
          have := (mem_filter.mp hp).2
          simp only [coe_range, Set.mem_Iio]; omega) (fun p hp q hq hpq => by
          have h1 := (mem_oddPrimesLE.mp (mem_filter.mp hp).1).1
          have h2 := (mem_oddPrimesLE.mp (mem_filter.mp hq).1).1
          simp only at hpq; omega)
      simpa using this
    have hcard' : (((oddPrimesLE n).filter (fun p => ¬ B ≤ n - p)).card : ℝ) ≤ B := by
      exact_mod_cast hcard
    have hB3 : (B : ℝ) ^ 3 ≤ 8 * ((n : ℝ) ^ 3 / L ^ 4) / L ^ 2 := by
      calc (B : ℝ) ^ 3 ≤ (2 * ((n : ℝ) / L ^ 2)) ^ 3 := pow_le_pow_left₀ hB0 hB2' 3
        _ = 8 * ((n : ℝ) ^ 3 / L ^ 4) / L ^ 2 := by field_simp; ring
    have hZ : 0 ≤ (n : ℝ) ^ 3 / L ^ 4 := by positivity
    calc (((oddPrimesLE n).filter (fun p => ¬ B ≤ n - p)).card : ℝ) * ((1 + C3) * (B : ℝ) ^ 2)
        ≤ (B : ℝ) * ((1 + C3) * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ = (1 + C3) * (B : ℝ) ^ 3 := by ring
      _ ≤ (1 + C3) * (8 * ((n : ℝ) ^ 3 / L ^ 4) / L ^ 2) :=
          mul_le_mul_of_nonneg_left hB3 (by positivity)
      _ = ((n : ℝ) ^ 3 / L ^ 4) * (16 * (1 + C3)) / (2 * L ^ 2) := by field_simp; ring
      _ ≤ ((n : ℝ) ^ 3 / L ^ 4) * (δ * L ^ 2) / (2 * L ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hL2 hZ
      _ = δ / 2 * ((n : ℝ) ^ 3 / L ^ 4) := by field_simp
  linarith

end ThmE

open Real Finset Filter

/-- **Hardy-Littlewood 1923, Theorem E, (3.63)**, with no hypothesis. -/
theorem theoremE : theoremE_stmt := by
  intro ε hε
  have hC3 := C3_pos
  have hC4 := C4_pos
  have h1 := ThmE.N4_vs_S (ε * C4 / 6) (by positivity)
  have h2 := ThmE.S_asymp (ε * C4 / (6 * C3)) (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (h1.and (h2.and (eventually_ge_atTop 2)))
  refine ⟨n₀, fun n hn hn0 => ?_⟩
  obtain ⟨a, b, hn2⟩ := hn₀ n hn0
  have a := a hn
  have b := b hn
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn0' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP := one_le_Pi4 n
  set L := Real.log n
  have b' : |C3 * ThmE.Sfun n / L ^ 3 - C4 * (n : ℝ) ^ 3 / (3 * L ^ 4) * Pi4 n| ≤
      ε * C4 / 6 * ((n : ℝ) ^ 3 / L ^ 4) := by
    have e : C3 * ThmE.Sfun n / L ^ 3 - C4 * (n : ℝ) ^ 3 / (3 * L ^ 4) * Pi4 n =
        C3 / L ^ 3 * (ThmE.Sfun n - C4 * Pi4 n * (n : ℝ) ^ 3 / (3 * C3 * L)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    calc C3 / L ^ 3 * |ThmE.Sfun n - C4 * Pi4 n * (n : ℝ) ^ 3 / (3 * C3 * L)|
        ≤ C3 / L ^ 3 * (ε * C4 / (6 * C3) * ((n : ℝ) ^ 3 / L)) :=
          mul_le_mul_of_nonneg_left b (by positivity)
      _ = ε * C4 / 6 * ((n : ℝ) ^ 3 / L ^ 4) := by field_simp
  have hM : C4 * (n : ℝ) ^ 3 / (3 * L ^ 4) ≤ C4 * (n : ℝ) ^ 3 / (3 * L ^ 4) * Pi4 n := by
    have : 0 ≤ C4 * (n : ℝ) ^ 3 / (3 * L ^ 4) := by positivity
    nlinarith
  have hfin : ε * C4 / 6 * ((n : ℝ) ^ 3 / L ^ 4) = ε / 2 * (C4 * (n : ℝ) ^ 3 / (3 * L ^ 4)) := by
    field_simp; ring
  rw [hfin] at a b'
  have hε2 := mul_le_mul_of_nonneg_left hM hε.le
  rw [abs_le] at a b' ⊢
  constructor <;> nlinarith [a.1, a.2, b'.1, b'.2]

/-- Theorem E, first sentence: every large even number is the sum of four odd primes. -/
theorem theoremE_four : ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n → 0 < N4bar n := by
  obtain ⟨n₀, h⟩ := theoremE (1 / 2) (by norm_num)
  refine ⟨max n₀ 2, fun n hn hn0 => ?_⟩
  have hb := h n hn (le_of_max_le_left hn0)
  have hC4 := C4_pos
  have hP : (1 : ℝ) ≤ Pi4 n := one_le_Pi4 n
  have hL : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmain : 0 < C4 * (n : ℝ) ^ 3 / (3 * Real.log n ^ 4) * Pi4 n := by
    have : (0 : ℝ) < Pi4 n := by linarith
    positivity
  have := (abs_le.mp hb).1
  have : (0 : ℝ) < N4bar n := by linarith
  exact_mod_cast this

end LeanLab.HardyLittlewood1923

