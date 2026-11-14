module

public import Mathlib
public import LeanLab.HeathBrown1985.Statements

/-!
P0096 Heath-Brown 1985, elementary inputs for the deduction of Theorem 2 on page 52 to 53.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-- A finset of positive integers has reciprocal sum at most the harmonic sum of its size. -/
theorem sum_inv_le_harmonic (S : Finset ℕ) (hS : ∀ s ∈ S, 1 ≤ s) :
    ∑ s ∈ S, (s : ℝ)⁻¹ ≤ ∑ j ∈ Icc 1 S.card, (j : ℝ)⁻¹ := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ih' := ih (fun t ht => hS t (mem_insert_of_mem ht))
    have ha1 : 1 ≤ a := hS a (mem_insert_self a s)
    have hsub : s ⊆ Icc 1 (a - 1) := by
      intro t ht
      have := hS t (mem_insert_of_mem ht)
      have := hlt t ht
      simp only [mem_Icc]; omega
    have hcard : s.card + 1 ≤ a := by
      have := card_le_card hsub
      simp at this; omega
    rw [sum_insert ha, card_insert_of_notMem ha, sum_Icc_succ_top (by omega)]
    have : (a : ℝ)⁻¹ ≤ ((s.card + 1 : ℕ) : ℝ)⁻¹ := by
      apply inv_anti₀ (by positivity); exact_mod_cast hcard
    linarith

theorem sum_inv_Icc_le_log (n : ℕ) : ∑ j ∈ Icc 1 n, (j : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have := harmonic_le_one_add_log n
  simpa [harmonic_eq_sum_Icc] using this

/-- `ω(k) log 2 ≤ log k`. -/
theorem card_primeFactors_mul_log_two_le (k : ℕ) (hk : 1 ≤ k) :
    (k.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log k := by
  have h1 : 2 ^ k.primeFactors.card ≤ ∏ p ∈ k.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ k.primeFactors, p ≤ k := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd k)
  have h3 : ((2 : ℕ) : ℝ) ^ k.primeFactors.card ≤ (k : ℝ) := by exact_mod_cast h1.trans h2
  have := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at this
  simpa using this

/-- `k / φ(k) ≤ e (1 + ω(k))`. -/
theorem div_totient_le (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) / (Nat.totient k : ℝ) ≤ Real.exp 1 * (1 + k.primeFactors.card) := by
  have hφ : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hP : ∀ p ∈ k.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have key := Nat.totient_mul_prod_primeFactors k
  have keyR : (Nat.totient k : ℝ) * ∏ p ∈ k.primeFactors, (p : ℝ) =
      (k : ℝ) * ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) key
    push_cast at this
    rw [this]
    congr 1
    apply prod_congr rfl
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [this]; ring
  have hpos : (0 : ℝ) < ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) :=
    prod_pos (fun p hp => by linarith [hP p hp])
  have hratio : (k : ℝ) / (Nat.totient k : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [prod_div_distrib, div_eq_div_iff hφ.ne' hpos.ne']
    linarith [keyR]
  rw [hratio]
  have hexp : ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (∑ p ∈ k.primeFactors, ((p : ℝ) - 1)⁻¹) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro p hp; have := hP p hp; apply div_nonneg <;> linarith
    · intro p hp
      have h2 := hP p hp
      have : (p : ℝ) / ((p : ℝ) - 1) = ((p : ℝ) - 1)⁻¹ + 1 := by
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp; ring
      rw [this]; exact Real.add_one_le_exp _
  have hsum : ∑ p ∈ k.primeFactors, ((p : ℝ) - 1)⁻¹ ≤ 1 + Real.log k.primeFactors.card := by
    have hinj : Set.InjOn (fun p : ℕ => p - 1) (k.primeFactors : Set ℕ) := by
      intro a ha b hb hab
      have := (Nat.prime_of_mem_primeFactors ha).one_le
      have := (Nat.prime_of_mem_primeFactors hb).one_le
      simp at hab; omega
    have e1 : ∑ p ∈ k.primeFactors, ((p : ℝ) - 1)⁻¹ =
        ∑ s ∈ k.primeFactors.image (fun p : ℕ => p - 1), (s : ℝ)⁻¹ := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).one_le
      push_cast [this]; ring
    rw [e1]
    have h1 := sum_inv_le_harmonic (k.primeFactors.image (fun p : ℕ => p - 1)) (by
      intro s hs
      simp only [mem_image] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega)
    rw [card_image_of_injOn hinj] at h1
    exact h1.trans (sum_inv_Icc_le_log _)
  calc _ ≤ _ := hexp
    _ ≤ Real.exp (1 + Real.log k.primeFactors.card) := Real.exp_le_exp.mpr hsum
    _ ≤ Real.exp 1 * (1 + k.primeFactors.card) := by
      rw [Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      rcases Nat.eq_zero_or_pos k.primeFactors.card with h | h
      · simp [h]
      · rw [Real.exp_log (by exact_mod_cast h)]; linarith

/-- `Σ_{k ≤ N} d(k)/k ≤ (Σ_{a ≤ N} 1/a)²`. -/
theorem sum_divisors_div_le (N : ℕ) :
    ∑ k ∈ Icc 1 N, (k.divisors.card : ℝ) / k ≤ (∑ a ∈ Icc 1 N, (a : ℝ)⁻¹) ^ 2 := by
  have e1 : ∑ k ∈ Icc 1 N, (k.divisors.card : ℝ) / k =
      ∑ k ∈ Icc 1 N, ∑ a ∈ k.divisors, (k : ℝ)⁻¹ := by
    apply sum_congr rfl; intro k _; rw [sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [e1, Finset.sum_comm' (t' := Icc 1 N) (s' := fun a => (Icc 1 N).filter (a ∣ ·))]
  · rw [sq, sum_mul]
    apply sum_le_sum
    intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
    rw [mul_sum]
    have hsub : (Icc 1 N).filter (a ∣ ·) ⊆ (Icc 1 N).image (a * ·) := by
      intro k hk
      simp only [mem_filter, mem_Icc] at hk
      obtain ⟨⟨hk1, hkN⟩, b, rfl⟩ := hk
      simp only [mem_image, mem_Icc]
      refine ⟨b, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos b with h | h
        · subst h; simp at hk1
        · exact h
      · exact le_trans (Nat.le_mul_of_pos_left b (by omega)) hkN
    calc ∑ k ∈ (Icc 1 N).filter (a ∣ ·), (k : ℝ)⁻¹
        ≤ ∑ k ∈ (Icc 1 N).image (a * ·), (k : ℝ)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ b ∈ Icc 1 N, ((a * b : ℕ) : ℝ)⁻¹ := by
          rw [sum_image]; intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h
      _ = ∑ b ∈ Icc 1 N, (a : ℝ)⁻¹ * (b : ℝ)⁻¹ := by
          apply sum_congr rfl; intro b _; push_cast; rw [mul_inv]
  · intro k a
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have := Nat.le_of_dvd (by omega) h3
      have : 1 ≤ a := Nat.pos_of_dvd_of_pos h3 (by omega)
      exact ⟨⟨⟨h1, h2⟩, h3⟩, by omega, by omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨h1, h2⟩, h3, by omega⟩

theorem sum_divisors_div_le_log (N : ℕ) :
    ∑ k ∈ Icc 1 N, (k.divisors.card : ℝ) / k ≤ (1 + Real.log N) ^ 2 := by
  refine (sum_divisors_div_le N).trans ?_
  have h0 : 0 ≤ ∑ a ∈ Icc 1 N, (a : ℝ)⁻¹ := sum_nonneg (fun _ _ => by positivity)
  exact pow_le_pow_left₀ h0 (sum_inv_Icc_le_log N) 2

/-- At most `N/k + 1` integers in `[1, N]` lie in one residue class mod `k`. -/
theorem card_residue_le (N k r : ℕ) (hk : 1 ≤ k) :
    ((Icc 1 N).filter (fun n => n % k = r)).card ≤ N / k + 1 := by
  have : ((Icc 1 N).filter (fun n => n % k = r)).card ≤ (range (N / k + 1)).card := by
    apply card_le_card_of_injOn (fun n => n / k)
    · intro n hn
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hn
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)
    · intro n hn m hm h
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hn hm
      simp only at h
      rw [← Nat.div_add_mod n k, ← Nat.div_add_mod m k, h, hn.2, hm.2]
  simpa using this

theorem psi_nonneg (x : ℝ) (k l : ℕ) : 0 ≤ psi x k l :=
  sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem psi_le (x : ℝ) (hx : 1 ≤ x) (k l : ℕ) (hk : 1 ≤ k) :
    psi x k l ≤ Real.log x * (x / k + 1) := by
  unfold psi
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  calc _ ≤ ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), Real.log x := by
        apply sum_le_sum
        intro n hn
        simp only [mem_filter, mem_Icc] at hn
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        apply Real.log_le_log (by exact_mod_cast hn.1.1)
        exact (Nat.cast_le.mpr hn.1.2).trans (Nat.floor_le (by linarith))
    _ = ((Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k)).card * Real.log x := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((⌊x⌋₊ / k : ℕ) + 1 : ℝ) * Real.log x := by
        apply mul_le_mul_of_nonneg_right _ hL
        exact_mod_cast card_residue_le _ _ _ hk
    _ ≤ (x / k + 1) * Real.log x := by
        apply mul_le_mul_of_nonneg_right _ hL
        have h1 : ((⌊x⌋₊ / k : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / k := Nat.cast_div_le
        have h2 : (⌊x⌋₊ : ℝ) / k ≤ x / k :=
          div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
        linarith
    _ = _ := by ring

/-- The constant of the pointwise bound. -/
def Mpt : ℝ := 2 + Real.exp 1 * (1 + 1 / Real.log 2)

theorem Mpt_pos : 0 < Mpt := by unfold Mpt; have := Real.log_pos one_lt_two; positivity

/-- Pointwise: `|ψ(x;k,l) - x/φ(k)| ≤ M x L / k` for `1 ≤ k ≤ x`, `L = log x ≥ 1`. -/
theorem abs_err_le (x : ℝ) (hL : 1 ≤ Real.log x) (k l : ℕ) (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ x) :
    |psi x k l - x / (Nat.totient k : ℝ)| ≤ Mpt * x * Real.log x / k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : 1 ≤ x := hk1.trans hkx
  have hkpos : (0 : ℝ) < k := by linarith
  have hφ : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hl2 := Real.log_pos one_lt_two
  set L := Real.log x with hLdef
  have hψ0 := psi_nonneg x k l
  have hψ := psi_le x hx1 k l hk
  have hxk : 1 ≤ x / k := by rw [le_div_iff₀ hkpos]; linarith
  have hω : (k.primeFactors.card : ℝ) ≤ L / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    refine (card_primeFactors_mul_log_two_le k hk).trans ?_
    exact Real.log_le_log hkpos hkx
  have hdt := div_totient_le k hk
  have hxφ : x / (Nat.totient k : ℝ) = (x / k) * ((k : ℝ) / Nat.totient k) := by
    field_simp
  have hxφ_le : x / (Nat.totient k : ℝ) ≤ (x / k) * (Real.exp 1 * (L + L / Real.log 2)) := by
    rw [hxφ]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine hdt.trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
    linarith
  have habs : |psi x k l - x / (Nat.totient k : ℝ)| ≤ psi x k l + x / (Nat.totient k : ℝ) := by
    rw [abs_le]; constructor <;> nlinarith [div_nonneg (by linarith : (0:ℝ) ≤ x) hφ.le]
  have hψ2 : psi x k l ≤ 2 * L * (x / k) := by nlinarith
  calc _ ≤ _ := habs
    _ ≤ 2 * L * (x / k) + (x / k) * (Real.exp 1 * (L + L / Real.log 2)) := add_le_add hψ2 hxφ_le
    _ = Mpt * x * L / k := by unfold Mpt; field_simp

end LeanLab.HeathBrown1985
