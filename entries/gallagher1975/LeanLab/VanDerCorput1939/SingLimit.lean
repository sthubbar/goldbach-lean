module

public import Mathlib
public import LeanLab.PNTPort.Vinogradov.SingPos
public import LeanLab.VanDerCorput1939.Global
public import LeanLab.VanDerCorput1939.KBounds

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5704, paper P0067.
P0067 van der Corput 1939: the truncated ternary singular series tends to K P(N),
uniformly over odd N. For every ε > 0 there is P₀ with
|∑_{q ≤ Q} f_N(q) - K P(N)| ≤ ε for all Q ≥ P₀ and all odd N with log N ≤ Q,
where f_N(q) = μ(q) c_q(N)/φ(q)³ is `LeanLab.PNTPort.Vinogradov.fS N q`.
The proof gives the bound e⁸/√Q + |A_Q - K| + K/(Q - 1), with A_Q the partial Euler product
of K over primes up to Q; the hypothesis log N ≤ Q is not needed and is carried only to match
the stated form. No cited input. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013. Binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.VanDerCorput1939

open Real Finset Filter Topology
open LeanLab.PNTPort.Vinogradov

attribute [local instance] Classical.propDecidable

/-- The local factor of `P(N)`. -/
def cP (N p : ℕ) : ℝ := if p ∣ N then 1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3) else 1

/-- The partial Euler product of `K`. -/
def AK (Q : ℕ) : ℝ := ∏ p ∈ Nat.primesLE Q, (1 + 1 / ((p : ℝ) - 1) ^ 3)

/-- The partial product of `P(N)` over primes up to `Q`. -/
def BP (N Q : ℕ) : ℝ := ∏ p ∈ Nat.primesLE Q, cP N p

/-- Step 1: the truncated sum is the Euler product up to an error `e⁸/√Q`, for every `n`. -/
theorem abs_sum_fS_sub_euler (n : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    |∑ q ∈ Icc 1 Q, fS n q - ∏ p ∈ Nat.primesLE Q, (1 + fS n p)| ≤
      Real.exp 8 / Real.sqrt Q := by
  have hPr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hsP : 0 < Real.sqrt Q := Real.sqrt_pos.2 hPr
  rw [sum_Icc_eq_divisors]
  have hsplit : ∑ d ∈ (primorial Q).divisors.filter (fun d => d ≤ Q), fS n d +
      ∑ d ∈ (primorial Q).divisors.filter (fun d => ¬ d ≤ Q), fS n d =
      ∏ p ∈ Nat.primesLE Q, (1 + fS n p) := by
    rw [sum_filter_add_sum_filter_not, sum_divisors_primorial]
  have htail : |∑ d ∈ (primorial Q).divisors.filter (fun d => ¬ d ≤ Q), fS n d| ≤
      Real.exp 8 / Real.sqrt Q := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ (primorial Q).divisors.filter (fun d => ¬ d ≤ Q), |fS n d|
        ≤ ∑ d ∈ (primorial Q).divisors.filter (fun d => ¬ d ≤ Q), hS n d / Real.sqrt Q := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_filter] at hd
          rw [hS_apply, le_div_iff₀ hsP]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Real.sqrt_le_sqrt (by exact_mod_cast (not_le.1 hd.2).le)
      _ ≤ ∑ d ∈ (primorial Q).divisors, hS n d / Real.sqrt Q := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro d _ _; rw [hS_apply]; positivity
      _ = (∏ p ∈ Nat.primesLE Q, (1 + hS n p)) / Real.sqrt Q := by
          rw [← sum_div, sum_divisors_hS]
      _ ≤ Real.exp 8 / Real.sqrt Q := by
          apply div_le_div_of_nonneg_right (euler_hS_le n Q) hsP.le
  rw [← hsplit]
  rw [show ∀ a b : ℝ, a - (a + b) = -b by intros; ring, abs_neg]
  exact htail

/-- Step 2: the Euler factor `1 + f_N(p)` splits as the factor of `K` times that of `P(N)`. -/
theorem one_add_fS_prime_eq (N : ℕ) {p : ℕ} (hp : p.Prime) :
    1 + fS N p = (1 + 1 / ((p : ℝ) - 1) ^ 3) * cP N p := by
  rw [fS_prime hp, cP]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  split_ifs with h
  · rw [euler_factor_prime hp]
    field_simp
    ring
  · field_simp

/-- Step 3. -/
theorem euler_eq_AK_mul_BP (N Q : ℕ) :
    ∏ p ∈ Nat.primesLE Q, (1 + fS N p) = AK Q * BP N Q := by
  rw [AK, BP, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  exact one_add_fS_prime_eq N (Nat.mem_primesLE.1 hp).2

/-- Step 4: `A_Q → K`. -/
theorem tendsto_AK : Tendsto AK atTop (𝓝 K) := by
  have hK := K_multipliable.hasProd
  set F : ℕ → Finset {p : ℕ // p.Prime} := fun Q => (Nat.primesLE Q).subtype (fun p => p.Prime)
  have hF : Tendsto F atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro a b hab x hx
      simp only [F, mem_subtype, Nat.mem_primesLE] at hx ⊢
      exact ⟨hx.1.trans hab, hx.2⟩
    · intro x
      refine ⟨x, ?_⟩
      simp only [F, mem_subtype, Nat.mem_primesLE]
      exact ⟨le_rfl, x.2⟩
  have h : HasProd (fun p : {p : ℕ // p.Prime} => 1 + 1 / ((p : ℝ) - 1) ^ 3) K := hK
  have hc := h.comp hF
  refine hc.congr fun Q => ?_
  simp only [Function.comp, F, AK]
  rw [prod_subtype_eq_prod_filter (f := fun p : ℕ => 1 + 1 / ((p : ℝ) - 1) ^ 3)]
  rw [filter_true_of_mem (fun p hp => (Nat.mem_primesLE.1 hp).2)]

/-- The factor of `P(N)` at an odd prime lies in `(0, 1]`. -/
theorem cP_mem {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 0 < cP N p ∧ cP N p ≤ 1 := by
  unfold cP
  split_ifs
  · have h3 : (3 : ℝ) ≤ p := by
      have := hp.two_le; exact_mod_cast (by omega : 3 ≤ p)
    have hd : 1 < (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
    have h1 : 1 / ((p : ℝ) ^ 2 - 3 * p + 3) < 1 := by rw [div_lt_one (by linarith)]; exact hd
    have h0 : 0 < 1 / ((p : ℝ) ^ 2 - 3 * p + 3) := by apply div_pos one_pos; linarith
    constructor <;> linarith
  · exact ⟨one_pos, le_rfl⟩

/-- Weierstrass product inequality. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have hai := ha i (mem_insert_self i s)
    have ih' := ih (fun j hj => ha j (mem_insert_of_mem hj))
    have hs : 0 ≤ ∑ j ∈ s, a j := sum_nonneg fun j hj => (ha j (mem_insert_of_mem hj)).1
    nlinarith

/-- The telescoping sum `∑_{m=Q+1}^{M} (1/(m-2) - 1/(m-1)) = 1/(Q-1) - 1/(M-1)`. -/
theorem tele_sum (Q M : ℕ) (hM : Q ≤ M) :
    ∑ m ∈ Icc (Q + 1) M, (1 / ((m : ℝ) - 2) - 1 / ((m : ℝ) - 1)) =
      1 / ((Q : ℝ) - 1) - 1 / ((M : ℝ) - 1) := by
  induction M, hM using Nat.le_induction with
  | base => rw [Icc_eq_empty (by omega)]; simp
  | succ M hM ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- Each factor beyond `Q` is close to `1`: `1/(m² - 3m + 3) ≤ 1/(m-2) - 1/(m-1)`. -/
theorem inv_le_tele {m : ℝ} (hm : 3 ≤ m) :
    1 / (m ^ 2 - 3 * m + 3) ≤ 1 / (m - 2) - 1 / (m - 1) := by
  have h1 : 0 < m - 2 := by linarith
  have h2 : 0 < m - 1 := by linarith
  rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-- Step 5: `B_Q - P(N)` is at most `1/(Q-1)`, for odd `N`. -/
theorem BP_sub_P {N Q : ℕ} (hN : Odd N) (hQ : 2 ≤ Q) :
    0 ≤ BP N Q ∧ BP N Q ≤ 1 ∧ |BP N Q - P N| ≤ 1 / ((Q : ℝ) - 1) := by
  have hN0 : N ≠ 0 := by rintro rfl; exact absurd hN (by decide)
  have hodd : ∀ p ∈ N.primeFactors, p ≠ 2 := by
    intro p hp e
    rw [e] at hp
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  -- `P N = ∏_{p ∣ N} cP N p`
  have hP : P N = ∏ p ∈ N.primeFactors, cP N p := by
    unfold P
    refine prod_congr rfl fun p hp => ?_
    rw [cP, if_pos (Nat.dvd_of_mem_primeFactors hp)]
  -- `B_Q = ∏_{p ∣ N, p ≤ Q} cP N p`
  have hB : BP N Q = ∏ p ∈ N.primeFactors.filter (fun p => p ≤ Q), cP N p := by
    unfold BP
    have hsub : N.primeFactors.filter (fun p => p ≤ Q) ⊆ Nat.primesLE Q := by
      intro p hp
      rw [mem_filter] at hp
      exact Nat.mem_primesLE.2 ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
    symm
    apply prod_subset hsub
    intro p hp hpn
    rw [Nat.mem_primesLE] at hp
    rw [cP, if_neg]
    intro hd
    exact hpn (mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp.2, hd, hN0⟩, hp.1⟩)
  set S := N.primeFactors.filter (fun p => ¬ p ≤ Q) with hS
  set B := BP N Q with hBdef
  set R := ∏ p ∈ S, cP N p with hR
  have hPBR : P N = B * R := by
    rw [hP, hB, hR, hS, prod_filter_mul_prod_filter_not]
  have hmem : ∀ p ∈ N.primeFactors, 0 < cP N p ∧ cP N p ≤ 1 := fun p hp =>
    cP_mem (Nat.prime_of_mem_primeFactors hp) (hodd p hp)
  have hB0 : 0 ≤ B := by
    rw [hB]; exact prod_nonneg fun p hp => (hmem p (mem_filter.1 hp).1).1.le
  have hB1 : B ≤ 1 := by
    rw [hB]; exact prod_le_one₀ (fun p hp => (hmem p (mem_filter.1 hp).1).1.le)
      (fun p hp => (hmem p (mem_filter.1 hp).1).2)
  have hR1 : R ≤ 1 := prod_le_one₀ (fun p hp => (hmem p (mem_filter.1 hp).1).1.le)
      (fun p hp => (hmem p (mem_filter.1 hp).1).2)
  -- lower bound on `R`
  have hS3 : ∀ p ∈ S, (3 : ℝ) ≤ p ∧ (Q : ℝ) + 1 ≤ p := by
    intro p hp
    rw [hS, mem_filter] at hp
    have : Q + 1 ≤ p := by omega
    constructor
    · exact_mod_cast (by omega : 3 ≤ p)
    · exact_mod_cast this
  have hRlow : 1 - 1 / ((Q : ℝ) - 1) ≤ R := by
    have hRe : R = ∏ p ∈ S, (1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3)) := by
      rw [hR]
      refine prod_congr rfl fun p hp => ?_
      rw [cP, if_pos (Nat.dvd_of_mem_primeFactors (mem_filter.1 hp).1)]
    rw [hRe]
    refine le_trans ?_ (one_sub_sum_le_prod S _ ?_)
    · have hsum : ∑ p ∈ S, 1 / ((p : ℝ) ^ 2 - 3 * p + 3) ≤ 1 / ((Q : ℝ) - 1) := by
        calc ∑ p ∈ S, 1 / ((p : ℝ) ^ 2 - 3 * p + 3)
            ≤ ∑ p ∈ S, (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) :=
              sum_le_sum fun p hp => inv_le_tele (hS3 p hp).1
          _ ≤ ∑ m ∈ Icc (Q + 1) (max N Q), (1 / ((m : ℝ) - 2) - 1 / ((m : ℝ) - 1)) := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp
                rw [hS, mem_filter] at hp
                have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0)
                  (Nat.dvd_of_mem_primeFactors hp.1)
                rw [mem_Icc]; constructor <;> omega
              · intro m hm _
                rw [mem_Icc] at hm
                have : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
                have h1 : 0 < (m : ℝ) - 2 := by linarith
                rw [sub_nonneg]
                apply one_div_le_one_div_of_le h1; linarith
          _ = 1 / ((Q : ℝ) - 1) - 1 / (((max N Q : ℕ) : ℝ) - 1) :=
              tele_sum Q _ (le_max_right _ _)
          _ ≤ 1 / ((Q : ℝ) - 1) := by
              have : (2 : ℝ) ≤ ((max N Q : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ max N Q)
              have : 0 ≤ 1 / (((max N Q : ℕ) : ℝ) - 1) := by
                apply div_nonneg zero_le_one; linarith
              linarith
      linarith
    · intro p hp
      have h3 := (hS3 p hp).1
      have hd : 1 < (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
      constructor
      · apply div_nonneg zero_le_one; linarith
      · rw [div_le_one (by linarith)]; linarith
  refine ⟨hB0, hB1, ?_⟩
  rw [hPBR, show B - B * R = B * (1 - R) by ring, abs_of_nonneg (mul_nonneg hB0 (by linarith))]
  have hQ1 : (0 : ℝ) < (Q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have : 0 ≤ 1 - R := by linarith
  calc B * (1 - R) ≤ 1 * (1 - R) := mul_le_mul_of_nonneg_right hB1 this
    _ ≤ 1 / ((Q : ℝ) - 1) := by linarith

/-- Step 6, the quantitative bound. -/
theorem abs_sum_fS_sub_KP_le {N Q : ℕ} (hN : Odd N) (hQ : 2 ≤ Q) :
    |∑ q ∈ Icc 1 Q, fS N q - K * P N| ≤
      Real.exp 8 / Real.sqrt Q + |AK Q - K| + K / ((Q : ℝ) - 1) := by
  have h1 := abs_sum_fS_sub_euler N (by omega : 1 ≤ Q)
  rw [euler_eq_AK_mul_BP] at h1
  obtain ⟨hB0, hB1, hBP⟩ := BP_sub_P hN hQ
  have hK : 0 < K := lt_trans (by norm_num) K_gt
  have e : ∑ q ∈ Icc 1 Q, fS N q - K * P N =
      (∑ q ∈ Icc 1 Q, fS N q - AK Q * BP N Q) + (AK Q - K) * BP N Q +
        K * (BP N Q - P N) := by ring
  rw [e]
  have h2 : |(AK Q - K) * BP N Q| ≤ |AK Q - K| := by
    rw [abs_mul, abs_of_nonneg hB0]
    calc |AK Q - K| * BP N Q ≤ |AK Q - K| * 1 := mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
      _ = |AK Q - K| := mul_one _
  have h3 : |K * (BP N Q - P N)| ≤ K / ((Q : ℝ) - 1) := by
    rw [abs_mul, abs_of_pos hK, mul_comm]
    calc |BP N Q - P N| * K ≤ 1 / ((Q : ℝ) - 1) * K := mul_le_mul_of_nonneg_right hBP hK.le
      _ = K / ((Q : ℝ) - 1) := by ring
  calc _ ≤ |∑ q ∈ Icc 1 Q, fS N q - AK Q * BP N Q| + |(AK Q - K) * BP N Q| +
        |K * (BP N Q - P N)| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- **The truncated singular series tends to `K P(N)`, uniformly over odd `N`.** -/
theorem fS_sum_tendsto_KP : ∀ ε : ℝ, 0 < ε → ∃ P₀ : ℕ, ∀ Q N : ℕ, P₀ ≤ Q → Odd N →
    Real.log N ≤ Q →
    |∑ q ∈ Finset.Icc 1 Q, LeanLab.PNTPort.Vinogradov.fS N q - K * P N| ≤ ε := by
  intro ε hε
  have hK : 0 < K := lt_trans (by norm_num) K_gt
  have t1 : Tendsto (fun Q : ℕ => Real.exp 8 / Real.sqrt Q) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have t2 : Tendsto (fun Q : ℕ => |AK Q - K|) atTop (𝓝 0) := by
    have := (tendsto_AK.sub_const K).abs
    simpa using this
  have t3 : Tendsto (fun Q : ℕ => K / ((Q : ℝ) - 1)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop
  have e1 := (tendsto_order.1 t1).2 (ε / 3) (by positivity)
  have e2 := (tendsto_order.1 t2).2 (ε / 3) (by positivity)
  have e3 := (tendsto_order.1 t3).2 (ε / 3) (by positivity)
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 ((e1.and e2).and (e3.and (eventually_ge_atTop 2)))
  refine ⟨Q₀, fun Q N hQ hN _ => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hQ₀ Q hQ
  have := abs_sum_fS_sub_KP_le hN h4
  linarith

end LeanLab.VanDerCorput1939

