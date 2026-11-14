module

public import LeanLab.VanDerCorput1939.Vinogradov1Proof
public import LeanLab.PNTPort.Vinogradov.TernaryLower

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5705, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III, Theorem D, (3.61) and (3.62)

Read from `papers/P0004.pdf`, Acta Math. 44, p. 31, page image, and p. 6 for `N_r(n)`:
"the number of representations of n by a sum of r primes, attention being paid to order, and
repetitions of the same prime being allowed". Theorem D: every large odd `n` is the sum of three
odd primes, and the number `N̄₃(n)` of representations by three odd primes satisfies

  `N̄₃(n) ∼ C₃ n²/(log n)³ ∏_{p ∣ n} (p - 1)(p - 2)/(p² - 3p + 3)`,  `C₃ = ∏_{ϖ ≥ 3} (1 + 1/(ϖ - 1)³)`.

Hardy and Littlewood prove it on their Hypothesis R, a form of GRH. Here it is PROVED with no
hypothesis, from `VanDerCorput1939.vinogradov1`, the lab's own unconditional circle method; the
two statements differ by `K = 2 C₃`, the factor at `p = 2`, and by the at most 3 ordered triples
that use the prime 2. Not a formalization of Hardy and Littlewood's argument. Ternary Goldbach is
Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter
open LeanLab.VanDerCorput1939 (I K P Vinogradov1 vinogradov1 r3_le_I K_multipliable
  summable_inv_sub_one_cube P_pos one_le_K)

attribute [local instance] Classical.propDecidable

/-- `N̄₃(n)`: ordered triples of odd primes with sum `n`, repetitions allowed. -/
noncomputable def N3bar (n : ℕ) : ℕ :=
  #{t ∈ (range (n + 1)) ×ˢ (range (n + 1)) | (t.1.Prime ∧ t.2.Prime ∧ n - t.1 - t.2 ≠ 0 ∧
    (n - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ n) ∧ (Odd t.1 ∧ Odd t.2 ∧ Odd (n - t.1 - t.2))}

/-- (3.62) `C₃ = ∏_{ϖ ≥ 3 prime} (1 + 1/(ϖ - 1)³)`, the factor at `2` replaced by `1`. -/
noncomputable def C3 : ℝ :=
  ∏' p : {p : ℕ // p.Prime}, if p = ⟨2, Nat.prime_two⟩ then 1 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- The product in (3.61), over the prime divisors of `n`. -/
noncomputable def Pi3 (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) ^ 2 - 3 * p + 3)

/-- Theorem D, (3.61), in the `ε` form of `∼`. -/
def theoremD_stmt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Odd n → n₀ ≤ n →
    |(N3bar n : ℝ) - C3 * (n : ℝ) ^ 2 / Real.log n ^ 3 * Pi3 n| ≤
      ε * (C3 * (n : ℝ) ^ 2 / Real.log n ^ 3 * Pi3 n)

/-- The factor at `2`: `K = 2 C₃`. -/
theorem K_eq_two_mul_C3 : K = 2 * C3 := by
  set f : {p : ℕ // p.Prime} → ℝ := fun p => 1 + 1 / ((p : ℝ) - 1) ^ 3 with hf
  set b : {p : ℕ // p.Prime} := ⟨2, Nat.prime_two⟩
  have hsum : Summable (Function.update
      (fun p : {p : ℕ // p.Prime} => 1 / ((p : ℝ) - 1) ^ 3) b 0) :=
    (summable_inv_sub_one_cube.subtype (fun p : ℕ => p.Prime)).update b 0
  have hmul : Multipliable (Function.update f b 1) := by
    have := Real.multipliable_one_add_of_summable hsum
    refine this.congr fun p => ?_
    by_cases h : p = b
    · subst h; simp
    · simp [Function.update_of_ne h, hf]
  have := Multipliable.tprod_eq_mul_tprod_ite' b hmul
  unfold K C3
  rw [this]
  have hb : f b = 2 := by simp [hf, b]; norm_num
  rw [hb]

/-- `P(n) = ∏_{p ∣ n} (p - 1)(p - 2)/(p² - 3p + 3)`, factor by factor. -/
theorem P_eq_Pi3 (n : ℕ) : P n = Pi3 n := by
  unfold P Pi3
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hd : (p : ℝ) ^ 2 - 3 * p + 3 ≠ 0 := by nlinarith
  rw [one_sub_div hd]
  congr 1
  ring

/-- At most 3 ordered prime triples with sum odd `n` use the prime `2`. -/
theorem I_sub_N3bar_le (n : ℕ) (hn : Odd n) : (I n : ℝ) ≤ N3bar n + 3 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := {t ∈ (range (n + 1)) ×ˢ (range (n + 1)) | t.1.Prime ∧ t.2.Prime ∧ n - t.1 - t.2 ≠ 0 ∧
      (n - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ n})
    (fun t : ℕ × ℕ => Odd t.1 ∧ Odd t.2 ∧ Odd (n - t.1 - t.2))
  have hN : N3bar n = #({t ∈ (range (n + 1)) ×ˢ (range (n + 1)) | t.1.Prime ∧ t.2.Prime ∧
      n - t.1 - t.2 ≠ 0 ∧ (n - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ n}.filter
      (fun t : ℕ × ℕ => Odd t.1 ∧ Odd t.2 ∧ Odd (n - t.1 - t.2))) := by
    unfold N3bar; rw [Finset.filter_filter]
  have hbad : #({t ∈ (range (n + 1)) ×ˢ (range (n + 1)) | t.1.Prime ∧ t.2.Prime ∧
      n - t.1 - t.2 ≠ 0 ∧ (n - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ n}.filter
      (fun t : ℕ × ℕ => ¬ (Odd t.1 ∧ Odd t.2 ∧ Odd (n - t.1 - t.2)))) ≤ 3 := by
    refine (Finset.card_le_card (t := {(2, 2), (2, n - 4), (n - 4, 2)}) ?_).trans
      (Finset.card_le_three)
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
    obtain ⟨⟨_, hp1, hp2, hne, hp3, hle⟩, hnot⟩ := ht
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    have o1 := hp1.eq_two_or_odd'
    have o2 := hp2.eq_two_or_odd'
    have o3 := hp3.eq_two_or_odd'
    obtain ⟨k, hk⟩ := hn
    rcases o1 with h1 | h1 <;> rcases o2 with h2 | h2 <;> rcases o3 with h3 | h3
    · omega
    · left; exact ⟨h1, h2⟩
    · right; left; omega
    · exfalso; obtain ⟨a, ha⟩ := h2; obtain ⟨c, hc⟩ := h3; omega
    · right; right; omega
    · exfalso; obtain ⟨a, ha⟩ := h1; obtain ⟨c, hc⟩ := h3; omega
    · exfalso; obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2; omega
    · exact absurd ⟨h1, h2, h3⟩ hnot
  have hI : I n = #{t ∈ (range (n + 1)) ×ˢ (range (n + 1)) | t.1.Prime ∧ t.2.Prime ∧
      n - t.1 - t.2 ≠ 0 ∧ (n - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ n} := rfl
  have : I n ≤ N3bar n + 3 := by omega
  exact_mod_cast this

theorem N3bar_le_I (n : ℕ) : N3bar n ≤ I n := by
  unfold N3bar I
  rw [← Finset.filter_filter]
  exact Finset.card_filter_le _ _

/-- **Hardy-Littlewood 1923, Theorem D, (3.61)**, PROVED with no hypothesis. -/
theorem theoremD : theoremD_stmt := by
  intro ε hε
  have hmain : ∀ n : ℕ, C3 * (n : ℝ) ^ 2 / Real.log n ^ 3 * Pi3 n =
      (n : ℝ) ^ 2 * K * P n / (2 * Real.log n ^ 3) := by
    intro n; rw [K_eq_two_mul_C3, P_eq_Pi3]; ring
  obtain ⟨n₁, h1⟩ := vinogradov1 (ε / 2) (by positivity)
  obtain ⟨n₂, h2⟩ := vinogradov1 (1 / 2) (by norm_num)
  obtain ⟨N₀, hlow⟩ := LeanLab.PNTPort.Vinogradov.r3_lower
  obtain ⟨n₃, hup⟩ := r3_le_I (1 / 80) (by norm_num)
  -- n²/log³ n → ∞
  have hgrow : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / Real.log n ^ 3) atTop atTop := by
    have hb := (isLittleO_pow_log_id_atTop (n := 3)).bound (show (0 : ℝ) < 1 by norm_num)
    have hb' : ∀ᶠ n : ℕ in atTop, ‖Real.log (n : ℝ) ^ 3‖ ≤ 1 * ‖((n : ℝ))‖ :=
      tendsto_natCast_atTop_atTop.eventually hb
    refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    filter_upwards [hb', eventually_ge_atTop 3] with n hn h3
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hL : 0 < Real.log n := Real.log_pos hn1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hL 3),
      abs_of_pos (by linarith), one_mul] at hn
    rw [le_div_iff₀ (pow_pos hL 3)]
    nlinarith
  have hev : ∀ᶠ n : ℕ in atTop, 120 * (6 / ε) ≤ (n : ℝ) ^ 2 / Real.log n ^ 3 ∧ N₀ ≤ (n : ℝ) ∧
      n₁ ≤ n ∧ n₂ ≤ n ∧ n₃ ≤ n ∧ 3 ≤ n :=
    (hgrow.eventually_ge_atTop _).and ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((eventually_ge_atTop n₁).and ((eventually_ge_atTop n₂).and ((eventually_ge_atTop n₃).and
        (eventually_ge_atTop 3)))))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀, fun n hn hn0 => ?_⟩
  obtain ⟨hg, hN0, hn1, hn2, hn3, hn3'⟩ := hn₀ n hn0
  rw [hmain]
  set M := (n : ℝ) ^ 2 * K * P n / (2 * Real.log n ^ 3) with hM
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hL3 : 0 < Real.log n ^ 3 := by positivity
  -- I ≥ n²/(80 log³ n)
  have hr3 := hlow n hN0 hn
  have hu := hup n hn3
  have hIlow : (n : ℝ) ^ 2 / Real.log n ^ 3 / 80 ≤ I n := by
    have : (n : ℝ) ^ 2 / 80 ≤ (I n : ℝ) * Real.log n ^ 3 := by nlinarith
    rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
  -- M ≥ 2 I / 3
  have hM2 := h2 n hn hn2
  have hMI : (2 / 3) * (I n : ℝ) ≤ M := by
    have := (abs_le.mp hM2).2; linarith
  have hMbig : 6 / ε ≤ M := by nlinarith
  have hε1 := h1 n hn hn1
  have hA := I_sub_N3bar_le n hn
  have hB : (N3bar n : ℝ) ≤ I n := by exact_mod_cast N3bar_le_I n
  have h3 : 3 ≤ ε / 2 * M := by
    have := mul_le_mul_of_nonneg_left hMbig (by positivity : (0 : ℝ) ≤ ε / 2)
    rw [show ε / 2 * (6 / ε) = 3 by field_simp; ring] at this
    linarith
  rw [abs_le] at hε1 ⊢
  constructor <;> nlinarith [hε1.1, hε1.2]

/-- Theorem D, first sentence: every large odd number is the sum of three odd primes. -/
theorem theoremD_ternary : ∃ n₀ : ℕ, ∀ n, Odd n → n₀ ≤ n → 0 < N3bar n := by
  obtain ⟨n₀, h⟩ := theoremD (1 / 2) (by norm_num)
  refine ⟨max n₀ 3, fun n hn hn0 => ?_⟩
  have hb := h n hn (le_of_max_le_left hn0)
  have hC : 0 < C3 := by have := one_le_K; rw [K_eq_two_mul_C3] at this; linarith
  have hP : 0 < Pi3 n := by rw [← P_eq_Pi3]; exact P_pos hn
  have hL : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmain : 0 < C3 * (n : ℝ) ^ 2 / Real.log n ^ 3 * Pi3 n := by positivity
  have := (abs_le.mp hb).1
  have : (0 : ℝ) < N3bar n := by linarith
  exact_mod_cast this

end LeanLab.HardyLittlewood1923

