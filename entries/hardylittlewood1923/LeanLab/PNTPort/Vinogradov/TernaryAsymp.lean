module

public import LeanLab.PNTPort.Vinogradov.TernaryUncond
public import LeanLab.PNTPort.BV.Helpers

/-!
# Vinogradov's asymptotic for `r₃(n)`

Lab proof, unit U-5255. AI wrote this file. Known mathematics, no cited input.

`err_arith`: the explicit error of `ternary_uncond` is at most `C N² / L^A` once the growth
facts `h1` to `h7` hold, `L = log N`, `p = P`, `Q + 1 ≥ N/p³`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real

/-- Pure arithmetic: the three error terms against `N²/L^A`. -/
lemma err_arith {N L p Q M K Ex A Λ2 K1 K2 K3 K4 K5 : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hp : 1 ≤ p) (hQ0 : 0 ≤ Q) (hQ1 : N / p ^ 3 ≤ Q + 1)
    (hQ2 : Q ≤ N / p ^ 3) (hM : N ≤ M) (hK : 0 ≤ K) (hEx : 0 ≤ Ex) (hLA : 0 < L ^ A)
    (hΛ : Λ2 ≤ 6 * N * L) (hΛ0 : 0 ≤ Λ2) (hlp : 0 ≤ Real.log p / Real.log 2)
    (hlp2 : Real.log p / Real.log 2 ≤ 2 * p)
    (h1 : L ^ 5 / Real.sqrt p ≤ 2 / L ^ A)
    (h2 : L ^ 5 * N ^ ((4 : ℝ) / 5) ≤ K1 * N / L ^ A)
    (h3 : p ^ 8 * Real.sqrt N ≤ K2 * N / L ^ A)
    (h4 : p ^ 9 * Ex ≤ K3 / L ^ A)
    (h5 : p ^ 9 * L ≤ K4 * N / L ^ A)
    (h6 : 1 / p ≤ 2 / L ^ A)
    (h7 : p ^ 2 ≤ K5 * N / L ^ A) :
    300 * (N / Real.sqrt p + N ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) * (1 + L) ^ 4 * Λ2
      + p ^ 2 * (2 / (Q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * N) ^ 2 *
        ((7 * Real.sqrt N + p * K * N * Ex + Real.log p / Real.log 2 * L) *
          (1 + 2 * π * N / (Q + 1))))
      + N * p ^ 2 * (Q + 1) / 2
    ≤ (28800 * (4 + K1) + 2592 * (7 * K2 + K * K3 + 2 * K4) + 1 + K5 / 2) * N ^ 2 / L ^ A := by
  have hN0 : 0 < N := by linarith
  have hp0 : 0 < p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hQ1pos : 0 < Q + 1 := by linarith
  have hp3 : 0 < p ^ 3 := by positivity
  have hLA' : 0 < 1 / L ^ A := by positivity
  -- term 1
  have hNQ : Real.sqrt (N * Q) ≤ N / Real.sqrt p := by
    have hq' : N * Q ≤ N * (N / p ^ 3) := mul_le_mul_of_nonneg_left hQ2 hN0.le
    have hpp : N * (N / p ^ 3) ≤ (N / Real.sqrt p) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hp0.le]
      have h3 : p ≤ p ^ 3 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ 3 := pow_le_pow_right₀ hp (by norm_num)
      have : N / p ^ 3 ≤ N / p := div_le_div_of_nonneg_left hN0.le hp0 h3
      calc N * (N / p ^ 3) ≤ N * (N / p) := mul_le_mul_of_nonneg_left this hN0.le
        _ = N ^ 2 / p := by ring
    have := Real.sqrt_le_sqrt (hq'.trans hpp)
    rwa [Real.sqrt_sq (by positivity)] at this
  have h1L : (1 + L) ^ 4 ≤ 16 * L ^ 4 := by
    have : 1 + L ≤ 2 * L := by linarith
    calc (1 + L) ^ 4 ≤ (2 * L) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
      _ = 16 * L ^ 4 := by ring
  have hT1 : 300 * (N / Real.sqrt p + N ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) * (1 + L) ^ 4 * Λ2
      ≤ 28800 * (4 + K1) * N ^ 2 / L ^ A := by
    have hN45 : 0 ≤ N ^ ((4 : ℝ) / 5) := by positivity
    calc 300 * (N / Real.sqrt p + N ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) * (1 + L) ^ 4 * Λ2
        ≤ 300 * (2 * (N / Real.sqrt p) + N ^ ((4 : ℝ) / 5)) * (16 * L ^ 4) * (6 * N * L) := by
          have ha : N / Real.sqrt p + N ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q) ≤
              2 * (N / Real.sqrt p) + N ^ ((4 : ℝ) / 5) := by linarith
          have hb : 0 ≤ N / Real.sqrt p + N ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q) := by positivity
          exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) h1L
            (by positivity) (by positivity)) hΛ hΛ0 (by positivity)
      _ = 28800 * (2 * N ^ 2 * (L ^ 5 / Real.sqrt p) + N * (L ^ 5 * N ^ ((4 : ℝ) / 5))) := by
          ring
      _ ≤ 28800 * (2 * N ^ 2 * (2 / L ^ A) + N * (K1 * N / L ^ A)) := by
          gcongr
      _ = 28800 * (4 + K1) * N ^ 2 / L ^ A := by ring
  -- term 2
  have hiQ : 1 / (Q + 1) ≤ p ^ 3 / N := by
    rw [div_le_div_iff₀ hQ1pos hN0, one_mul]
    rw [div_le_iff₀ hp3] at hQ1; linarith
  have hiM : 1 / M ≤ 1 / N := one_div_le_one_div_of_le hN0 hM
  have hp3N : 1 / N ≤ p ^ 3 / N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    exact one_le_pow₀ hp
  have hfac1 : 2 / (Q + 1) + 1 / M ≤ 3 * p ^ 3 / N := by
    have : 2 / (Q + 1) = 2 * (1 / (Q + 1)) := by ring
    rw [this]
    have : 3 * p ^ 3 / N = 2 * (p ^ 3 / N) + p ^ 3 / N := by ring
    rw [this]; linarith
  have hfac2 : 1 + 2 * π * N / (Q + 1) ≤ 8 * p ^ 3 := by
    have h1 : N / (Q + 1) ≤ p ^ 3 := by
      rw [div_le_iff₀ hQ1pos]; rw [div_le_iff₀ hp3] at hQ1; linarith
    have hπ : π < 3.15 := Real.pi_lt_d2
    have h3p : 1 ≤ p ^ 3 := one_le_pow₀ hp
    have : 2 * π * N / (Q + 1) = 2 * π * (N / (Q + 1)) := by ring
    rw [this]
    nlinarith [Real.pi_pos]
  have hR : (Real.log 4 + 4) * N ≤ 6 * N := by
    have := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    nlinarith
  have hR0 : 0 ≤ (Real.log 4 + 4) * N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
  have hE0 : 0 ≤ 7 * Real.sqrt N + p * K * N * Ex + Real.log p / Real.log 2 * L := by positivity
  have hT2 : p ^ 2 * (2 / (Q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * N) ^ 2 *
        ((7 * Real.sqrt N + p * K * N * Ex + Real.log p / Real.log 2 * L) *
          (1 + 2 * π * N / (Q + 1)))) ≤ 2592 * (7 * K2 + K * K3 + 2 * K4) * N ^ 2 / L ^ A := by
    have hb1 : 0 ≤ 2 / (Q + 1) + 1 / M := by
      have : 0 < M := by linarith
      positivity
    calc p ^ 2 * (2 / (Q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * N) ^ 2 *
          ((7 * Real.sqrt N + p * K * N * Ex + Real.log p / Real.log 2 * L) *
            (1 + 2 * π * N / (Q + 1))))
        ≤ p ^ 2 * (3 * p ^ 3 / N) * (3 * (6 * N) ^ 2 *
          ((7 * Real.sqrt N + p * K * N * Ex + 2 * p * L) * (8 * p ^ 3))) := by
          gcongr
      _ = 2592 * N * (7 * (p ^ 8 * Real.sqrt N) + K * N * (p ^ 9 * Ex) + 2 * (p ^ 9 * L)) := by
          field_simp; ring
      _ ≤ 2592 * N * (7 * (K2 * N / L ^ A) + K * N * (K3 / L ^ A) + 2 * (K4 * N / L ^ A)) := by
          gcongr
      _ = 2592 * (7 * K2 + K * K3 + 2 * K4) * N ^ 2 / L ^ A := by ring
  -- term 3
  have hT3 : N * p ^ 2 * (Q + 1) / 2 ≤ (1 + K5 / 2) * N ^ 2 / L ^ A := by
    have hQ' : Q + 1 ≤ N / p ^ 3 + 1 := by linarith
    calc N * p ^ 2 * (Q + 1) / 2 ≤ N * p ^ 2 * (N / p ^ 3 + 1) / 2 := by gcongr
      _ = N ^ 2 * (1 / p) / 2 + N * p ^ 2 / 2 := by field_simp
      _ ≤ N ^ 2 * (2 / L ^ A) / 2 + N * (K5 * N / L ^ A) / 2 := by gcongr
      _ = (1 + K5 / 2) * N ^ 2 / L ^ A := by ring
  have : (28800 * (4 + K1) + 2592 * (7 * K2 + K * K3 + 2 * K4) + 1 + K5 / 2) * N ^ 2 / L ^ A =
      28800 * (4 + K1) * N ^ 2 / L ^ A + 2592 * (7 * K2 + K * K3 + 2 * K4) * N ^ 2 / L ^ A +
        (1 + K5 / 2) * N ^ 2 / L ^ A := by ring
  rw [this]
  linarith

lemma sum_vonMangoldt_sq_le (N : ℕ) :
    ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2 ≤ 6 * N * Real.log N := by
  have hψ := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at hψ
  have hI : Ioc 0 N = Icc 1 N := by ext m; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI] at hψ
  have hlN := Real.log_natCast_nonneg N
  have h4 : Real.log 4 + 4 ≤ 6 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  calc ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2
      ≤ ∑ m ∈ Icc 1 N, Real.log N * ArithmeticFunction.vonMangoldt m := by
        refine sum_le_sum fun m hm => ?_
        rw [mem_Icc] at hm
        have h1 : ArithmeticFunction.vonMangoldt m ≤ Real.log N :=
          ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast hm.1) (by exact_mod_cast hm.2))
        rw [sq]
        exact mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log N * ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m := by rw [mul_sum]
    _ ≤ Real.log N * ((Real.log 4 + 4) * N) := mul_le_mul_of_nonneg_left hψ hlN
    _ ≤ Real.log N * (6 * N) := by gcongr
    _ = 6 * N * Real.log N := by ring

lemma lp_bound {p : ℝ} (hp1 : 1 ≤ p) : Real.log p / Real.log 2 ≤ 2 * p := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < p by linarith)
  have h2 := Real.log_two_gt_d9
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma rpow_mul_rpow {L : ℝ} (hL : 0 < L) (x y : ℝ) : L ^ x * L ^ y = L ^ (x + y) :=
  (Real.rpow_add hL x y).symm

lemma g_h1 {L p A B : ℝ} (hL1 : 1 ≤ L) (hB : B = 2 * A + 12) (hpL : L ^ B / 2 ≤ p) :
    L ^ 5 / Real.sqrt p ≤ 2 / L ^ A := by
  have hL0 : 0 < L := by linarith
  have hLB : 0 < L ^ B := Real.rpow_pos_of_pos hL0 B
  have hp0 : 0 < p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  rw [div_le_div_iff₀ hsp hLA]
  have e5 : L ^ 5 * L ^ A = L ^ (A + 5) := by
    rw [show L ^ 5 = L ^ ((5 : ℕ) : ℝ) by rw [Real.rpow_natCast], rpow_mul_rpow hL0]; ring_nf
  rw [e5]
  have hsq : (L ^ (A + 5)) ^ 2 ≤ (2 * Real.sqrt p) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp0.le, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    have : L ^ ((A + 5) * ((2 : ℕ) : ℝ)) ≤ L ^ B := by
      apply Real.rpow_le_rpow_of_exponent_le hL1; push_cast; rw [hB]; linarith
    linarith
  have hx : 0 ≤ L ^ (A + 5) := by positivity
  have hy : 0 ≤ 2 * Real.sqrt p := by positivity
  nlinarith

lemma g_h2 {L N A K1 : ℝ} (hL0 : 0 < L) (hN : 1 ≤ N)
    (g : L ^ (A + 5) ≤ K1 * N ^ ((1 : ℝ) / 5)) :
    L ^ 5 * N ^ ((4 : ℝ) / 5) ≤ K1 * N / L ^ A := by
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  rw [le_div_iff₀ hLA]
  have e1 : L ^ 5 * N ^ ((4 : ℝ) / 5) * L ^ A = L ^ (A + 5) * N ^ ((4 : ℝ) / 5) := by
    rw [show L ^ 5 = L ^ ((5 : ℕ) : ℝ) by rw [Real.rpow_natCast], mul_right_comm,
      rpow_mul_rpow hL0]
    ring_nf
  rw [e1]
  have hN45 : 0 ≤ N ^ ((4 : ℝ) / 5) := by positivity
  calc L ^ (A + 5) * N ^ ((4 : ℝ) / 5) ≤ K1 * N ^ ((1 : ℝ) / 5) * N ^ ((4 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right g hN45
    _ = K1 * N := by rw [mul_assoc, ← Real.rpow_add (by linarith)]; norm_num

lemma g_h3 {L N p A B K2 : ℝ} (hL0 : 0 < L) (hN : 0 ≤ N) (hp : p ^ 8 ≤ L ^ (8 * B))
    (g : L ^ (8 * B + A) ≤ K2 * Real.sqrt N) : p ^ 8 * Real.sqrt N ≤ K2 * N / L ^ A := by
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  rw [le_div_iff₀ hLA]
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
  have hs0 := Real.sqrt_nonneg N
  calc p ^ 8 * Real.sqrt N * L ^ A ≤ L ^ (8 * B) * Real.sqrt N * L ^ A := by gcongr
    _ = L ^ (8 * B + A) * Real.sqrt N := by rw [mul_right_comm, rpow_mul_rpow hL0]
    _ ≤ K2 * Real.sqrt N * Real.sqrt N := by gcongr
    _ = K2 * N := by rw [mul_assoc, hsN]

lemma g_h4 {L p A B K3 Ex : ℝ} (hL0 : 0 < L) (hp : p ^ 9 ≤ L ^ (9 * B)) (hEx : 0 ≤ Ex)
    (g : Ex ≤ K3 / L ^ (9 * B + A)) : p ^ 9 * Ex ≤ K3 / L ^ A := by
  have hLp : 0 < L ^ (9 * B) := Real.rpow_pos_of_pos hL0 _
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  calc p ^ 9 * Ex ≤ L ^ (9 * B) * (K3 / L ^ (9 * B + A)) :=
        mul_le_mul hp g hEx hLp.le
    _ = K3 / L ^ A := by rw [← rpow_mul_rpow hL0]; field_simp

lemma g_h5 {L N p A B K4 : ℝ} (hL0 : 0 < L) (hp : p ^ 9 ≤ L ^ (9 * B))
    (g : L ^ (9 * B + A + 1) ≤ K4 * N) : p ^ 9 * L ≤ K4 * N / L ^ A := by
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  rw [le_div_iff₀ hLA]
  calc p ^ 9 * L * L ^ A ≤ L ^ (9 * B) * L * L ^ A := by gcongr
    _ = L ^ (9 * B + A + 1) := by
        rw [← rpow_mul_rpow hL0, ← rpow_mul_rpow hL0, Real.rpow_one]; ring
    _ ≤ K4 * N := g

lemma g_h6 {L p A B : ℝ} (hL1 : 1 ≤ L) (hAB : A ≤ B) (hpL : L ^ B / 2 ≤ p) (hp0 : 0 < p) :
    1 / p ≤ 2 / L ^ A := by
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos (by linarith) A
  rw [div_le_div_iff₀ hp0 hLA]
  have : L ^ A ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 hAB
  linarith

lemma g_h7 {L N p A B K5 : ℝ} (hL0 : 0 < L) (hp : p ^ 2 ≤ L ^ (2 * B))
    (g : L ^ (2 * B + A) ≤ K5 * N) : p ^ 2 ≤ K5 * N / L ^ A := by
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  rw [le_div_iff₀ hLA]
  calc p ^ 2 * L ^ A ≤ L ^ (2 * B) * L ^ A := by gcongr
    _ = L ^ (2 * B + A) := rpow_mul_rpow hL0 _ _
    _ ≤ K5 * N := g

lemma g_p5 {L N p B K6 : ℝ} (hN : 0 ≤ N) (hp : p ^ 5 ≤ L ^ (5 * B))
    (g : L ^ (5 * B) ≤ K6 * Real.sqrt N) (hK6 : 0 ≤ K6) (hNK : 4 * K6 ^ 2 + 1 ≤ N) :
    2 * p ^ 5 ≤ N := by
  have hs : 2 * K6 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by positivity) hN]; nlinarith
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
  have hs0 := Real.sqrt_nonneg N
  nlinarith

lemma Q_facts {N p : ℝ} (hp1 : 1 ≤ p) (hp5 : 2 * p ^ 5 ≤ N) :
    1 ≤ ⌊N / p ^ 3⌋₊ ∧ ((⌊N / p ^ 3⌋₊ : ℕ) : ℝ) ≤ N ∧
      2 / (((⌊N / p ^ 3⌋₊ : ℕ) : ℝ) + 1) < 1 / p ^ 2 ∧
      N / p ^ 3 ≤ ((⌊N / p ^ 3⌋₊ : ℕ) : ℝ) + 1 ∧ ((⌊N / p ^ 3⌋₊ : ℕ) : ℝ) ≤ N / p ^ 3 := by
  have hp3 : 0 < p ^ 3 := by positivity
  have hp35 : p ^ 3 ≤ p ^ 5 := pow_le_pow_right₀ hp1 (by norm_num)
  have h5 : 0 < p ^ 5 := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hQ2 : ((⌊N / p ^ 3⌋₊ : ℕ) : ℝ) ≤ N / p ^ 3 := Nat.floor_le (by positivity)
  have hQ1 := Nat.lt_floor_add_one (N / p ^ 3)
  refine ⟨Nat.one_le_floor_iff _ |>.2 (by rw [le_div_iff₀ hp3]; linarith), ?_, ?_, hQ1.le, hQ2⟩
  · exact hQ2.trans (div_le_self hN0 (one_le_pow₀ hp1))
  · have h2 : 2 * p ^ 2 ≤ N / p ^ 3 := by
      rw [le_div_iff₀ hp3]
      have : 2 * p ^ 2 * p ^ 3 = 2 * p ^ 5 := by ring
      linarith
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- **Vinogradov's three primes theorem, asymptotic form**, unconditional and ineffective:
for every `A > 0` there are `C`, `N₀` with, for `N ≥ N₀`, `n ≤ 3N` and `P = ⌊(log N)^{2A+12}⌋`,
`|r₃(n) - J(n) 𝔖_P(n)| ≤ C N² / (log N)^A`. -/
theorem vinogradov_asymptotic (A : ℝ) (hA : 0 < A) :
    ∃ C N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, n ≤ 3 * N →
      ‖(r3 N n : ℂ) - (J N n : ℂ) * singP ⌊Real.log N ^ (2 * A + 12)⌋₊ n‖ ≤
        C * N ^ 2 / Real.log N ^ A := by
  set B := 2 * A + 12 with hB
  have hB1 : 1 ≤ B := by linarith
  obtain ⟨c, hc, K, hK, hmain⟩ := ternary_uncond B (by linarith)
  obtain ⟨K1, hK1, g1⟩ := BV.log_rpow_le_rpow (A + 5) (1 / 5) (by norm_num)
  obtain ⟨K2, hK2, g2⟩ := BV.log_rpow_le_sqrt (8 * B + A)
  obtain ⟨K3, hK3, g3⟩ := BV.exp_neg_sqrt_log_le (c / Real.sqrt 2) (by positivity) (9 * B + A)
  obtain ⟨K4, hK4, g4⟩ := BV.log_rpow_le_rpow (9 * B + A + 1) 1 one_pos
  obtain ⟨K5, hK5, g5⟩ := BV.log_rpow_le_rpow (2 * B + A) 1 one_pos
  obtain ⟨K6, hK6, g6⟩ := BV.log_rpow_le_sqrt (5 * B)
  refine ⟨28800 * (4 + K1) + 2592 * (7 * K2 + K * K3 + 2 * K4) + 1 + K5 / 2,
    max (Real.exp 4) (4 * K6 ^ 2 + 1), ?_⟩
  intro N hN n hn
  have hN4 : Real.exp 4 ≤ N := le_trans (le_max_left _ _) hN
  have hNK : 4 * K6 ^ 2 + 1 ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN4
  have hN2 : (2 : ℝ) ≤ N := by have := Real.add_one_le_exp 4; linarith
  have hL4 : 4 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 4) hN4; rwa [Real.log_exp] at this
  have hL1 : 1 ≤ Real.log N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hLB : Real.log N ≤ Real.log N ^ B := by
    calc Real.log N = Real.log N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log N ^ B := Real.rpow_le_rpow_of_exponent_le hL1 hB1
  have hLB1 : 1 ≤ Real.log N ^ B := by linarith
  have hpU : ((⌊Real.log N ^ B⌋₊ : ℕ) : ℝ) ≤ Real.log N ^ B := Nat.floor_le (by linarith)
  have hpL : Real.log N ^ B / 2 ≤ ((⌊Real.log N ^ B⌋₊ : ℕ) : ℝ) := floor_ge_half hLB1
  have hp1 : (1 : ℝ) ≤ ((⌊Real.log N ^ B⌋₊ : ℕ) : ℝ) := by linarith
  have hP1 : 1 ≤ ⌊Real.log N ^ B⌋₊ := by exact_mod_cast hp1
  have hpow : ∀ k : ℕ, ((⌊Real.log N ^ B⌋₊ : ℕ) : ℝ) ^ k ≤ Real.log N ^ ((k : ℝ) * B) := by
    intro k
    calc ((⌊Real.log N ^ B⌋₊ : ℕ) : ℝ) ^ k ≤ (Real.log N ^ B) ^ k :=
          pow_le_pow_left₀ (by linarith) hpU k
      _ = Real.log N ^ ((k : ℝ) * B) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, mul_comm]
  have hp5 := hpow 5
  have hp8 := hpow 8
  have hp9 := hpow 9
  have hp2 := hpow 2
  push_cast at hp5 hp8 hp9 hp2
  have h2p5 := g_p5 (Nat.cast_nonneg N) hp5 (g6 N hN2) hK6.le hNK
  obtain ⟨hQone, hQN, hPQ, hQ1, hQ2⟩ := Q_facts hp1 h2p5
  have : NeZero (3 * N + 1) := ⟨by omega⟩
  have hQN' : ⌊(N : ℝ) / ((⌊Real.log N ^ B⌋₊ : ℕ) : ℝ) ^ 3⌋₊ ≤ N := by exact_mod_cast hQN
  refine (hmain (N := N) (M := 3 * N + 1) (P := ⌊Real.log N ^ B⌋₊)
    (Q := ⌊(N : ℝ) / ((⌊Real.log N ^ B⌋₊ : ℕ) : ℝ) ^ 3⌋₊) (n := n) hN4 (by omega)
    (by omega) hP1 hpU hQone hQN' hPQ).trans ?_
  have hM : (N : ℝ) ≤ ((3 * N + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hex : Real.exp (-c * Real.sqrt (Real.log N / 2)) =
      Real.exp (-(c / Real.sqrt 2) * Real.sqrt (Real.log N)) := by
    congr 1
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have h4 := g_h4 (Ex := Real.exp (-c * Real.sqrt (Real.log N / 2))) (A := A) (K3 := K3) hL0 hp9
    (Real.exp_pos _).le (by rw [hex]; exact g3 N hN2)
  have g4' := g4 N hN2
  have g5' := g5 N hN2
  rw [Real.rpow_one] at g4' g5'
  exact err_arith hN1 hL1 hp1 (Nat.cast_nonneg _) hQ1 hQ2 hM hK (Real.exp_pos _).le
    (Real.rpow_pos_of_pos hL0 A) (sum_vonMangoldt_sq_le N) (sum_nonneg fun _ _ => sq_nonneg _)
    (div_nonneg (Real.log_nonneg hp1) (Real.log_nonneg (by norm_num))) (lp_bound hp1)
    (g_h1 hL1 hB hpL) (g_h2 hL0 hN1 (g1 N hN2)) (g_h3 hL0 (Nat.cast_nonneg N) hp8 (g2 N hN2))
    h4 (g_h5 hL0 hp9 g4') (g_h6 hL1 (by linarith) hpL (by linarith)) (g_h7 hL0 hp2 g5')

end LeanLab.PNTPort.Vinogradov

