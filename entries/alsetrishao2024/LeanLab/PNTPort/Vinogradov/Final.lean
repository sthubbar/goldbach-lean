module

public import LeanLab.PNTPort.Vinogradov.TypeIIBound

/-!
# Vinogradov's minor arc bound for `∑ Λ(n) e(αn)`

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input: Vinogradov
1937, in the form of Vaughan 1977, Davenport ch. 25, Vaughan's book Theorem 3.1.

* `vinogradov_uv`: for `(a, q) = 1`, `q ≥ 1`, `|α - a/q| ≤ 1/q²` and any `u, v ≥ 1`, an explicit
  bound for `S(α) = ∑_{n ≤ N} Λ(n) e(αn)` from the four Vaughan sums.
* `vinogradov_minor`: with `u = v = ⌊N^{2/5}⌋`, for `1 ≤ q ≤ N`,
  `|S(α)| ≤ 300 (N/√q + N^{4/5} + √(Nq)) (1 + log N)⁴`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real

/-- The explicit bound with free parameters `u`, `v`. -/
theorem vinogradov_uv {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N : ℕ) {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ‖S N α‖ ≤ (Real.log 4 + 4) * u
      + Real.log N * (12 * ((N : ℝ) / q + (u * v : ℕ) + q) * (1 + Real.log q + Real.log (u * v : ℕ)))
      + 2 * Real.log N * (12 * ((N : ℝ) / q + v + q) * (1 + Real.log q + Real.log v))
      + (2 * Real.log N + 1) *
        Real.sqrt (2 * (Real.log 4 + 4) * N * (1 + Real.log N) ^ 4 *
          (9 * ((N : ℝ) / v) + 8 * ((N : ℝ) / q) + 2 * ((N : ℝ) / u) * (1 + Real.log q) +
            2 * q * (1 + Real.log q))) := by
  rw [S_decomp N u v hv α]
  have h1 := norm_T1_le N u α
  have h2 := norm_T2_le hq hcop hα N u v
  have h3 := norm_T3_le hq hcop hα N v
  have h4 := norm_T4_le hq hcop hα N hu hv
  calc ‖T1 N u α - T2 N u v α + T3 N v α - T4 N u v α‖
      ≤ ‖T1 N u α‖ + ‖T2 N u v α‖ + ‖T3 N v α‖ + ‖T4 N u v α‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add_left ((norm_add_le _ _).trans ?_) _
        exact add_le_add_left (norm_sub_le _ _) _
    _ ≤ _ := by linarith

lemma floor_ge_half {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.2 hx
  rcases le_or_gt 2 x with h | h
  · linarith
  · linarith

lemma log4_bounds : 0 ≤ Real.log 4 ∧ Real.log 4 < 2 := by
  refine ⟨Real.log_nonneg (by norm_num), ?_⟩
  have := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith

/-- Arithmetic for the Type II term, in abstract reals. -/
lemma term4_arith {N q u p L lN lq X : ℝ} (hq1 : 1 ≤ q) (hp1 : 1 ≤ p) (hN : N = p ^ 5)
    (hu : p ^ 2 / 2 ≤ u) (hu1 : 1 ≤ u) (hL : L = 1 + lN) (hlN : 0 ≤ lN) (hlq0 : 0 ≤ lq)
    (hlq : lq ≤ lN) (hX : X = N / Real.sqrt q + p ^ 4 + Real.sqrt (N * q)) :
    (2 * lN + 1) * Real.sqrt (2 * (Real.log 4 + 4) * N * L ^ 4 *
      (9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq))) ≤
      40 * X * L ^ 4 := by
  obtain ⟨h40, h42⟩ := log4_bounds
  have hL1 : 1 ≤ L := by linarith
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hA : 0 ≤ N / Real.sqrt q := div_nonneg hN0 hsq.le
  have hB : 0 ≤ Real.sqrt (N * q) := Real.sqrt_nonneg _
  have hp4 : 0 ≤ p ^ 4 := by positivity
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hLq : 1 + lq ≤ L := by linarith
  have hupos : 0 < u := by linarith
  have hNu : N * (N / u) ≤ 2 * X ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hupos]
    have h1 : N * N = (p ^ 4) ^ 2 * p ^ 2 := by rw [hN]; ring
    have h2 : (p ^ 4) ^ 2 * p ^ 2 ≤ 2 * (p ^ 4) ^ 2 * u := by
      have : 0 ≤ (p ^ 4) ^ 2 := by positivity
      nlinarith
    have h3 : (p ^ 4) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hp4 (by rw [hX]; linarith) 2
    have h4 : 2 * (p ^ 4) ^ 2 * u ≤ 2 * X ^ 2 * u := by
      have := mul_le_mul_of_nonneg_right h3 hupos.le; linarith
    linarith
  have hNq : N * (N / q) ≤ X ^ 2 := by
    have : N * (N / q) = (N / Real.sqrt q) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by linarith)]; ring
    rw [this]
    exact pow_le_pow_left₀ hA (by rw [hX]; linarith) 2
  have hNq2 : N * q ≤ X ^ 2 := by
    have : N * q = (Real.sqrt (N * q)) ^ 2 := by
      rw [Real.sq_sqrt (mul_nonneg hN0 (by linarith))]
    rw [this]
    exact pow_le_pow_left₀ hB (by rw [hX]; linarith) 2
  have hNu0 : 0 ≤ N * (N / u) := mul_nonneg hN0 (div_nonneg hN0 hupos.le)
  have hlq1 : 0 ≤ 1 + lq := by linarith
  have a1 : 2 * (N * (N / u)) * (1 + lq) ≤ 2 * (2 * X ^ 2) * L :=
    mul_le_mul (by linarith) hLq hlq1 (by positivity)
  have a2 : 2 * (N * q) * (1 + lq) ≤ 2 * X ^ 2 * L :=
    mul_le_mul (by linarith) hLq hlq1 (by positivity)
  have a3 : X ^ 2 ≤ X ^ 2 * L := le_mul_of_one_le_right hX2 hL1
  have hinner : N * (9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq)) ≤
      32 * X ^ 2 * L := by
    have e1 : N * (9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq)) =
        9 * (N * (N / u)) + 8 * (N * (N / q)) + 2 * (N * (N / u)) * (1 + lq) +
          2 * (N * q) * (1 + lq) := by ring
    rw [e1]; linarith
  have hinner0 : 0 ≤ 9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq) := by
    have : 0 ≤ N / u := div_nonneg hN0 hupos.le
    have : 0 ≤ N / q := div_nonneg hN0 (by linarith)
    have : 0 ≤ q := by linarith
    positivity
  have hL4' : 0 ≤ L ^ 4 := by positivity
  have hsqrt : 2 * (Real.log 4 + 4) * N * L ^ 4 *
      (9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq)) ≤
      (20 * L ^ 3 * X) ^ 2 := by
    have e2 : 2 * (Real.log 4 + 4) * N * L ^ 4 *
        (9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq)) =
        2 * (Real.log 4 + 4) * L ^ 4 *
          (N * (9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq))) := by
      ring
    rw [e2]
    have hc0 : 2 * (Real.log 4 + 4) ≤ 12 := by linarith
    calc 2 * (Real.log 4 + 4) * L ^ 4 *
          (N * (9 * (N / u) + 8 * (N / q) + 2 * (N / u) * (1 + lq) + 2 * q * (1 + lq)))
        ≤ 12 * L ^ 4 * (32 * X ^ 2 * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hc0 hL4') hinner
            (mul_nonneg hN0 hinner0) (by positivity)
      _ = 384 * X ^ 2 * L ^ 5 := by ring
      _ ≤ 400 * X ^ 2 * L ^ 6 := by
          have h56 : L ^ 5 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
          have : 0 ≤ X ^ 2 * L ^ 5 := by positivity
          have : X ^ 2 * L ^ 5 ≤ X ^ 2 * L ^ 6 := mul_le_mul_of_nonneg_left h56 hX2
          nlinarith
      _ = (20 * L ^ 3 * X) ^ 2 := by ring
  have hs := Real.sqrt_le_sqrt hsqrt
  rw [Real.sqrt_sq (by positivity)] at hs
  have hf : 2 * lN + 1 ≤ 2 * L := by linarith
  calc (2 * lN + 1) * Real.sqrt _ ≤ (2 * L) * (20 * L ^ 3 * X) :=
        mul_le_mul hf hs (Real.sqrt_nonneg _) (by positivity)
    _ = 40 * X * L ^ 4 := by ring

/-- Arithmetic for a Type I term. -/
lemma termI_arith {lN s l L X c : ℝ} (hc : 0 ≤ c) (hL : L = 1 + lN) (hlN : 0 ≤ lN)
    (hs0 : 0 ≤ s) (hs : s ≤ 3 * X) (hl0 : 0 ≤ l) (hl : l ≤ 2 * L) :
    c * lN * (12 * s * l) ≤ 72 * c * X * L ^ 4 := by
  have hL1 : 1 ≤ L := by linarith
  have hX0 : 0 ≤ X := by linarith
  have h1 : c * lN * (12 * s * l) ≤ c * L * (12 * (3 * X) * (2 * L)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hc) _ (by positivity)
      (by positivity)
    exact mul_le_mul (by linarith) hl hl0 (by positivity)
  have h2 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have h3 : c * X * L ^ 2 ≤ c * X * L ^ 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc c * lN * (12 * s * l) ≤ c * L * (12 * (3 * X) * (2 * L)) := h1
    _ = 72 * (c * X * L ^ 2) := by ring
    _ ≤ 72 * (c * X * L ^ 4) := by linarith
    _ = 72 * c * X * L ^ 4 := by ring

/-- **Vinogradov's minor arc bound.** -/
theorem vinogradov_minor {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) {N : ℕ} (hqN : q ≤ N) :
    ‖S N α‖ ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
      (1 + Real.log N) ^ 4 := by
  have hN1 : 1 ≤ N := le_trans hq hqN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  obtain ⟨p, hp1, hp5, hp4⟩ : ∃ p : ℝ, 1 ≤ p ∧ p ^ 5 = N ∧ (N : ℝ) ^ ((4 : ℝ) / 5) = p ^ 4 := by
    refine ⟨(N : ℝ) ^ ((1 : ℝ) / 5), Real.one_le_rpow hNr (by norm_num), ?_, ?_⟩
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  rw [hp4]
  have hp2 : (1 : ℝ) ≤ p ^ 2 := one_le_pow₀ hp1
  obtain ⟨u, hu1, hur, hul⟩ : ∃ u : ℕ, 1 ≤ u ∧ (u : ℝ) ≤ p ^ 2 ∧ p ^ 2 / 2 ≤ (u : ℝ) :=
    ⟨⌊p ^ 2⌋₊, Nat.one_le_floor_iff _ |>.2 hp2, Nat.floor_le (by linarith), floor_ge_half hp2⟩
  have hu1r : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hmain := vinogradov_uv hq hcop hα N hu1 hu1
  refine hmain.trans ?_
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (N : ℝ) / Real.sqrt q + p ^ 4 + Real.sqrt (N * q) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + Real.log N := ⟨_, rfl⟩
  rw [← hX, ← hL]
  have hlN := Real.log_natCast_nonneg N
  have hlq0 := Real.log_natCast_nonneg q
  have hL1 : 1 ≤ L := by linarith
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hA : 0 ≤ (N : ℝ) / Real.sqrt q := by positivity
  have hB : 0 ≤ Real.sqrt (N * q) := Real.sqrt_nonneg _
  have hp40 : 0 ≤ p ^ 4 := by positivity
  have hp4X : p ^ 4 ≤ X := by rw [hX]; linarith
  have hNqX : (N : ℝ) / q ≤ X := by
    have : (N : ℝ) / q ≤ N / Real.sqrt q := by
      apply div_le_div_of_nonneg_left (by linarith) hsq
      calc Real.sqrt q = Real.sqrt q * 1 := (mul_one _).symm
        _ ≤ Real.sqrt q * Real.sqrt q := by
            gcongr; rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hqr
        _ = q := Real.mul_self_sqrt (by linarith)
    rw [hX]; linarith
  have hqX : (q : ℝ) ≤ X := by
    have : (q : ℝ) ≤ Real.sqrt (N * q) := by
      rw [Real.le_sqrt (by linarith) (by positivity), sq]
      exact mul_le_mul_of_nonneg_right hqNr (by linarith)
    rw [hX]; linarith
  have hp24 : p ^ 2 ≤ p ^ 4 := pow_le_pow_right₀ hp1 (by norm_num)
  have hp45 : p ^ 4 ≤ p ^ 5 := pow_le_pow_right₀ hp1 (by norm_num)
  have huu : (u : ℝ) * u ≤ p ^ 4 := by
    have : (u : ℝ) * u ≤ p ^ 2 * p ^ 2 := mul_le_mul hur hur (by linarith) (by positivity)
    have h' : p ^ 2 * p ^ 2 = p ^ 4 := by ring
    linarith
  have hlogle : ∀ n : ℕ, (n : ℝ) ≤ N → Real.log n ≤ Real.log N := fun n hn => by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simpa using hlN
    · exact Real.log_le_log (by exact_mod_cast h) hn
  have hlq : Real.log q ≤ Real.log N := hlogle q hqNr
  have hluu : Real.log (u * u : ℕ) ≤ Real.log N := hlogle _ (by push_cast; linarith)
  have hlu : Real.log u ≤ Real.log N := hlogle _ (by linarith)
  have hluu0 := Real.log_natCast_nonneg (u * u)
  have hlu0 := Real.log_natCast_nonneg u
  obtain ⟨h40, h42⟩ := log4_bounds
  have t1 : (Real.log 4 + 4) * u ≤ 6 * X * L ^ 4 := by
    have h1 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
    have h2 : (Real.log 4 + 4) * u ≤ 6 * X := by nlinarith
    have h3 : 6 * X ≤ 6 * X * L ^ 4 := le_mul_of_one_le_right (by linarith) h1
    linarith
  have t2 := termI_arith (c := 1) (s := (N : ℝ) / q + (u * u : ℕ) + q)
    (l := 1 + Real.log q + Real.log (u * u : ℕ)) (X := X) zero_le_one hL hlN (by positivity)
    (by push_cast; linarith) (by linarith) (by linarith)
  have t3 := termI_arith (c := 2) (s := (N : ℝ) / q + u + q)
    (l := 1 + Real.log q + Real.log u) (X := X) zero_le_two hL hlN (by positivity)
    (by linarith) (by linarith) (by linarith)
  have t4 := term4_arith (N := (N : ℝ)) (q := (q : ℝ)) (u := (u : ℝ)) (lN := Real.log N)
    (lq := Real.log q) hqr hp1 hp5.symm hul hu1r hL hlN hlq0 hlq hX
  simp only [one_mul] at t2
  rw [← hL] at hmain
  have hX0 : 0 ≤ X := by linarith
  have hXL : 0 ≤ X * L ^ 4 := by positivity
  linarith

end LeanLab.PNTPort.Vinogradov

namespace LeanLab.PNTPort.Vinogradov

/-- Vacuity check: the hypotheses of `vinogradov_minor` hold for `q = 1`, `a = 0`, `α = 1/2`
and every `N ≥ 1`; and for `q = 7`, `a = 3`, `α = 3/7 + 1/50`. -/
example (N : ℕ) (hN : 1 ≤ N) : ‖S N (1 / 2)‖ ≤ 300 * ((N : ℝ) / Real.sqrt (1 : ℕ) +
    (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * (1 : ℕ))) * (1 + Real.log N) ^ 4 :=
  vinogradov_minor (q := 1) (a := 0) le_rfl (isCoprime_zero_left.2 (by simp)) (by norm_num) hN

example : IsCoprime (3 : ℤ) ((7 : ℕ) : ℤ) ∧
    |(3 / 7 + 1 / 50 : ℝ) - ((3 : ℤ) : ℝ) / ((7 : ℕ) : ℝ)| ≤ 1 / ((7 : ℕ) : ℝ) ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  · norm_num [abs_of_pos]

end LeanLab.PNTPort.Vinogradov

