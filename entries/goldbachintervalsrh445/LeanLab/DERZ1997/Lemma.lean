module

public import Mathlib
public import LeanLab.DERZ1997.Statements

/-!
P0011 Deshouillers, Effinger, te Riele, Zinoviev 1997, ERA-AMS 3, page 101, Section 3,
"An intermediate lemma", read from papers/P0011.pdf and its text, cloud session
20261019T1116Z-cloud23, unit U-5460.

The paper's proof: for 10^12 ≤ n ≤ 10^20 apply Schoenfeld 1976 equation (6.1), quoted as
`|Θ(n) - n| < √n (log n - 2) log n / (8π)` for `n ≥ 2.3 · 10^9` under GRH; if no prime lies in
`(n - h, n]` except possibly two of `n - 5, ..., n`, then
`h < √n (log n - 2) log n / (4π) + 2 log n < 1.615 · 10^12`.

Here:
* `gap_of_theta` the argument itself, for any uniform bound `C` on `|θ x - x|`;
  the printed proof applies the Θ bound at `n - h` without saying why `n - h ≥ 2.3 · 10^9`;
  Bertrand's postulate supplies it, `p > (n - 4)/2`.
* `derz_lemma_of_schoenfeld61` the lemma with the printed constant `1.615 · 10^12`,
  CONDITIONAL ON `Schoenfeld61`, the bound exactly as P0011 quotes it.
* `derz_lemma_of_cor1` the same argument from Schoenfeld's Corollary 1, the `log² x` form,
  gives only `1.69 · 10^12`: the printed constant needs the `(log x - 2)` refinement.
  `1.69 · 10^12 < 10^13` still suffices for the main theorem, `derz_main_of_cor1`.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.DERZ1997
open Real Chebyshev

/-! ### θ over an interval of integers -/

/-- `θ b = θ a + Σ_{a < k ≤ b, k prime} log k` for `a ≤ b`. -/
theorem theta_nat_add {a b : ℕ} (hab : a ≤ b) :
    θ (b : ℝ) = θ (a : ℝ) + ∑ k ∈ Finset.Ioc a b, if k.Prime then Real.log k else 0 := by
  simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
  rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]

/-- No prime in `(p, m]` and `n = m + 4` give `θ n ≤ θ p + 2 log n`: of `m+1, ..., m+4`
two are even and larger than `2`. -/
theorem theta_gap {p m : ℕ} (hpm : p ≤ m) (h2 : 2 ≤ m)
    (hnp : ∀ k, p < k → k ≤ m → ¬ k.Prime) :
    θ ((m + 4 : ℕ) : ℝ) ≤ θ (p : ℝ) + 2 * Real.log ((m + 4 : ℕ) : ℝ) := by
  have hsplit := theta_nat_add (a := p) (b := m + 4) (by omega)
  rw [← Finset.sum_Ioc_consecutive _ hpm (by omega : m ≤ m + 4)] at hsplit
  have hzero : ∑ k ∈ Finset.Ioc p m, (if k.Prime then Real.log k else 0) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [Finset.mem_Ioc] at hk
      simp [hnp k hk.1 hk.2]
  rw [hzero, zero_add] at hsplit
  set f : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0 with hf
  have hIoc : Finset.Ioc m (m + 4) = {m + 1, m + 2, m + 3, m + 4} := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]; omega
  have hsum : ∑ k ∈ Finset.Ioc m (m + 4), f k = f (m + 1) + f (m + 2) + f (m + 3) + f (m + 4) := by
    rw [hIoc, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_singleton]; ring
  have hle : ∀ j, j ≤ 4 → f (m + j) ≤ Real.log ((m + 4 : ℕ) : ℝ) := by
    intro j hj
    simp only [hf]
    split_ifs with hp
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (by omega))
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m + 4))
  have hev : ∀ j, Even (m + j) → 2 < m + j → f (m + j) = 0 := by
    intro j he hj
    simp only [hf]
    rw [if_neg]
    intro hp
    exact absurd (hp.even_iff.mp he) (by omega)
  have key : f (m + 1) + f (m + 2) + f (m + 3) + f (m + 4) ≤
      2 * Real.log ((m + 4 : ℕ) : ℝ) := by
    rcases Nat.even_or_odd m with he | ho
    · have e2 := hev 2 (he.add (by decide)) (by omega)
      have e4 := hev 4 (he.add (by decide)) (by omega)
      have := hle 1 (by norm_num); have := hle 3 (by norm_num)
      rw [e2, e4]; linarith
    · have e1 := hev 1 ho.add_one (by omega)
      have e3 := hev 3 (ho.add_odd (by decide)) (by omega)
      have := hle 2 (by norm_num); have := hle 4 (by norm_num)
      rw [e1, e3]; linarith
  have hk := hsum.trans_le key
  rw [hsplit]; linarith

/-! ### The intermediate lemma for any uniform θ bound -/

/-- The P0011 argument, with the Bertrand step the printed proof leaves implicit: if
`|θ x - x| ≤ C` for `X₀ ≤ x ≤ 10^20` with `X₀ ≤ 10^11`, and `2C + 2 log 10^20 < H`,
`10^12 ≤ H`, then every `6 ≤ n ≤ 10^20` has a prime `p` with `4 ≤ n - p ≤ H`. -/
theorem gap_of_theta (X₀ C : ℝ) (H : ℕ) (hX₀ : X₀ ≤ 10 ^ 11)
    (hθ : ∀ x : ℝ, X₀ ≤ x → x ≤ 10 ^ 20 → |θ x - x| ≤ C)
    (hH : 2 * C + 2 * Real.log (10 ^ 20) < H) (hH1 : 10 ^ 12 ≤ H) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ H := by
  intro n h6 hn
  rcases Nat.lt_or_ge n (H + 4) with hsmall | hbig
  · rcases Nat.lt_or_ge n 7 with h7 | h7
    · exact ⟨2, Nat.prime_two, by omega, by omega⟩
    · exact ⟨3, Nat.prime_three, by omega, by omega⟩
  -- n ≥ H + 4 ≥ 10^12 + 4; m = n - 4, p the largest prime ≤ m
  set m := n - 4 with hm
  have hm12 : 10 ^ 12 ≤ m := by omega
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (m / 2) (by omega)
  have hqm : q ≤ m := by omega
  set p := Nat.findGreatest Nat.Prime m with hpdef
  have hqp : q ≤ p := Nat.le_findGreatest hqm hq
  have hp : p.Prime := Nat.findGreatest_spec hqm hq
  have hpm : p ≤ m := Nat.findGreatest_le m
  have hnp : ∀ k, p < k → k ≤ m → ¬ k.Prime := fun k h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have hp11 : 10 ^ 11 ≤ p := by omega
  refine ⟨p, hp, by omega, ?_⟩
  -- the real inequality n - p ≤ 2C + 2 log n
  have hθg := theta_gap hpm (by omega) hnp
  have hn4 : m + 4 = n := by omega
  rw [hn4] at hθg
  have hpR : (10 : ℝ) ^ 11 ≤ (p : ℝ) := by exact_mod_cast hp11
  have hnR : (n : ℝ) ≤ 10 ^ 20 := by exact_mod_cast hn
  have hpn : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
  have h1 := hθ n (by linarith) hnR
  have h2 := hθ p (by linarith) (by linarith)
  have hlog : Real.log n ≤ Real.log (10 ^ 20) :=
    Real.log_le_log (by linarith) hnR
  have hreal : (n : ℝ) - p < H := by
    have a1 := (abs_le.mp h1).1
    have a2 := (abs_le.mp h2).2
    linarith
  have : ((n - p : ℕ) : ℝ) < H := by rw [Nat.cast_sub (by omega)]; exact hreal
  exact_mod_cast this.le

/-! ### Numerical inputs -/

set_option exponentiation.threshold 3000 in
theorem log_ten_lt' : Real.log 10 < 2.30261 := by
  have hn : (10 : ℕ) ^ 643 < 2 ^ 2136 := by norm_num
  have h : (10 : ℝ) ^ 643 < 2 ^ 2136 := by exact_mod_cast hn
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  push_cast at h'
  have := Real.log_two_lt_d9
  linarith

theorem log_1e20_lt : Real.log (10 ^ 20) < 46.0522 := by
  rw [Real.log_pow]; have := log_ten_lt'; push_cast; linarith

theorem log_ge_two {x : ℝ} (hx : 10 ^ 9 ≤ x) : 2 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have : Real.exp 2 < 8 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  linarith

theorem sqrt_le_1e10 {x : ℝ} (hx : x ≤ 10 ^ 20) : √x ≤ 10 ^ 10 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num at hx ⊢; linarith

/-! ### Schoenfeld (6.1) as quoted in P0011: the printed constant -/

/-- Schoenfeld 1976, equation (6.1), exactly as P0011 page 101 quotes it, under GRH:
`|Θ(x) - x| < √x (log x - 2) log x / (8π)` for `x ≥ 23 · 10^8`. CITED, not proved here.
Lee and Nosal, arXiv 2312.05628, display (1.1), attribute this shape to Schoenfeld for `ψ`. -/
def Schoenfeld61 : Prop :=
  ∀ x : ℝ, 23 * 10 ^ 8 ≤ x → |θ x - x| < √x * (Real.log x - 2) * Real.log x / (8 * π)

theorem schoenfeld61_uniform (h : Schoenfeld61) (x : ℝ) (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) :
    |θ x - x| ≤ 807195 * 10 ^ 6 := by
  refine (h x (by linarith)).le.trans ?_
  have hL := Real.log_le_log (by linarith) h2
  have hL2 := log_1e20_lt
  have hg := log_ge_two (x := x) (by linarith)
  have hs := sqrt_le_1e10 h2
  have hs0 := Real.sqrt_nonneg x
  have hpi := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]
  have hprod : √x * (Real.log x - 2) * Real.log x ≤ 10 ^ 10 * (46.0522 - 2) * 46.0522 := by
    have hlx : Real.log x ≤ 46.0522 := hL.trans hL2.le
    have a : (Real.log x - 2) * Real.log x ≤ (46.0522 - 2) * 46.0522 :=
      mul_le_mul (by linarith) hlx (by linarith) (by norm_num)
    calc √x * (Real.log x - 2) * Real.log x = √x * ((Real.log x - 2) * Real.log x) := by ring
      _ ≤ 10 ^ 10 * ((46.0522 - 2) * 46.0522) := by
          apply mul_le_mul hs a (by nlinarith) (by norm_num)
      _ = _ := by ring
  nlinarith

/-- **P0011 intermediate lemma with the printed constant `1.615 · 10^12`**, CONDITIONAL ON
Schoenfeld (6.1) as P0011 quotes it. GRH enters only through that input. -/
theorem derz_lemma_of_schoenfeld61 (h : Schoenfeld61) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 :=
  gap_of_theta (10 ^ 11) (807195 * 10 ^ 6) (1615 * 10 ^ 9) le_rfl
    (fun x h1 h2 => schoenfeld61_uniform h x h1 h2)
    (by have := log_1e20_lt; norm_num; linarith) (by norm_num)

/-- The lemma in the shape of the cited `derz_lemma`. -/
theorem derz_lemma_of (h : GRH → Schoenfeld61) :
    GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 :=
  fun hG => derz_lemma_of_schoenfeld61 (h hG)

/-! ### Schoenfeld Corollary 1, the `log² x` form: only `1.69 · 10^12` -/

/-- Schoenfeld 1976, Corollary 1, under RH: `|θ(x) - x| ≤ √x log² x / (8π)` for `x ≥ 599`.
Same statement as `LeanLab.ChirreHagen2025.SchoenfeldTheta`. CITED, not proved here. -/
def SchoenfeldCor1 : Prop :=
  ∀ u : ℝ, 599 ≤ u → |θ u - u| ≤ √u * Real.log u ^ 2 / (8 * π)

theorem cor1_uniform (h : SchoenfeldCor1) (x : ℝ) (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) :
    |θ x - x| ≤ 843842 * 10 ^ 6 := by
  refine (h x (by linarith)).trans ?_
  have hL := Real.log_le_log (by linarith) h2
  have hL2 := log_1e20_lt
  have hg := log_ge_two (x := x) (by linarith)
  have hs := sqrt_le_1e10 h2
  have hs0 := Real.sqrt_nonneg x
  have hpi := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]
  have hprod : √x * Real.log x ^ 2 ≤ 10 ^ 10 * 46.0522 ^ 2 := by
    have hlx : Real.log x ≤ 46.0522 := hL.trans hL2.le
    have a : Real.log x ^ 2 ≤ 46.0522 ^ 2 := pow_le_pow_left₀ (by linarith) hlx 2
    exact mul_le_mul hs a (by positivity) (by norm_num)
  nlinarith

/-- The P0011 lemma from Schoenfeld Corollary 1: the bound `1.69 · 10^12`. -/
theorem derz_lemma_of_cor1 (h : SchoenfeldCor1) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 169 * 10 ^ 10 :=
  gap_of_theta (10 ^ 11) (843842 * 10 ^ 6) (169 * 10 ^ 10) le_rfl
    (fun x h1 h2 => cor1_uniform h x h1 h2)
    (by have := log_1e20_lt; norm_num; linarith) (by norm_num)

/-- The paper's assembly with any gap bound `H ≤ 10^13`. -/
theorem derz_main_of_gap (H : ℕ) (hH : H ≤ 10 ^ 13)
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hL : GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ H)
    (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach := by
  intro hG n ho h7
  rcases Nat.lt_or_ge (10 ^ 20) n with hbig | hsmall
  · exact hZ hG n ho hbig
  rcases Nat.lt_or_ge n (10 ^ 13 + 4) with hlow | hmid
  · have hev : Even (n - 3) := Nat.Odd.sub_odd ho (by decide)
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - 3) hev (by omega) (by omega)
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩
  · obtain ⟨p, hp, h4, hle⟩ := hL hG n (by omega) hsmall
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
    have hev : Even (n - p) := Nat.Odd.sub_odd ho hpodd
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - p) hev h4 (by omega)
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

/-- **P0011 main theorem from Zinoviev, the `10^13` even check and Schoenfeld Corollary 1**:
the printed lemma constant is not needed. CONDITIONAL ON the three inputs. -/
theorem derz_main_of_cor1
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hS : GRH → SchoenfeldCor1) (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach :=
  derz_main_of_gap (169 * 10 ^ 10) (by norm_num) hZ
    (fun hG => derz_lemma_of_cor1 (hS hG)) hD

/-! ### Vacuity: the hypotheses of `gap_of_theta` are satisfiable -/

/-- `gap_of_theta` is not vacuous: Mathlib's `θ x ≤ log 4 · x` and `θ ≥ 0` give a uniform
bound `C = 10^20 · log 4` on `[1, 10^20]`, and `H` above `2C + 93` makes the theorem fire. -/
example : ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
    ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 10 ^ 21 := by
  refine gap_of_theta 1 (10 ^ 20 * 2) (10 ^ 21) (by norm_num) ?_ ?_ (by norm_num)
  · intro x h1 h2
    have hl4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have a := Chebyshev.theta_le_log4_mul_x (by linarith : (0 : ℝ) ≤ x)
    have b := Chebyshev.theta_nonneg x
    rw [abs_le]; constructor <;> nlinarith
  · have := log_1e20_lt; norm_num; linarith

end LeanLab.DERZ1997

