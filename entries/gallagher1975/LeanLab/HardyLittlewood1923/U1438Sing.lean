module

public import LeanLab.HardyLittlewood1923.TheoremD
public import LeanLab.VanDerCorput1939.SingLimit

/-!
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1603Z-28836, unit U-1438, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III: the ternary singular series

The singular series of Theorem A for `r = 3`,
`𝔖₃(n) = Σ_{q ≥ 1} (μ(q)/φ(q))³ c_q(n)`, `c_q(n)` Ramanujan's sum, as the lab's
`HeathBrown1985.ramanujan q n = Σ_{d ∣ (n, q)} d μ(q/d)`, which `PNTPort.Vinogradov.ramanujan_sum`
identifies with `Σ_{h mod q, (h, q) = 1} e(hn/q)`.

* `summable_sing3`: the series converges absolutely, every `n`.
* `abs_partial_sub_sing3`: `|Σ_{q ≤ Q} - 𝔖₃(n)| ≤ e⁸/√Q`, uniformly in `n`.
* `sing3_odd`: for odd `n`, `𝔖₃(n) = 2 C₃ ∏_{p ∣ n} (p-1)(p-2)/(p²-3p+3)`, the constant and the
  product of (3.61); `sing3_pos`: `𝔖₃(n) > 0` for odd `n`.
* `sing3_even`: `𝔖₃(n) = 0` for even `n ≥ 2`.

Known mathematics, no cited input. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1438

open Real Finset Filter Topology
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov (fS hS hS_apply fS_apply moebius_cube sum_divisors_hS euler_hS_le
  fS_eq_zero_of_not_sqf dvd_primorial_of_sqf fS_prime)
open LeanLab.VanDerCorput1939 (K P)

/-- The term `(μ(q)/φ(q))³ c_q(n)` of the ternary singular series. -/
noncomputable def singTerm (n q : ℕ) : ℝ :=
  ((μ q : ℝ) / (q.totient : ℝ)) ^ 3 * LeanLab.HeathBrown1985.ramanujan q n

/-- **The ternary singular series** `𝔖₃(n) = Σ_{q ≥ 1} (μ(q)/φ(q))³ c_q(n)`. The `q = 0` term
is `0` since `μ(0) = 0`. -/
noncomputable def sing3 (n : ℕ) : ℝ := ∑' q : ℕ, singTerm n q

lemma singTerm_eq_fS (n q : ℕ) : singTerm n q = fS n q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [singTerm]
  · rw [fS_apply hq, singTerm, div_pow, moebius_cube]; ring

lemma singTerm_eq : singTerm = fun n q => fS n q := by
  funext n q; exact singTerm_eq_fS n q

lemma hS_zero (n : ℕ) : hS n 0 = 0 := by simp

lemma hS_nonneg (n d : ℕ) : 0 ≤ hS n d := by rw [hS_apply]; positivity

lemma hS_eq_zero_of_not_sqf {n q : ℕ} (hq : 1 ≤ q) (h : ¬ Squarefree q) : hS n q = 0 := by
  rw [hS_apply, fS_eq_zero_of_not_sqf hq h]; simp

/-- Partial sums of `|f(q)| √q` over `q ≤ Q` are at most `e⁸`. -/
lemma sum_Icc_hS_le (n Q : ℕ) : ∑ q ∈ Icc 1 Q, hS n q ≤ Real.exp 8 := by
  have hsub : ∑ q ∈ Icc 1 Q, hS n q = ∑ d ∈ (primorial Q).divisors.filter (· ≤ Q), hS n d := by
    symm
    apply sum_subset
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hd.1.1 (primorial_pos Q), hd.2⟩
    · intro q hq hq'
      rw [mem_Icc] at hq
      by_contra hne
      apply hq'
      have hsqf : Squarefree q := by
        by_contra hs; exact hne (hS_eq_zero_of_not_sqf hq.1 hs)
      rw [mem_filter, Nat.mem_divisors]
      exact ⟨⟨dvd_primorial_of_sqf hsqf hq.2, (primorial_pos Q).ne'⟩, hq.2⟩
  rw [hsub]
  calc ∑ d ∈ (primorial Q).divisors.filter (· ≤ Q), hS n d
      ≤ ∑ d ∈ (primorial Q).divisors, hS n d :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun d _ _ => hS_nonneg n d)
    _ = ∏ p ∈ Nat.primesLE Q, (1 + hS n p) := sum_divisors_hS n Q
    _ ≤ Real.exp 8 := euler_hS_le n Q

lemma sum_range_hS_le (n Q : ℕ) : ∑ q ∈ range Q, hS n q ≤ Real.exp 8 := by
  have hsub : range Q ⊆ insert 0 (Icc 1 Q) := by
    intro q hq
    rw [mem_range] at hq
    rw [mem_insert, mem_Icc]
    omega
  calc ∑ q ∈ range Q, hS n q ≤ ∑ q ∈ insert 0 (Icc 1 Q), hS n q :=
        sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hS_nonneg n d)
    _ = ∑ q ∈ Icc 1 Q, hS n q := by
        rw [sum_insert (by simp), hS_zero, zero_add]
    _ ≤ Real.exp 8 := sum_Icc_hS_le n Q

lemma summable_hS (n : ℕ) : Summable (fun q => hS n q) :=
  summable_of_sum_range_le (hS_nonneg n) (sum_range_hS_le n)

lemma tsum_hS_le (n : ℕ) : ∑' q, hS n q ≤ Real.exp 8 :=
  Real.tsum_le_of_sum_range_le (hS_nonneg n) (sum_range_hS_le n)

lemma abs_fS_le_hS (n q : ℕ) : |fS n q| ≤ hS n q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · rw [hS_apply]
    have : (1 : ℝ) ≤ Real.sqrt q := by
      rw [Real.one_le_sqrt]; exact_mod_cast hq
    nlinarith [abs_nonneg (fS n q)]

/-- The ternary singular series converges absolutely. -/
theorem summable_sing3 (n : ℕ) : Summable (fun q => |singTerm n q|) := by
  simp only [singTerm_eq_fS]
  exact Summable.of_nonneg_of_le (fun q => abs_nonneg _) (abs_fS_le_hS n) (summable_hS n)

lemma summable_fS (n : ℕ) : Summable (fun q => fS n q) := by
  have := summable_sing3 n
  simp only [singTerm_eq_fS] at this
  exact this.of_abs

lemma sing3_eq_tsum_fS (n : ℕ) : sing3 n = ∑' q, fS n q := by
  unfold sing3; simp only [singTerm_eq_fS]

lemma sum_range_succ_eq_Icc (f : ℕ → ℝ) (h0 : f 0 = 0) (Q : ℕ) :
    ∑ q ∈ range (Q + 1), f q = ∑ q ∈ Icc 1 Q, f q := by
  have : range (Q + 1) = insert 0 (Icc 1 Q) := by
    ext q; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [this, sum_insert (by simp), h0, zero_add]

/-- **Tail bound**: `|Σ_{q ≤ Q} (μ(q)/φ(q))³ c_q(n) - 𝔖₃(n)| ≤ e⁸/√Q`, uniformly in `n`. -/
theorem abs_partial_sub_sing3 (n : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    |∑ q ∈ Icc 1 Q, singTerm n q - sing3 n| ≤ Real.exp 8 / Real.sqrt Q := by
  simp only [singTerm_eq_fS]
  rw [sing3_eq_tsum_fS]
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 (by exact_mod_cast hQ)
  have hsplit := (summable_fS n).sum_add_tsum_nat_add (Q + 1)
  rw [← hsplit, sum_range_succ_eq_Icc (fun q => fS n q) (by simp) Q]
  rw [show ∀ a b : ℝ, a - (a + b) = -b by intros; ring, abs_neg]
  have hsum_tail : Summable (fun i => hS n (i + (Q + 1))) :=
    (summable_nat_add_iff (Q + 1)).2 (summable_hS n)
  have hsum_tail_f : Summable (fun i => fS n (i + (Q + 1))) :=
    (summable_nat_add_iff (Q + 1)).2 (summable_fS n)
  have hle : ∀ i, |fS n (i + (Q + 1))| ≤ hS n (i + (Q + 1)) / Real.sqrt Q := by
    intro i
    rw [le_div_iff₀ hsQ, hS_apply]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact Real.sqrt_le_sqrt (by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have h1 : |∑' i, fS n (i + (Q + 1))| ≤ ∑' i, |fS n (i + (Q + 1))| := by
    have := norm_tsum_le_tsum_norm (f := fun i => fS n (i + (Q + 1)))
      (by simpa [Real.norm_eq_abs] using hsum_tail_f.abs)
    simpa [Real.norm_eq_abs] using this
  have h2 : ∑' i, |fS n (i + (Q + 1))| ≤ ∑' i, hS n (i + (Q + 1)) / Real.sqrt Q :=
    Summable.tsum_le_tsum hle hsum_tail_f.abs (hsum_tail.div_const _)
  have h3 : ∑' i, hS n (i + (Q + 1)) ≤ ∑' q, hS n q := by
    have := (summable_hS n).sum_add_tsum_nat_add (Q + 1)
    have h0 : 0 ≤ ∑ i ∈ range (Q + 1), hS n i := sum_nonneg fun i _ => hS_nonneg n i
    linarith
  rw [tsum_div_const] at h2
  have h4 : (∑' i, hS n (i + (Q + 1))) / Real.sqrt Q ≤ Real.exp 8 / Real.sqrt Q :=
    div_le_div_of_nonneg_right (h3.trans (tsum_hS_le n)) hsQ.le
  linarith

lemma tendsto_exp8_div_sqrt : Tendsto (fun Q : ℕ => Real.exp 8 / Real.sqrt Q) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma eq_of_abs_le_two_mul {x y : ℝ} (h : ∀ ε : ℝ, 0 < ε → |x - y| ≤ 2 * ε) : x = y := by
  by_contra hxy
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
  have := h (|x - y| / 4) (by positivity)
  linarith

/-- For odd `n`, `𝔖₃(n) = K P(n)`, van der Corput's product. -/
theorem sing3_eq_KP {n : ℕ} (hn : Odd n) : sing3 n = K * P n := by
  apply eq_of_abs_le_two_mul
  intro ε hε
  obtain ⟨P₀, hP₀⟩ := LeanLab.VanDerCorput1939.fS_sum_tendsto_KP ε hε
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.1 ((tendsto_order.1 tendsto_exp8_div_sqrt).2 ε hε)
  set Q := max (max P₀ Q₁) (max 1 ⌈Real.log n⌉₊) with hQ
  have hQ1 : 1 ≤ Q := le_trans (le_max_left _ _) (le_max_right _ _)
  have hlog : Real.log n ≤ Q := by
    have : ⌈Real.log n⌉₊ ≤ Q := le_trans (le_max_right _ _) (le_max_right _ _)
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have h1 := hP₀ Q n (le_trans (le_max_left _ _) (le_max_left _ _)) hn hlog
  have h2 := abs_partial_sub_sing3 n hQ1
  have h3 := hQ₁ Q (le_trans (le_max_right _ _) (le_max_left _ _))
  simp only [singTerm_eq_fS] at h2
  calc |sing3 n - K * P n|
      = |(∑ q ∈ Icc 1 Q, fS n q - K * P n) - (∑ q ∈ Icc 1 Q, fS n q - sing3 n)| := by
        congr 1; ring
    _ ≤ |∑ q ∈ Icc 1 Q, fS n q - K * P n| + |∑ q ∈ Icc 1 Q, fS n q - sing3 n| := abs_sub _ _
    _ ≤ 2 * ε := by linarith

/-- **The singular series for odd `n`**: `𝔖₃(n) = 2 C₃ ∏_{p ∣ n} (p-1)(p-2)/(p²-3p+3)`,
the constant (3.62) and the product of (3.61). -/
theorem sing3_odd {n : ℕ} (hn : Odd n) : sing3 n = 2 * C3 * Pi3 n := by
  rw [sing3_eq_KP hn, K_eq_two_mul_C3, P_eq_Pi3]

/-- **Positivity**: `𝔖₃(n) > 0` for every odd `n`. -/
theorem sing3_pos {n : ℕ} (hn : Odd n) : 0 < sing3 n := by
  rw [sing3_eq_KP hn]
  exact mul_pos (lt_trans (by norm_num) LeanLab.VanDerCorput1939.K_gt)
    (LeanLab.VanDerCorput1939.P_pos hn)

/-- **Even `n`**: `𝔖₃(n) = 0`, the Euler factor at `2` vanishes. -/
theorem sing3_even {n : ℕ} (hn : Even n) : sing3 n = 0 := by
  have h2 : 1 + fS n 2 = 0 := by
    rw [fS_prime Nat.prime_two, if_pos (even_iff_two_dvd.1 hn)]; norm_num
  have hb : ∀ Q : ℕ, 2 ≤ Q → |sing3 n| ≤ 2 * (Real.exp 8 / Real.sqrt Q) := by
    intro Q hQ
    have e1 := LeanLab.VanDerCorput1939.abs_sum_fS_sub_euler n (by omega : 1 ≤ Q)
    have hprod : ∏ p ∈ Nat.primesLE Q, (1 + fS n p) = 0 :=
      prod_eq_zero (Nat.mem_primesLE.2 ⟨hQ, Nat.prime_two⟩) h2
    rw [hprod, sub_zero] at e1
    have e2 := abs_partial_sub_sing3 n (by omega : 1 ≤ Q)
    simp only [singTerm_eq_fS] at e2
    calc |sing3 n| = |(∑ q ∈ Icc 1 Q, fS n q) - (∑ q ∈ Icc 1 Q, fS n q - sing3 n)| := by
          congr 1; ring
      _ ≤ |∑ q ∈ Icc 1 Q, fS n q| + |∑ q ∈ Icc 1 Q, fS n q - sing3 n| := abs_sub _ _
      _ ≤ 2 * (Real.exp 8 / Real.sqrt Q) := by linarith
  apply eq_of_abs_le_two_mul
  intro ε hε
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.1 ((tendsto_order.1 tendsto_exp8_div_sqrt).2 ε hε)
  have h := hb (max Q₁ 2) (le_max_right _ _)
  have h' := hQ₁ (max Q₁ 2) (le_max_left _ _)
  rw [sub_zero]
  linarith

/-- `|𝔖₃(n)| ≤ e⁸` for every `n`. -/
theorem abs_sing3_le (n : ℕ) : |sing3 n| ≤ Real.exp 8 := by
  rw [sing3_eq_tsum_fS]
  have h1 : |∑' q, fS n q| ≤ ∑' q, |fS n q| := by
    have := norm_tsum_le_tsum_norm (f := fun q => fS n q)
      (by simpa [Real.norm_eq_abs] using (summable_fS n).abs)
    simpa [Real.norm_eq_abs] using this
  exact h1.trans ((Summable.tsum_le_tsum (abs_fS_le_hS n) (summable_fS n).abs
    (summable_hS n)).trans (tsum_hS_le n))

end LeanLab.HardyLittlewood1923.U1438
