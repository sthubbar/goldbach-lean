module

public import LeanLab.Linnik.MajorArcEnergy.Defs
public import LeanLab.Linnik.MajorArcEnergy.Basic13

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy.Leaves13Principal


open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (Jn)
open LeanLab.PNTPort.LargeSieve (dist0 norm_e e_add e_neg norm_geom_le)


/-- Gallagher 1975 p.130, the partial summation above display 9, in its Abel form:
for a nonnegative nonincreasing weight f, the weighted sum of z is at most f(0) times
a bound B for every partial sum of z. -/
theorem abel_antitone_bound (f : ℕ → ℝ) (z : ℕ → ℂ) (B : ℝ) (hf : Antitone f)
    (hf0 : ∀ i, 0 ≤ f i) (hZ : ∀ k, ‖∑ i ∈ range k, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ range n, (f i : ℂ) * z i‖ ≤ f 0 * B := by
  have hid : ∀ n, ∑ i ∈ range n, (f i : ℂ) * z i =
      (f n : ℂ) * ∑ i ∈ range n, z i +
        ∑ i ∈ range n, ((f i - f (i + 1) : ℝ) : ℂ) * ∑ j ∈ range (i + 1), z j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih,
        sum_range_succ (fun i => ((f i - f (i + 1) : ℝ) : ℂ) * ∑ j ∈ range (i + 1), z j),
        sum_range_succ z]
      push_cast
      ring
  rw [hid]
  have hd : ∀ i, 0 ≤ f i - f (i + 1) := fun i => sub_nonneg.mpr (hf (Nat.le_succ i))
  calc _ ≤ ‖(f n : ℂ) * ∑ i ∈ range n, z i‖ +
        ‖∑ i ∈ range n, ((f i - f (i + 1) : ℝ) : ℂ) * ∑ j ∈ range (i + 1), z j‖ :=
        norm_add_le _ _
    _ ≤ f n * B + ∑ i ∈ range n, (f i - f (i + 1)) * B := by
        gcongr ?_ + ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 n)]
          exact mul_le_mul_of_nonneg_left (hZ n) (hf0 n)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hd i)]
          exact mul_le_mul_of_nonneg_left (hZ _) (hd i)
    _ = f 0 * B := by rw [← sum_mul, sum_range_sub' f n]; ring

/-- Gallagher 1975 p.130 above display 9: the part of T over N^(1/4) < m at most N,
here M < m at most N, is at most 1/log(M+1) times the geometric sum bound
1/(2 ||beta||), by partial summation. -/
theorem principalMain_upper_part (N M : ℕ) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 < dist0 β) :
    ‖∑ m ∈ Ioc M N, (1 / Real.log m : ℂ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β)‖ ≤
      1 / Real.log ((M : ℝ) + 1) * (1 / (2 * dist0 β)) := by
  have hre : ∑ m ∈ Ioc M N, (1 / Real.log m : ℂ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β) =
      ∑ i ∈ range (N - M), ((1 / Real.log ((M : ℝ) + 1 + i) : ℝ) : ℂ) *
        LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 + i) * β) := by
    rw [show Ioc M N = Ico (M + 1) (N + 1) by ext; simp, Finset.sum_Ico_eq_sum_range,
      show N + 1 - (M + 1) = N - M by omega]
    apply sum_congr rfl
    intro i _
    push_cast
    ring_nf
  rw [hre]
  have h0 : (1 : ℝ) / Real.log ((M : ℝ) + 1) = 1 / Real.log ((M : ℝ) + 1 + ((0 : ℕ) : ℝ)) := by
    simp
  rw [h0]
  apply abel_antitone_bound (fun i : ℕ => 1 / Real.log ((M : ℝ) + 1 + i))
    (fun i : ℕ => LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 + i) * β)) (1 / (2 * dist0 β))
  · intro i j hij
    have hi : (1 : ℝ) < (M : ℝ) + 1 + i := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact one_div_le_one_div_of_le (Real.log_pos hi)
      (Real.log_le_log (by linarith) (by linarith))
  · intro i
    have : (1 : ℝ) ≤ (M : ℝ) + 1 + i := by
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    exact one_div_nonneg.mpr (Real.log_nonneg this)
  · intro k
    have hs : ∑ i ∈ range k, LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 + i) * β) =
        LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * β) * ∑ i ∈ range k, LeanLab.PNTPort.LargeSieve.e ((i : ℝ) * β) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [← e_add]
      ring_nf
    rw [hs, norm_mul, norm_e, one_mul]
    exact norm_geom_le k hβ

/-- Gallagher 1975 p.130 above display 9: T(beta) equals the sum over m at most M plus
the sum over M < m at most N; the first is at most 2M trivially and the second is
bounded by partial summation, giving |T(beta)| at most 2M + 1/(2 log(M+1) ||beta||). -/
theorem principalMain_split_bound (N M : ℕ) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 < dist0 β) :
    ‖principalMain N β‖ ≤ 2 * M + 1 / Real.log ((M : ℝ) + 1) * (1 / (2 * dist0 β)) := by
  unfold principalMain
  rw [← sum_filter_add_sum_filter_not (Ioc 1 N) (fun m => m ≤ M)]
  have hup : (Ioc 1 N).filter (fun m => ¬ m ≤ M) = Ioc M N := by
    ext m; simp only [mem_filter, mem_Ioc]; omega
  rw [hup]
  refine (norm_add_le _ _).trans (add_le_add ?_ (principalMain_upper_part N M hM hβ))
  have hsub : (Ioc 1 N).filter (fun m => m ≤ M) ⊆ Ioc 0 M := by
    intro m hm; simp only [mem_filter, mem_Ioc] at hm ⊢; omega
  have hcard : (((Ioc 1 N).filter (fun m => m ≤ M)).card : ℝ) ≤ M := by
    have := card_le_card hsub
    simp only [Nat.card_Ioc, Nat.sub_zero] at this
    exact_mod_cast this
  have hterm : ∀ m ∈ (Ioc 1 N).filter (fun m => m ≤ M),
      ‖(1 / Real.log m : ℂ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β)‖ ≤ 2 := by
    intro m hm
    have hm2 : (2 : ℝ) ≤ m := by
      have := (mem_Ioc.mp (mem_filter.mp hm).1).1
      exact_mod_cast this
    have hl2 : 1 / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2
    have hlpos : 0 < Real.log m := by linarith
    rw [norm_mul, norm_e, mul_one, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg hlpos.le]
    rw [div_le_iff₀ hlpos]
    linarith
  calc _ ≤ ∑ m ∈ (Ioc 1 N).filter (fun m => m ≤ M), ‖(1 / Real.log m : ℂ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ (Ioc 1 N).filter (fun m => m ≤ M), (2 : ℝ) := sum_le_sum hterm
    _ = 2 * (((Ioc 1 N).filter (fun m => m ≤ M)).card : ℝ) := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * M := by linarith

/-- The distance to the nearest integer is |beta| when |beta| is at most 1/2. -/
theorem dist0_eq_abs {β : ℝ} (hβ : |β| ≤ 1 / 2) : dist0 β = |β| := by
  apply le_antisymm
  · simpa using LeanLab.PNTPort.LargeSieve.dist0_le_abs_sub_int β 0
  · unfold dist0
    by_cases hr : round β = 0
    · simp [hr]
    · have h1 : (1 : ℝ) ≤ |((round β : ℤ) : ℝ)| := by
        have : (1 : ℤ) ≤ |round β| := Int.one_le_abs hr
        exact_mod_cast this
      have h2 := abs_sub_abs_le_abs_sub ((round β : ℤ) : ℝ) β
      rw [abs_sub_comm] at h2
      linarith

/-- Gallagher 1975 p.130 above display 9 with the cut at M equal to the integer fourth
root of N: for N at least 2 and 0 < |beta| at most 1/2,
|T(beta)|^2 is at most 8 N^(1/2) + 8 L^(-2) beta^(-2), which is the square of
the printed bound (N^(1/4) + ||beta||^(-1)) L^(-1) up to the form of its first part. -/
theorem principalMain_sq_le {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ0 : 0 < |β|) (hβ : |β| ≤ 1 / 2) :
    ‖principalMain N β‖ ^ 2 ≤
      8 * Real.sqrt N + 8 / Real.log N ^ 2 * β ^ (-2 : ℤ) := by
  set s := Nat.sqrt N with hs
  set M := Nat.sqrt s with hMdef
  have hs1 : 1 ≤ s := Nat.sqrt_pos.mpr (by omega)
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hs1
  have hNs : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have hsM : s < (M + 1) * (M + 1) := Nat.lt_succ_sqrt s
  have hN4 : N ≤ (M + 1) ^ 4 := by
    have : s + 1 ≤ (M + 1) * (M + 1) := hsM
    have h2 : (s + 1) * (s + 1) ≤ ((M + 1) * (M + 1)) * ((M + 1) * (M + 1)) :=
      Nat.mul_le_mul this this
    nlinarith
  have hMs : M * M ≤ s := Nat.sqrt_le s
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogM : Real.log N ≤ 4 * Real.log ((M : ℝ) + 1) := by
    rw [show (4 : ℝ) * Real.log ((M : ℝ) + 1) = Real.log (((M : ℝ) + 1) ^ 4) by
      rw [Real.log_pow]; norm_num]
    exact Real.log_le_log hNpos (by exact_mod_cast hN4)
  have hlM : 0 < Real.log ((M : ℝ) + 1) := by linarith
  have hd : dist0 β = |β| := dist0_eq_abs hβ
  have hb := principalMain_split_bound N M hM1 (β := β) (by rw [hd]; exact hβ0)
  rw [hd] at hb
  have hinv : 1 / Real.log ((M : ℝ) + 1) ≤ 4 / Real.log N := by
    rw [div_le_div_iff₀ hlM hL]; linarith
  have hb2 : ‖principalMain N β‖ ≤ 2 * M + 2 / (Real.log N * |β|) := by
    refine hb.trans (add_le_add le_rfl ?_)
    calc 1 / Real.log ((M : ℝ) + 1) * (1 / (2 * |β|)) ≤ 4 / Real.log N * (1 / (2 * |β|)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = 2 / (Real.log N * |β|) := by field_simp; ring
  have hMsq : (M : ℝ) ^ 2 ≤ Real.sqrt N := by
    have h1 : ((M * M : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hMs
    have h2 : (s : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    push_cast at h1
    nlinarith
  have hz : β ^ (-2 : ℤ) = 1 / |β| ^ 2 := by
    rw [zpow_neg, sq_abs]; simp
  rw [hz]
  have hT0 := norm_nonneg (principalMain N β)
  set x := 2 / (Real.log N * |β|) with hx
  have hx2 : x ^ 2 = 4 / Real.log N ^ 2 * (1 / |β| ^ 2) := by
    rw [hx]; field_simp; ring
  have hsq : ‖principalMain N β‖ ^ 2 ≤ (2 * M + x) ^ 2 :=
    pow_le_pow_left₀ hT0 hb2 2
  have hexp : (2 * (M : ℝ) + x) ^ 2 ≤ 8 * (M : ℝ) ^ 2 + 2 * x ^ 2 := by
    nlinarith [sq_nonneg (2 * (M : ℝ) - x)]
  rw [hx2, show 2 * (4 / Real.log N ^ 2 * (1 / |β| ^ 2)) =
    8 / Real.log N ^ 2 * (1 / |β| ^ 2) by ring] at hexp
  linarith

/-- Orthogonality of the additive characters over the period from -1/2 to 1/2,
used for the full period integral on p.130 above display 9. -/
theorem integral_e_int_half (k : ℤ) :
    (∫ β in (-(1 / 2 : ℝ))..(1 / 2), LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * β)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, LeanLab.PNTPort.LargeSieve.e_zero]
    norm_num
  · let c : ℂ := 2 * Real.pi * Complex.I * (k : ℂ)
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero) hkc
    have he (γ : ℝ) : LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * γ) = Complex.exp (c * γ) := by
      unfold LeanLab.PNTPort.LargeSieve.e
      congr 1
      simp only [c]
      push_cast
      ring
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    have h1 : c * ((1 / 2 : ℝ) : ℂ) = c * ((-(1 / 2) : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [c]; push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp [hk]

/-- Gallagher 1975 p.130 above display 9: the full period integral of |T(beta)|^2 LeanLab.PNTPort.LargeSieve.e(n beta)
over -1/2 to 1/2 equals J(n), by expanding the square and orthogonality. -/
theorem principalMain_full_period (N : ℕ) (n : ℤ) :
    (∫ β in (-(1 / 2 : ℝ))..(1 / 2),
      star (principalMain N β) * principalMain N β * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β)) = (Jn N n : ℂ) := by
  have hexp : ∀ β : ℝ, star (principalMain N β) * principalMain N β * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β) =
      ∑ p ∈ Ioc 1 N ×ˢ Ioc 1 N, ((1 / (Real.log p.1 * Real.log p.2) : ℝ) : ℂ) *
        LeanLab.PNTPort.LargeSieve.e ((((p.2 : ℤ) - p.1 + n : ℤ) : ℝ) * β) := by
    intro β
    unfold principalMain
    rw [star_sum, sum_mul_sum, sum_mul, sum_product]
    apply sum_congr rfl
    intro a _
    rw [sum_mul]
    apply sum_congr rfl
    intro b _
    simp only [star_mul', Complex.star_def, map_div₀, map_one, Complex.conj_ofReal, ← e_neg]
    have h : LeanLab.PNTPort.LargeSieve.e ((((b : ℤ) - a + n : ℤ) : ℝ) * β) =
        LeanLab.PNTPort.LargeSieve.e (-((a : ℝ) * β)) * LeanLab.PNTPort.LargeSieve.e ((b : ℝ) * β) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β) := by
      rw [← e_add, ← e_add]; congr 1; push_cast; ring
    rw [h]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (g := fun β => ∑ p ∈ Ioc 1 N ×ˢ Ioc 1 N,
      ((1 / (Real.log p.1 * Real.log p.2) : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((p.2 : ℤ) - p.1 + n : ℤ) : ℝ) * β))
      (fun β _ => hexp β)]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_e_int_half, mul_ite, mul_one,
      mul_zero]
    rw [← sum_filter]
    unfold Jn
    push_cast
    apply sum_congr
    · apply filter_congr
      intro p _
      omega
    · intro p _
      rfl
  · intro p _
    apply Continuous.intervalIntegrable
    unfold LeanLab.PNTPort.LargeSieve.e
    fun_prop

/-- The integral of N^(1/2) + beta^(-2) type bounds over delta to 1/2, used for the tail
integral on p.130 above display 9. -/
theorem integral_tail_bound (c d : ℝ) {a b : ℝ} (_hab : a ≤ b) (h0 : (0 : ℝ) ∉ Set.uIcc a b) :
    (∫ β in a..b, (c + d * β ^ (-2 : ℤ))) = c * (b - a) + d * (a⁻¹ - b⁻¹) := by
  have hz : IntervalIntegrable (fun β : ℝ => β ^ (-2 : ℤ)) volume a b :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr h0)
  rw [intervalIntegral.integral_add intervalIntegrable_const (hz.const_mul d),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  simp only [smul_eq_mul]
  norm_num
  ring

/-- Gallagher 1975 p.130 above display 9: for 0 < delta at most 1/2, the integral of
|T(beta)|^2 LeanLab.PNTPort.LargeSieve.e(n beta) over |beta| at most delta differs from J(n) by the tail over
delta to 1/2, which the partial summation bound makes at most
8 N^(1/2) + 16 L^(-2) / delta. -/
theorem principalMain_window_main {N : ℕ} (hN : 2 ≤ N) (n : ℤ) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖(∫ β in (-δ)..δ, star (principalMain N β) * principalMain N β * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β)) -
        (Jn N n : ℂ)‖ ≤ 8 * Real.sqrt N + 16 / Real.log N ^ 2 / δ := by
  set g : ℝ → ℂ := fun β => star (principalMain N β) * principalMain N β * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β)
    with hg
  have hT := continuous_principalMain N
  have hgc : Continuous g := by
    simp only [hg]
    unfold LeanLab.PNTPort.LargeSieve.e
    exact ((continuous_star.comp hT).mul hT).mul (by fun_prop)
  have hsplit : (∫ β in (-(1 / 2 : ℝ))..(1 / 2), g β) =
      (∫ β in (-(1 / 2 : ℝ))..(-δ), g β) + (∫ β in (-δ)..δ, g β) +
        ∫ β in δ..(1 / 2), g β := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _)]
  have hfull : (∫ β in (-(1 / 2 : ℝ))..(1 / 2), g β) = (Jn N n : ℂ) :=
    principalMain_full_period N n
  have hdiff : (∫ β in (-δ)..δ, g β) - (Jn N n : ℂ) =
      -((∫ β in (-(1 / 2 : ℝ))..(-δ), g β) + ∫ β in δ..(1 / 2), g β) := by
    rw [← hfull, hsplit]; ring
  change ‖(∫ β in (-δ)..δ, g β) - (Jn N n : ℂ)‖ ≤ _
  rw [hdiff, norm_neg]
  set c := 8 * Real.sqrt N with hc
  set d := 8 / Real.log N ^ 2 with hd
  have hd0 : 0 ≤ d := by positivity
  have hpt : ∀ β : ℝ, δ ≤ |β| → |β| ≤ 1 / 2 → ‖g β‖ ≤ c + d * β ^ (-2 : ℤ) := by
    intro β h1 h2
    have : ‖g β‖ = ‖principalMain N β‖ ^ 2 := by
      simp only [hg, norm_mul, norm_star, norm_e, mul_one, sq]
    rw [this]
    exact principalMain_sq_le hN (by linarith) h2
  have h0r : (0 : ℝ) ∉ Set.uIcc δ (1 / 2) := by
    rw [Set.uIcc_of_le hδ2]; intro h; linarith [h.1]
  have h0l : (0 : ℝ) ∉ Set.uIcc (-(1 / 2)) (-δ) := by
    rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.2]
  have hintr : IntervalIntegrable (fun β : ℝ => c + d * β ^ (-2 : ℤ)) volume δ (1 / 2) :=
    intervalIntegrable_const.add
      ((intervalIntegral.intervalIntegrable_zpow (Or.inr h0r)).const_mul d)
  have hintl : IntervalIntegrable (fun β : ℝ => c + d * β ^ (-2 : ℤ)) volume (-(1 / 2)) (-δ) :=
    intervalIntegrable_const.add
      ((intervalIntegral.intervalIntegrable_zpow (Or.inr h0l)).const_mul d)
  have hright : ‖∫ β in δ..(1 / 2), g β‖ ≤ c * (1 / 2 - δ) + d * (δ⁻¹ - (1 / 2)⁻¹) := by
    rw [← integral_tail_bound c d hδ2 h0r]
    refine intervalIntegral.norm_integral_le_of_norm_le hδ2
      (Filter.Eventually.of_forall fun β hβ => hpt β ?_ ?_) hintr
    · rw [abs_of_pos (by linarith [hβ.1])]; exact hβ.1.le
    · rw [abs_of_pos (by linarith [hβ.1])]; exact hβ.2
  have hleft : ‖∫ β in (-(1 / 2 : ℝ))..(-δ), g β‖ ≤
      c * (-δ - -(1 / 2)) + d * ((-(1 / 2))⁻¹ - (-δ)⁻¹) := by
    rw [← integral_tail_bound c d (by linarith) h0l]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall fun β hβ => hpt β ?_ ?_) hintl
    · rw [abs_of_neg (by linarith [hβ.2])]; linarith [hβ.2]
    · rw [abs_of_neg (by linarith [hβ.2])]; linarith [hβ.1]
  have hsum := (norm_add_le _ _).trans (add_le_add hleft hright)
  refine hsum.trans ?_
  have hsN : 0 ≤ c := by positivity
  have hdδ : d * (δ⁻¹ - (1 / 2)⁻¹) ≤ d * δ⁻¹ := by
    apply mul_le_mul_of_nonneg_left _ hd0; norm_num
  have hdδ' : d * ((-(1 / 2))⁻¹ - (-δ)⁻¹) ≤ d * δ⁻¹ := by
    apply mul_le_mul_of_nonneg_left _ hd0
    rw [inv_neg]; norm_num
  have h16 : 16 / Real.log N ^ 2 / δ = 2 * (d * δ⁻¹) := by rw [hd]; field_simp; ring
  rw [h16]
  nlinarith

/-- Gallagher 1975 p.130 above display 9, the comparison of the two error terms:
for theta at most 1/8, N^(1/2) L^2 P is at most 29 N, so N^(1/2) is O(q Q L^(-2)). -/
theorem sqrt_le_qQ {N : ℕ} (hN : 1 ≤ N) {θ : ℝ} (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8) :
    Real.sqrt N * Real.log N ^ 2 * (N : ℝ) ^ θ ≤ 29 * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hlog : Real.log N ≤ (N : ℝ) ^ (3 / 16 : ℝ) / (3 / 16) :=
    Real.log_le_rpow_div hNpos.le (by norm_num)
  have hL2 : Real.log N ^ 2 ≤ (256 / 9) * (N : ℝ) ^ (3 / 8 : ℝ) := by
    have h1 : Real.log N ^ 2 ≤ ((N : ℝ) ^ (3 / 16 : ℝ) / (3 / 16)) ^ 2 :=
      pow_le_pow_left₀ hL0 hlog 2
    have h2 : ((N : ℝ) ^ (3 / 16 : ℝ) / (3 / 16)) ^ 2 = (256 / 9) * (N : ℝ) ^ (3 / 8 : ℝ) := by
      rw [div_pow, sq, ← Real.rpow_add hNpos]; norm_num; ring
    linarith
  have hexp : Real.sqrt N * (N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ θ ≤ N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    calc (N : ℝ) ^ (1 / 2 + 3 / 8 + θ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = N := Real.rpow_one _
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hP0 : 0 ≤ (N : ℝ) ^ θ := (Real.rpow_pos_of_pos hNpos θ).le
  calc Real.sqrt N * Real.log N ^ 2 * (N : ℝ) ^ θ ≤
        Real.sqrt N * ((256 / 9) * (N : ℝ) ^ (3 / 8 : ℝ)) * (N : ℝ) ^ θ := by gcongr
    _ = (256 / 9) * (Real.sqrt N * (N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ θ) := by ring
    _ ≤ (256 / 9) * N := by gcongr
    _ ≤ 29 * N := by nlinarith

/-- Gallagher 1975 p.130 display 9, proved from the printed steps above it:
A(1) = T + R, the main term from `principalMain_window_main`, the three R terms by the
Schwarz inequality `arc_integral_le_window`, and ||T|| at most 2 N^(1/2) L^(-1) from
J(0) asymptotic to N/log^2 N. The statement is exactly that of `principal_arc_integral`. -/
theorem principal_arc_integral_of_steps :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ,
        ∀ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
          ‖arcIntegral N ((N : ℝ) ^ θ) n q one one - (Jn N n : ℂ)‖ ≤
            K * (q * ((N : ℝ) / (N : ℝ) ^ θ) / Real.log N ^ 2 +
              Real.sqrt N / Real.log N * remNorm N ((N : ℝ) ^ θ) +
              remNorm N ((N : ℝ) ^ θ) ^ 2) := by
  obtain ⟨N₁, hN₁⟩ := LeanLab.Linnik.Decomp486c.principalMain_window_mean_eventually 1 one_pos
  refine ⟨248, 1 / 8, by norm_num, by norm_num, fun θ hθ hθ8 => ⟨max 4 N₁, fun N hN n q hq => ?_⟩⟩
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hcmp := sqrt_le_qQ (by omega : 1 ≤ N) hθ hθ8
  set P := (N : ℝ) ^ θ with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hNpos θ
  have hPsqrt : P ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hsqrt2 : 2 ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hNr
  have hsqrtsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hPN : P / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]; nlinarith
  set δ := P / (q * N) with hδ
  have hδpos : 0 < δ := by positivity
  have hδR : δ ≤ P / N := by
    rw [hδ, mul_comm, ← div_div]
    exact div_le_self (div_nonneg hPpos.le hNpos.le) hqr
  have hδ2 : δ ≤ 1 / 2 := hδR.trans hPN
  set T : ℝ → ℂ := principalMain N with hTdef
  set R : ℝ → ℂ := fun β => primeAmplitude one.2 N β - principalMain N β with hRdef
  have hTc : Continuous T := continuous_principalMain N
  have hRc : Continuous R := (continuous_primeAmplitude one.2 N).sub hTc
  have hec : Continuous (fun β : ℝ => LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β)) := by
    unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
  set F : (ℝ → ℂ) → (ℝ → ℂ) → ℝ → ℂ := fun f g β => star (f β) * g β * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β)
    with hF
  have hint (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
      Integrable (F f g) (volume.restrict (Set.Icc (-δ) δ)) :=
    (((continuous_star.comp hf).mul hg).mul hec).integrableOn_Icc
  have hfun : (fun β => star (primeAmplitude one.2 N β) * primeAmplitude one.2 N β *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β)) = fun β => F T T β + F T R β + F R T β + F R R β := by
    funext β
    have hA : primeAmplitude one.2 N β = T β + R β := by simp [hRdef, hTdef]
    simp only [hF]
    rw [hA, star_add]; ring
  have harc : arcIntegral N P n q one one =
      (∫ β in Set.Icc (-δ) δ, F T T β) + (∫ β in Set.Icc (-δ) δ, F T R β) +
        (∫ β in Set.Icc (-δ) δ, F R T β) + ∫ β in Set.Icc (-δ) δ, F R R β := by
    unfold arcIntegral
    show (∫ β in Set.Icc (-δ) δ, _) = _
    rw [hfun, integral_add, integral_add, integral_add]
    · exact hint T T hTc hTc
    · exact hint T R hTc hRc
    · exact (hint T T hTc hTc).add (hint T R hTc hRc)
    · exact hint R T hRc hTc
    · exact ((hint T T hTc hTc).add (hint T R hTc hRc)).add (hint R T hRc hTc)
    · exact hint R R hRc hRc
  have hmain : ‖(∫ β in Set.Icc (-δ) δ, F T T β) - (Jn N n : ℂ)‖ ≤
      8 * Real.sqrt N + 16 / Real.log N ^ 2 / δ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact principalMain_window_main (by omega) n hδpos hδ2
  set tn := Real.sqrt (∫ β in Set.Icc (-(P / N)) (P / N), ‖T β‖ ^ 2) with htn
  set rn := remNorm N P with hrn
  have hrn' : Real.sqrt (∫ β in Set.Icc (-(P / N)) (P / N), ‖R β‖ ^ 2) = rn := rfl
  have h1 : ‖∫ β in Set.Icc (-δ) δ, F T R β‖ ≤ tn * rn := by
    have := arc_integral_le_window T R hTc hRc δ (P / N) n hδR
    rw [hrn'] at this; exact this
  have h2 : ‖∫ β in Set.Icc (-δ) δ, F R T β‖ ≤ rn * tn := by
    have := arc_integral_le_window R T hRc hTc δ (P / N) n hδR
    rw [hrn'] at this; exact this
  have h3 : ‖∫ β in Set.Icc (-δ) δ, F R R β‖ ≤ rn * rn := by
    have := arc_integral_le_window R R hRc hRc δ (P / N) n hδR
    rw [hrn'] at this; exact this
  have htn_le : tn ≤ 2 * (Real.sqrt N / Real.log N) := by
    have hT2 := hN₁ N ((le_max_right _ _).trans hN) (P / N) hPN
    have hsq : (2 * (Real.sqrt N / Real.log N)) ^ 2 = 4 * ((N : ℝ) / Real.log N ^ 2) := by
      rw [mul_pow, div_pow, Real.sq_sqrt hNpos.le]; ring
    rw [htn, ← Real.sqrt_sq (by positivity : 0 ≤ 2 * (Real.sqrt N / Real.log N)), hsq]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
    linarith
  have hrn0 : 0 ≤ rn := Real.sqrt_nonneg _
  have htn0 : 0 ≤ tn := Real.sqrt_nonneg _
  set Qq := q * ((N : ℝ) / P) / Real.log N ^ 2 with hQq
  have hδQ : 16 / Real.log N ^ 2 / δ = 16 * Qq := by
    rw [hQq, hδ]; field_simp
  have hsQ : Real.sqrt N ≤ 29 * Qq := by
    rw [hQq, mul_div_assoc', le_div_iff₀ (by positivity)]
    have hq0 : 0 ≤ (q : ℝ) - 1 := by linarith
    have : Real.sqrt N * Real.log N ^ 2 * P ≤ 29 * N := hcmp
    rw [show 29 * (q * ((N : ℝ) / P)) = 29 * q * N / P by ring, le_div_iff₀ hPpos]
    nlinarith [mul_nonneg hq0 hNpos.le]
  rw [harc]
  have hsplit : (∫ β in Set.Icc (-δ) δ, F T T β) + (∫ β in Set.Icc (-δ) δ, F T R β) +
        (∫ β in Set.Icc (-δ) δ, F R T β) + (∫ β in Set.Icc (-δ) δ, F R R β) - (Jn N n : ℂ) =
      ((∫ β in Set.Icc (-δ) δ, F T T β) - (Jn N n : ℂ)) + (∫ β in Set.Icc (-δ) δ, F T R β) +
        (∫ β in Set.Icc (-δ) δ, F R T β) + (∫ β in Set.Icc (-δ) δ, F R R β) := by ring
  rw [hsplit]
  set X0 := (∫ β in Set.Icc (-δ) δ, F T T β) - (Jn N n : ℂ)
  set X1 := ∫ β in Set.Icc (-δ) δ, F T R β
  set X2 := ∫ β in Set.Icc (-δ) δ, F R T β
  set X3 := ∫ β in Set.Icc (-δ) δ, F R R β
  have hnorm : ‖X0 + X1 + X2 + X3‖ ≤ ‖X0‖ + ‖X1‖ + ‖X2‖ + ‖X3‖ := by
    have a1 := norm_add_le (X0 + X1 + X2) X3
    have a2 := norm_add_le (X0 + X1) X2
    have a3 := norm_add_le X0 X1
    linarith
  refine hnorm.trans ?_
  rw [hδQ] at hmain
  have hQ0 : 0 ≤ Qq := by positivity
  have htr : tn * rn ≤ 2 * (Real.sqrt N / Real.log N) * rn :=
    mul_le_mul_of_nonneg_right htn_le hrn0
  have hsl : 0 ≤ Real.sqrt N / Real.log N * rn := by positivity
  nlinarith

end LeanLab.Linnik.MajorArcEnergy.Leaves13Principal
