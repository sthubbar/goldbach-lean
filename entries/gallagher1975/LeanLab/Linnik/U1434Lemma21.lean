module

public import LeanLab.Linnik.U1429Display58
public import LeanLab.Linnik.LiLiuDisplay37PNT

/-!
Li-Liu, arXiv 2610.15784, Section 2, Lemma 2.1, display (13), with (8) to (12). Read by WebFetch on
the unversioned arxiv.org/html/2610.15784, 2026-10-21.

Lemma 2.1. For every sufficiently large even N,
  r₆''(N) ≥ 4(1-a-b)² N L⁶ - ∫_0^1 |S(α) F(G(α))|² dα + o(N L⁶).
Proof in the paper: with f = r₃' - aL r₂' - bL² r₁', g = max(f, 0), U_N the odd n < N,
  r₆''(N) ≥ ∑_{U_N} g(n) g(N-n) = ½ ∑ (g(n) + g(N-n))² - ∑ g(n)² ≥ (4/N)(∑ g)² - ∑ g²,
(11): ∑_{U_N} g ≥ ∑_{U_N} f = (1-a-b+o(1)) N L³ by the prime number theorem, and
(12): ∑_{U_N} g² ≤ ∑_n f(n)² = ∫_0^1 |S F(G)|² by Parseval.

This file proves `U1429Display58.Lemma21 κ` for every κ > 0, using the lab's PNT `theta_pnt`
(LiLiuDisplay37PNT, from the StrongPNT port), and derives `r6_lower'`, the statement of
`U1429Display58.r6_lower` with the hypothesis `Lemma21 κ` removed.

Unit U-1434, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1434Lemma21

open Set Real MeasureTheory Filter Finset
open LeanLab.Linnik.U1412Display53 (eC)
open LeanLab.Linnik.LiLiuDisplay37 (primesIn logw)
open LeanLab.Linnik.LiLiuLemma43 (SA)
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58

/-! ### The one-prime counts r_j'(n), display (8) -/

/-- `2^{ν₁} + ⋯ + 2^{ν_j}` with `ν i : Fin L` encoding `νᵢ - 1`. -/
def sv {j L : ℕ} (ν : Fin j → Fin L) : ℕ := ∑ i, 2 ^ ((ν i : ℕ) + 1)

/-- `r_j'(n) = ∑_{n = p + 2^{ν₁} + ⋯ + 2^{ν_j}, N₁ < p ≤ N, 1 ≤ νᵢ ≤ L} log p`. -/
noncomputable def rj (j N1 N L : ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ primesIn N1 N, ∑ ν : Fin j → Fin L, if p + sv ν = n then Real.log p else 0

/-- `f = r₃' - aL r₂' - bL² r₁'`, display (9). -/
noncomputable def ff (a b : ℝ) (N1 N L : ℕ) (n : ℕ) : ℝ :=
  rj 3 N1 N L n - a * L * rj 2 N1 N L n - b * (L : ℝ) ^ 2 * rj 1 N1 N L n

lemma rj_nonneg (j N1 N L n : ℕ) : 0 ≤ rj j N1 N L n :=
  sum_nonneg fun p _ => sum_nonneg fun ν _ => by
    split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_rfl

lemma sv_le {j L : ℕ} (ν : Fin j → Fin L) : sv ν ≤ j * 2 ^ L := by
  unfold sv
  calc ∑ i, 2 ^ ((ν i : ℕ) + 1) ≤ ∑ _i : Fin j, 2 ^ L :=
        sum_le_sum fun i _ => Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = j * 2 ^ L := by simp

lemma sv_even {j L : ℕ} (ν : Fin j → Fin L) : sv ν % 2 = 0 := by
  unfold sv
  have : ∑ i, 2 ^ ((ν i : ℕ) + 1) = 2 * ∑ i, 2 ^ (ν i : ℕ) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  omega

/-! ### Fourier side: S G^j and S F(G) as exponential sums -/

lemma e_eq_eC (x : ℝ) : LeanLab.PNTPort.LargeSieve.e x = eC x := by
  unfold LeanLab.PNTPort.LargeSieve.e eC; congr 1; push_cast; ring

lemma eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma Gs_fin (L : ℕ) (α : ℝ) : Gs L α = ∑ i : Fin L, eC (2 ^ ((i : ℕ) + 1) * α) := by
  unfold Gs
  rw [Fin.sum_univ_eq_sum_range (fun i => eC (2 ^ (i + 1) * α)) L]
  have : Finset.Icc 1 L = (range L).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [this, sum_map]
  rfl

lemma eC_prod {j : ℕ} (t : Fin j → ℝ) : ∏ i, eC (t i) = eC (∑ i, t i) := by
  unfold eC; rw [← Complex.exp_sum]; congr 1; push_cast; rw [mul_sum]

lemma Gs_pow (j L : ℕ) (α : ℝ) :
    Gs L α ^ j = ∑ ν : Fin j → Fin L, eC (sv ν * α) := by
  rw [Gs_fin, ← Fin.prod_const, Fintype.prod_sum]
  refine sum_congr rfl fun ν _ => ?_
  rw [eC_prod]; congr 1; unfold sv; push_cast; rw [sum_mul]

/-- `S(α) G(α)^j = ∑_{n < R} r_j'(n) e(nα)` for `R > N + j 2^L`. -/
lemma SG_pow (j N1 N L R : ℕ) (hR : N + j * 2 ^ L < R) (α : ℝ) :
    Sm N1 N α * Gs L α ^ j = SA (range R) (fun n => (rj j N1 N L n : ℂ)) α := by
  rw [Gs_pow]
  unfold Sm SA rj
  simp_rw [e_eq_eC]
  simp_rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun p hp => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  have hpN : p ≤ N := (mem_Ioc.mp (mem_filter.mp hp).1).2
  refine sum_congr rfl fun ν _ => ?_
  have hmem : p + sv ν ∈ range R := Finset.mem_range.mpr (by have := sv_le ν; omega)
  rw [Finset.sum_eq_single_of_mem (p + sv ν) hmem (fun x _ hx => by
    rw [if_neg (Ne.symm hx)]; simp), if_pos rfl, logw, mul_assoc, ← eC_add]
  congr 2; push_cast; ring

/-- `S(α) F(G(α)) = ∑_{n < R} f(n) e(nα)`, for `L ≥ 1`. -/
lemma SFG_sum (a b : ℝ) (N1 N L R : ℕ) (hL : 1 ≤ L) (hR : N + 3 * 2 ^ L < R) (α : ℝ) :
    Sm N1 N α * FG a b L α = SA (range R) (fun n => (ff a b N1 N L n : ℂ)) α := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have h : Sm N1 N α * FG a b L α = Sm N1 N α * Gs L α ^ 3 - a * L * (Sm N1 N α * Gs L α ^ 2) -
      b * (L : ℂ) ^ 2 * (Sm N1 N α * Gs L α ^ 1) := by
    unfold FG Qc; field_simp
  rw [h, SG_pow 3 N1 N L R hR, SG_pow 2 N1 N L R (by omega), SG_pow 1 N1 N L R (by omega)]
  unfold SA ff
  push_cast
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- **Display (12), equality form, PROVED**: `∫_0^1 |S F(G)|² = ∑_{n < R} f(n)²`. -/
theorem integral_SFG (κ : ℝ) (N R : ℕ) (hL : 1 ≤ Lfun N) (hR : N + 3 * 2 ^ Lfun N < R) :
    ∫ α in Icc (0 : ℝ) 1, SFG κ N α = ∑ n ∈ range R, ff (1 / 4) (1 / 16) (N1f κ N) N (Lfun N) n ^ 2 := by
  unfold SFG
  simp_rw [SFG_sum (1 / 4) (1 / 16) (N1f κ N) N (Lfun N) R hL hR]
  exact parseval _ _

/-! ### r₆'' as a convolution of r₃' -/

lemma inner_sum (A B N : ℕ) (x y : ℝ) :
    ∑ n ∈ range (N + 1), (if A = n then x else 0) * (if B = N - n then y else 0) =
      if A + B = N then x * y else 0 := by
  simp_rw [ite_mul, zero_mul]
  rw [sum_ite_eq (range (N + 1)) A]
  by_cases hA : A ≤ N
  · rw [if_pos (Finset.mem_range.mpr (by omega))]
    by_cases hB : A + B = N
    · rw [if_pos (by omega), if_pos hB, mul_comm]
    · rw [if_neg (by omega), if_neg hB]; simp
  · rw [if_neg (by simp; omega), if_neg (by omega)]

lemma split6 (N L p1 p2 : ℕ) (x : ℝ) :
    (∑ ν : Fin 6 → Fin L, if p1 + p2 + ∑ i, 2 ^ ((ν i : ℕ) + 1) = N then x else 0) =
      ∑ ν1 : Fin 3 → Fin L, ∑ ν2 : Fin 3 → Fin L,
        if p1 + sv ν1 + (p2 + sv ν2) = N then x else 0 := by
  rw [← Fintype.sum_prod_type', ← (Fin.appendEquiv 3 3).sum_comp]
  refine Fintype.sum_congr _ _ fun ν => ?_
  have h : p1 + p2 + ∑ i, 2 ^ (((Fin.appendEquiv 3 3 ν) i : ℕ) + 1) =
      p1 + sv ν.1 + (p2 + sv ν.2) := by
    simp only [Fin.appendEquiv_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right, sv]
    ring
  rw [h]

/-- **PROVED**: `r₆''(N) = ∑_{n ≤ N} r₃'(n) r₃'(N - n)`. -/
theorem r6pp_eq (N1 N L : ℕ) :
    r6pp N1 N L = ∑ n ∈ range (N + 1), rj 3 N1 N L n * rj 3 N1 N L (N - n) := by
  unfold r6pp
  simp_rw [split6]
  unfold rj
  simp_rw [Finset.sum_mul_sum]
  symm
  rw [Finset.sum_comm]
  refine sum_congr rfl fun p1 _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun p2 _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun ν1 _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun ν2 _ => ?_
  exact inner_sum _ _ _ _ _

/-! ### The odd n < N and the reflection n ↦ N - n -/

/-- `U_N = {1 ≤ n < N : n odd}`. -/
def UN (N : ℕ) : Finset ℕ := (range N).filter (fun n => n % 2 = 1)

lemma sum_UN_refl {N : ℕ} (hN : N % 2 = 0) (φ : ℕ → ℝ) :
    ∑ n ∈ UN N, φ (N - n) = ∑ n ∈ UN N, φ n := by
  refine Finset.sum_nbij' (fun n => N - n) (fun n => N - n) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [UN, Finset.mem_filter, Finset.mem_range] at ha ⊢; omega
  · intro a ha; simp only [UN, Finset.mem_filter, Finset.mem_range] at ha ⊢; omega
  · intro a ha; simp only [UN, Finset.mem_filter, Finset.mem_range] at ha ⊢; omega
  · intro a ha; simp only [UN, Finset.mem_filter, Finset.mem_range] at ha ⊢; omega
  · intro a _; rfl

lemma card_UN (N : ℕ) : ((UN N).card : ℝ) ≤ N / 2 := by
  have h : UN N ⊆ (range (N / 2)).image (fun k => 2 * k + 1) := by
    intro n hn
    simp only [UN, mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨n / 2, by omega, by omega⟩
  have h1 : (UN N).card ≤ N / 2 := (Finset.card_le_card h).trans (Finset.card_image_le.trans (by simp))
  calc ((UN N).card : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ N / 2 := Nat.cast_div_le

/-- **The Cauchy step of Lemma 2.1, PROVED**:
`∑_{U} g(n) g(N-n) ≥ (4/N)(∑_U g)² - ∑_U g²` for even `N > 0`. -/
theorem cauchy_step {N : ℕ} (hN : N % 2 = 0) (hN0 : 0 < N) (g : ℕ → ℝ) :
    4 / N * (∑ n ∈ UN N, g n) ^ 2 - ∑ n ∈ UN N, g n ^ 2 ≤ ∑ n ∈ UN N, g n * g (N - n) := by
  have hS : ∑ n ∈ UN N, (g n + g (N - n)) = 2 * ∑ n ∈ UN N, g n := by
    rw [sum_add_distrib, sum_UN_refl hN g]; ring
  have hQ : ∑ n ∈ UN N, (g n + g (N - n)) ^ 2 =
      2 * ∑ n ∈ UN N, g n ^ 2 + 2 * ∑ n ∈ UN N, g n * g (N - n) := by
    have h2 := sum_UN_refl hN (fun n => g n ^ 2)
    have : ∀ n, (g n + g (N - n)) ^ 2 = g n ^ 2 + g (N - n) ^ 2 + 2 * (g n * g (N - n)) :=
      fun n => by ring
    simp_rw [this, sum_add_distrib, h2, ← mul_sum]; ring
  have hC := sq_sum_le_card_mul_sum_sq (s := UN N) (f := fun n => g n + g (N - n))
  rw [hS, hQ] at hC
  have hcard := card_UN N
  have hnn : 0 ≤ ∑ n ∈ UN N, (g n + g (N - n)) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  rw [hQ] at hnn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have key : 4 * (∑ n ∈ UN N, g n) ^ 2 ≤
      N * (∑ n ∈ UN N, g n ^ 2 + ∑ n ∈ UN N, g n * g (N - n)) := by
    have := mul_le_mul_of_nonneg_right hcard hnn
    nlinarith
  have : 4 * (∑ n ∈ UN N, g n) ^ 2 / N ≤
      ∑ n ∈ UN N, g n ^ 2 + ∑ n ∈ UN N, g n * g (N - n) := by
    rw [div_le_iff₀ hNr]; linarith
  rw [div_mul_eq_mul_div]
  linarith

/-! ### Display (11): the sums of r_j' over U_N -/

lemma sum_UN_rj (j N1 N L : ℕ) : ∑ n ∈ UN N, rj j N1 N L n =
    ∑ p ∈ primesIn N1 N, ∑ ν : Fin j → Fin L, if p + sv ν ∈ UN N then Real.log p else 0 := by
  unfold rj
  rw [Finset.sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun ν _ => sum_ite_eq (UN N) _ _

lemma card_fun (j L : ℕ) : (Finset.univ : Finset (Fin j → Fin L)).card = L ^ j := by simp

lemma sum_primes_le_theta (N1 N : ℕ) :
    ∑ p ∈ primesIn N1 N, Real.log p ≤ Chebyshev.theta N := by
  have h := LiLiuDisplay37.sum_primesIn (Nat.zero_le N)
  rw [Nat.cast_zero, Chebyshev.theta_zero, sub_zero] at h
  rw [← h]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
  intro p hp
  simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
  exact ⟨⟨hp.2.pos, hp.1.2⟩, hp.2⟩

/-- **Upper half of (11), PROVED**: `∑_{U_N} r_j' ≤ L^j θ(N)`. -/
theorem sum_UN_rj_le (j N1 N L : ℕ) :
    ∑ n ∈ UN N, rj j N1 N L n ≤ (L : ℝ) ^ j * Chebyshev.theta N := by
  rw [sum_UN_rj]
  calc _ ≤ ∑ p ∈ primesIn N1 N, ∑ _ν : Fin j → Fin L, Real.log p :=
        sum_le_sum fun p _ => sum_le_sum fun ν _ => by
          split_ifs
          · exact le_rfl
          · exact Real.log_natCast_nonneg p
    _ = (L : ℝ) ^ j * ∑ p ∈ primesIn N1 N, Real.log p := by
        rw [mul_sum]; refine sum_congr rfl fun p _ => ?_
        rw [sum_const, card_fun, nsmul_eq_mul]; push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_primes_le_theta N1 N) (by positivity)

/-- **Lower half of (11) for r₃', PROVED**:
`∑_{U_N} r₃' ≥ L³ (θ(N - 3·2^L - 1) - θ(max(N₁, 2)))`. -/
theorem sum_UN_r3_ge (N1 N L : ℕ) :
    (L : ℝ) ^ 3 * (Chebyshev.theta ((N - (3 * 2 ^ L + 1) : ℕ) : ℝ) -
      Chebyshev.theta ((max N1 2 : ℕ) : ℝ)) ≤ ∑ n ∈ UN N, rj 3 N1 N L n := by
  rw [sum_UN_rj]
  have hnn : 0 ≤ ∑ p ∈ primesIn N1 N, ∑ ν : Fin 3 → Fin L,
      (if p + sv ν ∈ UN N then Real.log p else 0) :=
    sum_nonneg fun p _ => sum_nonneg fun ν _ => by
      split_ifs
      · exact Real.log_natCast_nonneg p
      · exact le_rfl
  by_cases hMK : max N1 2 ≤ N - (3 * 2 ^ L + 1)
  · rw [← LiLiuDisplay37.sum_primesIn hMK, mul_sum]
    calc _ = ∑ p ∈ primesIn (max N1 2) (N - (3 * 2 ^ L + 1)), ∑ ν : Fin 3 → Fin L,
          (if p + sv ν ∈ UN N then Real.log p else 0) := by
          refine sum_congr rfl fun p hp => ?_
          simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
          have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.2.odd_of_ne_two (by omega))
          have hin : ∀ ν : Fin 3 → Fin L, p + sv ν ∈ UN N := fun ν => by
            have h1 := sv_le ν; have h2 := sv_even ν
            simp only [UN, Finset.mem_filter, Finset.mem_range]; omega
          simp_rw [if_pos (hin _)]
          rw [sum_const, card_fun, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => sum_nonneg fun ν _ => by
            split_ifs
            · exact Real.log_natCast_nonneg p
            · exact le_rfl
          intro p hp
          simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
          exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · have : Chebyshev.theta ((N - (3 * 2 ^ L + 1) : ℕ) : ℝ) ≤
        Chebyshev.theta ((max N1 2 : ℕ) : ℝ) :=
      Chebyshev.theta_mono (by exact_mod_cast (show N - (3 * 2 ^ L + 1) ≤ max N1 2 by omega))
    have h2 : (L : ℝ) ^ 3 * (Chebyshev.theta ((N - (3 * 2 ^ L + 1) : ℕ) : ℝ) -
        Chebyshev.theta ((max N1 2 : ℕ) : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith

/-! ### The prime number theorem inputs: 3·2^L = o(N), N₁ = o(N) -/

lemma two_pow_small {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, 3 * (2 : ℝ) ^ Lfun N + 1 ≤ η * N := by
  have hx : Tendsto (fun N : ℕ => Real.logb 2 N) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun N : ℕ => Real.sqrt (Real.logb 2 N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hx
  filter_upwards [hx.eventually_ge_atTop 1, hs.eventually_ge_atTop (Real.logb 2 (8 / η)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / η), eventually_ge_atTop 1]
    with N h1 h2 h3 hN1
  set x := Real.logb 2 N with hxdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsx : Real.sqrt x ≤ x := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hL : (Lfun N : ℝ) ≤ x - Real.sqrt x := Nat.floor_le (by linarith)
  have h2L : (2 : ℝ) ^ Lfun N ≤ N / 2 ^ Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hNpos,
      ← Real.rpow_sub (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hL
  have h8 : 8 / η ≤ (2 : ℝ) ^ Real.sqrt x := by
    calc 8 / η = (2 : ℝ) ^ Real.logb 2 (8 / η) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  have hpos : (0 : ℝ) < 2 ^ Real.sqrt x := by positivity
  have h3' : N / 2 ^ Real.sqrt x ≤ η * N / 8 := by
    rw [div_le_iff₀ hpos]
    have : η * N / 8 * (8 / η) = N := by field_simp
    have := mul_le_mul_of_nonneg_left h8 (by positivity : (0 : ℝ) ≤ η * N / 8)
    linarith
  have : 2 ≤ η * N := by rwa [div_le_iff₀' hη] at h3
  linarith

lemma N1_small {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ((max (N1f κ N) 2 : ℕ) : ℝ) ≤ η * N := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-κ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (ge_mem_nhds (half_pos hη)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 / η), eventually_ge_atTop 1]
    with N h1 h2 hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : (N : ℝ) ^ (1 - κ) = N * (N : ℝ) ^ (-κ) := by
    rw [sub_eq_add_neg, Real.rpow_add hNpos, Real.rpow_one]
  have hfl : (N1f κ N : ℝ) ≤ η / 2 * N := by
    calc (N1f κ N : ℝ) ≤ (N : ℝ) ^ (1 - κ) := Nat.floor_le (by positivity)
      _ ≤ η / 2 * N := by rw [hr]; nlinarith
  have h2' : 2 ≤ η / 2 * N := by
    rw [div_le_iff₀' hη] at h2; linarith
  rw [Nat.cast_max]; push_cast
  exact max_le (by linarith) (by linarith)

/-- **The PNT window, PROVED from `theta_pnt`**: for `0 < ε ≤ 1`, eventually
`θ(N - 3·2^L - 1) - θ(max(N₁,2)) ≥ (1-ε)N` and `θ(N) ≤ (1+ε)N`. -/
theorem pnt_window {κ : ℝ} (hκ : 0 < κ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      (1 - ε) * N ≤ Chebyshev.theta ((N - (3 * 2 ^ Lfun N + 1) : ℕ) : ℝ) -
        Chebyshev.theta ((max (N1f κ N) 2 : ℕ) : ℝ) ∧ Chebyshev.theta N ≤ (1 + ε) * N := by
  obtain ⟨C, hC⟩ := LiLiuDisplay37PNT.theta_pnt (ε / 4) (by positivity)
  have hC0 : 0 ≤ C := by have := hC 0; simp at this; linarith
  filter_upwards [two_pow_small (η := ε / 4) (by positivity), N1_small hκ (η := ε / 8)
    (by positivity), tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 * C / ε)]
    with N h2 hM hCN
  have hCN' : 8 * C ≤ ε * N := by rwa [div_le_iff₀' hε] at hCN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  set K := N - (3 * 2 ^ Lfun N + 1) with hK
  set M := max (N1f κ N) 2
  have hKle : 3 * 2 ^ Lfun N + 1 ≤ N := by
    have : ((3 * 2 ^ Lfun N + 1 : ℕ) : ℝ) ≤ N := by push_cast; nlinarith
    exact_mod_cast this
  have hKr : (K : ℝ) = N - (3 * 2 ^ Lfun N + 1 : ℝ) := by
    rw [hK, Nat.cast_sub hKle]; push_cast; ring
  have hθK := hC K
  have hθM := hC M
  have hθN := hC N
  rw [abs_le] at hθK hθM hθN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  constructor
  · have hKN : (1 - ε / 4) * N ≤ (K : ℝ) := by rw [hKr]; linarith
    have hq : (1 - ε / 2) * N ≤ (1 - ε / 4) * K := by
      have := mul_le_mul_of_nonneg_left hKN (by linarith : (0 : ℝ) ≤ 1 - ε / 4)
      nlinarith
    nlinarith
  · nlinarith

/-! ### Lemma 2.1 -/

lemma g_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (N1 N L n : ℕ) :
    max (ff a b N1 N L n) 0 ≤ rj 3 N1 N L n := by
  unfold ff
  have h2 := rj_nonneg 2 N1 N L n
  have h1 := rj_nonneg 1 N1 N L n
  have h3 := rj_nonneg 3 N1 N L n
  have : 0 ≤ a * L * rj 2 N1 N L n := by positivity
  have : 0 ≤ b * (L : ℝ) ^ 2 * rj 1 N1 N L n := by positivity
  exact max_le (by linarith) h3

lemma g_sq_le (x : ℝ) : max x 0 ^ 2 ≤ x ^ 2 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, zero_pow two_ne_zero]; exact sq_nonneg x
  · rw [max_eq_left h]

/-- **Lemma 2.1 of Li-Liu, PROVED for every κ > 0**, in the form `U1429Display58.Lemma21 κ`:
for every `δ > 0`, for all large even `N`,
`r₆''(N) ≥ 4(1-a-b)² N L⁶ - ∫_0^1 |S F(G)|² - δ N L⁶` at `a = 1/4`, `b = 1/16`. -/
theorem lemma21 {κ : ℝ} (hκ : 0 < κ) : Lemma21 κ := by
  intro δ hδ
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (δ / 32) (1 / 8) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by positivity) (by norm_num)
  have hε8 : ε ≤ 1 / 8 := by rw [hεdef]; exact min_le_right _ _
  have hεδ : ε ≤ δ / 32 := by rw [hεdef]; exact min_le_left _ _
  filter_upwards [pnt_window hκ hε0 (by linarith), eventually_Lfun_ge_one,
    eventually_ge_atTop 1] with N hpnt hL hN1 hEven
  obtain ⟨hlo, hup⟩ := hpnt
  have hN2 : N % 2 = 0 := Nat.even_iff.mp hEven
  set L := Lfun N
  set N1 := N1f κ N
  set f := ff (1 / 4) (1 / 16) N1 N L
  set g : ℕ → ℝ := fun n => max (f n) 0 with hg
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLr : (0 : ℝ) ≤ L := by positivity
  -- step 1: r₆'' ≥ ∑_U g(n) g(N-n)
  have hgle : ∀ n, g n ≤ rj 3 N1 N L n := fun n => g_le (by norm_num) (by norm_num) N1 N L n
  have hg0 : ∀ n, 0 ≤ g n := fun n => le_max_right _ _
  have hUsub : UN N ⊆ range (N + 1) := fun n hn => by
    simp only [UN, Finset.mem_filter, Finset.mem_range] at hn ⊢; omega
  have step1 : ∑ n ∈ UN N, g n * g (N - n) ≤ r6pp N1 N L := by
    rw [r6pp_eq]
    calc _ ≤ ∑ n ∈ UN N, rj 3 N1 N L n * rj 3 N1 N L (N - n) :=
          sum_le_sum fun n _ => mul_le_mul (hgle n) (hgle _) (hg0 _) (rj_nonneg _ _ _ _ _)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hUsub fun n _ _ =>
          mul_nonneg (rj_nonneg _ _ _ _ _) (rj_nonneg _ _ _ _ _)
  -- step 2: Cauchy
  have step2 := cauchy_step hN2 (by omega) g
  -- step 3: Parseval
  have step3 : ∑ n ∈ UN N, g n ^ 2 ≤ ∫ α in Icc (0 : ℝ) 1, SFG κ N α := by
    rw [integral_SFG κ N (N + 3 * 2 ^ L + 1) hL (Nat.lt_succ_self _)]
    calc _ ≤ ∑ n ∈ UN N, f n ^ 2 := sum_le_sum fun n _ => g_sq_le _
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun n hn => by
          simp only [UN, Finset.mem_filter, Finset.mem_range] at hn ⊢; omega)
          fun n _ _ => sq_nonneg _
  -- step 4: display (11)
  have h3 := sum_UN_r3_ge N1 N L
  have h2 := sum_UN_rj_le 2 N1 N L
  have h1 := sum_UN_rj_le 1 N1 N L
  have hsf : ∑ n ∈ UN N, f n = ∑ n ∈ UN N, rj 3 N1 N L n -
      1 / 4 * L * ∑ n ∈ UN N, rj 2 N1 N L n - 1 / 16 * (L : ℝ) ^ 2 * ∑ n ∈ UN N, rj 1 N1 N L n := by
    simp only [f, ff, sum_sub_distrib, mul_sum]
  set m : ℝ := 11 / 16 - 21 / 16 * ε with hm
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have step4 : N * L ^ 3 * m ≤ ∑ n ∈ UN N, g n := by
    have hfg : ∑ n ∈ UN N, f n ≤ ∑ n ∈ UN N, g n := sum_le_sum fun n _ => le_max_left _ _
    have hL3 : (0 : ℝ) ≤ (L : ℝ) ^ 3 := by positivity
    have a3 : (L : ℝ) ^ 3 * ((1 - ε) * N) ≤ ∑ n ∈ UN N, rj 3 N1 N L n :=
      le_trans (mul_le_mul_of_nonneg_left hlo hL3) h3
    have a2 : 1 / 4 * L * ∑ n ∈ UN N, rj 2 N1 N L n ≤ 1 / 4 * L * ((L : ℝ) ^ 2 * ((1 + ε) * N)) :=
      mul_le_mul_of_nonneg_left (le_trans h2 (mul_le_mul_of_nonneg_left hup (by positivity)))
        (by positivity)
    have a1 : 1 / 16 * (L : ℝ) ^ 2 * ∑ n ∈ UN N, rj 1 N1 N L n ≤
        1 / 16 * (L : ℝ) ^ 2 * ((L : ℝ) ^ 1 * ((1 + ε) * N)) :=
      mul_le_mul_of_nonneg_left (le_trans h1 (mul_le_mul_of_nonneg_left hup (by positivity)))
        (by positivity)
    have : N * (L : ℝ) ^ 3 * m = (L : ℝ) ^ 3 * ((1 - ε) * N) -
        1 / 4 * L * ((L : ℝ) ^ 2 * ((1 + ε) * N)) -
        1 / 16 * (L : ℝ) ^ 2 * ((L : ℝ) ^ 1 * ((1 + ε) * N)) := by rw [hm]; ring
    linarith
  -- step 5: assemble
  have hX0 : (0 : ℝ) ≤ N * (L : ℝ) ^ 6 := by positivity
  have hsq : (N * (L : ℝ) ^ 3 * m) ^ 2 ≤ (∑ n ∈ UN N, g n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) step4 2
  have h4 : 4 / N * (N * (L : ℝ) ^ 3 * m) ^ 2 = 4 * m ^ 2 * (N * (L : ℝ) ^ 6) := by
    field_simp
  have h5 : 4 / N * (N * (L : ℝ) ^ 3 * m) ^ 2 ≤ 4 / N * (∑ n ∈ UN N, g n) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hmc : 4 * (1 - 1 / 4 - 1 / 16 : ℝ) ^ 2 - δ ≤ 4 * m ^ 2 := by rw [hm]; nlinarith
  have h6 := mul_le_mul_of_nonneg_right hmc hX0
  have h7 : 4 * (1 - 1 / 4 - 1 / 16 : ℝ) ^ 2 * N * (L : ℝ) ^ 6 - δ * (N * (L : ℝ) ^ 6) =
      (4 * (1 - 1 / 4 - 1 / 16 : ℝ) ^ 2 - δ) * (N * (L : ℝ) ^ 6) := by ring
  linarith

/-- Vacuity of the hypotheses of `lemma21`: `κ = 1/2` satisfies `0 < κ`, so `Lemma21 (1/2)`
holds outright. -/
theorem lemma21_half : Lemma21 (1 / 2) := lemma21 (by norm_num)

/-! ### r₆''(N) ≫ N L⁶ with Lemma 2.1 discharged -/

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON `Display30Upper`, `Minor35`, `MinorSup1924 P`, the
conditions (24) on `P`, and the cited constants of `k6_wired`**: Platt-Trudgian
`C₀R₀ < 1.2784421041`, Johnston-Trudgian `A(2), A(3)`, the tail `T`. This is
`U1429Display58.r6_lower` with the hypothesis `Lemma21 κ` removed, by `lemma21`. -/
theorem r6_lower' {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) :
    ∃ e1 > 0, ∀ e0 : ℝ, 0 ≤ e0 → e0 < e1 → ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      Display30Upper κ P (∑ i, ∑ j, (LiLiu.v i : ℝ) * ((LiLiu.Astar i j : ℝ) + T i j) *
        (LiLiu.v j : ℝ)) e0 →
      Minor35 κ P CR e0 →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  obtain ⟨e1, he1, h⟩ := r6_lower T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33
  exact ⟨e1, he1, fun e0 he0 he01 κ hκ P hP11 hPup hP2 hMS h30 h35 =>
    h e0 he0 he01 hκ P hP11 hPup hP2 hMS h30 h35 (lemma21 hκ)⟩

end LeanLab.Linnik.U1434Lemma21
