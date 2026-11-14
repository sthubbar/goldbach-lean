module

public import LeanLab.Linnik.U7200Minor35

/-!
Li-Liu, arXiv 2610.15784, Section 4, display (33) from the cited inputs (31) and (20), with
the Parseval step of (33), the bound (32) and the prime number theorem for `R(0)`. Read by
WebFetch on the unversioned arxiv.org/html/2610.15784, 2026-10-21.

The paper's argument for (33):
  ∫_0^1 |S G|² = L R(0) + ∑_{1 ≤ ν ≠ μ ≤ L} R(2^μ - 2^ν),
  R(h) = ∑_{N₁ < p, p' ≤ N, p - p' = h} log p log p' ≤ log² N · #{p, p' ≤ N : p - p' = h},
  (31) bounds the count by (C₁ + o(1))/2 · N 𝔖(h)/log² N, (20) bounds ∑_{ν ≠ μ} 𝔖 by
  2L²(C₀R₀ + o(1)), and L R(0) ≤ L log N θ(N) ≤ N L²(log 2 + o(1)) by the prime number theorem
  and L = log₂ N + O(√log N).

Contents.
* `r1`, `SG_r1`: `S(α)G(α) = ∑_{n < R} r₁'(n) e(nα)`. PROVED.
* `sq_sum_expand`: `∑_n (∑_x [g x = n] w x)² = ∑_{x,y} [g x = g y] w x w y`. PROVED.
* `integral_SG_le`: the finite form of (32) and the Parseval step of (33),
  `∫_0^1 |S G|² ≤ L ∑_p log² p + ∑_{ν,μ} [ν ≠ μ] log² N · pairCount N (2^μ - 2^ν)`. PROVED.
* `diag_small`: `L ∑_p log² p ≤ N L² (log 2 + δ)` eventually, from `theta_pnt`. PROVED.
* `display33`: `Display33 κ CR` from `Display31 6.7814` and `SingSum20 CR`. PROVED as an
  implication, so `Display33` is CONDITIONAL ON (31) and (20) only.
* `r6_lower'''`: r₆''(N) ≫ N L⁶, CONDITIONAL ON `Display30Upper`, `Display31 6.7814`,
  `SingSum20 CR`, `Display34Lower`, `MinorSup1924 P`, conditions (24) and the cited constants of
  `k6_wired`; `Display33` is gone.

Unit U-7203, CLOUD MANUAL-N2. AI-written Lean code, Claude. KNOWN mathematics, the paper's own
argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U7203Display33

open Set Real MeasureTheory Filter Finset
open LeanLab.Linnik.U1412Display53 (eC)
open LeanLab.Linnik.LiLiuDisplay37 (primesIn logw)
open LeanLab.Linnik.LiLiuLemma43 (SA)
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7200Minor35

/-! ### Parseval for `S G` -/

/-- `r₁'(n) = ∑_{n = p + 2^ν, N₁ < p ≤ N, 1 ≤ ν ≤ L} log p`. -/
noncomputable def r1 (N1 N L : ℕ) (n : ℕ) : ℝ :=
  ∑ x ∈ primesIn N1 N ×ˢ Finset.Icc 1 L, if x.1 + 2 ^ x.2 = n then Real.log x.1 else 0

/-- `S(α) G(α) = ∑_{n < R} r₁'(n) e(nα)` for `R > N + 2^L`. PROVED. -/
lemma SG_r1 (N1 N L R : ℕ) (hR : N + 2 ^ L < R) (α : ℝ) :
    Sm N1 N α * Gs L α = SA (range R) (fun n => (r1 N1 N L n : ℂ)) α := by
  unfold Sm SA r1 Gs
  simp_rw [U1434Lemma21.e_eq_eC, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_product]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hpN : p ≤ N := (mem_Ioc.mp (mem_filter.mp hp).1).2
  have hνL : ν ≤ L := (Finset.mem_Icc.mp hν).2
  have hmem : p + 2 ^ ν ∈ range R := Finset.mem_range.mpr (by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hνL; omega)
  rw [Finset.sum_eq_single_of_mem (p + 2 ^ ν) hmem (fun x _ hx => by
    rw [if_neg (Ne.symm hx)]; simp), if_pos rfl, logw, mul_assoc, ← U1434Lemma21.eC_add]
  congr 2; push_cast; ring

/-- **Expansion of a square of a counting sum, PROVED.** -/
lemma sq_sum_expand {ι : Type*} (A : Finset ι) (g : ι → ℕ) (w : ι → ℝ) (R : ℕ)
    (hg : ∀ x ∈ A, g x < R) :
    ∑ n ∈ range R, (∑ x ∈ A, if g x = n then w x else 0) ^ 2 =
      ∑ x ∈ A, ∑ y ∈ A, if g x = g y then w x * w y else 0 := by
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single_of_mem (g x) (Finset.mem_range.mpr (hg x hx)) (fun n _ hn => by
    rw [if_neg (Ne.symm hn), zero_mul])]
  by_cases h : g x = g y
  · simp [h]
  · have h' : g y ≠ g x := fun e => h e.symm
    simp [h, h']

lemma log_le_logN {N1 N p : ℕ} (hp : p ∈ primesIn N1 N) : Real.log p ≤ Real.log N := by
  have h := mem_filter.mp hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.2.one_lt.le
  exact Real.log_le_log (by linarith) (by exact_mod_cast (mem_Ioc.mp h.1).2)

lemma log_nonneg_p (p : ℕ) : 0 ≤ Real.log p := Real.log_natCast_nonneg p

/-- One diagonal block: `∑_{p,p'} [p + 2^ν = p' + 2^ν] log p log p' = ∑_p log² p`. -/
lemma diag_block (P : Finset ℕ) (ν : ℕ) :
    ∑ p ∈ P, ∑ p' ∈ P, (if p + 2 ^ ν = p' + 2 ^ ν then Real.log p * Real.log p' else 0) =
      ∑ p ∈ P, Real.log p ^ 2 := by
  simp only [Nat.add_right_cancel_iff]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_ite_eq, if_pos hp, sq]

/-- One off-diagonal block, (32) in finite form:
`∑_{p,p'} [p + 2^ν = p' + 2^μ] log p log p' ≤ log² N · pairCount N (2^μ - 2^ν)`. PROVED. -/
lemma offdiag_block (N1 N ν μ : ℕ) :
    ∑ p ∈ primesIn N1 N, ∑ p' ∈ primesIn N1 N,
        (if p + 2 ^ ν = p' + 2 ^ μ then Real.log p * Real.log p' else 0) ≤
      Real.log N ^ 2 * pairCount N ((2 : ℤ) ^ μ - 2 ^ ν) := by
  have hsp := Finset.sum_product' (s := primesIn N1 N) (t := primesIn N1 N) (f := fun p p' : ℕ =>
    if p + 2 ^ ν = p' + 2 ^ μ then Real.log p * Real.log p' else 0)
  rw [← hsp, ← Finset.sum_filter]
  calc _ ≤ ∑ _x ∈ (primesIn N1 N ×ˢ primesIn N1 N).filter
          (fun x : ℕ × ℕ => x.1 + 2 ^ ν = x.2 + 2 ^ μ), Real.log N ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hx' := Finset.mem_product.mp (mem_filter.mp hx).1
        rw [sq]
        exact mul_le_mul (log_le_logN hx'.1) (log_le_logN hx'.2) (log_nonneg_p _)
          (Real.log_natCast_nonneg N)
    _ = Real.log N ^ 2 * ((primesIn N1 N ×ˢ primesIn N1 N).filter
          (fun x : ℕ × ℕ => x.1 + 2 ^ ν = x.2 + 2 ^ μ)).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        unfold pairCount
        refine Nat.cast_le.mpr (Finset.card_le_card fun x hx => ?_)
        · show x ∈ _
          obtain ⟨hxP, hxe⟩ := mem_filter.mp hx
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxP
          have sub : ∀ {q}, q ∈ primesIn N1 N → q ∈ primesIn 0 N := fun {q} hq => by
            have := mem_filter.mp hq
            exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨this.2.pos, (mem_Ioc.mp this.1).2⟩, this.2⟩
          refine mem_filter.mpr ⟨Finset.mem_product.mpr ⟨sub h1, sub h2⟩, ?_⟩
          have := congrArg (Nat.cast : ℕ → ℤ) hxe
          push_cast at this
          linarith

/-- **The Parseval step of (33) and (32), finite form, PROVED**:
`∫_0^1 |S G|² ≤ L ∑_{N₁ < p ≤ N} log² p + ∑_{ν ≠ μ} log² N · pairCount N (2^μ - 2^ν)`. -/
theorem integral_SG_le (κ : ℝ) (N : ℕ) :
    ∫ α in Icc (0 : ℝ) 1, SG κ N α ≤
      (Lfun N : ℝ) * ∑ p ∈ primesIn (N1f κ N) N, Real.log p ^ 2 +
        ∑ ν ∈ Finset.Icc 1 (Lfun N), ∑ μ ∈ Finset.Icc 1 (Lfun N),
          (if ν = μ then 0 else Real.log N ^ 2 * pairCount N ((2 : ℤ) ^ μ - 2 ^ ν)) := by
  set L := Lfun N
  set P := primesIn (N1f κ N) N
  set I := Finset.Icc 1 L
  have hR : N + 2 ^ L < N + 2 ^ L + 1 := by omega
  have h1 : ∀ α, SG κ N α =
      ‖SA (range (N + 2 ^ L + 1)) (fun n => (r1 (N1f κ N) N L n : ℂ)) α‖ ^ 2 := fun α => by
    unfold SG; rw [SG_r1 (N1f κ N) N L _ hR]
  simp_rw [h1]
  rw [parseval]
  unfold r1
  have hexp := sq_sum_expand (P ×ˢ I) (fun x => x.1 + 2 ^ x.2) (fun x => Real.log x.1)
    (N + 2 ^ L + 1) (fun x hx => by
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
      have hpN : x.1 ≤ N := (mem_Ioc.mp (mem_filter.mp h1).1).2
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Finset.mem_Icc.mp h2).2
      omega)
  rw [hexp, Finset.sum_product]
  simp_rw [Finset.sum_product]
  have hre : ∑ p ∈ P, ∑ ν ∈ I, ∑ p' ∈ P, ∑ μ ∈ I,
      (if p + 2 ^ ν = p' + 2 ^ μ then Real.log p * Real.log p' else 0) =
      ∑ ν ∈ I, ∑ μ ∈ I, ∑ p ∈ P, ∑ p' ∈ P,
      (if p + 2 ^ ν = p' + 2 ^ μ then Real.log p * Real.log p' else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    exact (Finset.sum_congr rfl fun p _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hre]
  calc _ ≤ ∑ ν ∈ I, ∑ μ ∈ I, ((if ν = μ then ∑ p ∈ P, Real.log p ^ 2 else 0) +
        (if ν = μ then 0 else Real.log N ^ 2 * pairCount N ((2 : ℤ) ^ μ - 2 ^ ν))) := by
        refine Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun μ _ => ?_
        by_cases h : ν = μ
        · subst h; rw [if_pos rfl, if_pos rfl, add_zero, diag_block]
        · rw [if_neg h, if_neg h, zero_add]; exact offdiag_block _ N ν μ
    _ = _ := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        simp only [Finset.sum_ite_eq, I, Finset.mem_Icc]
        rw [Finset.sum_ite_of_true (fun ν hν => Finset.mem_Icc.mp hν), Finset.sum_const,
          Nat.card_Icc, nsmul_eq_mul]
        simp

/-! ### The asymptotic inputs: `L → ∞`, and `L R(0) ≤ N L² (log 2 + o(1))` -/

lemma Lfun_tendsto : Tendsto Lfun atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hx : Tendsto (fun N : ℕ => Real.logb 2 N) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hx.eventually_ge_atTop (max 4 (2 * (b : ℝ) + 2))] with N hN
  have hl := Lfun_lower N
  set t := Real.logb 2 N
  have h4 := le_max_left 4 (2 * (b : ℝ) + 2)
  have hb := le_max_right 4 (2 * (b : ℝ) + 2)
  have hs : Real.sqrt t ≤ t / 2 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have : (b : ℝ) < Lfun N := by linarith
  exact_mod_cast this.le

/-- **The diagonal term of (33), PROVED from `theta_pnt`**: for every `δ > 0`, eventually
`L ∑_{N₁ < p ≤ N} log² p ≤ N L² (log 2 + δ)`. -/
theorem diag_small (κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (Lfun N : ℝ) * ∑ p ∈ primesIn (N1f κ N) N, Real.log p ^ 2 ≤
      N * (Lfun N : ℝ) ^ 2 * (Real.log 2 + δ) := by
  obtain ⟨C, hC⟩ := LiLiuDisplay37PNT.theta_pnt (δ / 8) (by positivity)
  have hx : Tendsto (fun N : ℕ => Real.logb 2 N) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun N : ℕ => Real.sqrt (Real.logb 2 N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hx
  filter_upwards [hs.eventually_ge_atTop (3 * (1 + δ) / δ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 * |C| / δ), eventually_ge_atTop 2]
    with N hsN hCN hN2
  set x := Real.logb 2 N with hxdef
  set s := Real.sqrt x
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h3 : 3 ≤ 3 * (1 + δ) / δ := by rw [le_div_iff₀ hδ]; linarith
  have hs1 : 1 ≤ s := by linarith
  have hx0 : 0 ≤ x := by
    by_contra h
    push_neg at h
    have : s = 0 := Real.sqrt_eq_zero_of_nonpos h.le
    linarith
  have hsx : s * s = x := Real.mul_self_sqrt hx0
  have hlogN : Real.log N = x * Real.log 2 := by
    rw [hxdef, Real.logb, div_mul_cancel₀ _ hl2.ne']
  have hL : x - s - 1 < Lfun N := Lfun_lower N
  have hθ : Chebyshev.theta N ≤ (1 + δ / 4) * N := by
    have h1 := hC N
    have h2 : |C| ≤ δ * N / 8 := by
      rw [div_le_iff₀ hδ] at hCN; linarith
    have := le_abs_self C
    have := (abs_le.mp h1).2
    linarith
  have hsum : ∑ p ∈ primesIn (N1f κ N) N, Real.log p ^ 2 ≤ Real.log N * Chebyshev.theta N := by
    calc _ ≤ ∑ p ∈ primesIn (N1f κ N) N, Real.log N * Real.log p :=
          Finset.sum_le_sum fun p hp => by
            rw [sq]; exact mul_le_mul_of_nonneg_right (log_le_logN hp) (log_nonneg_p p)
      _ = Real.log N * ∑ p ∈ primesIn (N1f κ N) N, Real.log p := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (U1434Lemma21.sum_primes_le_theta _ N)
          (Real.log_natCast_nonneg N)
  have hδs : 3 * (1 + δ) ≤ δ * s := by
    rw [div_le_iff₀ hδ] at hsN; linarith
  have hkey : x * Real.log 2 * (1 + δ / 4) ≤ (x - s - 1) * (Real.log 2 + δ) := by
    rw [← hsx]
    have hA : (s + 1) * (Real.log 2 + δ) ≤ 2 * s * (1 + δ) := by nlinarith
    have hB : 2 * s * (1 + δ) ≤ 3 / 4 * δ * (s * s) := by nlinarith
    nlinarith
  have hmain : Real.log N * Chebyshev.theta N ≤ N * Lfun N * (Real.log 2 + δ) := by
    calc Real.log N * Chebyshev.theta N ≤ Real.log N * ((1 + δ / 4) * N) :=
          mul_le_mul_of_nonneg_left hθ (Real.log_natCast_nonneg N)
      _ = N * (x * Real.log 2 * (1 + δ / 4)) := by rw [hlogN]; ring
      _ ≤ N * ((x - s - 1) * (Real.log 2 + δ)) := mul_le_mul_of_nonneg_left hkey hNpos.le
      _ ≤ N * (Lfun N * (Real.log 2 + δ)) := by gcongr
      _ = _ := by ring
  have hL0 : (0 : ℝ) ≤ Lfun N := Nat.cast_nonneg _
  calc _ ≤ (Lfun N : ℝ) * (Real.log N * Chebyshev.theta N) :=
        mul_le_mul_of_nonneg_left hsum hL0
    _ ≤ (Lfun N : ℝ) * (N * Lfun N * (Real.log 2 + δ)) := mul_le_mul_of_nonneg_left hmain hL0
    _ = _ := by ring

/-! ### Display (33) from (31) and (20) -/

/-- The conditions of (31) for `h = 2^μ - 2^ν`, `1 ≤ ν ≠ μ ≤ L`, `2^L < N`. -/
lemma h_conds {ν μ L N : ℕ} (hν : ν ∈ Finset.Icc 1 L) (hμ : μ ∈ Finset.Icc 1 L) (hne : ν ≠ μ)
    (hLN : (2 : ℤ) ^ L < N) :
    ((2 : ℤ) ^ μ - 2 ^ ν) ≠ 0 ∧ Even ((2 : ℤ) ^ μ - 2 ^ ν) ∧ |(2 : ℤ) ^ μ - 2 ^ ν| < N := by
  obtain ⟨hν1, hνL⟩ := Finset.mem_Icc.mp hν
  obtain ⟨hμ1, hμL⟩ := Finset.mem_Icc.mp hμ
  refine ⟨fun e => hne ?_, (even_two.pow_of_ne_zero (by omega)).sub
    (even_two.pow_of_ne_zero (by omega)), ?_⟩
  · have e' : (2 : ℤ) ^ μ = 2 ^ ν := by linarith
    have : 2 ^ μ = 2 ^ ν := by exact_mod_cast e'
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  · have a1 : (2 : ℤ) ^ μ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hμL
    have a2 : (2 : ℤ) ^ ν ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hνL
    have b1 : (0 : ℤ) < 2 ^ μ := by positivity
    have b2 : (0 : ℤ) < 2 ^ ν := by positivity
    rw [abs_sub_lt_iff]; constructor <;> linarith

/-- **Display (33), PROVED from the cited (31) with `C₁ = 6.7814` and the cited (20)**:
`∫_0^1 |S G|² ≤ N L² (log 2 + C₁ C₀R₀ + o(1))`, for every `κ` and `CR`. -/
theorem display33 (κ CR : ℝ) (h31 : Display31 6.7814) (h20 : SingSum20 CR) :
    Display33 κ CR := by
  intro δ hδ
  set K : ℝ := 6.7814 + |CR| + 1 with hK
  have hKpos : 0 < K := by have := abs_nonneg CR; rw [hK]; linarith
  set d : ℝ := min 1 (δ / (2 * K)) with hd
  have hd0 : 0 < d := lt_min one_pos (by positivity)
  have hdK : d * K ≤ δ / 2 := by
    have := min_le_right 1 (δ / (2 * K))
    rw [← hd, le_div_iff₀ (by positivity)] at this; linarith
  filter_upwards [diag_small κ (half_pos hδ), h31 d hd0, Lfun_tendsto.eventually (h20 d hd0),
    U1434Lemma21.two_pow_small one_pos, eventually_ge_atTop 2] with N hdiag h31N h20N h2L hN2
  set L := Lfun N
  have hLN : (2 : ℤ) ^ L < N := by
    have : (2 : ℝ) ^ L < N := by have := pow_pos (show (0 : ℝ) < 2 by norm_num) L; linarith
    exact_mod_cast this
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hterm : ∀ ν ∈ Finset.Icc 1 L, ∀ μ ∈ Finset.Icc 1 L,
      (if ν = μ then 0 else Real.log N ^ 2 * pairCount N ((2 : ℤ) ^ μ - 2 ^ ν)) ≤
        (6.7814 + d) / 2 * N * (if ν = μ then 0 else singS ((2 : ℤ) ^ μ - 2 ^ ν)) := by
    intro ν hν μ hμ
    by_cases h : ν = μ
    · simp [h]
    · rw [if_neg h, if_neg h]
      obtain ⟨c1, c2, c3⟩ := h_conds hν hμ h hLN
      have hc := h31N _ c1 c2 c3
      have hl2 : (0 : ℝ) < Real.log N ^ 2 := by positivity
      calc Real.log N ^ 2 * pairCount N ((2 : ℤ) ^ μ - 2 ^ ν) ≤ Real.log N ^ 2 *
            ((6.7814 + d) / 2 * (N * singS ((2 : ℤ) ^ μ - 2 ^ ν) / Real.log N ^ 2)) :=
            mul_le_mul_of_nonneg_left hc hl2.le
        _ = _ := by field_simp
  have hswap : ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
      (if ν = μ then 0 else singS ((2 : ℤ) ^ μ - 2 ^ ν)) =
      ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
      (if ν = μ then 0 else singS ((2 : ℤ) ^ ν - 2 ^ μ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> first | rfl | omega
  have hprod : (6.7814 + d) * (CR + d) ≤ 6.7814 * CR + δ / 2 := by
    have := le_abs_self CR
    have hd1 : d ≤ 1 := min_le_left _ _
    have : d * (6.7814 + CR + d) ≤ d * K := by
      rw [hK]; apply mul_le_mul_of_nonneg_left _ hd0.le; linarith
    nlinarith
  calc ∫ α in Icc (0 : ℝ) 1, SG κ N α
      ≤ (L : ℝ) * ∑ p ∈ primesIn (N1f κ N) N, Real.log p ^ 2 +
        ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
          (if ν = μ then 0 else Real.log N ^ 2 * pairCount N ((2 : ℤ) ^ μ - 2 ^ ν)) :=
        integral_SG_le κ N
    _ ≤ N * (L : ℝ) ^ 2 * (Real.log 2 + δ / 2) + (6.7814 + d) / 2 * N *
        ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
          (if ν = μ then 0 else singS ((2 : ℤ) ^ μ - 2 ^ ν)) := by
        refine add_le_add hdiag ?_
        simp_rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun ν hν => Finset.sum_le_sum fun μ hμ => hterm ν hν μ hμ
    _ ≤ N * (L : ℝ) ^ 2 * (Real.log 2 + δ / 2) + (6.7814 + d) / 2 * N *
        (2 * (L : ℝ) ^ 2 * (CR + d)) := by
        rw [hswap]; gcongr
    _ = N * (L : ℝ) ^ 2 * (Real.log 2 + δ / 2) + N * (L : ℝ) ^ 2 * ((6.7814 + d) * (CR + d)) := by
        ring
    _ ≤ N * (L : ℝ) ^ 2 * (Real.log 2 + δ / 2) + N * (L : ℝ) ^ 2 * (6.7814 * CR + δ / 2) := by
        gcongr
    _ = _ := by ring

/-! ### The conclusion with `Display33` removed -/

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON `Display30Upper`, the cited (31) `Display31 6.7814`, the cited
(20) `SingSum20 CR`, `Display34Lower`, `MinorSup1924 P`, the conditions (24) on `P`, and the cited
constants of `k6_wired`**. This is `U7200Minor35.r6_lower''` with `Display33` replaced by
`display33`. -/
theorem r6_lower3 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814) (h20 : SingSum20 CR) :
    ∃ e1 > 0, ∀ e0 : ℝ, 0 ≤ e0 → e0 < e1 → ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      Display30Upper κ P (∑ i, ∑ j, (LiLiu.v i : ℝ) * ((LiLiu.Astar i j : ℝ) + T i j) *
        (LiLiu.v j : ℝ)) e0 →
      Display34Lower κ P CR e0 →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  obtain ⟨e1, he1, h⟩ := r6_lower'' T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33
  exact ⟨e1, he1, fun e0 he0 he01 κ hκ P hP11 hPup hP2 hMS h30 h34 =>
    h e0 he0 he01 hκ P hP11 hPup hP2 hMS h30 (display33 κ CR h31 h20) h34⟩

end LeanLab.Linnik.U7203Display33

