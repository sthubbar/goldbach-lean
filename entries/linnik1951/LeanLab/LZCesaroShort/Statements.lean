module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
P0058 A. Languasco and A. Zaccagnini, "A Cesàro average in short intervals for Goldbach
numbers", arXiv 1606.00869, read as v2 of 6 Jan 2017 with pdftotext on 2026-10-17.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here is about Goldbach for every even number: `R n > 0`
only says `n` is a sum of two prime POWERS, and the theorems are averages over `n`.

What the paper really proves, as read: the weight is the symmetric triangle (Fejér) weight
`1 - |n - N| / H` on `n ∈ [N - H, N + H]`, NOT a `Γ`-type Cesàro weight `(1 - n/N)^k / Γ(k+1)`;
there is no `k` and no `Γ` in Theorems 1 and 2. `Γ` appears only in the introduction, quoting
the authors' earlier unconditional paper, which is `lz_cesaro` in `GoldbachAverage/Unconditional`.
Theorems 1 and 2 assume RH. Lemmas 7 and 8 are unconditional.

Zero sums: over nontrivial zeros, counted with multiplicity by `analyticOrderNatAt`, as in
`GoldbachAverage/ZeroSums.lean`; that module is not built yet, so the two definitions are copied
here verbatim. A `tsum` that does not converge is `0` in Lean; the zero sums used here converge
absolutely for each fixed `N, H`: the terms of `ZH` are `O(N^{5/2} / |ρ|^3)` and those of Lemma 7 are
`O(M² / |ρ|²)`.
-/

@[expose] public section

open Finset Filter Asymptotics
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section
namespace LeanLab.LZCesaroShort

/-! ### Definitions -/

/-- `R(n) = ∑_{h + k = n} Λ(h) Λ(k)`, the paper's counting function. Same as
`GoldbachAverage.G`. -/
def R (n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, Λ p.1 * Λ p.2

/-- The short-interval Cesàro weight `1 - |n - N| / H` of Theorem 1. -/
def w (N H n : ℕ) : ℝ := 1 - |(n : ℝ) - N| / H

/-- `∑_{n = N-H}^{N+H} R(n) (1 - |n - N|/H)`, the left side of Theorem 1. -/
def cesaro (N H : ℕ) : ℝ := ∑ n ∈ Icc (N - H) (N + H), w N H n * R n

/-- Nontrivial zeros of ζ: zeros in the open critical strip. Copy of
`GoldbachAverage.NontrivialZero`. -/
def NontrivialZero : Type := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- `Σ_ρ m(ρ) f(ρ)` with multiplicity `m(ρ)`. Copy of `GoldbachAverage.zeroSum`. -/
def zeroSum (f : ℂ → ℂ) : ℂ :=
  ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * f ρ.1

/-- `S = Σ_ρ ((N+H)^{ρ+2} - 2 N^{ρ+2} + (N-H)^{ρ+2}) / (ρ(ρ+1)(ρ+2))`, the paper's `S`
of Section 5, the second difference term. -/
def ZH (N H : ℕ) : ℂ :=
  zeroSum (fun ρ => (((N : ℂ) + H) ^ (ρ + 2) - 2 * (N : ℂ) ^ (ρ + 2) + ((N : ℂ) - H) ^ (ρ + 2))
    / (ρ * (ρ + 1) * (ρ + 2)))

/-- The paper's eq. (2) and (3) sum, with `y` real: `∑_{N-H ≤ n ≤ N+y}
e^{-n/N} (R(n) - (2ψ(n) - n)) (1 - |n - N|/H)`. -/
def wsum (N H : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + y),
    Real.exp (-(n : ℝ) / N) * (R n - (2 * ψ n - n)) * w N H n

/-! ### The paper's statements, cited -/

/-- Theorem 1 and the abstract: for integers `N ≥ 2`, `1 ≤ H ≤ N`,
`Σ_{n=N-H}^{N+H} R(n)(1 - |n-N|/H) = HN - (2/H) S + O(N log(2N²/H) + H (log N)² log(2H))`,
with one absolute constant `K`. -/
def Theorem1 : Prop :=
  ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K * (N * Real.log (2 * (N : ℝ) ^ 2 / H) + H * Real.log N ^ 2 * Real.log (2 * H))

/-- Theorem 2 eq. (2): uniformly for real `y ∈ [-H, H)`, the partial weighted sum is
`≪ N (log N)² log(2H)`. -/
def Theorem2a : Prop :=
  ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N → ∀ y : ℝ, -(H : ℝ) ≤ y → y < H →
    |wsum N H y| ≤ K * N * Real.log N ^ 2 * Real.log (2 * H)

/-- Theorem 2 eq. (3): the full sum, `y = H`, is `≪ N log(2N²/H)`. -/
def Theorem2b : Prop :=
  ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    |wsum N H H| ≤ K * N * Real.log (2 * (N : ℝ) ^ 2 / H)

/-- Lemma 7, unconditional: for real `M > 1`,
`Σ_{n ≤ M} (ψ(n) - n) = -Σ_ρ M^{ρ+1}/(ρ(ρ+1)) + O(M)`. -/
def Lemma7 : Prop :=
  ∃ K : ℝ, ∀ M : ℝ, 1 < M →
    ‖((∑ n ∈ Icc 1 ⌊M⌋₊, (ψ n - n) : ℝ) : ℂ)
        + zeroSum (fun ρ => (M : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))‖ ≤ K * M

/-- Lemma 8, unconditional: for `N` large and `2 ≤ H ≤ N`,
`Σ_{n=N-H}^{N+H} (H - |n-N|)(ψ(n) - n) = -S + O(HN)`. -/
def Lemma8 : Prop :=
  ∃ N₀ : ℕ, ∃ K : ℝ, ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → H ≤ N →
    ‖((∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n) : ℝ) : ℂ)
        + ZH N H‖ ≤ K * H * N

/-- Section 5 under RH: the zero term of Theorem 1 is `≪ H N^{1/2} (log N)² + N`, i.e.
`S / H ≪ H √N (log N)² + N`. The paper derives it from Lemma 8, which needs `2 ≤ H` and `N`
large, so the statement keeps those ranges. -/
def Sec5RH : Prop :=
  ∃ N₀ : ℕ, ∃ K : ℝ, ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → H ≤ N →
    ‖ZH N H / (H : ℂ)‖ ≤ K * (H * Real.sqrt N * Real.log N ^ 2 + N)

/-! ### Proved links -/

/-- `R n ≥ 0`. -/
theorem R_nonneg (n : ℕ) : 0 ≤ R n :=
  sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg

/-- `R n > 0` means `n` is a sum of two prime powers; it does NOT give two primes. -/
theorem primePow_sum_of_R_pos {n : ℕ} (h : 0 < R n) :
    ∃ a b : ℕ, IsPrimePow a ∧ IsPrimePow b ∧ a + b = n := by
  have : ∃ p ∈ antidiagonal n, 0 < Λ p.1 * Λ p.2 := by
    by_contra hc
    push Not at hc
    have := sum_nonpos hc
    unfold R at h; linarith
  obtain ⟨p, hp, hpos⟩ := this
  refine ⟨p.1, p.2, ?_, ?_, mem_antidiagonal.mp hp⟩
  · exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (fun h0 => by simp [h0] at hpos)
  · exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (fun h0 => by simp [h0] at hpos)

/-- The weight is in `[0, 1]` on `[N - H, N + H]`. -/
theorem w_mem {N H n : ℕ} (hH : 1 ≤ H) (h1 : N - H ≤ n) (h2 : n ≤ N + H) (hHN : H ≤ N) :
    0 ≤ w N H n ∧ w N H n ≤ 1 := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hab : |(n : ℝ) - N| ≤ H := by
    rw [abs_le]
    have : (N : ℝ) - H ≤ n := by
      have := (Nat.cast_le (α := ℝ)).mpr h1; rw [Nat.cast_sub hHN] at this; exact this
    have : (n : ℝ) ≤ N + H := by exact_mod_cast h2
    constructor <;> linarith
  unfold w
  refine ⟨?_, ?_⟩
  · have : |(n : ℝ) - N| / H ≤ 1 := by rw [div_le_one hHp]; exact hab
    linarith
  · have : 0 ≤ |(n : ℝ) - N| / H := div_nonneg (abs_nonneg _) hHp.le
    linarith

/-- The weight is `1` at the centre. -/
theorem w_center (N H : ℕ) : w N H N = 1 := by simp [w]

/-- The Cesàro sum is nonnegative. -/
theorem cesaro_nonneg {N H : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) : 0 ≤ cesaro N H := by
  refine sum_nonneg fun n hn => ?_
  rw [mem_Icc] at hn
  exact mul_nonneg (w_mem hH hn.1 hn.2 hHN).1 (R_nonneg n)

/-- Sanity: for `H = 1` the Cesàro sum is just `R(N)`. -/
theorem cesaro_one {N : ℕ} (hN : 1 ≤ N) : cesaro N 1 = R N := by
  unfold cesaro
  rw [sum_eq_single N]
  · simp [w]
  · intro n hn hne
    rw [mem_Icc] at hn
    have : n = N - 1 ∨ n = N + 1 := by omega
    rcases this with rfl | rfl
    · simp [w, Nat.cast_sub hN]
    · simp [w]
  · intro h; exact absurd (mem_Icc.mpr ⟨by omega, by omega⟩) h

/-- Positivity of the Cesàro sum gives some `n ∈ [N-H, N+H]` with `R n > 0`. -/
theorem exists_R_pos_of_cesaro_pos {N H : ℕ} (h : 0 < cesaro N H) :
    ∃ n ∈ Icc (N - H) (N + H), 0 < R n := by
  by_contra hc
  push Not at hc
  have : cesaro N H ≤ 0 := by
    refine sum_nonpos fun n hn => ?_
    have : R n = 0 := le_antisymm (hc n hn) (R_nonneg n)
    simp [this]
  linarith

/-! #### The weight identities, the paper's "direct calculation" -/

/-- Reindexing `[N - H, N + H]` by `m = n - N ∈ [-H, H]`. -/
theorem sum_Icc_reindex {N H : ℕ} (hHN : H ≤ N) (f : ℕ → ℝ) :
    ∑ n ∈ Icc (N - H) (N + H), f n = ∑ m ∈ Icc (-(H : ℤ)) H, f ((N : ℤ) + m).toNat := by
  refine sum_nbij' (fun n => (n : ℤ) - N) (fun m => ((N : ℤ) + m).toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [mem_Icc] at hn ⊢; omega
  · intro m hm; simp only [mem_Icc] at hm ⊢; omega
  · intro n _; simp
  · intro m hm; simp only [mem_Icc] at hm; omega
  · intro n _; congr 1; omega

theorem Icc_succ_eq (H : ℕ) :
    Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1) = insert (-((H : ℤ) + 1)) (insert ((H : ℤ) + 1)
      (Icc (-(H : ℤ)) H)) := by
  ext m; simp only [mem_Icc, mem_insert]; omega

theorem sum_Icc_succ (H : ℕ) (g : ℤ → ℝ) :
    ∑ m ∈ Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1), g m
      = ∑ m ∈ Icc (-(H : ℤ)) H, g m + g (-((H : ℤ) + 1)) + g ((H : ℤ) + 1) := by
  rw [Icc_succ_eq, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
    sum_insert (by simp only [mem_Icc]; omega)]
  ring

/-- `Σ_{|m| ≤ H} (c + d m) = (2H+1) c`. -/
theorem sum_lin (H : ℕ) (c d : ℝ) :
    ∑ m ∈ Icc (-(H : ℤ)) H, (c + d * m) = (2 * H + 1) * c := by
  induction H with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [sum_Icc_succ, ih]; push_cast; ring

/-- `Σ_{|m| ≤ H} (H - |m|)(c + d m) = H² c`. -/
theorem sum_tri (H : ℕ) (c d : ℝ) :
    ∑ m ∈ Icc (-(H : ℤ)) H, ((H : ℝ) - |(m : ℝ)|) * (c + d * m) = (H : ℝ) ^ 2 * c := by
  induction H with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [sum_Icc_succ]
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have e1 : |((-((k : ℤ) + 1) : ℤ) : ℝ)| = k + 1 := by
      push_cast; rw [abs_neg, abs_of_nonneg (by linarith)]
    have e2 : |(((k : ℤ) + 1 : ℤ) : ℝ)| = k + 1 := by
      push_cast; rw [abs_of_nonneg (by linarith)]
    rw [e1, e2]
    have : ∑ m ∈ Icc (-(k : ℤ)) k, ((k : ℝ) + 1 - |(m : ℝ)|) * (c + d * m)
        = ∑ m ∈ Icc (-(k : ℤ)) k, ((k : ℝ) - |(m : ℝ)|) * (c + d * m)
          + ∑ m ∈ Icc (-(k : ℤ)) k, (c + d * m) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun m _ => by ring
    rw [this, ih, sum_lin]; ring

/-- The cast of the reindexed point. -/
theorem cast_toNat {N : ℕ} {H : ℕ} (hHN : H ≤ N) {m : ℤ} (hm : m ∈ Icc (-(H : ℤ)) H) :
    ((((N : ℤ) + m).toNat : ℕ) : ℝ) = N + m := by
  rw [mem_Icc] at hm
  have h0 : 0 ≤ (N : ℤ) + m := by omega
  have : ((((N : ℤ) + m).toNat : ℕ) : ℤ) = N + m := Int.toNat_of_nonneg h0
  have := congrArg (fun z : ℤ => (z : ℝ)) this
  push_cast at this
  exact this

/-- The paper's "direct calculation", end of Section 3:
`Σ_{n=N-H}^{N+H} t_H(n - N) n = H² N` with `t_H(m) = H - |m|`. -/
theorem sum_tH_mul_n {N H : ℕ} (hHN : H ≤ N) :
    ∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * n = (H : ℝ) ^ 2 * N := by
  rw [sum_Icc_reindex hHN, ← sum_tri H N 1]
  refine sum_congr rfl fun m hm => ?_
  rw [cast_toNat hHN hm]; ring_nf

/-- `Σ_{n=N-H}^{N+H} t_H(n - N) = H²`. -/
theorem sum_tH {N H : ℕ} (hHN : H ≤ N) :
    ∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) = (H : ℝ) ^ 2 := by
  have := sum_tri H 1 0
  rw [mul_one] at this
  rw [sum_Icc_reindex hHN, ← this]
  refine sum_congr rfl fun m hm => ?_
  rw [cast_toNat hHN hm]; ring_nf

theorem w_eq {N H n : ℕ} (hH : 1 ≤ H) : w N H n = ((H : ℝ) - |(n : ℝ) - N|) / H := by
  have : (H : ℝ) ≠ 0 := by positivity
  unfold w; field_simp

/-- The main term `HN` of Theorem 1 is exactly the same Cesàro average of `n`. -/
theorem sum_w_mul_n {N H : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    ∑ n ∈ Icc (N - H) (N + H), w N H n * n = (H : ℝ) * N := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  simp_rw [w_eq hH, div_mul_eq_mul_div, ← sum_div, sum_tH_mul_n hHN]
  field_simp

/-- The total weight is `H`. -/
theorem sum_w {N H : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    ∑ n ∈ Icc (N - H) (N + H), w N H n = H := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  simp_rw [w_eq hH, ← sum_div, sum_tH hHN]
  field_simp

/-! #### Theorem 1 and the Section 5 bound give `R n > 0` in `[N - H, N + H]` for
`H ≥ C log N` -/

/-- Eventual facts used below. -/
theorem eventually_small (a : ℝ) :
    ∀ᶠ N : ℕ in atTop, a * Real.log N ^ 3 ≤ N / 4 ∧ a * Real.log N ^ 2 ≤ Real.sqrt N / 4 := by
  have h1 : (fun x : ℝ => Real.log x ^ 3) =o[atTop] id := Real.isLittleO_pow_log_id_atTop
  have h2 : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop] fun x => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num)
  set c : ℝ := 1 / (4 * (|a| + 1)) with hc
  have cpos : 0 < c := by positivity
  have e1 := h1.bound cpos
  have e2 := h2.bound cpos
  have e3 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have e := (e1.and (e2.and e3))
  refine (tendsto_natCast_atTop_atTop.eventually e).mono ?_
  intro N hN
  obtain ⟨hA, hB, hx⟩ := hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hl : 0 ≤ Real.log N := Real.log_nonneg hx
  have hA' : Real.log N ^ 3 ≤ c * N := by
    have := le_trans (le_abs_self _) (Real.norm_eq_abs (Real.log (N : ℝ) ^ 3) ▸ hA)
    rwa [id, Real.norm_eq_abs, abs_of_nonneg hN0] at this
  have hB' : Real.log N ^ 2 ≤ c * Real.sqrt N := by
    have := le_trans (le_abs_self _) (Real.norm_eq_abs (Real.log (N : ℝ) ^ (2 : ℝ)) ▸ hB)
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN0 _), ← Real.sqrt_eq_rpow,
      Real.rpow_two] at this
  have hpos : 0 < 4 * (|a| + 1) := by positivity
  have hcm : c * (4 * (|a| + 1)) = 1 := by rw [hc]; field_simp
  have ha : a ≤ |a| := le_abs_self a
  constructor
  · have : 4 * (|a| + 1) * Real.log N ^ 3 ≤ N := by
      have := mul_le_mul_of_nonneg_left hA' hpos.le
      nlinarith
    nlinarith [abs_nonneg a, pow_nonneg hl 3]
  · have : 4 * (|a| + 1) * Real.log N ^ 2 ≤ Real.sqrt N := by
      have := mul_le_mul_of_nonneg_left hB' hpos.le
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    nlinarith [abs_nonneg a, pow_nonneg hl 2]

/-- Link: if Theorem 1 and the Section 5 bound both hold, then for some `C` and all large `N`,
every `H` with `C log N ≤ H ≤ N` has a positive Cesàro sum. The proof is ours: all error terms
are at most `HN/4` each. -/
theorem cesaro_pos_of (h1 : Theorem1) (h5 : Sec5RH) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ≤ H → H ≤ N → 0 < cesaro N H := by
  obtain ⟨K1', hK1⟩ := h1
  obtain ⟨N5, K2', hK2⟩ := h5
  set K1 := |K1'|
  set K2 := |K2'|
  have K1n : 0 ≤ K1 := abs_nonneg _
  have K2n : 0 ≤ K2 := abs_nonneg _
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp (eventually_small (2 * K1 + 2 * K2))
  refine ⟨12 * K1 + 8 * K2 + 4, max (max Ne N5) 3, fun N H hN hCH hHN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 ≤ Real.log N := by linarith
  have hHR : (4 : ℝ) ≤ H := by
    have : (4 : ℝ) * 1 ≤ (12 * K1 + 8 * K2 + 4) * Real.log N :=
      mul_le_mul (by linarith) hL1 (by norm_num) (by linarith)
    linarith
  have hH2 : 2 ≤ H := by exact_mod_cast (show (2 : ℝ) ≤ H by linarith)
  have hH1 : 1 ≤ H := by omega
  have hHle : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hHp : (0 : ℝ) < H := by linarith
  obtain ⟨hs1, hs2⟩ := hNe N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  -- the two cited bounds
  have b1 := hK1 N H (by omega) hH1 hHN
  have b2 := hK2 N H (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) hH2 hHN
  -- logs
  have hlogA : Real.log (2 * (N : ℝ) ^ 2 / H) ≤ 3 * Real.log N := by
    have : 2 * (N : ℝ) ^ 2 / H ≤ (N : ℝ) ^ 3 := by
      rw [div_le_iff₀ hHp]
      have h3 : 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
        nlinarith
      have : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 * H :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    calc _ ≤ Real.log ((N : ℝ) ^ 3) := Real.log_le_log (by positivity) this
      _ = 3 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogA0 : 0 ≤ Real.log (2 * (N : ℝ) ^ 2 / H) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hHp]
    have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    linarith
  have hlogB : Real.log (2 * (H : ℝ)) ≤ 2 * Real.log N := by
    have : 2 * (H : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogB0 : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  -- upgrade constants to absolute values
  have X1n : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H)
      + H * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  have b1' : ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K1 * (N * Real.log (2 * (N : ℝ) ^ 2 / H) + H * Real.log N ^ 2 * Real.log (2 * H)) :=
    le_trans b1 (mul_le_mul_of_nonneg_right (le_abs_self K1') X1n)
  have X2n : 0 ≤ (H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N := by positivity
  have b2' : ‖ZH N H / (H : ℂ)‖ ≤ K2 * (H * Real.sqrt N * Real.log N ^ 2 + N) :=
    le_trans b2 (mul_le_mul_of_nonneg_right (le_abs_self K2') X2n)
  -- real part bound
  set E : ℂ := 2 / (H : ℂ) * ZH N H
  have hE : ‖E‖ ≤ 2 * (K2 * ((H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N)) := by
    have : E = 2 * (ZH N H / (H : ℂ)) := by simp only [E]; ring
    rw [this, norm_mul]; simp only [Complex.norm_ofNat]; linarith
  have hreal : (H : ℝ) * N - cesaro N H ≤ ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + E‖ + ‖E‖ := by
    have e : (((H : ℝ) * N - cesaro N H : ℝ) : ℂ)
        = -((((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + E)) + E := by push_cast; ring
    calc (H : ℝ) * N - cesaro N H ≤ ‖((((H : ℝ) * N - cesaro N H : ℝ)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ _ := by rw [e]; exact le_trans (norm_add_le _ _) (by rw [norm_neg])
  -- each error term is small
  have t1 : K1 * (N * Real.log (2 * (N : ℝ) ^ 2 / H)) ≤ 3 * K1 * N * Real.log N := by
    have := mul_le_mul_of_nonneg_left hlogA (show 0 ≤ K1 * N by positivity); linarith
  have t2 : K1 * (H * Real.log N ^ 2 * Real.log (2 * H)) ≤ 2 * K1 * H * Real.log N ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlogB (show 0 ≤ K1 * H * Real.log N ^ 2 by positivity)
    have e : K1 * H * Real.log N ^ 2 * (2 * Real.log N) = 2 * K1 * H * Real.log N ^ 3 := by ring
    linarith
  have hCL : (12 * K1 + 8 * K2 + 4) * Real.log N * N ≤ H * N :=
    mul_le_mul_of_nonneg_right hCH (by positivity)
  have t3 : 2 * K1 * H * Real.log N ^ 3 ≤ H * N / 4 := by
    have : 2 * K1 * Real.log N ^ 3 ≤ N / 4 := by
      have : 2 * K1 * Real.log N ^ 3 ≤ (2 * K1 + 2 * K2) * Real.log N ^ 3 := by
        nlinarith [pow_nonneg hL0 3]
      linarith
    have := mul_le_mul_of_nonneg_left this hHp.le
    have e : (H : ℝ) * (2 * K1 * Real.log N ^ 3) = 2 * K1 * H * Real.log N ^ 3 := by ring
    linarith
  have t4 : 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) ≤ H * N / 4 := by
    have hs : 2 * K2 * Real.log N ^ 2 ≤ Real.sqrt N / 4 := by
      have : 2 * K2 * Real.log N ^ 2 ≤ (2 * K1 + 2 * K2) * Real.log N ^ 2 := by
        nlinarith [pow_nonneg hL0 2]
      linarith
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
    have hsqn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have := mul_le_mul_of_nonneg_left hs (show 0 ≤ (H : ℝ) * Real.sqrt N by positivity)
    have e1 : (H : ℝ) * Real.sqrt N * (Real.sqrt N / 4) = H * N / 4 := by
      rw [mul_assoc, ← mul_div_assoc, hsq]; ring
    have e2 : (H : ℝ) * Real.sqrt N * (2 * K2 * Real.log N ^ 2)
        = 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) := by ring
    linarith
  have t5 : 2 * K2 * (N : ℝ) ≤ 2 * K2 * N * Real.log N := by
    have := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ 2 * K2 * (N : ℝ) by positivity)
    linarith
  have t6 : 3 * K1 * N * Real.log N + 2 * K2 * N * Real.log N ≤ H * N / 4 := by
    have : 0 ≤ Real.log N * N := by positivity
    linarith
  have hfin : (H : ℝ) * N - cesaro N H ≤ 3 * (H * N) / 4 := by
    have e1 : K1 * ((N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H)
        + H * Real.log N ^ 2 * Real.log (2 * H))
        = K1 * (N * Real.log (2 * (N : ℝ) ^ 2 / H)) + K1 * (H * Real.log N ^ 2 * Real.log (2 * H)) :=
      by ring
    have e2 : 2 * (K2 * ((H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N))
        = 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) + 2 * K2 * N := by ring
    linarith
  have : 0 < (H : ℝ) * N := by positivity
  linarith

/-- Link, conditional on the two cited bounds: Goldbach-type numbers `n` with `R n > 0`,
sums of two prime powers, in every `[N - H, N + H]` with `C log N ≤ H ≤ N`, `N` large. -/
theorem exists_R_pos_short (h1 : Theorem1) (h5 : Sec5RH) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ≤ H → H ≤ N →
      ∃ n ∈ Icc (N - H) (N + H), ∃ a b : ℕ, IsPrimePow a ∧ IsPrimePow b ∧ a + b = n := by
  obtain ⟨C, N₀, h⟩ := cesaro_pos_of h1 h5
  refine ⟨C, N₀, fun N H hN hC hH => ?_⟩
  obtain ⟨n, hn, hR⟩ := exists_R_pos_of_cesaro_pos (h N H hN hC hH)
  exact ⟨n, hn, primePow_sum_of_R_pos hR⟩

end LeanLab.LZCesaroShort

