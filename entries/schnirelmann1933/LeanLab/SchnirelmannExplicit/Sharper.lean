module

public import LeanLab.SchnirelmannExplicit.Main

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Sharper explicit Schnirelmann constant (unit U-0029): every integer `n ≥ 2` is a sum of at most
`H₁ = 24336863622` primes (about 2.43 * 10^10). The sieve level in S1u is lowered to
`z = N^(1/3)` and S1u is only claimed for `N ≥ N₁ = 5920000000`, which gives the constant
`347` in place of `128 + 5 * 17^8 + 12`; small `N` are absorbed by the S4 step.
-/

@[expose] public section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit.Sharper

open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannExplicit

lemma exp_ge_poly8 (t : ℝ) (ht : 0 ≤ t) : (1 + t / 12) ^ 8 ≤ Real.exp (2 * t / 3) := by
  have h1 : t / 12 + 1 ≤ Real.exp (t / 12) := Real.add_one_le_exp _
  have h2 : Real.exp (2 * t / 3) = Real.exp (t / 12) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2]
  exact pow_le_pow_left₀ (by positivity) (by linarith) 8

lemma exp15_ge : (3269017 : ℝ) ≤ Real.exp 15 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 15 = Real.exp 1 ^ 15 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (3269017 : ℝ) ≤ 2.7182818283 ^ 15 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h.le 15

lemma poly_le_exp (u : ℝ) (hu : 45 / 2 ≤ u) :
    (1 + u / 3) ^ 6 * u ^ 2 ≤ 5841 / 100 * Real.exp (2 * u / 3) := by
  set t := u - 45 / 2 with ht
  have ht0 : 0 ≤ t := by linarith
  have hs : 0 ≤ 1 + t / 12 := by linarith
  have ha : 1 + u / 3 ≤ 17 / 2 * (1 + t / 12) := by rw [ht]; linarith
  have hb : u ≤ 45 / 2 * (1 + t / 12) := by rw [ht]; linarith
  have he : Real.exp (2 * u / 3) = Real.exp 15 * Real.exp (2 * t / 3) := by
    rw [← Real.exp_add]; congr 1; rw [ht]; ring
  have hE := exp_ge_poly8 t ht0
  have h15 := exp15_ge
  have hu0 : 0 ≤ u := by linarith
  calc (1 + u / 3) ^ 6 * u ^ 2 ≤ (17 / 2 * (1 + t / 12)) ^ 6 * (45 / 2 * (1 + t / 12)) ^ 2 := by
        gcongr
    _ = (17 / 2) ^ 6 * (45 / 2) ^ 2 * (1 + t / 12) ^ 8 := by ring
    _ ≤ 5841 / 100 * 3269017 * (1 + t / 12) ^ 8 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
    _ ≤ 5841 / 100 * (Real.exp 15 * Real.exp (2 * t / 3)) := by
        rw [mul_assoc]; gcongr
    _ = _ := by rw [he]

lemma err_bound (u : ℝ) (hu : 45 / 2 ≤ u) :
    (Real.exp (u / 3) * (1 + u / 3) ^ 6 + 2 * (Real.exp (u / 3) + 1)) * u ^ 2
      ≤ 59 * Real.exp u := by
  set z := Real.exp (u / 3)
  have hz1 : 1 ≤ z := Real.one_le_exp (by linarith)
  have hP := poly_le_exp u hu
  have hA : (17 / 2 : ℝ) ^ 6 ≤ (1 + u / 3) ^ 6 := by gcongr; linarith
  have hzu : z * Real.exp (2 * u / 3) = Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have h4 : 2 * (z + 1) ≤ (1 + u / 3) ^ 6 * z / 10000 := by
    have : (17 / 2 : ℝ) ^ 6 * z ≤ (1 + u / 3) ^ 6 * z := by gcongr
    norm_num at this ⊢; nlinarith
  have hzP : z * ((1 + u / 3) ^ 6 * u ^ 2) ≤ z * (5841 / 100 * Real.exp (2 * u / 3)) := by gcongr
  have hE0 : 0 ≤ Real.exp u := (Real.exp_pos _).le
  calc (z * (1 + u / 3) ^ 6 + 2 * (z + 1)) * u ^ 2
      ≤ (z * (1 + u / 3) ^ 6 + (1 + u / 3) ^ 6 * z / 10000) * u ^ 2 := by gcongr
    _ = 10001 / 10000 * (z * ((1 + u / 3) ^ 6 * u ^ 2)) := by ring
    _ ≤ 10001 / 10000 * (z * (5841 / 100 * Real.exp (2 * u / 3))) := by gcongr
    _ = 10001 / 10000 * (5841 / 100) * Real.exp u := by rw [← hzu]; ring
    _ ≤ 59 * Real.exp u := by gcongr; norm_num

/-- `exp (45/2) ≤ N₁ = 5920000000`. -/
lemma exp_le_N₁ : Real.exp (45 / 2) ≤ 5920000000 := by
  have h := Real.exp_one_lt_d9
  have h45 : Real.exp (45 / 2) ^ 2 = Real.exp 1 ^ 45 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have : Real.exp (45 / 2) ^ 2 ≤ (5920000000 : ℝ) ^ 2 := by
    rw [h45]
    calc Real.exp 1 ^ 45 ≤ (2.7182818286 : ℝ) ^ 45 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le h.le 45
      _ ≤ _ := by norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) this

/-- The threshold from which the sharper S1u bound is claimed. -/
def N₁ : ℕ := 5920000000

open LeanLab.SchnirelmannGoldbach.S1 in
/-- **S1u, sharper.** For `N ≥ N₁ = 5920000000` and `1 ≤ n ≤ N`,
`r n ≤ 347 N / log² N · singProd n`. Sieve level `z = exp (log N / 3) = N^(1/3)`. -/
theorem S1u_sharp : ∀ N : ℕ, N₁ ≤ N → ∀ n ∈ Icc 1 N,
    (r n : ℝ) ≤ 347 * N / (Real.log N) ^ 2 * singProd n := by
  intro N hN n hn
  simp only [mem_Icc] at hn
  have hNR : (5920000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set u := Real.log N with hu_def
  have hu : 45 / 2 ≤ u := by
    rw [hu_def, Real.le_log_iff_exp_le hNpos]
    exact exp_le_N₁.trans hNR
  have hupos : 0 < u := by linarith
  have hsp := one_le_singProd n
  have hexpu : Real.exp u = N := Real.exp_log hNpos
  have hNl : (N : ℝ) / u ^ 2 ≥ 1 / 4 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [log_sq_le N (by linarith)]
  have hQ0 : 0 ≤ (N : ℝ) / u ^ 2 := by positivity
  by_cases hev : Even n ∧ 4 ≤ n
  · obtain ⟨hev, hn4⟩ := hev
    set z := Real.exp (u / 3) with hz
    have hz1 : 1 < z := by rw [hz]; exact Real.one_lt_exp_iff.mpr (by linarith)
    have hrz := r_le_of_even hev (by omega) hz1
    have hlogz : Real.log z = u / 3 := Real.log_exp _
    rw [hlogz] at hrz
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    have hmain : 32 * n * singProd n / (u / 3) ^ 2 ≤ 288 * (N / u ^ 2 * singProd n) := by
      have e : 32 * n * singProd n / (u / 3) ^ 2 = 288 * (n / u ^ 2 * singProd n) := by
        field_simp; ring
      rw [e]
      gcongr
    have herr : z * (1 + u / 3) ^ 6 + 2 * (z + 1) ≤ 59 * (N / u ^ 2 * singProd n) := by
      have h1 := err_bound u hu
      rw [hexpu] at h1
      have h2 : z * (1 + u / 3) ^ 6 + 2 * (z + 1) ≤ 59 * (N / u ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        exact h1
      have h3 : 59 * (N / u ^ 2) ≤ 59 * (N / u ^ 2 * singProd n) := by nlinarith
      linarith
    calc (r n : ℝ) ≤ 288 * (N / u ^ 2 * singProd n) + 59 * (N / u ^ 2 * singProd n) := by
          linarith
      _ = 347 * N / u ^ 2 * singProd n := by ring
  · have h3 : (r n : ℝ) ≤ 3 := by exact_mod_cast r_le_three_of_not hev
    have : (3 : ℝ) ≤ 347 * (N / u ^ 2 * singProd n) := by nlinarith
    calc (r n : ℝ) ≤ 347 * (N / u ^ 2 * singProd n) := by linarith
      _ = 347 * N / u ^ 2 * singProd n := by ring

/-- **S3, explicit, with a threshold on S1u.** As `S3_explicit_of`, but the S1u bound is only
assumed for `N ≥ N₁`; the conclusion then holds for `N ≥ max (2 m₀ + 6) N₁`. -/
theorem S3_explicit_from (C₀ D₀ c : ℝ) (hc : 0 < c) (m₀ N₁ : ℕ)
    (hC : ∀ N : ℕ, N₁ ≤ N → ∀ n ∈ Icc 1 N,
      (r n : ℝ) ≤ C₀ * N / (Real.log N) ^ 2 * singProd n)
    (hD : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ D₀ * N)
    (hm : ∀ m : ℕ, m₀ ≤ m → c * m / Real.log m ≤ (Nat.primeCounting m : ℝ)) :
    ∀ N ≥ 2 * m₀ + 6, N₁ ≤ N → c ^ 4 / (81 * (max C₀ 1) ^ 2 * (max D₀ 1)) * N ≤
      #{n ∈ Icc 1 N | n ∈ G} := by
  set C := max C₀ 1
  set D := max D₀ 1
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  intro N hN hN₁
  set m := N / 2
  have hm2 : 2 * m ≤ N := Nat.mul_div_le N 2
  have hmge : m₀ ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hNR : (6 : ℝ) ≤ N := by exact_mod_cast (show 6 ≤ N by omega)
  have hmR : (N : ℝ) ≤ 3 * m := by
    have : N ≤ 3 * m := by omega
    exact_mod_cast this
  have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  set L := Real.log N
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogm_le : Real.log m ≤ L := Real.log_le_log (by linarith) (by
    have : m ≤ N := by omega
    exact_mod_cast this)
  have hpi := hm m hmge
  have hR1 : ((Nat.primeCounting m : ℝ)) ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by
    exact_mod_cast sum_r_ge m N hm2
  have hpiL : c * N / (3 * L) ≤ (Nat.primeCounting m : ℝ) := by
    refine le_trans ?_ hpi
    rw [div_le_div_iff₀ (by positivity) hlogm_pos]
    have : c * N * Real.log m ≤ c * (3 * m) * L := by
      have := mul_le_mul hmR hlogm_le hlogm_pos.le (by positivity)
      nlinarith
    linarith
  have hA : (c * N / (3 * L)) ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) :=
    le_trans (pow_le_pow_left₀ (by positivity) hpiL 2) hR1
  have hR2 : ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * (D * N) := by
    have hpt : ∀ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := by
      intro n hn
      have h := hC N hN₁ n hn
      have h' : (r n : ℝ) ≤ C * N / L ^ 2 * singProd n := by
        refine h.trans ?_
        gcongr
        · exact singProd_nonneg n
        · exact le_max_left _ _
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h' 2
    calc ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2
        ≤ ∑ n ∈ Icc 1 N, (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := Finset.sum_le_sum hpt
      _ = (C * N / L ^ 2) ^ 2 * ∑ n ∈ Icc 1 N, singProd n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * N / L ^ 2) ^ 2 * (D * N) := by
          gcongr
          exact (hD N (by omega)).trans (by gcongr; exact le_max_left _ _)
  have hCS := cauchy_schwarz_r N
  set K : ℝ := ((#{n ∈ Icc 1 N | n ∈ G} : ℕ) : ℝ) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hcomb : ((c * N / (3 * L)) ^ 2) ^ 2 ≤ K * ((C * N / L ^ 2) ^ 2 * (D * N)) := by
    calc ((c * N / (3 * L)) ^ 2) ^ 2 ≤ (((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hA 2
      _ ≤ K * ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 := hCS
      _ ≤ K * ((C * N / L ^ 2) ^ 2 * (D * N)) := by gcongr
  have hNpos : (0 : ℝ) < N := by linarith
  have e1 : ((c * N / (3 * L)) ^ 2) ^ 2 = c ^ 4 * N ^ 4 / (81 * L ^ 4) := by
    field_simp; ring
  have e2 : K * ((C * N / L ^ 2) ^ 2 * (D * N)) = K * (C ^ 2 * D * N ^ 3) / L ^ 4 := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at hcomb
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hL4 : 0 < L ^ 4 := by positivity
  have hN3 : 0 < (N : ℝ) ^ 3 := by positivity
  have : c ^ 4 * N ^ 4 ≤ K * (C ^ 2 * D * N ^ 3) * 81 := by
    have := hcomb
    nlinarith [hL4]
  nlinarith [hN3, hNpos]


/-- **S3, sharper constants.** For `N ≥ N₁ = 5920000000`, at least
`(log 2 / 2)^4 / (81 · 347^2 · 9) · N` integers in `[1, N]` are Goldbach sums. -/
theorem S3_sharp : ∀ N ≥ N₁,
    (Real.log 2 / 2) ^ 4 / (81 * 347 ^ 2 * 9) * N ≤ #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN
  have h := S3_explicit_from 347 9 (Real.log 2 / 2) (by positivity) 100 N₁
    S1u_sharp S2_explicit pi_lower_explicit N (by unfold N₁ at hN; omega) hN
  have hC1 : max (347 : ℝ) 1 = 347 := by norm_num
  have h9 : max (9 : ℝ) 1 = 9 := by norm_num
  rw [hC1, h9] at h
  exact h

/-- A rational lower bound for the sharper S3 density constant, using `log 2 > 0.6931471803`. -/
noncomputable def α₁ : ℝ := (6931471803 / 20000000000 : ℝ) ^ 4 / (81 * 347 ^ 2 * 9)

/-- `K₁ = ⌈1 / α₁⌉`. -/
def K₁ : ℕ := 6084215905

/-- The sharper explicit Schnirelmann constant. -/
def H₁ : ℕ := 4 * K₁ + 2

lemma H₁_eq : H₁ = 24336863622 := by norm_num [H₁, K₁]

lemma α₁_le_density : α₁ ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  have h4 := S4_explicit _ N₁ S3_sharp
  refine le_trans ?_ h4
  apply le_min
  · unfold α₁
    have hl2 := Real.log_two_gt_d9
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply pow_le_pow_left₀ (by norm_num)
    norm_num at hl2 ⊢
    linarith
  · norm_num [α₁, N₁]

lemma one_le_α₁_mul_K₁ : 1 ≤ α₁ * (K₁ : ℝ) := by
  norm_num [α₁, K₁]

/-- **Schnirelmann's theorem, sharper explicit form.** Every integer `n ≥ 2` is a sum of at
most `H₁ = 24336863622` primes. -/
theorem schnirelmann_bounded_primes_sharper :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₁, SumOfPrimes k n := by
  have hh : (2 * K₁) • ({0, 1} ∪ G : Set ℕ) = Set.univ := by
    have := nsmul_eq_univ_of_le_density ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) α₁
      (by convert α₁_le_density) K₁ one_le_α₁_mul_K₁
    exact this
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num [H₁], [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num [H₁], [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ (2 * K₁) • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ (2 * K₁) (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by unfold H₁; omega, hs⟩

/-- Corollary with a round constant: at most `2.5 · 10^10` primes suffice. -/
theorem schnirelmann_bounded_primes_sharper_round :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ 25 * 10 ^ 9, SumOfPrimes k n := by
  intro n hn
  obtain ⟨k, hk, hs⟩ := schnirelmann_bounded_primes_sharper n hn
  exact ⟨k, hk.trans (by rw [H₁_eq]; norm_num), hs⟩

/-- The new constant is strictly smaller than the old one, by a factor above `10^16`. -/
lemma H₁_lt_H₀ : H₁ * 10 ^ 16 < H₀ := by norm_num [H₁, K₁, H₀, K₀]

end LeanLab.SchnirelmannExplicit.Sharper
