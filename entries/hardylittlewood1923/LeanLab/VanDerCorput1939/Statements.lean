module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
P0067 J. G. van der Corput, Sur la démonstration de l'hypothèse de Goldbach pour les nombres
impairs, donnée par M. Vinogradow, Bull. Soc. Math. France 67 1939, supplément, 87-99,
a lecture of 8 July 1937. Read from the numdam scan, pages 87 to 94, run 20261016T2204Z-20593.
STATED: Vinogradov's asymptotic (1) to (3) for I(N), the number of ways to write odd N as a sum
of three primes, as van der Corput reports it.
PROVED, no gaps: the Euler factor identity (1 + 1/(p-1)³)(1 - 1/(p² - 3p + 3)) = 1 - 1/(p-1)²,
prime by prime; the global identity of K P(N) with the singular series is NOT formalized;
K ≥ 1; that (1) gives every large odd N as a sum of three primes; and, in Totient.lean, the
lecture's φ(q) ≥ (1/2) q^{3/4}.
Not stated: the major and minor arc estimates of pages 91 to 99, whose constants c_m, γ_i
are not explicit.
AI-written Lean code, Claude. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013.
-/

@[expose] public section

noncomputable section
namespace LeanLab.VanDerCorput1939

open Real Finset

attribute [local instance] Classical.propDecidable

/-- `I(N)`, ordered triples of primes `p₁ + p₂ + p₃ = N`, the count `∫₀¹ S³(α) e(-αN) dα` of (4). -/
def I (N : ℕ) : ℕ :=
  #{t ∈ (range (N + 1)) ×ˢ (range (N + 1)) | t.1.Prime ∧ t.2.Prime ∧ N - t.1 - t.2 ≠ 0 ∧
    (N - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ N}

/-- (2) `K = ∏_p (1 + 1/(p-1)³)` over all primes. -/
def K : ℝ := ∏' p : {p : ℕ // p.Prime}, (1 + 1 / ((p : ℝ) - 1) ^ 3)

/-- (3) `P(N) = ∏_{p ∣ N} (1 - 1/(p² - 3p + 3))`. -/
def P (N : ℕ) : ℝ := ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3))

/-- (1) Vinogradov: `I(N) = (1 + ε) N² K P(N) / (2 (log N)³)` with `ε → 0` over odd `N`. -/
def Vinogradov1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N, Odd N → N0 ≤ N →
    |(I N : ℝ) - (N : ℝ) ^ 2 * K * P N / (2 * Real.log N ^ 3)| ≤
      ε * ((N : ℝ) ^ 2 * K * P N / (2 * Real.log N ^ 3))

/-! ### The Euler factors -/

theorem euler_factor (p : ℝ) (hp : 3 ≤ p) :
    (1 + 1 / (p - 1) ^ 3) * (1 - 1 / (p ^ 2 - 3 * p + 3)) = 1 - 1 / (p - 1) ^ 2 := by
  have h1 : (p - 1) ≠ 0 := by intro h; linarith
  have h2 : p ^ 2 - 3 * p + 3 ≠ 0 := by nlinarith
  rw [one_add_div (pow_ne_zero 3 h1), one_sub_div h2, one_sub_div (pow_ne_zero 2 h1),
    div_mul_div_comm, div_eq_div_iff (mul_ne_zero (pow_ne_zero 3 h1) h2) (pow_ne_zero 2 h1)]
  ring

theorem P_factor_pos {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    0 < 1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3) := by
  have h3 : (3 : ℝ) ≤ p := by
    have := hp.two_le; exact_mod_cast (by omega : 3 ≤ p)
  have hd : 1 < (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
  have : 1 / ((p : ℝ) ^ 2 - 3 * p + 3) < 1 := by rw [div_lt_one (by linarith)]; exact hd
  linarith

theorem P_pos {N : ℕ} (hN : Odd N) : 0 < P N := by
  unfold P
  apply Finset.prod_pos
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  apply P_factor_pos hpp
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hdvd)

/-- (1), with `K > 0`, gives every large odd `N` as a sum of three primes. -/
theorem ternary_of_vinogradov1 (hV : Vinogradov1) (hK : 0 < K) :
    ∃ N0 : ℕ, ∀ N, Odd N → N0 ≤ N → IsTernarySum N := by
  obtain ⟨N0, hN0⟩ := hV (1 / 2) (by norm_num)
  refine ⟨max N0 2, fun N hN hle => ?_⟩
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hle
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hM : 0 < (N : ℝ) ^ 2 * K * P N / (2 * Real.log N ^ 3) := by
    have := P_pos hN; positivity
  have h := hN0 N hN (le_of_max_le_left hle)
  have hI : 0 < (I N : ℝ) := by
    have := (abs_le.mp h).1; linarith
  have hI' : 0 < I N := by exact_mod_cast hI
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hI'
  simp only [Finset.mem_filter] at ht
  obtain ⟨-, h1, h2', -, h3, hs⟩ := ht
  exact ⟨t.1, t.2, N - t.1 - t.2, h1, h2', h3, by omega⟩

theorem one_le_K_factor (p : {p : ℕ // p.Prime}) : 1 ≤ 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
    apply div_nonneg zero_le_one; apply pow_nonneg; linarith
  linarith

/-- `K ≥ 1`, whether or not the product converges; it does, but that is not needed here. -/
theorem one_le_K : 1 ≤ K := by
  unfold K
  by_cases h : Multipliable (fun p : {p : ℕ // p.Prime} => 1 + 1 / ((p : ℝ) - 1) ^ 3)
  · have := h.prod_le_tprod_of_nonneg (s := ∅) (by simp)
      (fun i _ => one_le_K_factor i)
    simpa using this
  · rw [tprod_eq_one_of_not_multipliable h]

/-- (1) gives every large odd `N` as a sum of three primes, unconditionally in `K`. -/
theorem ternary_of_vinogradov1' (hV : Vinogradov1) :
    ∃ N0 : ℕ, ∀ N, Odd N → N0 ≤ N → IsTernarySum N :=
  ternary_of_vinogradov1 hV (by linarith [one_le_K])

end LeanLab.VanDerCorput1939
