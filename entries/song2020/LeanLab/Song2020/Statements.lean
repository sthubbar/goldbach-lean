module

public import Mathlib

/-!
# Song 2020, the statement of Theorem 1

Yanbo Song, The ternary Goldbach-Vinogradov theorem with almost equal Piatetski-Shapiro
primes, arXiv 2012.06322 v1, 2020.

Theorem 1: for every large enough odd number n the equation
  n = p₁ + p₂ + p₃,  |pᵢ − n/3| ≤ y,  pᵢ ∈ A_γ  (1 ≤ i ≤ 3)
is solvable for y > n^{(52−45γ)/8} and 44/45 < γ < 1.
Here A_γ = {prime p | p = [m^{1/γ}], m ≥ 1}, [x] the greatest integer not exceeding x,
and γ = 1/c with c > 1.

Encoding: "large enough" is an explicit existential threshold `N₀`, chosen after `γ`
and before `n` and `y`; the paper's wording puts "for every large enough n" before
"solvable for y > ...", so `N₀` does not depend on `y`.

AI wrote the Lean code, Claude, 2026-10-17. Checked by the Lean kernel.
Binary Goldbach is open; ternary Goldbach is a theorem of Helfgott 2013.
-/

@[expose] public section

namespace LeanLab.Song2020

/-- Piatetski-Shapiro prime for `γ`: a prime `p` with `p = [m^{1/γ}]` for some `m ≥ 1`. -/
def IsPSPrime (γ : ℝ) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, 1 ≤ m ∧ (p : ℤ) = ⌊(m : ℝ) ^ (1 / γ)⌋

/-- `n` is a sum of three Piatetski-Shapiro primes for `γ`, each within `y` of `n/3`. -/
def IsAlmostEqualPSTernary (γ : ℝ) (n : ℕ) (y : ℝ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, IsPSPrime γ p₁ ∧ IsPSPrime γ p₂ ∧ IsPSPrime γ p₃ ∧ p₁ + p₂ + p₃ = n ∧
    |(p₁ : ℝ) - n / 3| ≤ y ∧ |(p₂ : ℝ) - n / 3| ≤ y ∧ |(p₃ : ℝ) - n / 3| ≤ y

/-- For every large enough odd `n`, every `y > n^θ` admits a representation. -/
def SongWindow (γ θ : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ θ < y →
    IsAlmostEqualPSTernary γ n y

/-- The paper's window exponent `(52 − 45γ)/8`. -/
noncomputable def songExponent (γ : ℝ) : ℝ := (52 - 45 * γ) / 8

/-- Song 2020, Theorem 1. -/
def SongTheorem1 : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → SongWindow γ (songExponent γ)


theorem IsPSPrime.prime {γ : ℝ} {p : ℕ} (h : IsPSPrime γ p) : p.Prime := h.1

/-- At `γ = 1` the Piatetski-Shapiro primes are exactly the primes. -/
theorem isPSPrime_one_iff (p : ℕ) : IsPSPrime 1 p ↔ p.Prime := by
  refine ⟨fun h => h.1, fun hp => ⟨hp, p, hp.one_lt.le, ?_⟩⟩
  simp

theorem isAlmostEqualPSTernary_mono {γ : ℝ} {n : ℕ} {y y' : ℝ} (hy : y ≤ y')
    (H : IsAlmostEqualPSTernary γ n y) : IsAlmostEqualPSTernary γ n y' := by
  obtain ⟨a, b, c, ha, hb, hc, hs, h1, h2, h3⟩ := H
  exact ⟨a, b, c, ha, hb, hc, hs, h1.trans hy, h2.trans hy, h3.trans hy⟩

/-- A smaller window exponent is a stronger statement. -/
theorem songWindow_mono {γ θ θ' : ℝ} (hθ : θ ≤ θ') (H : SongWindow γ θ) :
    SongWindow γ θ' := by
  obtain ⟨N₀, hN⟩ := H
  refine ⟨max N₀ 1, fun n ho hn y hy => ?_⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  exact hN n ho ((le_max_left _ _).trans hn) y
    (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le h1 hθ) hy)


/-- On the paper's range the window exponent lies strictly between 7/8 and 1. -/
theorem songExponent_mem {γ : ℝ} (h1 : 44 / 45 < γ) (h2 : γ < 1) :
    7 / 8 < songExponent γ ∧ songExponent γ < 1 := by
  unfold songExponent; constructor <;> linarith

/-! ### Why `γ` must be restricted: at `γ = 1/2` there are no such primes -/

theorem not_isPSPrime_half (p : ℕ) : ¬ IsPSPrime (1 / 2) p := by
  rintro ⟨hp, m, hm1, hm⟩
  have : (m : ℝ) ^ (1 / (1 / 2 : ℝ)) = ((m ^ 2 : ℕ) : ℝ) := by
    rw [show (1 / (1 / 2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; rfl
  rw [this, Int.floor_natCast] at hm
  have hpm : p = m ^ 2 := by exact_mod_cast hm
  rw [hpm] at hp
  rcases hp.eq_one_or_self_of_dvd m (dvd_pow_self m two_ne_zero) with h | h
  · subst h; norm_num at hp
  · have h2 := hp.two_le
    nlinarith

theorem not_songWindow_half (θ : ℝ) : ¬ SongWindow (1 / 2) θ := by
  rintro ⟨N₀, hN⟩
  obtain ⟨a, -, -, ha, -⟩ := hN (2 * N₀ + 1) ⟨N₀, rfl⟩ (by omega) _ (lt_add_one _)
  exact not_isPSPrime_half a ha

/-! ### Kernel checks at the sample exponent `γ = 2/3`, that is `c = 3/2` -/

theorem floor_rpow_threeHalves (m : ℕ) :
    ⌊(m : ℝ) ^ (1 / (2 / 3 : ℝ))⌋ = (Nat.sqrt (m ^ 3) : ℤ) := by
  have : (m : ℝ) ^ (1 / (2 / 3 : ℝ)) = √((m ^ 3 : ℕ) : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (1 / (2 / 3 : ℝ)) = ((3 : ℕ) : ℝ) * (1 / 2) by norm_num,
      Real.rpow_mul (by positivity), Real.rpow_natCast]
    push_cast; rfl
  rw [this, Real.floor_real_sqrt_eq_nat_sqrt]

theorem isPSPrime_twoThirds_iff (p : ℕ) :
    IsPSPrime (2 / 3) p ↔ p.Prime ∧ ∃ m ∈ Finset.Icc 1 p, Nat.sqrt (m ^ 3) = p := by
  unfold IsPSPrime
  simp only [floor_rpow_threeHalves, Nat.cast_inj, Finset.mem_Icc]
  refine and_congr_right fun _ => ⟨fun ⟨m, hm, he⟩ => ⟨m, ⟨hm, ?_⟩, he.symm⟩,
    fun ⟨m, ⟨hm, _⟩, he⟩ => ⟨m, hm, he.symm⟩⟩
  rw [he]
  calc m = Nat.sqrt (m * m) := (Nat.sqrt_eq m).symm
    _ ≤ Nat.sqrt (m ^ 3) := Nat.sqrt_le_sqrt (by
        rw [pow_succ, sq]; exact Nat.le_mul_of_pos_right _ (by omega))

theorem isPSPrime_twoThirds_2 : IsPSPrime (2 / 3) 2 :=
  (isPSPrime_twoThirds_iff 2).2 ⟨by norm_num, by decide +kernel⟩
theorem isPSPrime_twoThirds_5 : IsPSPrime (2 / 3) 5 :=
  (isPSPrime_twoThirds_iff 5).2 ⟨by norm_num, by decide +kernel⟩
theorem isPSPrime_twoThirds_11 : IsPSPrime (2 / 3) 11 :=
  (isPSPrime_twoThirds_iff 11).2 ⟨by norm_num, by decide +kernel⟩
theorem isPSPrime_twoThirds_31 : IsPSPrime (2 / 3) 31 :=
  (isPSPrime_twoThirds_iff 31).2 ⟨by norm_num, by decide +kernel⟩
theorem not_isPSPrime_twoThirds_3 : ¬ IsPSPrime (2 / 3) 3 := by
  rw [isPSPrime_twoThirds_iff]; decide +kernel
theorem not_isPSPrime_twoThirds_7 : ¬ IsPSPrime (2 / 3) 7 := by
  rw [isPSPrime_twoThirds_iff]; decide +kernel
theorem not_isPSPrime_twoThirds_13 : ¬ IsPSPrime (2 / 3) 13 := by
  rw [isPSPrime_twoThirds_iff]; decide +kernel

end LeanLab.Song2020
