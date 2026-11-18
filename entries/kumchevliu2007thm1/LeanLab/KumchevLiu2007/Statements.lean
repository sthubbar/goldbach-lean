module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
P0088 A. V. Kumchev, J. Y. Liu, "Sums of primes and squares of primes in short intervals",
arXiv 0801.0130, v1 read 2026-10-17.
H2 is the set of even n with n not congruent to 1 mod 3, H3 the set of n with n congruent to
3 mod 24 and 5 not dividing n. E2(X) counts n in H2, n ≤ X, not of the form p1 + p2^2;
E3(X) counts n in H3, n ≤ X, not of the form p1^2 + p2^2 + p3^2; E4(X) counts n ≤ X with
n congruent to 4 mod 24, not a sum of four squares of primes.
Theorem 2: for fixed A > 0 and X^0.33 ≤ H ≤ X, E2(X+H) - E2(X) ≪ H (log X)^{-A}.
Theorem 3: for fixed A > 0 and X^{7/20} ≤ H ≤ X, E3(X+H) - E3(X) ≪ H (log X)^{-A}.
Corollary 1: for fixed A > 0 and X^0.27 ≤ H ≤ X, E4(X+H) - E4(X) ≪ H (log X)^{-A}.
Theorem 1, an asymptotic formula for R2(n), is not encoded: its R2 and r2 depend on a
parameter Y = X^θ1 that the paper fixes only inside the proof. Its stated consequence,
(2) for H ≥ X^{7/18+ε}, is derived below from Theorem 2.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here concerns it directly; these are Hua type problems.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007
open Real

attribute [local instance] Classical.propDecidable

/-! ### Definitions -/

/-- `n = p₁ + p₂²` with `p₁, p₂` prime. The paper's conjecture says "another prime", but its
counting function `R₂` and the sets `E₂` do not require `p₁ ≠ p₂`; we follow `E₂`. -/
def IsPrimePlusPrimeSq (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q ^ 2

/-- `n = p₁² + p₂² + p₃²` with primes `p₁, p₂, p₃`. -/
def IsThreePrimeSquares (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p ^ 2 + q ^ 2 + r ^ 2

/-- `n = p₁² + p₂² + p₃² + p₄²` with primes `p₁, …, p₄`. -/
def IsFourPrimeSquares (n : ℕ) : Prop :=
  ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ n = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2

/-- The paper's `ℋ₂ = {n ∈ ℕ : n ≢ 1 (mod 3), 2 ∣ n}`. -/
def InH2 (n : ℕ) : Prop := n % 3 ≠ 1 ∧ 2 ∣ n

/-- The paper's `ℋ₃ = {n ∈ ℕ : n ≡ 3 (mod 24), 5 ∤ n}`. -/
def InH3 (n : ℕ) : Prop := n % 24 = 3 ∧ ¬ 5 ∣ n

/-- The congruence class `n ≡ 4 (mod 24)` used for `E₄`. -/
def InH4 (n : ℕ) : Prop := n % 24 = 4

/-- `cntIoc S X H` is the number of natural `n` with `X < n ≤ X + H` and `S n`. -/
noncomputable def cntIoc (S : ℕ → Prop) (X H : ℝ) : ℕ :=
  ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n)).card

/-- The paper's `E₂(X + H) - E₂(X)`: exceptions in `ℋ₂ ∩ (X, X + H]`. -/
noncomputable def E2Short (X H : ℝ) : ℕ := cntIoc (fun n => InH2 n ∧ ¬ IsPrimePlusPrimeSq n) X H

/-- The paper's `E₃(X + H) - E₃(X)`: exceptions in `ℋ₃ ∩ (X, X + H]`. -/
noncomputable def E3Short (X H : ℝ) : ℕ :=
  cntIoc (fun n => InH3 n ∧ ¬ IsThreePrimeSquares n) X H

/-- The paper's `E₄(X + H) - E₄(X)`: exceptions `n ≡ 4 (mod 24)` in `(X, X + H]`. -/
noncomputable def E4Short (X H : ℝ) : ℕ :=
  cntIoc (fun n => InH4 n ∧ ¬ IsFourPrimeSquares n) X H

/-- `ShortExcBound S c`: for every fixed `A > 0`, the count of `n ∈ (X, X + H]` with `S n`
is `≪_A H (log X)^{-A}` whenever `X^c ≤ H ≤ X`. The `≪` is encoded by an explicit
existential constant `C` depending on `A`; the threshold `X0`, also depending on `A`,
only keeps `log X` away from `0` and is the usual reading of `≪` for large `X`. -/
def ShortExcBound (S : ℕ → Prop) (c : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X H : ℝ, X0 ≤ X → X ^ c ≤ H → H ≤ X →
    (cntIoc S X H : ℝ) ≤ C * H / Real.log X ^ A

/-- The `ε` form: for every `ε > 0` the bound holds in `X^{c+ε} ≤ H ≤ X`, constants
depending on `A` and `ε`. -/
def ShortExcBoundEps (S : ℕ → Prop) (c : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ShortExcBound S (c + ε)

/-! ### Monotonicity in the exponent -/

theorem shortExcBound_mono {S : ℕ → Prop} {c c' : ℝ} (hc : c ≤ c') (h : ShortExcBound S c) :
    ShortExcBound S c' := by
  intro A hA
  obtain ⟨C, X0, hC⟩ := h A hA
  refine ⟨C, max X0 1, fun X H hX hH hHX => hC X H (le_of_max_le_left hX) ?_ hHX⟩
  exact le_trans (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hX) hc) hH

theorem shortExcBoundEps_of_shortExcBound {S : ℕ → Prop} {c c' : ℝ} (hc : c ≤ c')
    (h : ShortExcBound S c) : ShortExcBoundEps S c' :=
  fun ε hε => shortExcBound_mono (by linarith) h

/-! ### Congruence conditions by reduction mod small primes -/

theorem sq_mod_three {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : p ^ 2 % 3 = 1 := by
  have b : ¬ 3 ∣ p := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  rw [Nat.pow_mod]
  have := Nat.mod_lt p (by norm_num : 3 > 0)
  interval_cases h : p % 3 <;> omega

theorem sq_mod_24 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : p ^ 2 % 24 = 1 := by
  have a : ¬ 2 ∣ p := fun h => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have b : ¬ 3 ∣ p := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  rw [Nat.pow_mod]
  have := Nat.mod_lt p (by norm_num : 24 > 0)
  interval_cases h : p % 24 <;> omega

theorem sq_mod_five {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : p ^ 2 % 5 = 1 ∨ p ^ 2 % 5 = 4 := by
  have c : ¬ 5 ∣ p := fun h => h5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm
  rw [Nat.pow_mod]
  have := Nat.mod_lt p (by norm_num : 5 > 0)
  interval_cases h : p % 5 <;> omega

/-- With both primes above `3`, `p₁ + p₂²` lies in `ℋ₂`. -/
theorem inH2_of_large {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq3 : 3 < q) :
    InH2 (p + q ^ 2) := by
  have hp2 : p % 2 = 1 := (hp.eq_one_or_self_of_dvd 2 |> fun h => by
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (h ⟨k, by omega⟩) (by omega)
    · omega)
  have hq24 := sq_mod_24 hq (by omega) (by omega)
  have hp3' : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  refine ⟨by omega, by omega⟩

/-- Why `n ≡ 1 (mod 3)` is excluded: such an `n = p₁ + p₂²` forces `p₁ = 3` or `p₂ = 3`,
a degenerate representation. -/
theorem three_of_mod_three_eq_one {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hn : n = p + q ^ 2) (h1 : n % 3 = 1) : p = 3 ∨ q = 3 := by
  by_contra hc
  push Not at hc
  have hq3 := sq_mod_three hq hc.2
  have : 3 ∣ p := by omega
  exact hc.1 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this).symm

/-- With all three primes above `5`, `p₁² + p₂² + p₃²` lies in `ℋ₃`. -/
theorem inH3_of_large {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp5 : 5 < p) (hq5 : 5 < q) (hr5 : 5 < r) : InH3 (p ^ 2 + q ^ 2 + r ^ 2) := by
  have a := sq_mod_24 hp (by omega) (by omega)
  have b := sq_mod_24 hq (by omega) (by omega)
  have c := sq_mod_24 hr (by omega) (by omega)
  have a5 := sq_mod_five hp (by omega)
  have b5 := sq_mod_five hq (by omega)
  have c5 := sq_mod_five hr (by omega)
  refine ⟨by omega, by omega⟩

/-- With all four primes above `3`, `p₁² + p₂² + p₃² + p₄² ≡ 4 (mod 24)`. -/
theorem inH4_of_large {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q) (hr3 : 3 < r) (hs3 : 3 < s) :
    InH4 (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) := by
  have a := sq_mod_24 hp (by omega) (by omega)
  have b := sq_mod_24 hq (by omega) (by omega)
  have c := sq_mod_24 hr (by omega) (by omega)
  have d := sq_mod_24 hs (by omega) (by omega)
  unfold InH4; omega

/-! ### Small kernel examples -/

theorem ex_12 : InH2 12 ∧ IsPrimePlusPrimeSq 12 := ⟨by unfold InH2; omega, ⟨3, 3, by norm_num, by norm_num, by norm_num⟩⟩

theorem ex_30 : InH2 30 ∧ IsPrimePlusPrimeSq 30 := ⟨by unfold InH2; omega, ⟨5, 5, by norm_num, by norm_num, by norm_num⟩⟩

/-- `16 = 7 + 3²` is outside `ℋ₂` yet representable, via the degenerate `p₂ = 3`. -/
theorem ex_16 : ¬ InH2 16 ∧ IsPrimePlusPrimeSq 16 :=
  ⟨by unfold InH2; omega, ⟨7, 3, by norm_num, by norm_num, by norm_num⟩⟩

theorem ex_27 : InH3 27 ∧ IsThreePrimeSquares 27 :=
  ⟨by unfold InH3; omega, ⟨3, 3, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

theorem ex_147 : InH3 147 ∧ IsThreePrimeSquares 147 :=
  ⟨by unfold InH3; omega, ⟨7, 7, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

theorem ex_196 : InH4 196 ∧ IsFourPrimeSquares 196 :=
  ⟨by unfold InH4; omega, ⟨7, 7, 7, 7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-! ### From a small exceptional count to a representable `n` in each interval -/

/-- If every `n ≡ r (mod m)` satisfies `S`, and fewer than about `H/m` of the `n` in `(X, X + H]`
satisfy `S` but not `P`, then some `n ∈ (X, X + H]` satisfies both `S` and `P`. -/
theorem exists_of_cnt_small (S P : ℕ → Prop) {m r : ℕ} (hm : 0 < m) (hr : r < m)
    (hS : ∀ n, n % m = r → S n) {X H : ℝ} (hX : 0 ≤ X)
    (hsmall : (cntIoc (fun n => S n ∧ ¬ P n) X H : ℝ) ≤ H / m - 2) :
    ∃ n : ℕ, X < n ∧ (n : ℝ) ≤ X + H ∧ S n ∧ P n := by
  by_contra hno
  push Not at hno
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℕ := ⌊X / m⌋₊ + 1 with ha
  set F : ℕ := ⌊(X + H) / m⌋₊ with hF
  set b : ℕ := F - 1 with hb
  have hsub : (Finset.Icc a b).image (fun k => m * k + r) ⊆
      (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ (S n ∧ ¬ P n)) := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_Icc] at hn
    obtain ⟨k, ⟨hak, hkb⟩, rfl⟩ := hn
    have hk1 : k + 1 ≤ F := by omega
    have hlow : X < ((m * k + r : ℕ) : ℝ) := by
      have h1 : X / m < (a : ℝ) := by rw [ha]; push_cast; exact Nat.lt_floor_add_one _
      have h2 : (a : ℝ) ≤ k := by exact_mod_cast hak
      have h3 : X < m * (k : ℝ) := by
        have := (div_lt_iff₀ hmR).mp (lt_of_lt_of_le h1 h2); linarith
      push_cast; have : (0 : ℝ) ≤ r := Nat.cast_nonneg _; linarith
    have hup : ((m * k + r : ℕ) : ℝ) ≤ X + H := by
      have h1 : m * k + r ≤ m * F := by
        calc m * k + r ≤ m * k + m := by omega
          _ = m * (k + 1) := by ring
          _ ≤ m * F := Nat.mul_le_mul_left _ hk1
      have hF0 : 0 < F := by omega
      have h2 : (F : ℝ) ≤ (X + H) / m := Nat.floor_le (by
        by_contra hneg; push Not at hneg
        have : F = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega)
      have h3 : ((m * k + r : ℕ) : ℝ) ≤ (m : ℝ) * F := by exact_mod_cast h1
      have h4 : (m : ℝ) * F ≤ X + H := by
        rw [le_div_iff₀ hmR] at h2; linarith
      linarith
    have hSn : S (m * k + r) := hS _ (by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr)
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor hup), hlow, hSn, fun hP => ?_⟩
    exact hno _ hlow hup hSn hP
  have hcard : (Finset.Icc a b).card ≤ cntIoc (fun n => S n ∧ ¬ P n) X H := by
    have hinj : Function.Injective (fun k : ℕ => m * k + r) := fun x y hxy => by
      have : m * x = m * y := by simpa using hxy
      exact Nat.eq_of_mul_eq_mul_left hm this
    rw [← Finset.card_image_of_injective (Finset.Icc a b) hinj]
    unfold cntIoc
    convert Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hnat : F ≤ (b + 1 - a) + a := by omega
  have hreal : (F : ℝ) ≤ (cntIoc (fun n => S n ∧ ¬ P n) X H : ℝ) + a := by
    have h1 : ((F : ℕ) : ℝ) ≤ ((b + 1 - a + a : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : ((b + 1 - a : ℕ) : ℝ) ≤ cntIoc (fun n => S n ∧ ¬ P n) X H := by exact_mod_cast hcard
    push_cast at h1; linarith
  have hF' : (X + H) / m < (F : ℝ) + 1 := Nat.lt_floor_add_one _
  have ha' : (a : ℝ) ≤ X / m + 1 := by
    rw [ha]; push_cast; linarith [Nat.floor_le (div_nonneg hX hmR.le)]
  have : (X + H) / m = X / m + H / m := add_div _ _ _
  linarith

/-- A `ShortExcBound` with exponent `c > 0` puts an `n` with `S n` and `P n` in every interval
`(X, X + H]` with `X^c ≤ H ≤ X` and `X` large, when a residue class mod `m` lies in `S`. -/
theorem exists_of_shortExcBound (S P : ℕ → Prop) {m r : ℕ} (hm : 0 < m) (hr : r < m)
    (hS : ∀ n, n % m = r → S n) {c : ℝ} (hc : 0 < c)
    (h : ShortExcBound (fun n => S n ∧ ¬ P n) c) :
    ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X → X ^ c ≤ H → H ≤ X →
      ∃ n : ℕ, X < n ∧ (n : ℝ) ≤ X + H ∧ S n ∧ P n := by
  obtain ⟨C, X0, hC⟩ := h 1 one_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set M := max C 0
  refine ⟨max (max X0 2) (max (Real.exp (2 * m * M)) ((4 * m : ℝ) ^ (1 / c))),
    fun X H hX hH hHX => ?_⟩
  have hX0 : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : (2 : ℝ) ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp (2 * m * M) ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX4 : (4 * m : ℝ) ^ (1 / c) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogM : 2 * m * M ≤ Real.log X := by
    rw [← Real.log_exp (2 * m * M)]; exact Real.log_le_log (Real.exp_pos _) hXe
  have h4m : (4 * m : ℝ) ≤ X ^ c := by
    calc (4 * m : ℝ) = ((4 * m : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hX4 hc.le
  have hH4 : 4 * m ≤ H := le_trans h4m hH
  have hHpos : 0 < H := by linarith
  have hM0 : 0 ≤ M := le_max_right _ _
  have hb := hC X H hX0 hH hHX
  rw [Real.rpow_one] at hb
  apply exists_of_cnt_small S P hm hr hS hXpos.le
  have hkey : M * H / Real.log X ≤ H / (2 * m) := by
    rw [div_le_div_iff₀ hlogpos (by positivity)]
    calc M * H * (2 * m) = (2 * m * M) * H := by ring
      _ ≤ Real.log X * H := by gcongr
      _ = H * Real.log X := by ring
  have hhalf : H / (2 * m) ≤ H / m - 2 := by
    have e1 : H / (2 * m) = H / m - H / (2 * m) := by field_simp; ring
    have e2 : 2 ≤ H / (2 * m) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  calc (cntIoc (fun n => S n ∧ ¬ P n) X H : ℝ) ≤ C * H / Real.log X := hb
    _ ≤ M * H / Real.log X := by gcongr; exact le_max_left _ _
    _ ≤ H / (2 * m) := hkey
    _ ≤ H / m - 2 := hhalf

end LeanLab.KumchevLiu2007
