module

public import Mathlib
public import LeanLab.Song2020.Statements
public import LeanLab.Common.CircleOrth

/-!
Yanbo Song, "The ternary Goldbach-Vinogradov theorem with almost equal
Piatetski-Shapiro primes", arXiv 2012.06322 v1, 2020.

The Lean in this file was written by an AI assistant, Claude, for the Lean Lab.
Checked by the Lean kernel.

Statements of the paper's Lemmas 3, 4, 5 and of the asymptotic formula for R(n) that
Section 4 proves and from which Theorem 1 follows. Theorem 1 itself is stated in
`LeanLab.Song2020.Statements`.

In this copy:
* `Lemma3` is the paper's citation of Theorem 3 of its reference [11], Pan and Pan 1988;
  it is not proved and enters the main theorems only as a hypothesis.
* `Lemma4`, the paper's main new estimate, is proved in `Wire1122Lemma4`.
* `song_lemma5`, the mean square bounds, is proved here.
* `Asymptotic`, the Section 4 formula for R(n), is a statement only.
* `singular_lower`, an elementary positivity fact the deduction of Theorem 1 needs, is
  proved here.

Encoding notes.
* Window: primes p with |p - n/3| < y, strict as in the definitions of f, g and R(n).
* f carries the weight (1/γ) p^{1-γ} and runs over Piatetski-Shapiro primes `IsPSPrime γ`,
  the paper's A_{1/γ} in its c = 1/γ notation.
* Lemma 4's hypothesis "there are a, q with q ≤ log n and |qα - a| < 1/log n" holds for
  every real α by Dirichlet, so the Lean form quantifies over every α.
* Every implied constant is an explicit existential C chosen before n, y and α.
* The extra hypothesis y ≤ n/3 makes each statement weaker than the printed one,
  never stronger; the paper only uses y below n^{1-ε}.
* The singular series is a `tprod` over primes; it converges absolutely, so `tprod` is its
  value.
-/

@[expose] public section

namespace LeanLab.Song2020.State1562

open LeanLab.Song2020
open scoped Classical

noncomputable section

/-- `e(x) = exp(2πix)`. -/
def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The primes `p` with `|p - n/3| < y`. -/
def windowPrimes (n : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun p => p.Prime ∧ |(p : ℝ) - (n : ℝ) / 3| < y)

/-- The Piatetski-Shapiro weight `(1/γ) p^{1-γ}`. -/
def psWeight (γ : ℝ) (p : ℕ) : ℝ := (1 / γ) * (p : ℝ) ^ (1 - γ)

/-- `f(α) = Σ_{|p-n/3|<y, p ∈ A_{1/γ}} (1/γ) p^{1-γ} e(αp)`. -/
def fS (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
    (psWeight γ p : ℂ) * eC (α * p)

/-- `g(α) = Σ_{|p-n/3|<y} e(αp)`. -/
def gS (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, eC (α * p)

/-- The local factor of `𝔖₃(n)` at a prime `p`. -/
def singFactor (n p : ℕ) : ℝ :=
  if p ∣ n then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- `𝔖₃(n) = Π_{p|n} (1 - 1/(p-1)²) Π_{p∤n} (1 + 1/(p-1)³)`. -/
def singular3 (n : ℕ) : ℝ := ∏' p : Nat.Primes, singFactor n p

/-- The main term `𝔖₃(n) · 3y² / log³ n`. -/
def mainTerm (n : ℕ) (y : ℝ) : ℝ := singular3 n * (3 * y ^ 2 / Real.log n ^ 3)

/-- `R(n) = ∫₀¹ f(α)³ e(-nα) dα`, the weighted count of Section 4. -/
def RS (γ : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, fS γ n y α ^ 3 * eC (-(n * α))

/-- `∫₀¹ g(α)³ e(-nα) dα`. -/
def gCube (n : ℕ) (y : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, gS n y α ^ 3 * eC (-(n * α))

/-- Lemma 3, for windows `y ≥ n^θ`: `∫₀¹ g³ e(-nα) = 𝔖₃(n) 3y²/log³ n + O(y²/log⁴ n)`,
restricted to odd `n` and `y ≤ n/3`. -/
def Lemma3 (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ θ ≤ y → y ≤ (n : ℝ) / 3 →
    ‖gCube n y - (mainTerm n y : ℂ)‖ ≤ C * (y ^ 2 / Real.log n ^ 4)

/-- Lemma 4: for `44/45 < γ < 1`, `y > n^{(52-45γ)/8}` and every `α`,
`f(α) = g(α) + O(n^{21/31 - 14γ/31 + ε} y^{23/31})`. -/
def Lemma4 : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ songExponent γ < y →
      y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
        ‖fS γ n y α - gS n y α‖ ≤
          C * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * y ^ ((23 : ℝ) / 31))

/-- Lemma 5: `∫₀¹ |f|² ≪ n^{1-γ} y` and `∫₀¹ |g|² ≪ y`, on the range of Lemma 4. -/
def Lemma5 : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ songExponent γ < y →
      y ≤ (n : ℝ) / 3 →
        (∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) ≤ C * ((n : ℝ) ^ (1 - γ) * y) ∧
        (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2) ≤ C * y

/-- Section 4: `R(n) = 𝔖₃(n) 3y²/log³ n + O(y²/log⁴ n)` for odd `n`. -/
def Asymptotic : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ songExponent γ < y →
      y ≤ (n : ℝ) / 3 →
        ‖RS γ n y - (mainTerm n y : ℂ)‖ ≤ C * (y ^ 2 / Real.log n ^ 4)

/-- For odd `n`, `𝔖₃(n)` is bounded below by a positive constant; used, unstated in the
paper, when Section 4 concludes `R(n) > 0`. -/
def SingularLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, Odd n → c ≤ singular3 n

/-! ### Sealed statements -/



/-! ### Mean square identities -/

/-- Section 3 Lemma 5. Parseval for a finite sum with natural frequencies. -/
theorem parseval_nat139 (s : Finset ℕ) (a : ℕ → ℂ) :
    (∫ α in (0 : ℝ)..1, ‖∑ p ∈ s, a p * eC (α * p)‖ ^ 2) =
      ∑ p ∈ s, ‖a p‖ ^ 2 := by
  have h := LeanLab.CircleOrth.parseval_norm
    (s.map (Nat.castEmbedding : ℕ ↪ ℤ)) (fun k => a k.toNat)
  simpa [LeanLab.CircleOrth.S, Finset.sum_map, eC, LeanLab.CircleOrth.ee, mul_comm] using h

/-- Section 3 Lemma 5. The exact mean square of g is its number of terms. -/
theorem gS_mean_square139 (n : ℕ) (y : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2) = (windowPrimes n y).card := by
  simpa [gS] using parseval_nat139 (windowPrimes n y) (fun _ => 1)

/-- Section 3 Lemma 5. The exact mean square of f is the sum of squared weights. -/
theorem fS_mean_square139 (γ : ℝ) (n : ℕ) (y : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) =
      ∑ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p), (psWeight γ p) ^ 2 := by
  simpa [fS, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    parseval_nat139 ((windowPrimes n y).filter (fun p => IsPSPrime γ p))
      (fun p => (psWeight γ p : ℂ))

/-- Section 3 Lemma 5. A window of radius y contains at most 2y + 2 integers. -/
theorem windowPrimes_card_le139 (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    ((windowPrimes n y).card : ℝ) ≤ 2 * y + 2 := by
  let a : ℤ := ⌊(n : ℝ) / 3 - y⌋
  let b : ℤ := ⌊(n : ℝ) / 3 + y⌋
  have hab : a ≤ b := Int.floor_mono (by linarith)
  have hc : (windowPrimes n y).card ≤ (Finset.Icc a b).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ => (p : ℤ))
    · intro p hp
      have hw := (Finset.mem_filter.mp hp).2.2
      have hpw := abs_lt.mp hw
      change (p : ℤ) ∈ Finset.Icc a b
      rw [Finset.mem_Icc]
      constructor
      · apply Int.le_of_lt_add_one
        have ha := Int.floor_le ((n : ℝ) / 3 - y)
        have hreal : (a : ℝ) < (p : ℝ) + 1 := by dsimp [a]; linarith
        exact_mod_cast hreal
      · exact Int.le_floor.mpr (by exact_mod_cast (show (p : ℝ) ≤ (n : ℝ) / 3 + y by linarith))
    · exact Nat.cast_injective.injOn
  have hcard : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
    Int.card_Icc_of_le a b (by omega)
  have hcardR : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
    exact_mod_cast hcard
  have ha := Int.lt_floor_add_one ((n : ℝ) / 3 - y)
  have hb := Int.floor_le ((n : ℝ) / 3 + y)
  have hcr : ((windowPrimes n y).card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by exact_mod_cast hc
  dsimp [a, b] at hcardR
  linarith

/-- Section 3 Lemma 5. For y at least one, the mean square of g is at most 4y. -/
theorem gS_mean_square_le139 (n : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2) ≤ 4 * y := by
  rw [gS_mean_square139]
  have h := windowPrimes_card_le139 n y (by linarith)
  linarith

/-- Section 3 Lemma 5. An injective integer family in a real interval has bounded size. -/
theorem card_real_interval139 {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : Function.Injective f) (A B : ℝ) (hAB : A ≤ B)
    (hb : ∀ i, A ≤ (f i : ℝ) ∧ (f i : ℝ) ≤ B) :
    (Fintype.card ι : ℝ) ≤ B - A + 2 := by
  classical
  let a : ℤ := ⌊A⌋
  let b : ℤ := ⌊B⌋
  have hab : a ≤ b := Int.floor_mono hAB
  have hc : Fintype.card ι ≤ (Finset.Icc a b).card := by
    have h := Finset.card_le_card_of_injOn (s := Finset.univ) (t := Finset.Icc a b)
      f (fun i _ => ?_) hf.injOn
    · simpa using h
    · change f i ∈ Finset.Icc a b
      rw [Finset.mem_Icc]
      constructor
      · apply Int.le_of_lt_add_one
        have ha := Int.floor_le A
        have hreal : (a : ℝ) < (f i : ℝ) + 1 := by dsimp [a]; linarith [(hb i).1]
        exact_mod_cast hreal
      · exact Int.le_floor.mpr (hb i).2
  have hcard : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
    Int.card_Icc_of_le a b (by omega)
  have hcardR : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
    exact_mod_cast hcard
  have ha := Int.lt_floor_add_one A
  have hb' := Int.floor_le B
  have hcr : (Fintype.card ι : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by exact_mod_cast hc
  dsimp [a, b] at hcardR
  linarith

/-- Section 3 Lemma 5. The defining floor witness lies between consecutive prime powers. -/
theorem ps_witness_bounds139 {γ : ℝ} (hγ : 0 < γ) {p m : ℕ}
    (hm : (p : ℤ) = ⌊(m : ℝ) ^ (1 / γ)⌋) :
    (p : ℝ) ^ γ ≤ m ∧ (m : ℝ) < ((p : ℝ) + 1) ^ γ := by
  have hlo := Int.floor_le ((m : ℝ) ^ (1 / γ))
  have hhi := Int.lt_floor_add_one ((m : ℝ) ^ (1 / γ))
  rw [← hm, Int.cast_natCast] at hlo hhi
  have he : ((m : ℝ) ^ (1 / γ)) ^ γ = m := by
    simpa only [one_div] using Real.rpow_inv_rpow (Nat.cast_nonneg m) hγ.ne'
  constructor
  · simpa only [he] using Real.rpow_le_rpow (Nat.cast_nonneg p) hlo hγ.le
  · simpa only [he] using Real.rpow_lt_rpow (by positivity) hhi hγ

/-- Section 3 Lemma 5. Floor witnesses bound the number of restricted primes in any interval. -/
theorem ps_card_of_power_bounds139 (γ : ℝ) (hγ : 0 < γ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, IsPSPrime γ p) (A B : ℝ) (hAB : A ≤ B)
    (hb : ∀ p ∈ s, A ≤ (p : ℝ) ^ γ ∧ ((p : ℝ) + 1) ^ γ ≤ B) :
    (s.card : ℝ) ≤ B - A + 2 := by
  classical
  let m : s → ℕ := fun p => Classical.choose (hs p p.property).2
  have hm (p : s) : (p.val : ℤ) = ⌊(m p : ℝ) ^ (1 / γ)⌋ :=
    (Classical.choose_spec (hs p p.property).2).2
  have hinj : Function.Injective (fun p : s => (m p : ℤ)) := by
    intro p q h
    have hm' : m p = m q := by
      change (m p : ℤ) = (m q : ℤ) at h
      exact_mod_cast h
    have hpq : (p.val : ℤ) = q.val := by rw [hm p, hm q, hm']
    apply Subtype.ext
    exact_mod_cast hpq
  have h := card_real_interval139 (fun p : s => (m p : ℤ)) hinj A B hAB (fun p => ?_)
  · simpa using h
  · have hw := ps_witness_bounds139 hγ (hm p)
    simpa only [Int.cast_natCast] using
      And.intro ((hb p p.property).1.trans hw.1) (hw.2.le.trans (hb p p.property).2)

/-- Section 3 Lemma 5. Concavity bounds an increment of a real power by its left slope. -/
theorem rpow_increment_le139 (γ A B : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hA : 0 < A) (hAB : A ≤ B) :
    B ^ γ - A ^ γ ≤ γ * A ^ (γ - 1) * (B - A) := by
  have hs : -1 ≤ (B - A) / A := by
    have := div_nonneg (sub_nonneg.mpr hAB) hA.le
    linarith
  have h := rpow_one_add_le_one_add_mul_self hs hγ hγ1
  have he : 1 + (B - A) / A = B / A := by field_simp; ring
  rw [he, Real.div_rpow (by linarith) hA.le] at h
  have hpow : 0 < A ^ γ := Real.rpow_pos_of_pos hA _
  have hmul := (div_le_iff₀ hpow).mp h
  rw [Real.rpow_sub hA, Real.rpow_one]
  calc
    B ^ γ - A ^ γ ≤ (1 + γ * ((B - A) / A)) * A ^ γ - A ^ γ := by linarith
    _ = γ * (A ^ γ / A) * (B - A) := by ring

/-- Section 3 Lemma 5. The number of restricted primes in the window has its natural scale. -/
theorem ps_window_card_le139 (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (n : ℕ) (hn : 6 ≤ n) (y : ℝ) (hy : 1 ≤ y)
    (hscale : (n : ℝ) ^ (1 - γ) ≤ y) (hyupper : y ≤ (n : ℝ) / 3) :
    (((windowPrimes n y).filter (fun p => IsPSPrime γ p)).card : ℝ) ≤
      20 * ((n : ℝ) ^ (γ - 1) * y) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : 0 < (n : ℝ) ^ (γ - 1) := Real.rpow_pos_of_pos hn0 _
  have hcancel : (n : ℝ) ^ (γ - 1) * (n : ℝ) ^ (1 - γ) = 1 := by
    rw [← Real.rpow_add hn0, show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero]
  have hscaled : 1 ≤ (n : ℝ) ^ (γ - 1) * y := by
    calc
      1 = (n : ℝ) ^ (γ - 1) * (n : ℝ) ^ (1 - γ) := hcancel.symm
      _ ≤ (n : ℝ) ^ (γ - 1) * y := mul_le_mul_of_nonneg_left hscale hpow.le
  let s := (windowPrimes n y).filter (fun p => IsPSPrime γ p)
  have hs : ∀ p ∈ s, IsPSPrime γ p := fun p hp => (Finset.mem_filter.mp hp).2
  have hwin (p : ℕ) (hp : p ∈ s) :
      (n : ℝ) / 3 - y < p ∧ (p : ℝ) < (n : ℝ) / 3 + y := by
    have := abs_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    constructor <;> linarith
  by_cases hlarge : (n : ℝ) / 6 ≤ y
  · have hc := ps_card_of_power_bounds139 γ hγ s hs 0 ((n : ℝ) ^ γ)
      (Real.rpow_nonneg hn0.le _) (fun p hp => ?_)
    · have hmul : (n : ℝ) ^ γ ≤ 6 * ((n : ℝ) ^ (γ - 1) * y) := by
        have hid : (n : ℝ) ^ (γ - 1) * n = (n : ℝ) ^ γ := by
          calc
            (n : ℝ) ^ (γ - 1) * n = (n : ℝ) ^ (γ - 1) * (n : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            _ = (n : ℝ) ^ γ := by
              rw [← Real.rpow_add hn0]
              congr 1
              ring
        nlinarith [mul_le_mul_of_nonneg_left hlarge hpow.le]
      dsimp [s] at hc
      linarith
    · constructor
      · positivity
      · apply Real.rpow_le_rpow (by positivity) _ hγ.le
        have := (hwin p hp).2
        linarith
  · have hlo : 0 < (n : ℝ) / 3 - y := by linarith
    have hAB : (n : ℝ) / 3 - y ≤ (n : ℝ) / 3 + y + 1 := by linarith
    have hc := ps_card_of_power_bounds139 γ hγ s hs
      (((n : ℝ) / 3 - y) ^ γ) (((n : ℝ) / 3 + y + 1) ^ γ)
      (Real.rpow_le_rpow hlo.le hAB hγ.le) (fun p hp => ?_)
    · have hinc := rpow_increment_le139 γ ((n : ℝ) / 3 - y)
        ((n : ℝ) / 3 + y + 1) hγ.le hγ1.le hlo hAB
      have hslope : ((n : ℝ) / 3 - y) ^ (γ - 1) ≤ 6 * (n : ℝ) ^ (γ - 1) := by
        calc
          ((n : ℝ) / 3 - y) ^ (γ - 1) ≤ ((n : ℝ) / 6) ^ (γ - 1) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          _ = (n : ℝ) ^ (γ - 1) * (6 : ℝ) ^ (1 - γ) := by
            rw [Real.div_rpow hn0.le (by norm_num), div_eq_mul_inv,
              ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6), neg_sub]
          _ ≤ (n : ℝ) ^ (γ - 1) * 6 := by
            apply mul_le_mul_of_nonneg_left _ hpow.le
            calc
              (6 : ℝ) ^ (1 - γ) ≤ (6 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 6 := Real.rpow_one _
          _ = 6 * (n : ℝ) ^ (γ - 1) := by ring
      have hslope0 : 0 ≤ ((n : ℝ) / 3 - y) ^ (γ - 1) := by positivity
      have hcoeff : γ * ((n : ℝ) / 3 - y) ^ (γ - 1) ≤ 6 * (n : ℝ) ^ (γ - 1) := by
        nlinarith
      have hwidth : 0 ≤ 2 * y + 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoeff hwidth
      have hywidth := mul_le_mul_of_nonneg_left (show 2 * y + 1 ≤ 3 * y by linarith)
        (show 0 ≤ 6 * (n : ℝ) ^ (γ - 1) by positivity)
      dsimp [s] at hc
      have hinc' : ((n : ℝ) / 3 + y + 1) ^ γ - ((n : ℝ) / 3 - y) ^ γ ≤
          γ * ((n : ℝ) / 3 - y) ^ (γ - 1) * (2 * y + 1) := by
        convert hinc using 1 <;> ring
      nlinarith
    · constructor
      · exact Real.rpow_le_rpow hlo.le (hwin p hp).1.le hγ.le
      · exact Real.rpow_le_rpow (by positivity) (by linarith [(hwin p hp).2]) hγ.le

/-- Section 3 Lemma 5. The weighted mean square has the stated scale, with constant 80. -/
theorem fS_mean_square_le139 (γ : ℝ) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (n : ℕ) (hn : 6 ≤ n) (y : ℝ) (hy : 1 ≤ y)
    (hscale : (n : ℝ) ^ (1 - γ) ≤ y) (hyupper : y ≤ (n : ℝ) / 3) :
    (∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) ≤
      80 * ((n : ℝ) ^ (1 - γ) * y) := by
  have hγ0 : 0 < γ := by linarith
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let s := (windowPrimes n y).filter (fun p => IsPSPrime γ p)
  have hcard := ps_window_card_le139 γ hγ0 hγ1 n hn y hy hscale hyupper
  have hweight (p : ℕ) (hp : p ∈ s) :
      (psWeight γ p) ^ 2 ≤ 4 * ((n : ℝ) ^ (1 - γ)) ^ 2 := by
    have hw := abs_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    have hpn : (p : ℝ) ≤ n := by linarith
    have hi : 1 / γ ≤ 2 := (div_le_iff₀ hγ0).mpr (by linarith)
    have hr := Real.rpow_le_rpow (Nat.cast_nonneg p) hpn (by linarith : 0 ≤ 1 - γ)
    have hle : psWeight γ p ≤ 2 * (n : ℝ) ^ (1 - γ) := by
      unfold psWeight
      exact mul_le_mul hi hr (by positivity) (by norm_num)
    have hnonneg : 0 ≤ psWeight γ p := by unfold psWeight; positivity
    have hsq := pow_le_pow_left₀ hnonneg hle 2
    nlinarith
  have hcancel : (n : ℝ) ^ (γ - 1) * (n : ℝ) ^ (1 - γ) = 1 := by
    rw [← Real.rpow_add hn0, show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero]
  calc
    (∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) = ∑ p ∈ s, (psWeight γ p) ^ 2 :=
      fS_mean_square139 γ n y
    _ ≤ ∑ p ∈ s, 4 * ((n : ℝ) ^ (1 - γ)) ^ 2 := Finset.sum_le_sum hweight
    _ = (s.card : ℝ) * (4 * ((n : ℝ) ^ (1 - γ)) ^ 2) := by simp
    _ ≤ (20 * ((n : ℝ) ^ (γ - 1) * y)) * (4 * ((n : ℝ) ^ (1 - γ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 80 * ((n : ℝ) ^ (1 - γ) * y) := by
      calc
        _ = 80 * ((n : ℝ) ^ (γ - 1) * (n : ℝ) ^ (1 - γ)) *
            ((n : ℝ) ^ (1 - γ) * y) := by ring
        _ = _ := by rw [hcancel]; ring

/-- Lemma 5. -/
theorem song_lemma5 : Lemma5 := by
  intro γ hγ hγ1
  refine ⟨80, 6, fun n hn y hy hyupper => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hθ : 0 ≤ songExponent γ := by unfold songExponent; linarith
  have hy1 : 1 ≤ y := (Real.one_le_rpow hnR hθ).trans hy.le
  have hscale : (n : ℝ) ^ (1 - γ) ≤ y := by
    refine (Real.rpow_le_rpow_of_exponent_le hnR ?_).trans hy.le
    unfold songExponent
    linarith
  constructor
  · exact fS_mean_square_le139 γ (by linarith) hγ1 n hn y hy1 hscale hyupper
  · have hg := gS_mean_square_le139 n y hy1
    linarith


/-! ### Elementary singular series bounds -/

/-- Section 4. A prime denominator is at least half the prime. -/
theorem reciprocal_shift_sq_le139 (x : ℝ) (hx : 2 ≤ x) :
    1 / (x - 1) ^ 2 ≤ 4 / x ^ 2 := by
  have hpos : 0 < x / 2 := by linarith
  calc
    1 / (x - 1) ^ 2 ≤ 1 / (x / 2) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hpos) (by nlinarith)
    _ = 4 / x ^ 2 := by ring

set_option backward.isDefEq.respectTransparency false in
/-- Section 4. The absolute changes of the local factors are summable. -/
theorem summable_singFactor_sub_one139 (n : ℕ) :
    Summable (fun p : Nat.Primes => singFactor n p - 1) := by
  have hs : Summable (fun p : Nat.Primes => 4 / (p : ℝ) ^ 2) := by
    convert! ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).subtype
      Nat.Prime).mul_left (4 : ℝ) using 1
    ext p
    simp [Function.comp_apply, div_eq_mul_inv]
  apply Summable.of_norm
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp1 : 1 ≤ (p : ℝ) - 1 := by linarith
  unfold singFactor
  split_ifs
  · simpa only [sub_sub_cancel_left, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2)] using
      reciprocal_shift_sq_le139 p hp
  · simp only [add_sub_cancel_left, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3)]
    exact (one_div_pow_le_one_div_pow_of_le hp1 (by norm_num : 2 ≤ 3)).trans
      (reciprocal_shift_sq_le139 p hp)

/-- Section 4. A positive reference factor at every prime. -/
noncomputable def lowerFactor139 (p : Nat.Primes) : ℝ :=
  if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- Section 4. Every reference factor is positive. -/
theorem lowerFactor_pos139 (p : Nat.Primes) : 0 < lowerFactor139 p := by
  unfold lowerFactor139
  split_ifs with h
  · norm_num
  · have hp : (3 : ℝ) ≤ p := by
      have := p.property.two_le
      exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
    have hsq : 1 < ((p : ℝ) - 1) ^ 2 := by nlinarith
    have := (div_lt_one (by positivity : 0 < ((p : ℝ) - 1) ^ 2)).2 hsq
    linarith

/-- Section 4. The reference factors have summable deviations from one. -/
theorem summable_lowerFactor_sub_one139 :
    Summable (fun p : Nat.Primes => lowerFactor139 p - 1) := by
  apply Summable.of_norm
  apply (summable_singFactor_sub_one139 0).norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  by_cases h : (p : ℕ) = 2
  · simp [lowerFactor139, h]
  · simp [lowerFactor139, h, singFactor]

/-- Section 4. For odd n each singular factor exceeds the positive reference factor. -/
theorem lowerFactor_le_singFactor139 (n : ℕ) (hn : Odd n) (p : Nat.Primes) :
    lowerFactor139 p ≤ singFactor n p := by
  by_cases h : (p : ℕ) = 2
  · have hnot : ¬ (p : ℕ) ∣ n := by simpa [h] using hn.not_two_dvd_nat
    simp [lowerFactor139, h, singFactor, hn.not_two_dvd_nat]
  · unfold lowerFactor139 singFactor
    rw [if_neg h]
    split_ifs
    · rfl
    · have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
      have h2 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      have hp1 : 0 ≤ (p : ℝ) - 1 := by linarith
      have h3 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by positivity
      linarith

/-- The singular series lower bound for odd `n`. -/
theorem singular_lower : SingularLower := by
  have hlog : Summable (fun p : Nat.Primes => Real.log (lowerFactor139 p)) := by
    simpa only [add_sub_cancel] using
      Real.summable_log_one_add_of_summable summable_lowerFactor_sub_one139
  refine ⟨Real.exp (∑' p : Nat.Primes, Real.log (lowerFactor139 p)), Real.exp_pos _, ?_⟩
  intro n hn
  have hpos : ∀ p : Nat.Primes, 0 < singFactor n p := fun p =>
    (lowerFactor_pos139 p).trans_le (lowerFactor_le_singFactor139 n hn p)
  have hlogn : Summable (fun p : Nat.Primes => Real.log (singFactor n p)) := by
    simpa only [add_sub_cancel] using
      Real.summable_log_one_add_of_summable (summable_singFactor_sub_one139 n)
  rw [singular3, ← Real.rexp_tsum_eq_tprod hpos hlogn]
  apply Real.exp_le_exp.mpr
  exact hlog.tsum_le_tsum (fun p => Real.log_le_log (lowerFactor_pos139 p)
    (lowerFactor_le_singFactor139 n hn p)) hlogn

/-! ### Vacuity: the hypotheses can hold -/

/-- At `γ = 89/90` the window exponent is `15/16`. -/
theorem songExponent_89_90 : songExponent (89 / 90) = 15 / 16 := by
  unfold songExponent; norm_num

/-- `γ = 89/90` lies in the paper's range. -/
theorem gamma_mem : (44 : ℝ) / 45 < 89 / 90 ∧ (89 : ℝ) / 90 < 1 := by norm_num

/-- With `γ = 89/90`, `n = 2^64 + 1` odd and `y = 2^62`, every hypothesis of Lemmas 4, 5
and the asymptotic holds: `n^{15/16} < y ≤ n/3`. -/
theorem vacuity_window :
    Odd (2 ^ 64 + 1 : ℕ) ∧
    ((2 ^ 64 + 1 : ℕ) : ℝ) ^ songExponent (89 / 90) < (2 : ℝ) ^ 62 ∧
    (2 : ℝ) ^ 62 ≤ ((2 ^ 64 + 1 : ℕ) : ℝ) / 3 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [songExponent_89_90]
    have hle : ((2 ^ 64 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (65 : ℝ) := by
      rw [show (65 : ℝ) = ((65 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; norm_num
    calc ((2 ^ 64 + 1 : ℕ) : ℝ) ^ ((15 : ℝ) / 16)
        ≤ ((2 : ℝ) ^ (65 : ℝ)) ^ ((15 : ℝ) / 16) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (2 : ℝ) ^ ((65 : ℝ) * (15 / 16)) := by rw [← Real.rpow_mul (by norm_num)]
      _ < (2 : ℝ) ^ (62 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = (2 : ℝ) ^ 62 := by
          rw [show (62 : ℝ) = ((62 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  · push_cast; norm_num

/-- Lemma 3's hypotheses hold too: `n^{7/8} ≤ y ≤ n/3` at the same `n`, `y`. -/
theorem vacuity_lemma3 :
    ((2 ^ 64 + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) ≤ (2 : ℝ) ^ 62 := by
  have h := (vacuity_window).2.1
  rw [songExponent_89_90] at h
  refine le_trans (Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num : (7 : ℝ) / 8 ≤ 15 / 16))
    h.le
  push_cast; norm_num

/-- The window of `vacuity_window` contains a prime: `2^61 - 1` is prime and within `y`
of `n/3`. Primality by the Lucas-Lehmer test of Mathlib. -/
theorem vacuity_windowPrime :
    (2 ^ 61 - 1 : ℕ) ∈ windowPrimes (2 ^ 64 + 1) ((2 : ℝ) ^ 62) := by
  have hp : (2 ^ 61 - 1 : ℕ).Prime := by
    have := lucas_lehmer_sufficiency 61 (by norm_num) (by norm_num)
    simpa [mersenne] using this
  unfold windowPrimes
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hp, ?_⟩
  · have : ((2 ^ 61 - 1 : ℕ) : ℝ) ≤ ((2 ^ 64 + 1 : ℕ) : ℝ) / 3 + (2 : ℝ) ^ 62 := by
      push_cast; norm_num
    have h2 := Nat.le_ceil (((2 ^ 64 + 1 : ℕ) : ℝ) / 3 + (2 : ℝ) ^ 62)
    have h3 : (2 ^ 61 - 1 : ℕ) ≤ Nat.ceil (((2 ^ 64 + 1 : ℕ) : ℝ) / 3 + (2 : ℝ) ^ 62) := by
      exact_mod_cast this.trans h2
    omega
  · rw [abs_lt]; push_cast; constructor <;> norm_num

end

end LeanLab.Song2020.State1562
