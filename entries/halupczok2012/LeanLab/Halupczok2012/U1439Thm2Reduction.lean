module

public import LeanLab.Halupczok2012.U1439Combin
public import LeanLab.Halupczok2012.NonCoprime

/-!
# P0077 Halupczok 2012, Theorem 2 reduced to Theorem 5 and the main term step, unit U-1439

AI wrote the Lean code, Claude, run 20261021T1603Z-28836. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper proves Theorem 2 by writing the ternary sum as `∑_{p₁} log p₁ · binSum(n - p₁)` and
splitting `binSum(n - p₁) - T(n,q,a) Y₁ Y₂ / …` into

* the BINARY PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ (binSum(n - p₁) - 𝔖(n - p₁) Y₂)|`, bounded from
  the Perelli-Pintz mean square, the paper's Theorem 5, and its Lemma 1; and
* the MAIN TERM PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ 𝔖(n - p₁) - 𝔗(n,q,a) Y₁|`, bounded from the
  Perelli-Pintz-Salerno short interval Bombieri-Vinogradov theorem, the paper's Theorem 3, and
  the singular series computation with the Chinese remainder theorem.

Here:

* `binaryPart`: the binary part is `≪ Y₁ Y₂ L^{-A}`. PROVED CONDITIONAL ON `Theorem5` only.
  The paper's Lemma 1 is NOT needed: in Theorem 2, `Q ≪ Y₁ X₁^{-1/2} L^{-B}` gives `Q² ≪ Y₁`,
  so the elementary divisor moment `divisor_moment` and Cauchy-Schwarz suffice.
* `theorem2_of_inputs : Theorem5 → MainTermMV → Theorem2`. CONDITIONAL ON both.
* `theorem2Zeroed_of_inputs`: the F-0008 repair, the all-`q` form with `T0`, CONDITIONAL ON the
  same two inputs instead of the paper's Theorem 2.

`MainTermMV` is still the paper's own main term step, its displays after (10); its standard
input is `Theorem3`, Perelli-Pintz-Salerno, stated below; `U1457SingSeries` derives
`MainTermMV` from `Theorem3` and the singular series facts proved in `U1462Tails`.
The lab's `PNTPort.BV.BombieriVinogradov` is for `ψ(x; q, a)` over `[1, x]`; it does not give
intervals of length `Y₁ = X₁^{3/5+ε}`, so it cannot replace `Theorem3`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-! ### The cited inputs -/

/-- **Theorem 5 of the paper**, Perelli-Pintz: for `Y^{1/3+ε} ≪ R ≪ Y ≍ 2X₁ - X₂ - Y ≥ 0`,
`R ≤ X₁`, `X₂^{7/12+ε₂} ≪ Y ≤ X₂`,
`∑_{k ∈ [X₁, X₁+R]} |∑_{p₂+p₃=2k, p₂ ∈ [X₂,X₂+Y]} log p₂ log p₃ - 𝔖(2k) Y|² ≪ R Y² L^{-A}`,
`L = log Y`. Cited input. -/
def Theorem5 : Prop :=
  ∀ A ε ε2 : ℝ, 0 < A → 0 < ε → 0 < ε2 →
  ∀ c1 c2 c3 c4 c5 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → 0 < c5 →
  ∃ C Y0 : ℝ, ∀ X1 X2 Y R : ℝ, Y0 ≤ Y →
    c1 * X2 ^ (7 / 12 + ε2) ≤ Y → Y ≤ X2 → c2 * Y ^ (1 / 3 + ε) ≤ R → R ≤ c3 * Y → R ≤ X1 →
    0 ≤ 2 * X1 - X2 - Y → c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      C * R * Y ^ 2 * Real.log Y ^ (-A)

/-- `∑_{p₁ ∈ [X₁,X₁+Y₁], p₁ ≡ a (q)} log p₁ · 𝔖(n - p₁)`, the main term sum. -/
noncomputable def mainSum (n : ℕ) (X1 Y1 : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ P1 n X1 Y1 q a, Real.log p * S (n - p)

/-- **The main term step of the proof of Theorem 2**, as a named input: under the hypotheses of
Theorem 2, `∑_{q ≤ Q, (a,q)=1} |∑_{p₁ ≡ a (q)} log p₁ 𝔖(n - p₁) - 𝔗(n,q,a) Y₁| ≪ Y₁ L^{-A}`.
The paper derives it from Theorem 3, the truncation of `𝔖` at `s ≤ L^C`, the Chinese remainder
theorem and the Euler product of `𝔗`. Derived in `U1457SingSeries`, not in this file. -/
def MainTermMV : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
  ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ, ∃ C Y0 : ℝ,
  ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
    ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |mainSum n X1 Y1 q a - T n q a * Y1| ≤ C * Y1 * Real.log Y2 ^ (-A)

/-- `∑_{p ∈ [X, X+Y], p ≡ a (q)} log p`. -/
noncomputable def thetaAP (X Y : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ (range (⌈X + Y⌉₊ + 1)).filter (fun p : ℕ => p.Prime ∧ X < p ∧ (p : ℝ) ≤ X + Y ∧
    (p : ℤ) ≡ a [ZMOD q]), Real.log p

/-- **Theorem 3 of the paper**, Perelli-Pintz-Salerno, for the record: for
`X ≥ Y ≫ X^{3/5+ε}` and `Q ≪ Y X^{-1/2} (log X)^{-B}`,
`∑_{q ≤ Q} max_{(a,q)=1} |∑_{p ∈ [X,X+Y], p ≡ a (q)} log p - Y/φ(q)| ≪ Y L^{-A}`,
`L = log Y`; the max is a choice of reduced residues `a q`. Used from `U1452MainTermMV` on. -/
def Theorem3 : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ c1 c2 : ℝ, 0 < c1 → 0 < c2 →
  ∃ C Y0 : ℝ, ∀ X Y Q : ℝ, Y0 ≤ Y → Y ≤ X → c1 * X ^ (3 / 5 + ε) ≤ Y →
    Q ≤ c2 * Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B) →
    ∀ a : ℕ → ℤ, (∀ q, Int.gcd (a q) q = 1) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, |thetaAP X Y q (a q) - Y / q.totient| ≤ C * Y * Real.log Y ^ (-A)

/-! ### Helpers -/

/-- The primes `p₁ ∈ [X₁, X₁ + Y₁]`, `p₁ ≤ n`, with no congruence. -/
noncomputable def P1w (n : ℕ) (X1 Y1 : ℝ) : Finset ℕ :=
  (range (n + 1)).filter (fun p => p.Prime ∧ X1 < p ∧ (p : ℝ) ≤ X1 + Y1)

theorem P1_eq_filter (n : ℕ) (X1 Y1 : ℝ) (q : ℕ) (a : ℤ) :
    P1 n X1 Y1 q a = (P1w n X1 Y1).filter (fun p : ℕ => (p : ℤ) ≡ a [ZMOD q]) := by
  ext p; simp [P1, P1w, and_assoc]

/-- `X ≤ (Y/c)²` from `c X^{e} ≤ Y` with `e ≥ 1/2`, `X ≥ 1`. -/
theorem le_sq_of_rpow {c X Y e : ℝ} (hc : 0 < c) (hX : 1 ≤ X) (he : 1 / 2 ≤ e)
    (h : c * X ^ e ≤ Y) : X ≤ (Y / c) ^ 2 := by
  have h1 : X ^ (1 / 2 : ℝ) ≤ X ^ e := Real.rpow_le_rpow_of_exponent_le hX he
  have h2 : Real.sqrt X ≤ Y / c := by
    rw [Real.sqrt_eq_rpow, le_div_iff₀ hc]; nlinarith
  have h3 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  calc X = Real.sqrt X ^ 2 := (Real.sq_sqrt (by linarith)).symm
    _ ≤ (Y / c) ^ 2 := by gcongr

/-- The cover of a window by `m` windows of length `R/m`. -/
theorem kRange_subset_biUnion (X R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) :
    kRange X R ⊆ (range m).biUnion (fun j => kRange (X + j * (R / m)) (R / m)) := by
  intro k hk
  unfold kRange at hk ⊢
  rw [Finset.mem_filter] at hk
  obtain ⟨-, hk1, hk2⟩ := hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hRm : 0 < R / m := div_pos hR hm'
  set t := ((k : ℝ) - X) / (R / m) with ht
  have ht0 : 0 < t := div_pos (by linarith) hRm
  have htm : t ≤ m := by
    rw [ht, div_le_iff₀ hRm]; field_simp; linarith
  have hc1 : 1 ≤ ⌈t⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ht0).ne'
  have hcm : ⌈t⌉₊ ≤ m := Nat.ceil_le.mpr htm
  rw [Finset.mem_biUnion]
  refine ⟨⌈t⌉₊ - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hj : ((⌈t⌉₊ - 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hc1]; simp
  have hlt : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0.le
  have hge : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have hkt : (k : ℝ) = X + t * (R / m) := by rw [ht]; field_simp; ring
  rw [Finset.mem_filter, hj]
  have hA : X + ((⌈t⌉₊ : ℝ) - 1) * (R / m) < k := by
    rw [hkt]; nlinarith
  have hB : (k : ℝ) ≤ X + ((⌈t⌉₊ : ℝ) - 1) * (R / m) + R / m := by
    rw [hkt]; nlinarith
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, hA, hB⟩
  have := hB.trans (Nat.le_ceil (X + ((⌈t⌉₊ : ℝ) - 1) * (R / m) + R / m))
  exact_mod_cast this

/-- A sum over a finite union of nonnegative terms. -/
theorem sum_biUnion_le_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ∑ k ∈ s.biUnion t, g k ≤ ∑ j ∈ s, ∑ k ∈ t j, g k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have := Finset.sum_union_inter (s₁ := t j) (s₂ := s.biUnion t) (f := g)
    have h0 : 0 ≤ ∑ k ∈ t j ∩ s.biUnion t, g k := Finset.sum_nonneg (fun k _ => hg k)
    linarith

/-- Sum over the pieces of a cover. -/
theorem sum_kRange_le_pieces (X R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) :
    ∑ k ∈ kRange X R, g k ≤ ∑ j ∈ range m, ∑ k ∈ kRange (X + j * (R / m)) (R / m), g k :=
  (Finset.sum_le_sum_of_subset_of_nonneg (kRange_subset_biUnion X R hR m hm)
    (fun k _ _ => hg k)).trans (sum_biUnion_le_nonneg _ _ g hg)

/-- From the primes `p₁` to the `k = (n - p₁)/2` of Theorem 5. -/
theorem sum_P1w_le (n : ℕ) (X1 Y1 : ℝ) (hn : Odd n) (hX : 2 ≤ X1) (f : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) :
    ∑ p ∈ P1w n X1 Y1, f (n - p) ≤
      ∑ k ∈ kRange (((n : ℝ) - X1 - Y1) / 2 - 1) (Y1 / 2 + 1), f (2 * k) := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hodd : ∀ p ∈ P1w n X1 Y1, p ≤ n ∧ p % 2 = 1 ∧ X1 < p ∧ (p : ℝ) ≤ X1 + Y1 := by
    intro p hp
    simp only [P1w, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨by omega, ?_, h3, h4⟩
    rcases h2.eq_two_or_odd with h | h
    · exfalso; subst h; norm_num at h3; linarith
    · exact h
  have h2k : ∀ p ∈ P1w n X1 Y1, 2 * ((n - p) / 2) = n - p := by
    intro p hp; obtain ⟨h1, h2, -⟩ := hodd p hp; omega
  calc ∑ p ∈ P1w n X1 Y1, f (n - p) = ∑ p ∈ P1w n X1 Y1, f (2 * ((n - p) / 2)) := by
        apply Finset.sum_congr rfl; intro p hp; rw [h2k p hp]
    _ = ∑ k ∈ (P1w n X1 Y1).image (fun p => (n - p) / 2), f (2 * k) := by
        rw [Finset.sum_image]
        intro p hp p' hp' he
        simp only at he
        obtain ⟨h1, h2, -⟩ := hodd p hp
        obtain ⟨h1', h2', -⟩ := hodd p' hp'
        omega
    _ ≤ ∑ k ∈ kRange (((n : ℝ) - X1 - Y1) / 2 - 1) (Y1 / 2 + 1), f (2 * k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun k _ _ => hf _)
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨p, hp, rfl⟩ := hk
        obtain ⟨h1, -, h3, h4⟩ := hodd p hp
        have e := h2k p hp
        have ec : (2 : ℝ) * (((n - p) / 2 : ℕ) : ℝ) = (n : ℝ) - p := by
          have : ((2 * ((n - p) / 2) : ℕ) : ℝ) = ((n - p : ℕ) : ℝ) := by rw [e]
          push_cast [Nat.cast_sub h1] at this
          linarith
        unfold kRange
        rw [Finset.mem_filter]
        have hA : ((n : ℝ) - X1 - Y1) / 2 - 1 < (((n - p) / 2 : ℕ) : ℝ) := by linarith
        have hB : ((((n - p) / 2 : ℕ)) : ℝ) ≤ ((n : ℝ) - X1 - Y1) / 2 - 1 + (Y1 / 2 + 1) := by
          linarith
        refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, hA, hB⟩
        have := hB.trans (Nat.le_ceil (((n : ℝ) - X1 - Y1) / 2 - 1 + (Y1 / 2 + 1)))
        exact_mod_cast this

/-- `L² · L³ · L^{-(2A+5)} = (L^{-A})²`. -/
theorem log_pow_identity {L A : ℝ} (hL : 0 < L) :
    L ^ 2 * L ^ 3 * L ^ (-(2 * A + 5)) = (L ^ (-A)) ^ 2 := by
  have e1 : L ^ 2 * L ^ 3 = L ^ (5 : ℝ) := by
    rw [← pow_add, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : (L ^ (-A)) ^ 2 = L ^ (-A * 2) := by
    rw [Real.rpow_mul hL.le, Real.rpow_two]
  rw [e1, ← Real.rpow_add hL, e2]
  congr 1; ring

/-- The binary part of the proof of Theorem 2, for one modulus. -/
noncomputable def binPart (n : ℕ) (X1 Y1 X2 Y2 : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ P1 n X1 Y1 q a, Real.log p * (binSum X2 Y2 (n - p) - S (n - p) * Y2)

/-- **The binary part of Theorem 2**, CONDITIONAL ON `Theorem5`:
`∑_{q ≤ Q} |∑_{p₁ ≡ a (q)} log p₁ (binSum(n - p₁) - 𝔖(n - p₁) Y₂)| ≪ Y₁ Y₂ L^{-A}`
under `Thm2Hyp`, for every `B > 0` and every integer `a`. -/
theorem binaryPart (h5 : Theorem5) : ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 →
    ∀ B : ℝ, 0 < B → ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ a : ℤ, ∃ C Y0 : ℝ,
    ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, |binPart n X1 Y1 X2 Y2 q a| ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A) := by
  intro A ε ε1 ε2 hA hε hε1 hε2 B hB c hc a
  have c0 := hc 0; have c1 := hc 1; have c2 := hc 2; have c3 := hc 3
  have c4 := hc 4; have c5 := hc 5; have c6 := hc 6
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈c 3⌉₊ + 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hc3m : c 3 ≤ m := by
    have := Nat.le_ceil (c 3); rw [hmdef]; push_cast; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  obtain ⟨C5, Y05, h5'⟩ := h5 (2 * A + 5) ε ε2 (by linarith) hε hε2 (c 1) (c 2 / (2 * m))
    (c 3 + 1) (c 4 / 2) (c 5 + c 3 + 3) c1 (by positivity) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = (c 3 / c 0) ^ 2 + c 3 + (1 / c 1) ^ 2 + 1 + c 5 := ⟨_, rfl⟩
  have hK0pos : 0 < K0 := by rw [hK0]; positivity
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = |Real.log K0| + 2 := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = |Real.log (c 6 ^ 2 * c 3)| + 2 := ⟨_, rfl⟩
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = K1 ^ 2 * max C5 0 * (K2 ^ 3 + c 6 ^ 2) := ⟨_, rfl⟩
  have hKnn : 0 ≤ K := by
    rw [hK]; have := le_max_right C5 0; positivity
  refine ⟨Real.sqrt K, max Y05 (max (Real.exp 1) (max 4 (4 / c 4))), ?_⟩
  intro n X1 Y1 X2 Y2 Q hY1 hY2 hH
  obtain ⟨hn, hYX1, h0, hYX2, h1, h2, h3, hD0, hD1, hD2, hQ1, hQ2⟩ := hH
  have hY05 : Y05 ≤ Y2 := le_trans (le_max_left _ _) hY2
  have hYe : Real.exp 1 ≤ Y2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY2
  have hY4 : 4 ≤ Y2 := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hY2
  have hY4c : 4 / c 4 ≤ Y2 := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hY2
  have hY14 : 4 ≤ Y1 := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hY1
  have hc4Y : 4 ≤ c 4 * Y2 := by
    have := mul_le_mul_of_nonneg_left hY4c c4.le
    rwa [mul_div_cancel₀ _ c4.ne'] at this
  have hL1 : 1 ≤ Real.log Y2 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hYe
  have hL0 : 0 < Real.log Y2 := by linarith
  have hX1 : 4 ≤ X1 := by linarith
  have hX2 : 4 ≤ X2 := by linarith
  -- the size of `n`
  have hX1sq : X1 ≤ (Y1 / c 0) ^ 2 := le_sq_of_rpow c0 (by linarith) (by linarith) h0
  have hX2sq : X2 ≤ (Y2 / c 1) ^ 2 := le_sq_of_rpow c1 (by linarith) (by linarith) h1
  have hnpos : (0 : ℝ) < n := by linarith
  have hnK : (n : ℝ) ≤ K0 * Y2 ^ 2 := by
    have e1 : (Y1 / c 0) ^ 2 ≤ (c 3 / c 0) ^ 2 * Y2 ^ 2 := by
      rw [div_pow, div_pow, div_mul_eq_mul_div, ← mul_pow]
      gcongr
    have e2 : (Y2 / c 1) ^ 2 = (1 / c 1) ^ 2 * Y2 ^ 2 := by ring
    have hYY : Y2 ≤ Y2 ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) (by linarith)
    have e3 : c 3 * Y2 ≤ c 3 * Y2 ^ 2 := mul_le_mul_of_nonneg_left hYY c3.le
    have e4 : c 5 * Y2 ≤ c 5 * Y2 ^ 2 := mul_le_mul_of_nonneg_left hYY c5.le
    have e5 : K0 * Y2 ^ 2 = (c 3 / c 0) ^ 2 * Y2 ^ 2 + c 3 * Y2 ^ 2 + (1 / c 1) ^ 2 * Y2 ^ 2 +
        Y2 ^ 2 + c 5 * Y2 ^ 2 := by rw [hK0]; ring
    rw [e5]
    linarith
  have hlogn : Real.log n ≤ K1 * Real.log Y2 := by
    have h := Real.log_le_log hnpos hnK
    rw [Real.log_mul hK0pos.ne' (by positivity), Real.log_pow] at h
    have := le_abs_self (Real.log K0)
    have : K1 * Real.log Y2 = |Real.log K0| * Real.log Y2 + 2 * Real.log Y2 := by
      rw [hK1]; ring
    have : |Real.log K0| ≤ |Real.log K0| * Real.log Y2 := by
      exact le_mul_of_one_le_right (abs_nonneg _) hL1
    push_cast at h
    linarith
  -- `Q`
  have hQ0 : 0 ≤ Q := by linarith
  have hQnQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0
  have hQn1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ1)
  have hQn1R : (1 : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hQn1
  have hLB : Real.log Y2 ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hX1pos : 0 < X1 := by linarith
  have hsq : Real.sqrt X1 ^ 2 = X1 := Real.sq_sqrt hX1pos.le
  have hsqpos : 0 < Real.sqrt X1 := Real.sqrt_pos.mpr hX1pos
  have hQs : Q * Real.sqrt X1 ≤ c 6 * Y1 := by
    have e : X1 ^ (-(1 / 2) : ℝ) = (Real.sqrt X1)⁻¹ := by
      rw [Real.rpow_neg hX1pos.le, Real.sqrt_eq_rpow]
    rw [e] at hQ2
    have hnn : 0 ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ := by positivity
    have : Q ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ := by
      calc Q ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ * Real.log Y2 ^ (-B) := hQ2
        _ ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ * 1 := mul_le_mul_of_nonneg_left hLB hnn
        _ = _ := mul_one _
    rw [← le_div_iff₀ hsqpos]; rwa [div_eq_mul_inv]
  have hQsq : Q ^ 2 ≤ c 6 ^ 2 * Y1 := by
    have h' : Q ^ 2 * X1 ≤ c 6 ^ 2 * Y1 ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hQs 2
      rw [mul_pow, hsq, mul_pow] at this; exact this
    have hYY : c 6 ^ 2 * Y1 ^ 2 ≤ c 6 ^ 2 * Y1 * X1 := by
      have : Y1 ^ 2 ≤ Y1 * X1 := by rw [sq]; exact mul_le_mul_of_nonneg_left hYX1 (by linarith)
      have := mul_le_mul_of_nonneg_left this (sq_nonneg (c 6))
      linarith
    have : Q ^ 2 * X1 ≤ (c 6 ^ 2 * Y1) * X1 := by linarith
    exact le_of_mul_le_mul_right this hX1pos
  have hQnsq : ((⌊Q⌋₊ : ℕ) : ℝ) ^ 2 ≤ c 6 ^ 2 * Y1 :=
    le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hQnQ 2) hQsq
  have hHb : 1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ≤ K2 * Real.log Y2 := by
    have hb : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ c 6 ^ 2 * c 3 * Y2 := by
      have e1 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_right (by linarith) hQn1R
      have e2 : c 6 ^ 2 * Y1 ≤ c 6 ^ 2 * (c 3 * Y2) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      linarith
    have h := Real.log_le_log (by linarith) hb
    rw [Real.log_mul (by positivity) (by linarith)] at h
    have := le_abs_self (Real.log (c 6 ^ 2 * c 3))
    have : K2 * Real.log Y2 = |Real.log (c 6 ^ 2 * c 3)| * Real.log Y2 + 2 * Real.log Y2 := by
      rw [hK2]; ring
    have : |Real.log (c 6 ^ 2 * c 3)| ≤ |Real.log (c 6 ^ 2 * c 3)| * Real.log Y2 := by
      exact le_mul_of_one_le_right (abs_nonneg _) hL1
    linarith
  have hH0 : 0 ≤ 1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ) := one_add_log_nonneg _
  -- the window and the weights
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ,
      w = fun p : ℕ => Real.log p * (binSum X2 Y2 (n - p) - S (n - p) * Y2) := ⟨_, rfl⟩
  have hrw : ∀ q, binPart n X1 Y1 X2 Y2 q a =
      ∑ p ∈ (P1w n X1 Y1).filter (fun p : ℕ => (p : ℤ) ≡ a [ZMOD q]), w p := by
    intro q; rw [binPart, P1_eq_filter, hw]
  simp_rw [hrw]
  have hCS := sum_q_abs_sq_le (P1w n X1 Y1) w ⌊Q⌋₊ a
  have hWin : ∀ p ∈ P1w n X1 Y1, X1 < p ∧ (p : ℝ) ≤ X1 + Y1 := by
    intro p hp
    simp only [P1w, Finset.mem_filter] at hp
    exact ⟨hp.2.2.1, hp.2.2.2⟩
  have hDm := divisor_moment (by linarith) hWin ⌊Q⌋₊ a
  have hDm' : ∑ m ∈ P1w n X1 Y1, ((Dq ⌊Q⌋₊ a m : ℕ) : ℝ) ^ 2 ≤
      Y1 * (K2 ^ 3 + c 6 ^ 2) * Real.log Y2 ^ 3 := by
    have e1 : (1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ)) ^ 3 ≤ (K2 * Real.log Y2) ^ 3 :=
      pow_le_pow_left₀ hH0 hHb 3
    have hL3 : 1 ≤ Real.log Y2 ^ 3 := one_le_pow₀ hL1
    have e2 : Y1 * (1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ)) ^ 3 ≤ Y1 * (K2 * Real.log Y2) ^ 3 :=
      mul_le_mul_of_nonneg_left e1 (by linarith)
    have e3 : c 6 ^ 2 * Y1 ≤ c 6 ^ 2 * Y1 * Real.log Y2 ^ 3 := by
      have : 0 ≤ c 6 ^ 2 * Y1 := by positivity
      exact le_mul_of_one_le_right this hL3
    have e4 : Y1 * (K2 ^ 3 + c 6 ^ 2) * Real.log Y2 ^ 3 =
        Y1 * (K2 * Real.log Y2) ^ 3 + c 6 ^ 2 * Y1 * Real.log Y2 ^ 3 := by ring
    rw [e4]
    linarith
  -- the weights: Theorem 5 on `m` pieces
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun r : ℕ => (binSum X2 Y2 r - S r * Y2) ^ 2 := ⟨_, rfl⟩
  have hbnn : ∀ r, 0 ≤ b r := by intro r; rw [hb]; exact sq_nonneg _
  obtain ⟨Xb, hXb⟩ : ∃ Xb : ℝ, Xb = ((n : ℝ) - X1 - Y1) / 2 - 1 := ⟨_, rfl⟩
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℝ, Rb = Y1 / 2 + 1 := ⟨_, rfl⟩
  have hRb0 : 0 < Rb := by rw [hRb]; linarith
  have hRbY : Rb ≤ Y1 := by rw [hRb]; linarith
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = Rb / m := ⟨_, rfl⟩
  have hR'0 : 0 < R' := by rw [hR']; exact div_pos hRb0 hmpos
  have hmR' : (m : ℝ) * R' = Rb := by rw [hR']; field_simp
  have hR'le : R' ≤ Rb := by rw [hR']; exact div_le_self hRb0.le hmR
  have hR'Y : R' ≤ Y2 / 2 + 1 := by
    rw [hR', div_le_iff₀ hmpos, hRb]
    have : Y1 ≤ m * Y2 := le_trans h3 (mul_le_mul_of_nonneg_right hc3m (by linarith))
    linarith
  have hpiece : ∀ j ∈ range m, ∑ k ∈ kRange (Xb + j * R') R', b (2 * k) ≤
      C5 * R' * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) := by
    intro j hj
    have hjm : (j : ℝ) + 1 ≤ m := by
      have := Finset.mem_range.mp hj; exact_mod_cast this
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjR : (j : ℝ) * R' ≤ Rb := by
      rw [← hmR']; exact mul_le_mul_of_nonneg_right (by linarith) hR'0.le
    have hjR0 : 0 ≤ (j : ℝ) * R' := by positivity
    have e2X : 2 * (Xb + j * R') - X2 - Y2 =
        ((n : ℝ) - X1 - Y1 - X2 - Y2) - 2 + 2 * (j * R') := by
      rw [hXb]; ring
    have hXbge : R' ≤ Xb := by rw [hXb]; linarith
    rw [hb]
    apply h5' (Xb + j * R') X2 Y2 R' hY05 h1 hYX2
    · -- lower bound for `R'`
      rw [hR', hRb]
      have : c 2 / (2 * m) * Y2 ^ (1 / 3 + ε) = (c 2 * Y2 ^ (1 / 3 + ε) / 2) / m := by
        field_simp
      rw [this]
      apply div_le_div_of_nonneg_right _ hmpos.le
      linarith
    · have := mul_nonneg c3.le (by linarith : (0 : ℝ) ≤ Y2); linarith
    · linarith
    · rw [e2X]; linarith
    · rw [e2X]; linarith
    · rw [e2X]; rw [hRb] at hjR; linarith
  have hLp : 0 ≤ Real.log Y2 ^ (-(2 * A + 5)) := Real.rpow_nonneg hL0.le _
  have hbsum : ∑ k ∈ kRange Xb Rb, b (2 * k) ≤
      max C5 0 * Y1 * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) := by
    have hcov := sum_kRange_le_pieces Xb Rb hRb0 m hm0 (fun k => b (2 * k)) (fun k => hbnn _)
    rw [← hR'] at hcov
    have hsum := Finset.sum_le_sum hpiece
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have e : (m : ℝ) * (C5 * R' * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) =
        C5 * Rb * (Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) := by rw [← hmR']; ring
    have hC : C5 * Rb ≤ max C5 0 * Y1 := by
      calc C5 * Rb ≤ max C5 0 * Rb := mul_le_mul_of_nonneg_right (le_max_left _ _) hRb0.le
        _ ≤ max C5 0 * Y1 := mul_le_mul_of_nonneg_left hRbY (le_max_right _ _)
    have hP : 0 ≤ Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) := mul_nonneg (sq_nonneg _) hLp
    have := mul_le_mul_of_nonneg_right hC hP
    have e2 : max C5 0 * Y1 * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) =
        max C5 0 * Y1 * (Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) := by ring
    rw [e2]
    linarith
  have hwsum : ∑ p ∈ P1w n X1 Y1, w p ^ 2 ≤
      (K1 * Real.log Y2) ^ 2 * (max C5 0 * Y1 * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) := by
    have hlog : ∀ p ∈ P1w n X1 Y1, Real.log p ^ 2 ≤ (K1 * Real.log Y2) ^ 2 := by
      intro p hp
      simp only [P1w, Finset.mem_filter, Finset.mem_range] at hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.1.one_lt.le
      have hpn : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
      have h0' : 0 ≤ Real.log p := Real.log_nonneg hp1
      have := Real.log_le_log (by linarith) hpn
      have : Real.log p ≤ K1 * Real.log Y2 := by linarith
      exact pow_le_pow_left₀ h0' this 2
    have hP1 := sum_P1w_le n X1 Y1 hn (by linarith) b hbnn
    rw [← hXb, ← hRb] at hP1
    calc ∑ p ∈ P1w n X1 Y1, w p ^ 2 = ∑ p ∈ P1w n X1 Y1, Real.log p ^ 2 * b (n - p) := by
          apply Finset.sum_congr rfl; intro p _; rw [hw, hb]; ring
      _ ≤ ∑ p ∈ P1w n X1 Y1, (K1 * Real.log Y2) ^ 2 * b (n - p) := by
          apply Finset.sum_le_sum; intro p hp
          exact mul_le_mul_of_nonneg_right (hlog p hp) (hbnn _)
      _ = (K1 * Real.log Y2) ^ 2 * ∑ p ∈ P1w n X1 Y1, b (n - p) := by rw [Finset.mul_sum]
      _ ≤ (K1 * Real.log Y2) ^ 2 * ∑ k ∈ kRange Xb Rb, b (2 * k) :=
          mul_le_mul_of_nonneg_left hP1 (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbsum (sq_nonneg _)
  -- assemble
  have hS0 : 0 ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊,
      |∑ p ∈ (P1w n X1 Y1).filter (fun p : ℕ => (p : ℤ) ≡ a [ZMOD q]), w p| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hLA : 0 ≤ Real.log Y2 ^ (-A) := Real.rpow_nonneg hL0.le (-A)
  have hM : 0 ≤ Y1 * Y2 * Real.log Y2 ^ (-A) := by
    have : 0 ≤ Y1 * Y2 := mul_nonneg (by linarith) (by linarith)
    exact mul_nonneg this hLA
  have hfin : (∑ q ∈ Icc 1 ⌊Q⌋₊,
      |∑ p ∈ (P1w n X1 Y1).filter (fun p : ℕ => (p : ℤ) ≡ a [ZMOD q]), w p|) ^ 2 ≤
      K * (Y1 * Y2 * Real.log Y2 ^ (-A)) ^ 2 := by
    have hDnn : 0 ≤ ∑ m ∈ P1w n X1 Y1, ((Dq ⌊Q⌋₊ a m : ℕ) : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hR1 : 0 ≤ (K1 * Real.log Y2) ^ 2 * (max C5 0 * Y1 * Y2 ^ 2 *
        Real.log Y2 ^ (-(2 * A + 5))) := by
      have := le_max_right C5 0
      have : 0 ≤ Y1 := by linarith
      positivity
    calc _ ≤ (∑ p ∈ P1w n X1 Y1, w p ^ 2) *
          ∑ m ∈ P1w n X1 Y1, ((Dq ⌊Q⌋₊ a m : ℕ) : ℝ) ^ 2 := hCS
      _ ≤ ((K1 * Real.log Y2) ^ 2 * (max C5 0 * Y1 * Y2 ^ 2 *
            Real.log Y2 ^ (-(2 * A + 5)))) * (Y1 * (K2 ^ 3 + c 6 ^ 2) * Real.log Y2 ^ 3) :=
          mul_le_mul hwsum hDm' hDnn hR1
      _ = K * (Y1 * Y2) ^ 2 * (Real.log Y2 ^ 2 * Real.log Y2 ^ 3 *
            Real.log Y2 ^ (-(2 * A + 5))) := by rw [hK]; ring
      _ = K * (Y1 * Y2 * Real.log Y2 ^ (-A)) ^ 2 := by rw [log_pow_identity hL0]; ring
  have := Real.sqrt_le_sqrt hfin
  rw [Real.sqrt_sq hS0, Real.sqrt_mul hKnn, Real.sqrt_sq hM] at this
  calc _ ≤ Real.sqrt K * (Y1 * Y2 * Real.log Y2 ^ (-A)) := this
    _ = Real.sqrt K * Y1 * Y2 * Real.log Y2 ^ (-A) := by ring

/-! ### Theorem 2 and the repair, conditional on the two inputs -/

/-- **Theorem 2, CONDITIONAL ON `Theorem5` and `MainTermMV`.** -/
theorem theorem2_of_inputs (h5 : Theorem5) (hm : MainTermMV) : Theorem2 := by
  intro A ε ε1 ε2 hA hε hε1 hε2
  obtain ⟨B, hB, hM⟩ := hm A ε ε1 ε2 hA hε hε1 hε2
  refine ⟨B, hB, fun c hc c7 hc7 a => ?_⟩
  obtain ⟨C1, Y01, hb⟩ := binaryPart h5 A ε ε1 ε2 hA hε hε1 hε2 B hB c hc a
  obtain ⟨C2, Y02, hmt⟩ := hM c hc c7 hc7 a
  refine ⟨C1 + C2, max Y01 (max Y02 0), fun n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ ha => ?_⟩
  have hY2nn : 0 ≤ Y2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY2
  have hbin := hb n X1 Y1 X2 Y2 Q (le_trans (le_max_left _ _) hY1)
    (le_trans (le_max_left _ _) hY2) hH
  have hmain := hmt n X1 Y1 X2 Y2 Q (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY1)
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY2) hH hQ ha
  have hsplit : ∀ q, ternSum n X1 Y1 X2 Y2 q a - T n q a * Y1 * Y2 =
      binPart n X1 Y1 X2 Y2 q a + Y2 * (mainSum n X1 Y1 q a - T n q a * Y1) := by
    intro q
    rw [ternSum_eq, binPart, mainSum]
    have : ∑ p ∈ P1 n X1 Y1 q a, Real.log p * binSum X2 Y2 (n - p) =
        ∑ p ∈ P1 n X1 Y1 q a, Real.log p * (binSum X2 Y2 (n - p) - S (n - p) * Y2) +
          Y2 * ∑ p ∈ P1 n X1 Y1 q a, Real.log p * S (n - p) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _; ring
    rw [this]; ring
  have hsub : ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |binPart n X1 Y1 X2 Y2 q a| ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, |binPart n X1 Y1 X2 Y2 q a| :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun q : ℕ => Int.gcd a (q : ℤ) = 1) (Icc 1 ⌊Q⌋₊))
      (fun _ _ _ => abs_nonneg _)
  have hmain' := mul_le_mul_of_nonneg_left hmain hY2nn
  have hle : ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |ternSum n X1 Y1 X2 Y2 q a - T n q a * Y1 * Y2| ≤
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        |binPart n X1 Y1 X2 Y2 q a| +
      Y2 * ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        |mainSum n X1 Y1 q a - T n q a * Y1| := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro q _
    rw [hsplit q]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hY2nn]
  have e : (C1 + C2) * Y1 * Y2 * Real.log Y2 ^ (-A) =
      C1 * Y1 * Y2 * Real.log Y2 ^ (-A) + Y2 * (C2 * Y1 * Real.log Y2 ^ (-A)) := by ring
  rw [e]
  linarith

/-- **The F-0008 repair, CONDITIONAL ON `Theorem5` and `MainTermMV`** instead of on the
paper's Theorem 2: the all-`q` form `Theorem2Zeroed` with `T0`. -/
theorem theorem2Zeroed_of_inputs (h5 : Theorem5) (hm : MainTermMV) : Theorem2Zeroed :=
  theorem2Zeroed_of_theorem2 (theorem2_of_inputs h5 hm)

/-! ### Vacuity: the hypotheses of `Theorem5` can hold -/

/-- `X₁ = 3/2`, `X₂ = Y = R = 1` and all constants `1` satisfy every hypothesis of `Theorem5`
other than the threshold. -/
theorem theorem5_hyp_instance (ε ε2 : ℝ) :
    (1 : ℝ) * (1 : ℝ) ^ (7 / 12 + ε2) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) * (1 : ℝ) ^ (1 / 3 + ε) ≤ 1 ∧
    (1 : ℝ) ≤ 1 * 1 ∧ (1 : ℝ) ≤ 3 / 2 ∧ (0 : ℝ) ≤ 2 * (3 / 2) - 1 - 1 ∧
    (1 : ℝ) * 1 ≤ 2 * (3 / 2) - 1 - 1 ∧ 2 * (3 / 2 : ℝ) - 1 - 1 ≤ 1 * 1 := by
  simp only [Real.one_rpow]; norm_num

end LeanLab.Halupczok2012
