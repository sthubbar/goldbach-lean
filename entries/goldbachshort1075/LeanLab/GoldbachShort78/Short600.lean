module

public import LeanLab.GoldbachShort78.Short1075

/-!
Goldbach numbers in short intervals at the exponent `13/600`.

`goldbach_short_600`: for every `ε > 0` and all large `x` there is an even sum of two primes in
`[x, x + 3 x^{13/600 + ε}]`, conditional on two cited results taken as explicit hypotheses, never as
axioms:
* `LiRow052`, R. Li, arXiv 2308.04458, Theorem 2, page 2, the row `θ = 0.52`, as in `Short1075.lean`.
* `LiIIIExceptionalCount`, R. Li, Primes in almost all short intervals III, Theorem 1.1, page 2:
  for almost all `n` the interval `[n − n^{1/24 + ε}, n]` contains primes.

R. Li prints the exponent `13/600` himself, as Theorem 8.1 of that paper, with no `ε` and no factor
`3`, so this is a check of a printed result. The argument is that of `goldbach_short_1075` with
`1/24` in place of `1/21.5`. The one new step, proved with no cited input, is
`almostAllCount_of_backward_exceptions`: a count of the `z` with no prime in the backward interval
`[z − z^a, z]` gives the forward count `AlmostAllCount` at any larger exponent.
-/

@[expose] public section

namespace LeanLab.GoldbachShort78

open Real

/-- Exceptions for the backward interval: `z ∈ [Y, 2Y]` with no prime in `[z - z^a, z]`. -/
noncomputable def backwardBadSet (a : ℝ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc Y (2 * Y)).filter fun z =>
    ∀ p : ℕ, (z : ℝ) - (z : ℝ) ^ a ≤ p → p ≤ z → ¬ p.Prime

/-- Cited input, R. Li, Primes in almost all short intervals III, Theorem 1.1, page 2, in exceptional
count form: for every `η > 0` and all large `Y`, at most `C Y / log³ Y` of the integers `z ∈ [Y, 2Y]`
have no prime in `[z − z^{1/24 + η}, z]`. The theorem allows every large power of the logarithm, and
the power three follows. It is printed for sufficiently small positive `ε`, and a longer interval can
only have fewer exceptions, so it extends to every `η > 0`. -/
def LiIIIExceptionalCount : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C y₀ : ℝ, 0 < C ∧ ∀ Y : ℕ, y₀ ≤ Y →
    ((backwardBadSet (1 / 24 + η) Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3

/-- The exponent arithmetic: `13/25 · 1/24 = 13/600`, below the `13/550` that R. Li prints from the
exponent `1/22`, which is below `26/1075`. -/
theorem exponent_600 :
    (13 : ℝ) / 25 * (1 / 24) = 13 / 600 ∧ (13 : ℝ) / 600 < 13 / 550 ∧ (13 : ℝ) / 550 < 26 / 1075 := by
  norm_num

/-- A sanity check on the set in `LiIIIExceptionalCount`: at `Y = 0` it has at most one member. It
does not show that the input holds. -/
theorem backwardBadSet_card_zero (a : ℝ) : (backwardBadSet a 0).card ≤ 1 := by
  classical
  unfold backwardBadSet
  refine (Finset.card_filter_le _ _).trans ?_
  simp

private lemma log_sq_le_rpow_of_slack {a δ : ℝ} (ha : a < 1) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ y : ℝ, Y₀ ≤ y → Real.log y ^ 2 ≤ δ * y ^ (1 - a) := by
  set e : ℝ := (1 - a) / 4 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hhalf : 0 < (1 - a) / 2 := by linarith
  have hde : 0 < δ * e ^ 2 := by positivity
  have hgt : ∀ᶠ y : ℝ in Filter.atTop, 1 / (δ * e ^ 2) ≤ y ^ ((1 - a) / 2) :=
    (tendsto_rpow_atTop hhalf).eventually_ge_atTop _
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hgt
  refine ⟨max A 1, ?_⟩
  intro y hy
  have hyA : A ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hypos : 0 < y := by linarith
  have hlog : Real.log y ≤ y ^ e / e := Real.log_le_rpow_div hypos.le he0
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hsq : Real.log y ^ 2 ≤ (y ^ e / e) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hlog0 hlog
  have hsq2 : (y ^ e / e) ^ 2 = y ^ ((1 - a) / 2) / e ^ 2 := by
    rw [div_pow, pow_two, pow_two, ← Real.rpow_add hypos]
    have h2e : e + e = (1 - a) / 2 := by rw [he]; ring
    rw [h2e]
  rw [hsq2] at hsq
  have hBle : 1 / (δ * e ^ 2) ≤ y ^ ((1 - a) / 2) := hA y hyA
  have hsplit : y ^ (1 - a) = y ^ ((1 - a) / 2) * y ^ ((1 - a) / 2) := by
    rw [← Real.rpow_add hypos]
    congr 1
    ring
  set S : ℝ := y ^ ((1 - a) / 2) with hS
  have hSpos : 0 < S := Real.rpow_pos_of_pos hypos _
  have h1 : 1 ≤ S * (δ * e ^ 2) := (div_le_iff₀ hde).mp hBle
  have h2 : S / e ^ 2 ≤ δ * (S * S) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < e ^ 2)]
    nlinarith [h1, hSpos]
  rw [hsplit]
  exact le_trans hsq h2

private lemma eventually_rpow_le_div_log_sq {a δ : ℝ} (ha : a < 1) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ y : ℝ, Y₀ ≤ y → y ^ a ≤ δ * y / Real.log y ^ 2 := by
  obtain ⟨A, hA⟩ := log_sq_le_rpow_of_slack ha hδ
  refine ⟨max A 2, ?_⟩
  intro y hy
  have hyA : A ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : (2 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hypos : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have hls := hA y hyA
  have hya : 0 < y ^ a := Real.rpow_pos_of_pos hypos a
  have hsub : y ^ (1 - a) = y / y ^ a := by
    rw [Real.rpow_sub hypos, Real.rpow_one]
  have hkey : y ^ a * Real.log y ^ 2 ≤ δ * y := by
    have h := mul_le_mul_of_nonneg_left hls hya.le
    rw [hsub] at h
    have hcancel : y ^ a * (δ * (y / y ^ a)) = δ * y := by
      field_simp
    linarith
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < Real.log y ^ 2)).mpr hkey

/-- A forward prime-free `[z, z+H]` with `H ≥ L` and `z + L ≤ 2Y` has `z + L` in the backward
bad set at exponent `a`, provided the backward step `L` is at least `(2Y)^a`. -/
private lemma add_shift_mem_backwardBadSet {a : ℝ} (ha : 0 ≤ a) {Y H L : ℕ}
    (hL : (2 * (Y : ℝ)) ^ a ≤ (L : ℝ)) (hLH : L ≤ H) {z : ℕ}
    (hz : z ∈ badSet Y H) (hzL : z + L ≤ 2 * Y) :
    z + L ∈ backwardBadSet a Y := by
  classical
  obtain ⟨hzmem, hfree⟩ := Finset.mem_filter.mp hz
  obtain ⟨hzY, hz2Y⟩ := Finset.mem_Icc.mp hzmem
  have hzLR : ((z + L : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast hzL
  have hcast : ((z + L : ℕ) : ℝ) = (z : ℝ) + L := by push_cast; ring
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hzL⟩, ?_⟩
  have hta : (((z + L : ℕ)) : ℝ) ^ a ≤ (L : ℝ) :=
    le_trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hzLR ha) hL
  intro p hp1 hp2 hpp
  have hpz : ((z : ℕ) : ℝ) ≤ (p : ℝ) := by rw [hcast] at hp1 hta; linarith
  have hpzN : z ≤ p := by exact_mod_cast hpz
  have hpH : p ≤ z + H := by omega
  exact hfree p (Finset.mem_Icc.mpr ⟨hpzN, hpH⟩) hpp

/-- The forward bad count is at most the backward one plus the `L + 1` points of the top slice
of `[Y, 2Y]` that are shifted out of range. -/
private lemma card_badSet_le_backward {a : ℝ} (ha : 0 ≤ a) {Y H L : ℕ}
    (hL : (2 * (Y : ℝ)) ^ a ≤ (L : ℝ)) (hLH : L ≤ H) :
    (badSet Y H).card ≤ (backwardBadSet a Y).card + (L + 1) := by
  classical
  set S1 := (badSet Y H).filter (fun z => z + L ≤ 2 * Y) with hS1
  set S2 := (badSet Y H).filter (fun z => ¬ z + L ≤ 2 * Y) with hS2
  have hsplit : (badSet Y H).card = S1.card + S2.card := by
    rw [hS1, hS2]
    exact (Finset.card_filter_add_card_filter_not (s := badSet Y H)
      (fun z => z + L ≤ 2 * Y)).symm
  have hS1le : S1.card ≤ (backwardBadSet a Y).card := by
    refine Finset.card_le_card_of_injOn (fun z => z + L) ?_ ?_
    · intro z hz
      simp only [hS1, Finset.coe_filter, Set.mem_ofPred_eq] at hz
      exact add_shift_mem_backwardBadSet ha hL hLH hz.1 hz.2
    · intro z _ w _ hzw
      simp only at hzw
      omega
  have hS2le : S2.card ≤ L + 1 := by
    have hsub : S2 ⊆ Finset.Icc (2 * Y - L) (2 * Y) := by
      intro z hz
      rw [hS2] at hz
      obtain ⟨hzbad, hznot⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzY, hz2Y⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hzbad).1
      exact Finset.mem_Icc.mpr ⟨by omega, hz2Y⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  omega

/-- Positive exponent slack turns the backward exception count into the forward almost-all
count: the dyadic factor `2^a` and the top-slice loss `L ≈ Y^a` are both `o(Y / log² Y)`. -/
private theorem almostAllCount_of_backward_exceptions {a b C y₀ : ℝ}
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) (_hC : 0 < C)
    (hin : ∀ Y : ℕ, y₀ ≤ Y → ((backwardBadSet a Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3) :
    ∃ X : ℝ, AlmostAllCount b X := by
  classical
  have ha1 : a < 1 := lt_of_lt_of_le hab hb1
  have hba : 0 < b - a := by linarith
  have h2a : (0 : ℝ) < 2 ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have hgrowth : ∀ᶠ y : ℝ in Filter.atTop, (2 : ℝ) ^ a ≤ y ^ (b - a) :=
    (tendsto_rpow_atTop hba).eventually_ge_atTop _
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hgrowth
  have hlogC : ∀ᶠ y : ℝ in Filter.atTop, max (2 * C) 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hlogC
  obtain ⟨D, hD⟩ := eventually_rpow_le_div_log_sq ha1 (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨E, hE⟩ := log_sq_le_rpow_of_slack (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨max (max y₀ 3) (max A (max B (max D (max E 1)))), ?_⟩
  intro Y hY H hH
  have hYy₀ : y₀ ≤ (Y : ℝ) := by grind
  have hY3 : (3 : ℝ) ≤ Y := by grind
  have hYA : A ≤ (Y : ℝ) := by grind
  have hYB : B ≤ (Y : ℝ) := by grind
  have hYD : D ≤ (Y : ℝ) := by grind
  have hYE : E ≤ (Y : ℝ) := by grind
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hYpos : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hCle : 2 * C ≤ Real.log Y := by
    have := hB (Y : ℝ) hYB
    linarith [le_max_left (2 * C) 1]
  -- the backward step
  set L : ℕ := ⌈(2 * (Y : ℝ)) ^ a⌉₊ with hLdef
  have hLle : (2 * (Y : ℝ)) ^ a ≤ (L : ℝ) := Nat.le_ceil _
  have hLmax : (2 * (Y : ℝ)) ^ a = 2 ^ a * (Y : ℝ) ^ a := Real.mul_rpow (by norm_num) hYpos.le
  have hYb : (Y : ℝ) ^ b = (Y : ℝ) ^ (b - a) * (Y : ℝ) ^ a := by
    rw [← Real.rpow_add hYpos]
    congr 1
    ring
  have h2Yle : (2 * (Y : ℝ)) ^ a ≤ (H : ℝ) := by
    rw [hLmax]
    calc 2 ^ a * (Y : ℝ) ^ a ≤ (Y : ℝ) ^ (b - a) * (Y : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (hA (Y : ℝ) hYA) (by positivity)
      _ = (Y : ℝ) ^ b := hYb.symm
      _ ≤ (H : ℝ) := hH
  have hLH : L ≤ H := Nat.ceil_le.mpr h2Yle
  have hcard := card_badSet_le_backward (a := a) ha0 (Y := Y) (H := H) (L := L) hLle hLH
  have hback := hin Y hYy₀
  have hceil : (L : ℝ) < (2 * (Y : ℝ)) ^ a + 1 := Nat.ceil_lt_add_one (by positivity)
  have hcardR : ((badSet Y H).card : ℝ) ≤ C * Y / Real.log Y ^ 3 + ((2 * (Y : ℝ)) ^ a + 2) := by
    have h1 : ((badSet Y H).card : ℝ) ≤ ((backwardBadSet a Y).card : ℝ) + ((L : ℝ) + 1) := by
      exact_mod_cast hcard
    linarith
  have hp : (2 * (Y : ℝ)) ^ a ≤ Y / (4 * Real.log Y ^ 2) := by
    have h1 := hD (Y : ℝ) hYD
    have h2a2 : (2 : ℝ) ^ a ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt ha1)
      simpa using h
    rw [hLmax]
    calc 2 ^ a * (Y : ℝ) ^ a ≤ 2 * (Y : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right h2a2 (by positivity)
      _ ≤ 2 * (1 / 8 * Y / Real.log Y ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = Y / (4 * Real.log Y ^ 2) := by ring
  have htwo : 2 ≤ Y / (4 * Real.log Y ^ 2) := by
    have h1 := hE (Y : ℝ) hYE
    have hsqrt : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ Y := by
      have := Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
      simpa using this
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log Y ^ 2)]
    nlinarith [h1, hsqrt, hlogY]
  have hCterm : C * Y / Real.log Y ^ 3 ≤ Y / (2 * Real.log Y ^ 2) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < Real.log Y ^ 3)
      (by positivity : (0 : ℝ) < 2 * Real.log Y ^ 2)]
    have hmul : (2 * C) * (Y * Real.log Y ^ 2) ≤ Real.log Y * (Y * Real.log Y ^ 2) :=
      mul_le_mul_of_nonneg_right hCle (by positivity)
    nlinarith
  have hmain : C * Y / Real.log Y ^ 3 + ((2 * (Y : ℝ)) ^ a + 2) ≤ Y / Real.log Y ^ 2 := by
    have heq : Y / (2 * Real.log Y ^ 2) + (Y / (4 * Real.log Y ^ 2) + Y / (4 * Real.log Y ^ 2))
        = Y / Real.log Y ^ 2 := by
      field_simp
      ring
    linarith
  linarith

/-- Goldbach numbers in `[x, x + 3 x^{13/600+ε}]`: for every `ε > 0` and all large natural `x` there
is an even sum of two primes in this interval. The two cited results `LiRow052` and
`LiIIIExceptionalCount` are explicit hypotheses. -/
theorem goldbach_short_600 (hRow : LiRow052) (hLi : LiIIIExceptionalCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (13 / 600 + ε : ℝ) := by
  obtain ⟨c, hc, hrow⟩ := hRow
  let η : ℝ := min (ε / 2) 0.005
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ 0.005 := min_le_right _ _
  obtain ⟨Xr, hXr⟩ := hrow η hη hη2
  have ha0 : (0 : ℝ) < 0.52 + η := by linarith
  have ha1 : (0.52 : ℝ) + η < 1 := by linarith
  obtain ⟨x₀, hW⟩ := windowCount_of_backward ha0.le ha1 hc hXr
  obtain ⟨C, y₀, hC, hbdd⟩ := hLi η hη
  have hb0 : (0 : ℝ) < 1 / 24 + η := by positivity
  have hbstep : (1 : ℝ) / 24 + η < 1 / 24 + 2 * η := by linarith
  have hb1 : (1 : ℝ) / 24 + 2 * η ≤ 1 := by linarith
  obtain ⟨y₁, hA⟩ := almostAllCount_of_backward_exceptions (a := 1 / 24 + η)
    (b := 1 / 24 + 2 * η) (C := C) (y₀ := y₀) hb0.le hbstep hb1 hC hbdd
  have hb0' : (0 : ℝ) ≤ 1 / 24 + 2 * η := by linarith
  obtain ⟨X, hX⟩ := goldbach_short_b_eventually ha0 ha1 hb0' hb1
    (by positivity : 0 < c / 32) hW hA
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hxX : X ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨n, hn, hnx, hupper⟩ := hX x hxX
  have he : (0.52 + η) * (1 / 24 + 2 * η) ≤ (13 / 600 + ε : ℝ) := by
    have hexp : (0.52 + η) * (1 / 24 + 2 * η) = 13 / 600 + η * (649 / 600 + 2 * η) := by ring
    rw [hexp]
    have hcoef : 649 / 600 + 2 * η ≤ 2 := by linarith
    have h1 : η * (649 / 600 + 2 * η) ≤ η * 2 := mul_le_mul_of_nonneg_left hcoef hη.le
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hx1 he
  exact ⟨n, hn, hnx, by linarith⟩

end LeanLab.GoldbachShort78
