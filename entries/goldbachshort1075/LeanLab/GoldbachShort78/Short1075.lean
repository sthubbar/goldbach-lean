module

public import LeanLab.GoldbachShort78.Tiling
public import LeanLab.GoldbachShort78.LiNormalization

/-!
Goldbach numbers in short intervals at the exponent `26/1075`.

`goldbach_short_1075`: for every `ε > 0` and all large `x` there is an even sum of two primes in
`[x, x + 3 x^{26/1075 + ε}]`, conditional on two cited results taken as explicit hypotheses, never as
axioms:
* `LiRow052`, R. Li, arXiv 2308.04458, Theorem 2, page 2, the row `θ = 0.52`, with some positive
  constant. The value printed for `LB(0.520)` differs between versions of the paper.
* `LiPrintedExceptionalCount`, R. Li, arXiv 2407.05651 v6, Theorem 1.1, page 2.

The argument is that of R. Li, arXiv 2407.05651 v6, Theorem 7.1, page 27, exponent `21/860` from
the `0.525` of Baker, Harman and Pintz. The exponent `26/1075` is lower by `1/4300`, and the gain is
only the replacement of `0.525` by Li's `0.52`. The same exponent is printed as Theorem 7 of
arXiv 2308.04458, with no `ε` and no factor `3`.

`windowCount_of_backward` is proved with no cited input: a count of primes in `(n − n^a, n]` gives
the count in the windows `[x − 2Y, x − Y]` at the same exponent.

AI wrote the Lean code, Claude. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.GoldbachShort78

open Real

/-- The exponent arithmetic: `0.52 · 1/21.5 = 26/1075`, below the `21/860` of R. Li, arXiv
2407.05651 v6, Theorem 7.1, by `1/4300`. -/
theorem exponent_1075 :
    (0.52 : ℝ) * (1 / 21.5) = 26 / 1075 ∧ (26 : ℝ) / 1075 < 21 / 860 ∧
      (21 : ℝ) / 860 - 26 / 1075 = 1 / 4300 := by
  norm_num

/-- Cited input, R. Li, arXiv 2308.04458, Theorem 2, page 2, the row `θ = 0.52`, with some positive
constant `c` in place of the printed `LB(0.520)`: for `0 < ε ≤ 0.005` and all large integers `n`, the
interval `(n − n^{0.52+ε}, n]` holds more than `c n^{0.52+ε} / log n` primes. The printed value of
`LB(0.520)` differs between versions of the paper, so only its positivity is assumed. -/
def LiRow052 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 0.005 → ∃ X : ℝ, ∀ n : ℕ, X ≤ n →
    c * (n : ℝ) ^ (0.52 + ε : ℝ) / Real.log n <
      ((primeInterval ((n : ℝ) - (n : ℝ) ^ (0.52 + ε : ℝ)) n).card : ℝ)

/-- Proved with no cited input: a count of primes in `(n − n^a, n]` for all large integers `n` gives
`WindowCount a (c/32)`. Tiles have the integer length `⌈x^a⌉`, so every right endpoint is an integer,
as the hypothesis needs. -/
theorem windowCount_of_backward {a c X : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hc : 0 < c)
    (hin : ∀ n : ℕ, X ≤ n →
      c * (n : ℝ) ^ a / Real.log n < ((primeInterval ((n : ℝ) - (n : ℝ) ^ a) n).card : ℝ)) :
    ∃ x₀ : ℝ, WindowCount a (c / 32) x₀ := by
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, (8 : ℝ) ≤ x ^ (1 - a) :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - a)).eventually_ge_atTop 8
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max (4 * max X 2) A, ?_⟩
  intro x hx Y hY hsize
  have hxX : 4 * max X 2 ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hxA : A ≤ (x : ℝ) := le_trans (le_max_right _ _) hx
  have hXm : X ≤ max X 2 := le_max_left _ _
  have h2m : (2 : ℝ) ≤ max X 2 := le_max_right _ _
  have hx8 : (8 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsizeR : 2 * (Y : ℝ) + 3 ≤ x := by exact_mod_cast hsize
  have hYx : Y ≤ x := by omega
  have h2Yx : 2 * Y ≤ x := by omega
  set P : ℝ := (x : ℝ) ^ a with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hxpos _
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) ha0
  let Ln : ℕ := ⌈P⌉₊
  let L : ℝ := (Ln : ℝ)
  have hPL : P ≤ L := Nat.le_ceil P
  have hLP : L < P + 1 := Nat.ceil_lt_add_one hP.le
  have hL : 0 < L := by linarith
  have hsmall : L ≤ (x : ℝ) / 4 := by
    have hprod : P * (x : ℝ) ^ (1 - a) = x := by
      rw [hPdef, ← Real.rpow_add hxpos]
      norm_num
    have := mul_le_mul_of_nonneg_left (hA x hxA) hP.le
    nlinarith
  have hLY : L ≤ (Y : ℝ) := by
    have hLnY : Ln ≤ Y := Nat.ceil_le.mpr hY
    change (Ln : ℝ) ≤ (Y : ℝ)
    exact_mod_cast hLnY
  obtain ⟨k, hk, hkY, hkmax, hkcover⟩ := exists_tile_number hL hLY
  have hkquarter : (k : ℝ) * L ≤ (x : ℝ) / 4 :=
    le_trans hkmax (max_le (by linarith) hsmall)
  have hleft : ((x - 2 * Y : ℕ) : ℝ) ≤ (x : ℝ) - Y - (k : ℝ) * L := by
    rw [Nat.cast_sub h2Yx]
    push_cast
    linarith
  have hright : (x : ℝ) - Y ≤ (x - Y : ℕ) := by
    rw [Nat.cast_sub hYx]
  have htiles := right_tiles_count hL.le hleft hright (d := c * (P / 4) / Real.log x)
  have hall : ∀ i ∈ Finset.range k,
      c * (P / 4) / Real.log x ≤
      ((primeInterval ((x : ℝ) - Y - ((i : ℝ) + 1) * L)
        ((x : ℝ) - Y - (i : ℝ) * L)).card : ℝ) := by
    intro i hi
    have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.mp hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hiL : (i : ℝ) * L ≤ (x : ℝ) / 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hik) hL.le]
    have hiLn : i * Ln + Y ≤ x := by
      have : ((i * Ln + Y : ℕ) : ℝ) ≤ x := by
        push_cast
        have : (i : ℝ) * (Ln : ℝ) ≤ (x : ℝ) / 4 := hiL
        linarith
      exact_mod_cast this
    let n : ℕ := x - (i * Ln + Y)
    have hn : (n : ℝ) = (x : ℝ) - Y - (i : ℝ) * L := by
      dsimp [n, L]
      rw [Nat.cast_sub hiLn]
      push_cast
      ring
    have hn4 : (x : ℝ) / 4 ≤ n := by rw [hn]; linarith
    have hnx : (n : ℝ) ≤ x := by
      rw [hn]
      nlinarith [mul_nonneg hi0 hL.le, show (0 : ℝ) ≤ Y from Nat.cast_nonneg _]
    have hnX : X ≤ n := by linarith
    have hn2 : (2 : ℝ) ≤ n := by linarith
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogle : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
    have hcount := hin n hnX
    have hpow4 : P / 4 ≤ (n : ℝ) ^ a := quarter_rpow_le hxpos.le hn4 ha0 ha1.le
    have hpowle : (n : ℝ) ^ a ≤ P := Real.rpow_le_rpow hn0 hnx ha0
    have hsub : primeInterval ((n : ℝ) - (n : ℝ) ^ a) n ⊆
        primeInterval ((x : ℝ) - Y - ((i : ℝ) + 1) * L) ((x : ℝ) - Y - (i : ℝ) * L) := by
      intro p hp
      obtain ⟨hpl, hpr, hpp⟩ := mem_primeInterval.mp hp
      refine mem_primeInterval.mpr ⟨?_, ?_, hpp⟩
      · have : (x : ℝ) - Y - ((i : ℝ) + 1) * L = (n : ℝ) - L := by rw [hn]; ring
        rw [this]
        linarith
      · rw [← hn]
        exact hpr
    calc
      c * (P / 4) / Real.log x ≤ c * (n : ℝ) ^ a / Real.log x := by
        apply div_le_div_of_nonneg_right _ hlogx.le
        exact mul_le_mul_of_nonneg_left hpow4 hc.le
      _ ≤ c * (n : ℝ) ^ a / Real.log n :=
        div_le_div_of_nonneg_left (by positivity) hlogn hlogle
      _ ≤ ((primeInterval ((n : ℝ) - (n : ℝ) ^ a) n).card : ℝ) := hcount.le
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub
  have htotal := htiles hall
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkP : (Y : ℝ) / 8 ≤ (k : ℝ) * P := by
    have hL2 : L ≤ 2 * P := by linarith
    have := mul_le_mul_of_nonneg_left hL2 hk0
    linarith
  calc
    (c / 32) * Y / Real.log x ≤ c * ((k : ℝ) * P / 4) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlogx.le
      nlinarith
    _ = (k : ℝ) * (c * (P / 4) / Real.log x) := by ring
    _ ≤ ((primeWindow x Y).card : ℝ) := htotal

/-- Goldbach numbers in `[x, x + 3 x^{26/1075+ε}]`: for every `ε > 0` and all large natural `x` there
is an even sum of two primes in this interval. The two cited results `LiRow052` and
`LiPrintedExceptionalCount` are explicit hypotheses. -/
theorem goldbach_short_1075 (hRow : LiRow052) (hLi : LiPrintedExceptionalCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (26 / 1075 + ε : ℝ) := by
  obtain ⟨c, hc, hrow⟩ := hRow
  let η : ℝ := min (ε / 2) 0.005
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ 0.005 := min_le_right _ _
  obtain ⟨Xr, hXr⟩ := hrow η hη hη2
  have ha0 : (0 : ℝ) < 0.52 + η := by linarith
  have ha1 : (0.52 : ℝ) + η < 1 := by linarith
  obtain ⟨x₀, hW⟩ := windowCount_of_backward ha0.le ha1 hc hXr
  obtain ⟨y₀, hA⟩ := liAlmostAllCountEps_of_printed hLi hη
  have hb0 : (0 : ℝ) ≤ 1 / 21.5 + η := by positivity
  have hb1 : (1 : ℝ) / 21.5 + η ≤ 1 := by
    have : (1 : ℝ) / 21.5 ≤ 1 / 2 := by norm_num
    linarith
  obtain ⟨X, hX⟩ := goldbach_short_b_eventually ha0 ha1 hb0 hb1 (by positivity : 0 < c / 32) hW hA
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hxX : X ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨n, hn, hnx, hupper⟩ := hX x hxX
  have he : (0.52 + η) * (1 / 21.5 + η) ≤ (26 / 1075 + ε : ℝ) := by
    have hexp : (0.52 + η) * (1 / 21.5 + η) = (26 / 1075 : ℝ) + η * (0.52 + 1 / 21.5 + η) := by
      ring_nf
    rw [hexp]
    have hsum : (0.52 : ℝ) + 1 / 21.5 + η ≤ 2 := by
      have : (1 : ℝ) / 21.5 ≤ 1 / 2 := by norm_num
      linarith
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hx1 he
  exact ⟨n, hn, hnx, by linarith⟩

end LeanLab.GoldbachShort78
