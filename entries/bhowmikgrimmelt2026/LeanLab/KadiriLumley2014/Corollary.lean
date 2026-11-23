module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.KadiriLumley2014.RowDefinition92
public import LeanLab.Verifications.Pratt

/-!
P0059 Kadiri-Lumley 2014, Corollary 1.2 proved from two Table 2 rows, the Oliveira e Silva,
Herzog and Pardi even verification to `4 · 10^18`, and one extra Goldbach partition of
`4 · 10^18 + 2`, certified here by Pratt certificates. The extra partition is needed at the
very top of the range: there `n - p` can be `4 · 10^18 + 2`.
Also: the lab's `KL45` input of DERZ1997/Unconditional follows from the `log x0 = 45` row.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014
open Real LeanLab.Verifications.Pratt

/-! ### `4 · 10^18 + 2 = 241 + 3999999999999999761` -/

theorem p777448979 : Nat.Prime 777448979 := pB (by decide +kernel)

theorem p13994081623 : Nat.Prime 13994081623 := by
  refine pratt 13994081623 3 [(2, 1), (3, 2), (777448979, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact p777448979

theorem pBig : Nat.Prime 3999999999999999761 := by
  refine pratt 3999999999999999761 7 [(2, 4), (5, 1), (3572939, 1), (13994081623, 1)]
    (by norm_num) (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_five
  · exact pB (by decide +kernel)
  · exact p13994081623

theorem goldbach_top : IsGoldbachSum (4 * 10 ^ 18 + 2) :=
  ⟨241, 3999999999999999761, by norm_num, pBig, by norm_num⟩

theorem exp60_le : Real.exp 60 ≤ 1.15 * 10 ^ 26 := by
  have h1 : Real.exp 60 = Real.exp 1 ^ 60 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  calc Real.exp 1 ^ 60 ≤ (2.7182818286 : ℝ) ^ 60 := by gcongr; exact Real.exp_one_lt_d9.le
    _ ≤ 1.15 * 10 ^ 26 := by norm_num

/-- One step of the ladder: a prime `p` with `n - p` even, `4 ≤ n - p ≤ 4 · 10^18 + 2`. -/
theorem step (h1 : KLRow (4 * 10 ^ 18) 36082898) (h2 : KLRow (Real.exp 60) 1966196911) :
    ∀ n : ℕ, Odd n → 4 * 10 ^ 18 + 3 < n → n < 1966196911 * (4 * 10 ^ 18) →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ p + 4 ≤ n ∧ n - p ≤ 4 * 10 ^ 18 + 2 := by
  intro n hn hlo hhi
  have hnR : (4 * 10 ^ 18 + 3 : ℝ) < n := by exact_mod_cast hlo
  have hnR2 : (n : ℝ) < 1966196911 * (4 * 10 ^ 18) := by exact_mod_cast hhi
  set x : ℝ := n - 3 with hx
  have hx0 : (4 * 10 ^ 18 : ℝ) < x := by rw [hx]; linarith
  -- a prime with (1 - 1/Δ) x < p < x and x/Δ < 4e18
  have key : ∃ p : ℕ, p.Prime ∧ x - 4 * 10 ^ 18 < p ∧ x / 2 < p ∧ (p : ℝ) < x := by
    rcases le_or_gt x (Real.exp 60) with hs | hb
    · obtain ⟨p, hp, hl, hu⟩ := h1 x hx0
      have : x ≤ 1.15 * 10 ^ 26 := le_trans hs exp60_le
      refine ⟨p, hp, ?_, ?_, hu⟩ <;> nlinarith
    · obtain ⟨p, hp, hl, hu⟩ := h2 x hb
      refine ⟨p, hp, ?_, ?_, hu⟩ <;> nlinarith
  obtain ⟨p, hp, hl, hhalf, hu⟩ := key
  have hp3 : p + 3 < n := by
    have : (p : ℝ) + 3 < n := by linarith
    exact_mod_cast this
  have hgap : n < p + (4 * 10 ^ 18 + 3) := by
    have : (n : ℝ) < p + (4 * 10 ^ 18 + 3) := by linarith
    exact_mod_cast this
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hhalf
    linarith
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hev : Even (n - p) := Nat.Odd.sub_odd hn hpo
  refine ⟨p, hp, hpo, ?_, by omega⟩
  -- n - p is even and greater than 3, so at least 4
  rcases hev with ⟨k, hk⟩
  omega

/-- Corollary 1.2 from the two Table 2 rows, the `4 · 10^18` even verification and the
certified partition of `4 · 10^18 + 2`. -/
theorem corollary1_2_of (h1 : KLRow (4 * 10 ^ 18) 36082898)
    (h2 : KLRow (Real.exp 60) 1966196911) (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ n : ℕ, Odd n → 5 < n → n < 1966196911 * (4 * 10 ^ 18) → IsTernarySum n := by
  intro n hn h5 hhi
  rcases Nat.lt_or_ge (4 * 10 ^ 18 + 3) n with hbig | hsmall
  · obtain ⟨p, hp, hpo, h4, hle⟩ := step h1 h2 n hn hbig hhi
    have hev : Even (n - p) := Nat.Odd.sub_odd hn hpo
    rcases Nat.lt_or_ge (n - p) (4 * 10 ^ 18 + 1) with hin | htop
    · obtain ⟨q, r, hq, hr, hqr⟩ := hE (n - p) hev (by omega) (by omega)
      exact ⟨p, q, r, hp, hq, hr, by omega⟩
    · have heq : n - p = 4 * 10 ^ 18 + 2 := by
        rcases hev with ⟨k, hk⟩; omega
      obtain ⟨q, r, hq, hr, hqr⟩ := goldbach_top
      exact ⟨p, q, r, hp, hq, hr, by omega⟩
  · have h7 : 7 ≤ n := by
      rcases hn with ⟨k, hk⟩; omega
    have hev : Even (n - 3) := Nat.Odd.sub_odd hn (by decide)
    obtain ⟨q, r, hq, hr, hqr⟩ := hE (n - 3) hev (by omega) (by omega)
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩

/-- The lab's natural number form `KL45` of DERZ1997/Unconditional follows from row 45. -/
theorem kl45_of_row (h : KLRow (Real.exp 45) 95381241) :
    ∀ y : ℕ, Real.exp 45 < y → ∃ p : ℕ, p.Prime ∧ p < y ∧ 95381241 * (y - p) < y := by
  intro y hy
  obtain ⟨p, hp, hl, hu⟩ := h y hy
  have hpy : p < y := by exact_mod_cast hu
  refine ⟨p, hp, hpy, ?_⟩
  have : (95381241 : ℝ) * ((y : ℝ) - p) < y := by
    have : (1 - 1 / (95381241 : ℝ)) * y = y - y / 95381241 := by ring
    rw [this] at hl
    have : (y : ℝ) - p < y / 95381241 := by linarith
    rw [lt_div_iff₀ (by norm_num)] at this
    linarith
  have hc : ((y - p : ℕ) : ℝ) = (y : ℝ) - p := by
    rw [Nat.cast_sub hpy.le]
  rw [← hc] at this
  exact_mod_cast this

end LeanLab.KadiriLumley2014
