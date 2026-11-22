module

public import LeanLab.KadiriLumley2014.PalomarEntry

/-!
Kadiri and Lumley 2014, a variant of Corollary 1.2 that uses Table 2 row 57 in place of
row 60. Page 2 Corollary 1.2 and its proof on page 13, with the row 57 entry of Table 2 on
page 13: Delta = 1886389443 from x0 = e^57.
An uncertified floating point check by the lab, with the computed low zeros of ζ and the
paper's zero density bound above height 3.061e10, found display 2.64 positive at the rows
log 4e18 to 57 and negative at rows 58, 59, 60 and 150. So this variant asks display 2.64 only
at rows that published zero data appears to support, at the cost of the smaller range
1886389443 times 4e18 in place of 1966196911 times 4e18.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.PalomarEntry57
open Real
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- `e^57 ≤ 1.15 · 10^26`, from the bound for `e^60`. -/
theorem exp57_le : Real.exp 57 ≤ 1.15 * 10 ^ 26 :=
  (Real.exp_le_exp.mpr (by norm_num)).trans exp60_le

/-- The ladder step of the page 13 proof with rows log 4e18 and 57: for odd `n` past
`4 · 10^18 + 3` and below `1886389443 · 4 · 10^18` a prime `p` leaves an even remainder
between 4 and `4 · 10^18 + 2`, as in the proof of Corollary 1.2 on page 13. -/
theorem step57 (h1 : KLRow (4 * 10 ^ 18) 36082898) (h2 : KLRow (Real.exp 57) 1886389443) :
    ∀ n : ℕ, Odd n → 4 * 10 ^ 18 + 3 < n → n < 1886389443 * (4 * 10 ^ 18) →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ p + 4 ≤ n ∧ n - p ≤ 4 * 10 ^ 18 + 2 := by
  intro n hn hlo hhi
  have hnR : (4 * 10 ^ 18 + 3 : ℝ) < n := by exact_mod_cast hlo
  have hnR2 : (n : ℝ) < 1886389443 * (4 * 10 ^ 18) := by exact_mod_cast hhi
  set x : ℝ := n - 3 with hx
  have hx0 : (4 * 10 ^ 18 : ℝ) < x := by rw [hx]; linarith
  have key : ∃ p : ℕ, p.Prime ∧ x - 4 * 10 ^ 18 < p ∧ x / 2 < p ∧ (p : ℝ) < x := by
    rcases le_or_gt x (Real.exp 57) with hs | hb
    · obtain ⟨p, hp, hl, hu⟩ := h1 x hx0
      have : x ≤ 1.15 * 10 ^ 26 := le_trans hs exp57_le
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
  rcases hev with ⟨k, hk⟩
  omega

/-- The corollary range from rows log 4e18 and 57, the even verification and the certified
partition of `4 · 10^18 + 2`, as in the proof of Corollary 1.2 on page 13. -/
theorem corollary57_of (h1 : KLRow (4 * 10 ^ 18) 36082898)
    (h2 : KLRow (Real.exp 57) 1886389443) (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ n : ℕ, Odd n → 5 < n → n < 1886389443 * (4 * 10 ^ 18) → IsTernarySum n := by
  intro n hn h5 hhi
  rcases Nat.lt_or_ge (4 * 10 ^ 18 + 3) n with hbig | hsmall
  · obtain ⟨p, hp, hpo, h4, hle⟩ := step57 h1 h2 n hn hbig hhi
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

/-- Corollary 1.2 with row 57 in place of row 60: every odd `n` with `5 < n` and
`n < 1886389443 · 4 · 10^18` is a sum of three primes, conditionally.
Named inputs, each an explicit hypothesis: hEven, the 4e18 verification of Oliveira e Silva,
Herzog and Pardi 2014; hMV, Montgomery and Vaughan 1973 Theorem 2; hDus, Dusart 2010
Theorem 5.2 row eta_2 = 0.05; h0 and h57, display 2.64 with the true zero sum at Table 2 rows
log 4e18 and 57. An uncertified floating point check found both rows positive from published
zero data alone, with margins about 0.27 and 0.011. -/
theorem corollary57_of_inputs (hEven : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    (hDus : ∀ t : ℝ, 122568683 ≤ t →
      |Chebyshev.theta t - t| < 0.05 * t / Real.log t ^ 2)
    (h0 : let r : PrintedRow := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)))
    (h57 : let r : PrintedRow := ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
    ∀ n : ℕ, Odd n → 5 < n → n < 1886389443 * (4 * 10 ^ 18) → IsTernarySum n := by
  have hC : CostaEstimate := CostaSplit.costa_of_dusart hDus
  have r0 : KLRow (4 * 10 ^ 18) 36082898 := by
    convert (PalomarEntry.row_of_inputs hC hMV
      (r := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩) (by decide +kernel) h0)
      using 1 <;> norm_num [Task64.PrintedRow.threshold, Task64.evenBase]
  have r57 : KLRow (Real.exp 57) 1886389443 := by
    convert (PalomarEntry.row_of_inputs hC hMV
      (r := ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩) (by decide +kernel) h57)
      using 1 <;> norm_num [Task64.PrintedRow.threshold, Task64.evenBase]
  exact corollary57_of r0 r57 hEven

end LeanLab.KadiriLumley2014.PalomarEntry57
