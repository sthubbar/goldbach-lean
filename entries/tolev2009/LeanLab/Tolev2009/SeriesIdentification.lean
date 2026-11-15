module

public import LeanLab.Tolev2009.Faithful

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.SeriesIdentification

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful

/-- Reduced representatives for Halupczok's coefficient on page 7. -/
def coeffRes (k l q : ℕ) : Finset ℕ :=
  (range q).filter (fun r => Nat.Coprime r q ∧ r % Nat.gcd k q = l % Nat.gcd k q)

/-- Halupczok's local exponential sum, using representatives from zero through q minus one. -/
noncomputable def coeff (k l q a : ℕ) : ℂ :=
  ∑ r ∈ coeffRes k l q, ee ((a : ℝ) * r / q)

/-- Changing to a congruent residue preserves coprimality with the modulus. -/
theorem coprime_modEq (m a b : ℕ) (h : a % m = b % m) :
    Nat.Coprime a m ↔ Nat.Coprime b m := by
  have hg : Nat.gcd a m = Nat.gcd b m := by
    calc
      _ = Nat.gcd m a := Nat.gcd_comm _ _
      _ = Nat.gcd (a % m) m := Nat.gcd_rec _ _
      _ = Nat.gcd (b % m) m := by rw [h]
      _ = Nat.gcd m b := (Nat.gcd_rec _ _).symm
      _ = _ := Nat.gcd_comm _ _
  change Nat.gcd a m = 1 ↔ Nat.gcd b m = 1
  rw [hg]

/-- Integer frequencies see a residue only modulo q. -/
theorem ee_rat_mod (a r q : ℕ) (hq : 1 ≤ q) :
    ee ((a : ℝ) * r / q) = ee ((a : ℝ) * (r % q : ℕ) / q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hr : (r : ℝ) = (r % q : ℕ) + (q : ℝ) * (r / q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div r q).symm
  have he : (a : ℝ) * r / q = (a : ℝ) * (r % q : ℕ) / q + ((a * (r / q) : ℕ) : ℝ) := by
    rw [hr]
    push_cast
    field_simp
  rw [he, ee_add, show ee (((a * (r / q) : ℕ) : ℝ)) = 1 from ee_int (a * (r / q) : ℕ), mul_one]

/-- CRT projects the lifted residues bijectively onto Halupczok's residues. -/
theorem liftRes_projection (k l q : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) (hl : Nat.Coprime l k) :
    (liftRes k l q).image (fun r => r % q) = coeffRes k l q := by
  ext r
  constructor
  · intro hr
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hr
    rcases mem_filter.mp hu with ⟨hu, hmod, hcop⟩
    simp only [coeffRes, mem_filter, mem_range]
    have hcq : Nat.Coprime u q := hcop.coprime_dvd_right (Nat.dvd_lcm_right k q)
    refine ⟨Nat.mod_lt _ (by omega), ?_, ?_⟩
    · exact (coprime_modEq q (u % q) u (Nat.mod_mod _ _)).mpr hcq
    · rw [Nat.mod_mod_of_dvd u (Nat.gcd_dvd_right k q)]
      exact Nat.ModEq.of_dvd (Nat.gcd_dvd_left k q) hmod
  · intro hr
    rcases mem_filter.mp hr with ⟨hr, hcop, hmod⟩
    have hcompat : l ≡ r [MOD Nat.gcd k q] := hmod.symm
    let u := Nat.chineseRemainder' hcompat
    have huk : (u : ℕ) ≡ l [MOD k] := u.property.1
    have huq : (u : ℕ) ≡ r [MOD q] := u.property.2
    have huck : Nat.Coprime (u : ℕ) k := (coprime_modEq k _ _ huk).mpr hl
    have hucq : Nat.Coprime (u : ℕ) q := (coprime_modEq q _ _ huq).mpr hcop
    refine mem_image.mpr ⟨u, ?_, ?_⟩
    · simp only [liftRes, mem_filter, mem_range]
      exact ⟨Nat.chineseRemainder'_lt_lcm hcompat (by omega) (by omega), huk, (huck.mul_right hucq).coprime_dvd_right (Nat.lcm_dvd_mul k q)⟩
    · exact (show (u : ℕ) % q = r % q from huq).trans (Nat.mod_eq_of_lt (mem_range.mp hr))

/-- The projection to q is injective on the lifted residue set. -/
theorem liftRes_projection_inj (k l q : ℕ) :
    Set.InjOn (fun r => r % q) ↑(liftRes k l q) := by
  intro x hx y hy hxy
  rcases mem_filter.mp hx with ⟨hx, hxk, _⟩
  rcases mem_filter.mp hy with ⟨hy, hyk, _⟩
  exact (Nat.mod_lcm (hxk.trans hyk.symm) hxy).eq_of_lt_of_lt (mem_range.mp hx) (mem_range.mp hy)

/-- The local factor in Faithful equals the coefficient used by Halupczok. -/
theorem localSum_eq_coeff (k l q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) (hl : Nat.Coprime l k) :
    localSum k l q a = ((k.totient : ℂ) / ((Nat.lcm k q).totient : ℂ)) * coeff k l q a := by
  unfold localSum coeff
  rw [← liftRes_projection k l q hk hq hl, sum_image (liftRes_projection_inj k l q)]
  congr 1
  exact sum_congr rfl fun r _ => ee_rat_mod a r q hq

/-- Halupczok's literal representatives from 1 through q on page 7. -/
noncomputable def coeffPaper (k l q a : ℕ) : ℂ :=
  ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q ∧ r % Nat.gcd k q = l % Nat.gcd k q),
    ee ((a : ℝ) * r / q)

/-- The printed and reduced representative conventions have the same coefficient. -/
theorem coeffPaper_eq_coeff (k l q a : ℕ) (hq : 1 ≤ q) :
    coeffPaper k l q a = coeff k l q a := by
  let f : ℕ → ℂ := fun r =>
    if Nat.Coprime r q ∧ r % Nat.gcd k q = l % Nat.gcd k q then ee ((a : ℝ) * r / q) else 0
  have hp : ∀ r, f r = f (r % q) := by
    intro r
    have hc := coprime_modEq q (r % q) r (Nat.mod_mod r q)
    have hm := Nat.mod_mod_of_dvd r (Nat.gcd_dvd_right k q)
    simp only [f, hc, hm]
    split_ifs
    · exact ee_rat_mod a r q hq
    · rfl
  have hend : f q = f 0 := by simpa only [Nat.mod_self] using hp q
  have hset : insert 0 (Icc 1 q) = insert q (range q) := by
    ext r
    simp only [mem_insert, mem_Icc, mem_range]
    omega
  have hsum := congrArg (fun s : Finset ℕ => ∑ r ∈ s, f r) hset
  rw [sum_insert (by simp), sum_insert (by simp), hend] at hsum
  have he := add_left_cancel hsum
  simpa only [coeffPaper, coeff, coeffRes, sum_filter, f] using he

/-- The qth singular series term in Halupczok 2008 page 11. -/
noncomputable def halupczokTerm (k l : Fin 3 → ℕ) (N q : ℕ) : ℂ :=
  (∏ i : Fin 3, (k i).totient / ((Nat.lcm (k i) q).totient : ℂ)) *
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ee (-((a : ℝ) * N / q)) * ∏ i : Fin 3, coeffPaper (k i) (l i) q a

/-- The finite term normalisation of Faithful is exactly Halupczok's printed one. -/
theorem ssTerm_eq_halupczokTerm (k l : Fin 3 → ℕ) (N q : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hq : 1 ≤ q) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    ssTerm k l N q = halupczokTerm k l N q := by
  have he : ∀ i a, localSum (k i) (l i) q a =
      ((k i).totient : ℂ) / ((Nat.lcm (k i) q).totient : ℂ) * coeffPaper (k i) (l i) q a := by
    intro i a
    rw [coeffPaper_eq_coeff _ _ _ _ hq]
    exact localSum_eq_coeff _ _ _ _ (hk i) hq (hl i)
  unfold ssTerm halupczokTerm
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp_rw [he]
  rw [prod_mul_distrib]
  ring

/-- Halupczok's explicit singular series, with the same real part convention as Faithful. -/
noncomputable def halupczokSeries (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (∑' q : ℕ, halupczokTerm k l N (q + 1)).re

/-- The existing explicit series agrees term by term with the cited printed formula.
The lab also has a legacy opaque series; the repository copy omits it. -/
theorem singSeries_eq_halupczokSeries (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    singSeries k l N = halupczokSeries k l N := by
  unfold singSeries halupczokSeries
  congr 1
  apply tsum_congr
  intro q
  exact ssTerm_eq_halupczokTerm k l N (q + 1) hk (by omega) hl

end LeanLab.Tolev2009.SeriesIdentification
