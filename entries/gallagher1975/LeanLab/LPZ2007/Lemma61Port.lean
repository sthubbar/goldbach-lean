module

public import Mathlib
public import LeanLab.LPZ2007.Elementary
public import LeanLab.Romanov.Lemma
public import LeanLab.PNTSieve.MertensProduct

/-!
P0045 Languasco, Pintz, Zaccagnini 2007, Lemma 6.1 p.9: the series (26), Σ' f(d)/ξ(d), converges.
PORTED into the PC encoding A, LPZ2007/, from the cloud encoding B,
LanguascoPintzZaccagnini2007/Lemma61.lean, which proves it for B's definitions. The two encodings
declare the same names in namespace `LeanLab.LPZ2007`, so neither can import the other; this file
copies B's proof and adapts it to A's `xi d = orderOf (2 : ZMod d)` and `OddSqf d = Odd d ∧
Squarefree d`. Only `xi_spec_sqf` is new.

Unit U-1229, T1 PROVE, PC run 20261020T1203Z-6833. Original proof: CLOUD unit in B, after
Romanov and the lab's Romanov/Lemma.lean.

* `lemma61_proved : Lemma61`, PROVED unconditional for A's `romanovTerm`.
* `few_Rpp_zero_of_eq25`: with MinorBoundProof, almost every even N ∈ J(X) is two primes plus k
  powers of two, at most B X^{3/5} (log X)^{10} exceptions, CONDITIONAL ON the repaired (25) only.

KNOWN mathematics. AI wrote this Lean code. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here is Goldbach.
-/

@[expose] public section

namespace LeanLab.LPZ2007.Lemma61Port

open Finset Real LeanLab.LPZ2007

attribute [local instance] Classical.propDecidable

noncomputable section

lemma prodH_le (n y : ℕ) (hy : 4 ≤ y) (hodd : ∀ p ∈ n.primeFactors, 3 ≤ p)
    (hω : n.primeFactors.card ≤ y) :
    ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 2)) ≤ exp 27 * log y := by
  have hy4 : (4 : ℝ) ≤ y := by exact_mod_cast hy
  have hly : 0 < log (y : ℝ) := log_pos (by linarith)
  have hp3 : ∀ p ∈ n.primeFactors, (3 : ℝ) ≤ p := fun p hp => by exact_mod_cast hodd p hp
  have h1 : ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 2)) ≤
      exp (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2)) := by
    rw [exp_sum]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have := hp3 p hp
      have : 0 < (p : ℝ) - 2 := by linarith
      positivity
    · have := add_one_le_exp (1 / ((p : ℝ) - 2))
      linarith
  set A := n.primeFactors.filter (fun p => p ≤ y)
  set B := n.primeFactors.filter (fun p => ¬ p ≤ y)
  have hsplit := sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ y)
    (fun p => 1 / ((p : ℝ) - 2))
  -- `1/(p - 2) ≤ 1/p + 6/p²` for `p ≥ 3`
  have hpt : ∀ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2) ≤ 1 / p + 6 * (1 / (p : ℝ) ^ 2) := by
    intro p hp
    have h3 := hp3 p hp
    have h0 : 0 < (p : ℝ) - 2 := by linarith
    rw [div_le_iff₀ h0]
    have : (1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2)) * ((p : ℝ) - 2) = 1 + 4 / p - 12 / p ^ 2 := by
      field_simp; ring
    rw [this]
    have : 12 / (p : ℝ) ^ 2 ≤ 4 / p := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hsubA : A ⊆ (Icc 1 y).filter Nat.Prime := by
    intro p hp
    simp only [A, mem_filter, Nat.mem_primeFactors] at hp
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨hp.1.1.one_lt.le, hp.2⟩, hp.1.1⟩
  have hA : ∑ p ∈ A, 1 / ((p : ℝ) - 2) ≤ log (log y) + 24 := by
    calc ∑ p ∈ A, 1 / ((p : ℝ) - 2) ≤ ∑ p ∈ A, (1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2)) :=
          sum_le_sum fun p hp => hpt p (mem_filter.1 hp).1
      _ = ∑ p ∈ A, 1 / (p : ℝ) + 6 * ∑ p ∈ A, 1 / (p : ℝ) ^ 2 := by
          rw [sum_add_distrib, mul_sum]
      _ ≤ (log (log y) + 12) + 6 * 2 := by
          gcongr
          · refine le_trans (sum_le_sum_of_subset_of_nonneg hsubA fun _ _ _ => by positivity) ?_
            exact LeanLab.PNTSieve.Mertens.sum_inv_primes_le y (by omega)
          · refine le_trans ?_ (LeanLab.PNTSieve.Mertens.sum_inv_sq_le_two y)
            refine sum_le_sum_of_subset_of_nonneg (hsubA.trans (filter_subset _ _))
              fun _ _ _ => by positivity
      _ = log (log y) + 24 := by ring
  have hB : ∑ p ∈ B, 1 / ((p : ℝ) - 2) ≤ 3 := by
    calc ∑ p ∈ B, 1 / ((p : ℝ) - 2) ≤ ∑ _p ∈ B, 3 / (y : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          simp only [B, mem_filter, not_le] at hp
          have hyp : (y : ℝ) < p := by exact_mod_cast hp.2
          have h3 := hp3 p hp.1
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          linarith
      _ = 3 * (B.card / (y : ℝ)) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 3 * 1 := by
          gcongr
          rw [div_le_one (by linarith)]
          exact_mod_cast le_trans (card_filter_le _ _) hω
      _ = 3 := by ring
  have hsum : ∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2) ≤ log (log y) + 27 := by
    rw [← hsplit]; linarith
  calc ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 2))
      ≤ exp (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2)) := h1
    _ ≤ exp (log (log y) + 27) := exp_le_exp.2 hsum
    _ = exp 27 * log y := by rw [exp_add, exp_log hly]; ring

lemma not_two_dvd_M (j : ℕ) : ¬ 2 ∣ Romanov.M j := by
  unfold Romanov.M
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  rintro ⟨e, he, h2⟩
  simp only [mem_Icc] at he
  have : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he.1
  have hev : Even (2 ^ e) := (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨m, hm⟩ := h2
  obtain ⟨r, hr⟩ := hev
  omega

lemma pf_M_ge_three (j : ℕ) : ∀ p ∈ (Romanov.M j).primeFactors, 3 ≤ p := by
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    exact not_two_dvd_M j (Nat.dvd_of_mem_primeFactors hp)
  have := hpr.two_le
  omega

theorem sumH_M_le (j : ℕ) :
    ∑ s ∈ (Romanov.M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2) ≤
      exp 27 * (2 * (j + 1) * log 2) := by
  rw [← prod_one_add]
  have hy : 4 ≤ 2 ^ (j + 1) * 2 ^ (j + 1) := by
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have h := prodH_le (Romanov.M j) _ hy (pf_M_ge_three j) (Romanov.card_pf_M_le j)
  have hlog : log ((2 ^ (j + 1) * 2 ^ (j + 1) : ℕ) : ℝ) = 2 * (j + 1) * log 2 := by
    push_cast
    rw [← pow_add, Real.log_pow]
    push_cast; ring
  rw [hlog] at h
  exact h

/-- The order facts for odd `d`, with `ξ(d)` the order of `2` in `ZMod d`. -/
lemma xi_spec_sqf {d : ℕ} (hd : OddSqf d) :
    1 ≤ xi d ∧ xi d ≤ d ∧ d ∣ 2 ^ xi d - 1 := by
  have hd0 : 0 < d := hd.1.pos
  haveI : NeZero d := ⟨hd0.ne'⟩
  refine ⟨xi_pos hd.1, ?_, ?_⟩
  · unfold xi
    calc orderOf (2 : ZMod d) ≤ Fintype.card (ZMod d) := orderOf_le_card_univ
      _ = d := ZMod.card d
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, two_pow_xi, sub_self]

lemma fd_eq {d : ℕ} (hd : OddSqf d) : fd d = ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) := by
  unfold fd
  congr 1
  refine filter_true_of_mem fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hd.1) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  have := hpr.two_le
  omega

lemma fd_nonneg {d : ℕ} (hd : OddSqf d) : 0 ≤ fd d := by
  rw [fd_eq hd]
  refine prod_nonneg fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hd.1) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  have : 3 ≤ p := by have := hpr.two_le; omega
  have : (3 : ℝ) ≤ p := by exact_mod_cast this
  have : 0 < (p : ℝ) - 2 := by linarith
  positivity

lemma romanovTerm_nonneg (d : ℕ) : 0 ≤ romanovTerm d := by
  unfold romanovTerm
  split_ifs with h
  · exact div_nonneg (fd_nonneg h) (Nat.cast_nonneg _)
  · exact le_rfl

/-- Every partial sum of the series (26) is at most `8 log 2 · e^27`. -/
theorem partial_le (D : ℕ) : ∑ d ∈ range D, romanovTerm d ≤ 8 * log 2 * exp 27 := by
  set F := (range D).filter OddSqf with hF
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have e1 : ∑ d ∈ range D, romanovTerm d = ∑ d ∈ F, fd d / xi d := by
    rw [← sum_subset (filter_subset OddSqf (range D))]
    · refine sum_congr rfl fun d hd => ?_
      unfold romanovTerm
      rw [if_pos (mem_filter.1 hd).2]
    · intro d _ hd
      unfold romanovTerm
      rw [if_neg]
      intro h
      exact hd (mem_filter.2 ⟨by assumption, h⟩)
  rw [e1]
  have hmaps : ∀ d ∈ F, Nat.log 2 (xi d) ∈ range (D + 1) := by
    intro d hd
    rw [mem_filter, mem_range] at hd
    have := (xi_spec_sqf hd.2).2.1
    have := Nat.log_le_self 2 (xi d)
    rw [mem_range]; omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  have block : ∀ j ∈ range (D + 1), ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / xi d ≤
      (2 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := by
    intro j _
    calc ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / xi d
        ≤ ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / 2 ^ j := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_filter, mem_filter] at hd
          have hs := xi_spec_sqf hd.1.2
          have hpow : 2 ^ j ≤ xi d := by rw [← hd.2]; exact Nat.pow_log_le_self 2 (by omega)
          have hpow' : (2 : ℝ) ^ j ≤ xi d := by exact_mod_cast hpow
          exact div_le_div_of_nonneg_left (fd_nonneg hd.1.2) (by positivity) hpow'
      _ = (∑ d ∈ F with Nat.log 2 (xi d) = j, fd d) / 2 ^ j := by rw [sum_div]
      _ ≤ (∑ s ∈ (Romanov.M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2)) / 2 ^ j := by
          gcongr
          calc ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d
              = ∑ d ∈ F with Nat.log 2 (xi d) = j,
                  ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) := by
                refine sum_congr rfl fun d hd => ?_
                rw [mem_filter, mem_filter] at hd
                exact fd_eq hd.1.2
            _ = ∑ s ∈ (F.filter (fun d => Nat.log 2 (xi d) = j)).image Nat.primeFactors,
                  ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
                rw [sum_image]
                intro a ha b hb hab
                have ha' : OddSqf a := (mem_filter.1 (mem_filter.1 (mem_coe.1 ha)).1).2
                have hb' : OddSqf b := (mem_filter.1 (mem_filter.1 (mem_coe.1 hb)).1).2
                rw [← Nat.prod_primeFactors_of_squarefree ha'.2,
                  ← Nat.prod_primeFactors_of_squarefree hb'.2, hab]
            _ ≤ ∑ s ∈ (Romanov.M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
                refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s hs _ => ?_
                · rw [mem_image] at hs
                  obtain ⟨d, hd, rfl⟩ := hs
                  rw [mem_filter, mem_filter] at hd
                  have hsp := xi_spec_sqf hd.1.2
                  have hlt : xi d < 2 ^ (j + 1) := by
                    rw [← hd.2]; exact Nat.lt_pow_succ_log_self (by norm_num) _
                  rw [mem_powerset]
                  exact Nat.primeFactors_mono (hsp.2.2.trans (Romanov.dvd_M hsp.1 hlt))
                    (Romanov.M_ne_zero j)
                · refine prod_nonneg fun p hp => ?_
                  have := pf_M_ge_three j p (mem_powerset.1 hs hp)
                  have : (3 : ℝ) ≤ p := by exact_mod_cast this
                  have : 0 < (p : ℝ) - 2 := by linarith
                  positivity
      _ ≤ (exp 27 * (2 * (j + 1) * log 2)) / 2 ^ j := by gcongr; exact sumH_M_le j
      _ = (2 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := by ring
  calc ∑ j ∈ range (D + 1), ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / xi d
      ≤ ∑ j ∈ range (D + 1), (2 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := sum_le_sum block
    _ = (2 * log 2 * exp 27) * ∑ j ∈ range (D + 1), (((j : ℝ) + 1) / 2 ^ j) := by rw [mul_sum]
    _ ≤ (2 * log 2 * exp 27) * 4 :=
        mul_le_mul_of_nonneg_left (Romanov.sum_succ_div_pow_le _) (by positivity)
    _ = 8 * log 2 * exp 27 := by ring

/-- **P0045 Lemma 6.1**, after Romanov: the series (26) converges. No cited input. -/
theorem lemma61_proved : Lemma61 :=
  summable_of_sum_range_le romanovTerm_nonneg partial_le

end

end LeanLab.LPZ2007.Lemma61Port

namespace LeanLab.LPZ2007

/-- The former cited declaration, now proved with its exact original statement. -/
theorem lemma61 : Lemma61 := Lemma61Port.lemma61_proved

end LeanLab.LPZ2007

