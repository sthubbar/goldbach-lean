module

public import LeanLab.PNTPort.BV.FromSW
public import LeanLab.PNTPort.BVMax.Primes
public import LeanLab.PNTPort.PsiChi.Unconditional

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 page 6, the fixed level discrepancy mean used on pages 9 to 11.
Proofs specialize the existing PNTPort BV, BVMax and PsiChi proof components.
All work stays in Tolev2009. The upstream declarations stay sealed.
-/

@[expose] public section

open Finset Real Filter ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt
namespace LeanLab.Tolev2009.QuantitativeBV346
open LeanLab.PNTPort LeanLab.PNTPort.BV LeanLab.PNTPort.BVMax
open LeanLab.HeathBrown1985 (psi)

/-- Halupczok page 6, explicit large conductor exponents from the proved BV components. -/
theorem large_conductor_fixed (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ (primSigma ⌊Real.sqrt x / Real.log x ^ (A + 5)⌋₊).filter
          (fun p => Real.log x ^ (A + 5) < p.1),
        ‖psiChi x p.2‖ / p.1.totient ≤ K * x / Real.log x ^ A := by
  obtain ⟨K₂, hK₂, hII⟩ := typeII_bound
  obtain ⟨K₃, hK₃, hlog⟩ := log_rpow_le_rpow (A + 5) (1 / 20) (by norm_num)
  refine ⟨(1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃) +
    12 / Real.log 2 ^ (A + 5), ?_⟩
  intro x hx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hs0 : 0 ≤ 12 / Real.log 2 ^ (A + 5) := by
    have := Real.rpow_pos_of_pos hl2 (A + 5); positivity
  have hm0 : 0 ≤ 1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃ := by positivity
  have hx0 : 0 ≤ x := by linarith
  rcases lt_or_ge (Real.log x) 1 with hL | hL
  · refine (small_case hA (by linarith) hx hL).trans ?_
    rw [div_le_div_iff_of_pos_right hLA]
    nlinarith
  · refine (main_case hA hK₂ hK₃ hII hlog hx hL).trans ?_
    rw [div_le_div_iff_of_pos_right hLA]
    nlinarith

set_option maxHeartbeats 1000000 in
/-- Halupczok page 6, the fixed level psi mean.
Derived from the explicitly supplied Siegel Walfisz statement. -/
theorem bv_fixed_of (hSW : LeanLab.HeathBrown1985.SiegelWalfisz) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
      (∀ q, Nat.Coprime (a q) q) →
        ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ (A + 6)⌋₊,
          |psi x q (a q) - x / q.totient| ≤ K * x / Real.log x ^ A := by
  let C₁ := A + 6
  let B := A + 6
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨K₁, hLC₁⟩ := large_conductor_fixed (A + 1) (by linarith)
  have hLC' : ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ (primSigma ⌊Real.sqrt x / Real.log x ^ B⌋₊).filter
          (fun p => Real.log x ^ C₁ < p.1),
        ‖psiChi x p.2‖ / p.1.totient ≤ K₁ * x / Real.log x ^ (A + 1) := by
    simpa only [C₁, B, add_assoc, show (1 : ℝ) + 5 = 6 by norm_num] using hLC₁
  set C := max C₁ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  obtain ⟨c₂, hc₂, K₂, hSW'⟩ := hSW C (by linarith)
  obtain ⟨c₀, hc₀, K₀, hP⟩ := LeanLab.PNTPort.psi_explicit_strong
  obtain ⟨Kp, hKp, hKpb⟩ := log_rpow_le_sqrt (A + 2)
  obtain ⟨Ke0, hKe0, hKe0b⟩ := exp_neg_sqrt_log_le c₀ hc₀ (A + 1)
  obtain ⟨Ke2, hKe2, hKe2b⟩ := exp_neg_sqrt_log_le c₂ hc₂ (A + 1 + 2 * C)
  obtain ⟨C4, hC4, hC4b⟩ := sum_inv_totient_le
  set K₀' := max K₀ 0 with hK₀'
  set K₁' := max K₁ 0 with hK₁'
  set K₂' := max K₂ 0 with hK₂'
  have hK₀0 : 0 ≤ K₀' := le_max_right _ _
  have hK₁0 : 0 ≤ K₁' := le_max_right _ _
  have hK₂0 : 0 ≤ K₂' := le_max_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Ks := 8 * 2 ^ A / Real.log 2 ^ B with hKsdef
  set Kb := Kp / Real.log 2 + 2 * C4 * K₀' * Ke0 + 2 * C4 * (K₁' + K₂' * Ke2) with hKbdef
  have hKs : 0 ≤ Ks := by positivity
  have hKb : 0 ≤ Kb := by positivity
  refine ⟨Ks + Kb, fun x hx a ha => ?_⟩
  set L := Real.log x with hLdef
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  set M := x / L ^ A with hMdef
  have hM : 0 ≤ M := by positivity
  rw [mul_div_assoc]
  set Q := ⌊Real.sqrt x / L ^ B⌋₊ with hQdef
  rcases lt_or_ge x 3 with hx3 | hx3
  ·
    have hterm : ∀ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient| ≤ 4 * x := by
      intro q hq
      rw [mem_Icc] at hq
      have hp0 : 0 ≤ HeathBrown1985.psi x q (a q) :=
        sum_nonneg fun _ _ => vonMangoldt_nonneg
      have hp1 : HeathBrown1985.psi x q (a q) ≤ 3 * x := by
        unfold HeathBrown1985.psi
        calc _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                (fun _ _ _ => vonMangoldt_nonneg)
          _ ≤ ∑ _n ∈ Icc 1 ⌊x⌋₊, x := by
              apply sum_le_sum
              intro n hn
              rw [mem_Icc] at hn
              have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn.2).trans (Nat.floor_le hx0.le)
              have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
              calc vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
                _ ≤ Real.log x := Real.log_le_log (by linarith) hnx
                _ ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
          _ = ⌊x⌋₊ * x := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
          _ ≤ x * x := by gcongr; exact Nat.floor_le hx0.le
          _ ≤ 3 * x := by nlinarith
      have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hd0 : 0 ≤ x / q.totient := by positivity
      have hd1 : x / q.totient ≤ x := div_le_self hx0.le hφ
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hsum : ∑ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient| ≤
        Q * (4 * x) := by
      refine (sum_le_sum hterm).trans (le_of_eq ?_)
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    have hsx : Real.sqrt x ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    have hLB : Real.log 2 ^ B ≤ L ^ B :=
      Real.rpow_le_rpow hl2.le (Real.log_le_log (by norm_num) hx) hB.le
    have hl2B : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hl2 B
    have hQ : (Q : ℝ) ≤ 2 / Real.log 2 ^ B := by
      refine (Nat.floor_le (by positivity)).trans ?_
      exact div_le_div₀ (by norm_num) hsx hl2B hLB
    have hL2 : L ≤ 2 := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
    have hLA2 : L ^ A ≤ 2 ^ A := Real.rpow_le_rpow hL0.le hL2 hA.le
    have hxM : x ≤ 2 ^ A * M := by
      rw [hMdef, mul_div_assoc', le_div_iff₀ hLA]
      rw [mul_comm (2 ^ A) x]; exact mul_le_mul_of_nonneg_left hLA2 hx0.le
    calc _ ≤ Q * (4 * x) := hsum
      _ ≤ 2 / Real.log 2 ^ B * (4 * x) := by gcongr
      _ ≤ 2 / Real.log 2 ^ B * (4 * (2 ^ A * M)) := by gcongr
      _ = Ks * M := by rw [hKsdef]; ring
      _ ≤ (Ks + Kb) * M := by nlinarith
  ·
    have hL1 : 1 ≤ L := by
      have h3 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      exact h3.le.trans (Real.log_le_log (by norm_num) hx3)
    have hLB : 1 ≤ L ^ B := Real.one_le_rpow hL1 hB.le
    have hsqx : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_left hx0.le]
      nlinarith
    have hQs : (Q : ℝ) ≤ Real.sqrt x :=
      (Nat.floor_le (by positivity)).trans (div_le_self (Real.sqrt_nonneg _) hLB)
    have hQx : (Q : ℝ) ≤ x := hQs.trans hsqx
    have hlogQ : 1 + Real.log Q ≤ 2 * L := by
      rcases Nat.eq_zero_or_pos Q with h0 | h0
      · rw [h0]; simp; linarith
      · have := Real.log_le_log (by exact_mod_cast h0) hQx
        linarith
    have hH : ∑ m ∈ Icc 1 Q, (1 : ℝ) / m.totient ≤ 2 * C4 * L := by
      refine (hC4b Q).trans ?_
      nlinarith
    set S : ℕ → ℝ := fun q => if hq : q = 0 then 0 else
      haveI : NeZero q := ⟨hq⟩
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChi x χ.primitiveCharacter‖ with hSdef
    have hstep : ∀ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient| ≤
        psiBad x q + |Chebyshev.psi x - x| * (1 / q.totient) + 1 / q.totient * S q := by
      intro q hq
      rw [mem_Icc] at hq
      have hq0 : q ≠ 0 := by omega
      have : NeZero q := ⟨hq0⟩
      have := term_le (q := q) x (ha q)
      simp only [hSdef, hq0, dite_false]
      rw [mul_one_div, one_div_mul_eq_div]
      exact this
    have hT1 : ∑ q ∈ Icc 1 Q, psiBad x q ≤ Kp / Real.log 2 * M := by
      have h1 : ∀ q ∈ Icc 1 Q, psiBad x q ≤ L / Real.log 2 * L := by
        intro q hq
        rw [mem_Icc] at hq
        refine (psiBad_le (by linarith) hq.1).trans ?_
        have hqx : (q : ℝ) ≤ x := (Nat.cast_le.2 hq.2).trans hQx
        have : Real.log q ≤ L := Real.log_le_log (by exact_mod_cast hq.1) hqx
        gcongr
      refine (sum_le_sum h1).trans ?_
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      have hK := hKpb x hx
      rw [Real.rpow_add hL0, Real.rpow_two] at hK
      have hsq := Real.mul_self_sqrt hx0.le
      have e : (Q : ℝ) * (L / Real.log 2 * L) ≤ Real.sqrt x * L ^ 2 / Real.log 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc', ← sq]
        apply div_le_div_of_nonneg_right _ hl2.le
        exact mul_le_mul_of_nonneg_right hQs (sq_nonneg L)
      refine e.trans ?_
      rw [hMdef, div_mul_div_comm, mul_comm (Real.log 2) (L ^ A)]
      rw [div_le_div_iff₀ hl2 (by positivity)]
      have : Real.sqrt x * (L ^ A * L ^ 2) ≤ Real.sqrt x * (Kp * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg _)
      have h3 : Real.sqrt x * (Kp * Real.sqrt x) = Kp * x := by rw [mul_left_comm, hsq]
      have h4 : Real.sqrt x * (L ^ A * L ^ 2) ≤ Kp * x := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h4 hl2.le]
    have hLA1 : L ^ (A + 1) = L ^ A * L := by rw [Real.rpow_add hL0, Real.rpow_one]
    have hT2 : ∑ q ∈ Icc 1 Q, |Chebyshev.psi x - x| * (1 / q.totient) ≤
        2 * C4 * K₀' * Ke0 * M := by
      rw [← mul_sum]
      have he0 := hKe0b x hx
      rw [← hLdef, hLA1] at he0
      have hPx : |Chebyshev.psi x - x| ≤ K₀' * x * (Ke0 / (L ^ A * L)) := by
        refine (hP x hx).trans ?_
        rw [← hLdef]
        have hex : 0 ≤ Real.exp (-c₀ * Real.sqrt L) := (Real.exp_pos _).le
        calc K₀ * x * Real.exp (-c₀ * Real.sqrt L) ≤ K₀' * x * Real.exp (-c₀ * Real.sqrt L) := by
              gcongr; exact le_max_left _ _
          _ ≤ K₀' * x * (Ke0 / (L ^ A * L)) := by gcongr
      calc |Chebyshev.psi x - x| * ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient
          ≤ K₀' * x * (Ke0 / (L ^ A * L)) * (2 * C4 * L) :=
            mul_le_mul hPx hH (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = 2 * C4 * K₀' * Ke0 * M := by rw [hMdef]; field_simp
    set F : (Σ d : ℕ, DirichletCharacter ℂ d) → ℝ := fun p => ‖psiChi x p.2‖ with hFdef
    have hF : ∀ p, 0 ≤ F p := fun p => norm_nonneg _
    set P := primSigma Q with hPdef
    have hstepa : ∀ q ∈ Icc 1 Q, 1 / (q.totient : ℝ) * S q ≤
        1 / (q.totient : ℝ) * ∑ p ∈ P.filter (fun p => 2 ≤ p.1 ∧ p.1 ∣ q), F p := by
      intro q hq
      rw [mem_Icc] at hq
      have hq0 : q ≠ 0 := by omega
      have : NeZero q := ⟨hq0⟩
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [hSdef, hq0, dite_false]
      exact sum_erase_le_primSigma hq.2 F hF
    have hstepc : ∀ p ∈ P.filter (fun p => 2 ≤ p.1),
        F p * ∑ q ∈ (Icc 1 Q).filter (fun q => p.1 ∣ q), (1 : ℝ) / q.totient ≤
          2 * C4 * L * (F p / p.1.totient) := by
      intro p hp
      rw [mem_filter] at hp
      have h := sum_dvd_inv_totient_le (d := p.1) (by omega) Q
      calc F p * ∑ q ∈ (Icc 1 Q).filter (fun q => p.1 ∣ q), (1 : ℝ) / q.totient
          ≤ F p * ((1 / p.1.totient) * (2 * C4 * L)) := by
            apply mul_le_mul_of_nonneg_left _ (hF p)
            exact h.trans (mul_le_mul_of_nonneg_left hH (by positivity))
        _ = 2 * C4 * L * (F p / p.1.totient) := by ring
    have hlarge : ∑ p ∈ (P.filter (fun p => 2 ≤ p.1)).filter
        (fun p => ¬ (p.1 : ℝ) ≤ L ^ C), F p / p.1.totient ≤ K₁' * M / L := by
      have hsub : (P.filter (fun p => 2 ≤ p.1)).filter (fun p => ¬ (p.1 : ℝ) ≤ L ^ C) ⊆
          P.filter (fun p => L ^ C₁ < p.1) := by
        intro p hp
        simp only [mem_filter, not_le] at hp ⊢
        refine ⟨hp.1.1, lt_of_le_of_lt ?_ hp.2⟩
        exact Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
      refine (sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => div_nonneg (hF p) (Nat.cast_nonneg _))).trans ?_
      refine (hLC' x hx).trans ?_
      rw [← hLdef, hLA1, hMdef]
      have : K₁ * x ≤ K₁' * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
      calc K₁ * x / (L ^ A * L) ≤ K₁' * x / (L ^ A * L) :=
            div_le_div_of_nonneg_right this (by positivity)
        _ = K₁' * (x / L ^ A) / L := by field_simp
    have hLC0 : 0 < L ^ C := Real.rpow_pos_of_pos hL0 C
    set E2 := K₂' * x * Real.exp (-c₂ * Real.sqrt L) with hE2
    have hsmall1 : ∀ p ∈ (P.filter (fun p => 2 ≤ p.1)).filter (fun p => (p.1 : ℝ) ≤ L ^ C),
        F p / p.1.totient ≤ E2 := by
      rintro ⟨d, χ⟩ hp
      simp only [hPdef, primSigma, mem_filter, mem_sigma, mem_Icc, mem_univ, true_and] at hp
      obtain ⟨⟨⟨⟨hd1, _⟩, hprim⟩, hd2⟩, hdL⟩ := hp
      have : NeZero d := ⟨by omega⟩
      have hχ : χ ≠ 1 := ne_one_of_isPrimitive hd2 hprim
      have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hb := norm_psiChi_le x χ hχ (E := E2) (fun b hb => by
        refine (hSW' x hx d b hd1 hb hdL).trans ?_
        rw [hE2, ← hLdef]
        have hex : 0 ≤ Real.exp (-c₂ * Real.sqrt L) := (Real.exp_pos _).le
        gcongr
        exact le_max_left _ _)
      show ‖psiChi x χ‖ / d.totient ≤ E2
      rw [div_le_iff₀ hφ, mul_comm]
      exact hb
    have hcard : ((((P.filter (fun p => 2 ≤ p.1)).filter
        (fun p => (p.1 : ℝ) ≤ L ^ C)).card : ℕ) : ℝ) ≤ (L ^ C) ^ 2 := by
      refine le_trans ?_ (card_primSigma_le Q hLC0.le)
      exact_mod_cast card_le_card (fun p hp => by
        simp only [mem_filter] at hp ⊢
        exact ⟨hp.1.1, hp.2⟩)
    have hE20 : 0 ≤ E2 := by rw [hE2]; have := (Real.exp_pos (-c₂ * Real.sqrt L)).le; positivity
    have hsmall : ∑ p ∈ (P.filter (fun p => 2 ≤ p.1)).filter
        (fun p => (p.1 : ℝ) ≤ L ^ C), F p / p.1.totient ≤ K₂' * Ke2 * M / L := by
      refine (sum_le_card_nsmul _ _ _ hsmall1).trans ?_
      rw [nsmul_eq_mul]
      have he2 := hKe2b x hx
      rw [← hLdef] at he2
      have hpow : L ^ (A + 1 + 2 * C) = L ^ A * L * (L ^ C) ^ 2 := by
        rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one, mul_comm 2 C,
          Real.rpow_mul hL0.le, Real.rpow_two]
      rw [hpow] at he2
      calc _ ≤ (L ^ C) ^ 2 * E2 := mul_le_mul_of_nonneg_right hcard hE20
        _ ≤ (L ^ C) ^ 2 * (K₂' * x * (Ke2 / (L ^ A * L * (L ^ C) ^ 2))) := by
            rw [hE2]; gcongr
        _ = K₂' * Ke2 * M / L := by rw [hMdef]; field_simp
    have hT3 : ∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ) * S q ≤
        2 * C4 * (K₁' + K₂' * Ke2) * M := by
      refine (sum_le_sum hstepa).trans ?_
      rw [sum_swap_filter (Icc 1 Q) P (fun p => 2 ≤ p.1) (fun p q => p.1 ∣ q)
        (fun q => 1 / (q.totient : ℝ)) F]
      refine (sum_le_sum hstepc).trans ?_
      rw [← mul_sum, ← sum_filter_add_sum_filter_not _ (fun p => (p.1 : ℝ) ≤ L ^ C)]
      calc 2 * C4 * L * (_ + _) ≤ 2 * C4 * L * (K₂' * Ke2 * M / L + K₁' * M / L) :=
            mul_le_mul_of_nonneg_left (add_le_add hsmall hlarge) (by positivity)
        _ = 2 * C4 * (K₁' + K₂' * Ke2) * M := by field_simp; ring
    calc ∑ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient|
        ≤ ∑ q ∈ Icc 1 Q, (psiBad x q + |Chebyshev.psi x - x| * (1 / q.totient) +
            1 / q.totient * S q) := sum_le_sum hstep
      _ = ∑ q ∈ Icc 1 Q, psiBad x q + ∑ q ∈ Icc 1 Q, |Chebyshev.psi x - x| * (1 / q.totient) +
            ∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ) * S q := by
          rw [sum_add_distrib, sum_add_distrib]
      _ ≤ Kp / Real.log 2 * M + 2 * C4 * K₀' * Ke0 * M + 2 * C4 * (K₁' + K₂' * Ke2) * M := by
          linarith
      _ = Kb * M := by rw [hKbdef]; ring
      _ ≤ (Ks + Kb) * M := by nlinarith

set_option maxHeartbeats 1000000 in
/-- Halupczok page 6, explicit grid level before absorbing the bounded x range.
Derived from the explicitly supplied Siegel Walfisz statement. -/
theorem bvMax_fixed_eventually_of (hSW : LeanLab.HeathBrown1985.SiegelWalfisz)
    (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → 2 ≤ Real.log x →
      Real.log x ^ (A + 4) ≤ Real.sqrt x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
        ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ (3 * A + 14)⌋₊,
          |psi (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A := by
  rw [show 3 * A + 14 = (2 * A + 4 + 6) + A + 4 by ring]
  let B1 := 2 * A + 4 + 6
  have hB1 : 0 < B1 := by dsimp [B1]; linarith
  obtain ⟨K1, hK1⟩ := bv_fixed_of hSW (2 * A + 4) (by linarith)
  obtain ⟨C, hC, hCsum⟩ := BV.sum_inv_totient_le
  have hK1nn : 0 ≤ K1 := by
    have h := hK1 2 le_rfl (fun _ => 1) (fun q => Nat.coprime_one_left q)
    have hs : 0 ≤ ∑ q ∈ Icc 1 ⌊Real.sqrt 2 / Real.log 2 ^ B1⌋₊,
        |psi 2 q 1 - 2 / q.totient| := sum_nonneg (fun _ _ => abs_nonneg _)
    have hl : 0 < Real.log 2 ^ (2 * A + 4) := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
    by_contra hneg
    push Not at hneg
    have : K1 * 2 / Real.log 2 ^ (2 * A + 4) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hl
    linarith
  refine ⟨K1 * 2 ^ (2 * A + 4) + 4 * C + 2, ?_⟩
  intro x hx hL hLx a ha y hy
  set L := Real.log x with hLdef
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hLA0 : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  have hLA3 : 1 ≤ L ^ (A + 3) := Real.one_le_rpow hL1 (by linarith)
  have hLA4 : L ^ (A + 4) = L ^ (A + 3) * L := by
    rw [show A + 4 = (A + 3) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
  set M : ℕ := ⌈L ^ (A + 3)⌉₊ with hMdef
  have hM1 : L ^ (A + 3) ≤ M := Nat.le_ceil _
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : (1 : ℝ) ≤ M := by linarith
  have hM2 : (M : ℝ) ≤ L ^ (A + 4) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ L ^ (A + 3) by linarith)
    rw [hLA4]; nlinarith
  set g : ℕ → ℝ := fun j => j * x / M with hg
  set J : ℕ → ℕ := fun q => ⌊y q * M / x⌋₊ with hJ
  have hJle : ∀ q, g (J q) ≤ y q := by
    intro q
    have h := Nat.floor_le (show 0 ≤ y q * M / x by
      have := (hy q).1; positivity)
    simp only [hg, hJ]
    rw [div_le_iff₀ hMpos]
    rw [le_div_iff₀ hx0] at h
    linarith
  have hJgap : ∀ q, y q - g (J q) ≤ x / M := by
    intro q
    have h := Nat.lt_floor_add_one (y q * M / x)
    simp only [hg, hJ]
    rw [div_lt_iff₀ hx0] at h
    have : y q * M ≤ (⌊y q * M / x⌋₊ : ℝ) * x + x := by linarith
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hMpos]
    linarith
  have hJM : ∀ q, J q ≤ M := by
    intro q
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hx0]
    have := (hy q).2
    nlinarith
  set Q : ℕ := ⌊Real.sqrt x / L ^ (B1 + A + 4)⌋₊ with hQdef
  have hLB : 1 ≤ L ^ (B1 + A + 4) := Real.one_le_rpow hL1 (by linarith)
  have hQx : (Q : ℝ) ≤ Real.sqrt x := by
    have h := Nat.floor_le (show 0 ≤ Real.sqrt x / L ^ (B1 + A + 4) by positivity)
    exact h.trans (div_le_self hsx0.le hLB)
  have hsxL : L ^ (A + 1) ≤ Real.sqrt x :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)).trans hLx
  have hstep : ∀ q ∈ Icc 1 Q, |psi (y q) q (a q) - y q / q.totient| ≤
      (∑ j ∈ Icc 1 M, |err (g j) q (a q)|) + (x / M * (L + 1)) * (1 / q.totient) + 2 * L := by
    intro q hq
    rw [mem_Icc] at hq
    have hq0 : 0 < q := by omega
    have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hg0 : 0 ≤ g (J q) := by simp only [hg]; positivity
    have hd := err_sub_le q (a q) hq0 hg0 (hJle q) (hy q).2 (by linarith)
    have hgap := hJgap q
    have hgap0 : 0 ≤ y q - g (J q) := by linarith [hJle q]
    have hxM : 0 ≤ x / M := by positivity
    have h1 : (y q - g (J q)) / q ≤ x / M * (1 / q.totient) := by
      rw [mul_one_div]
      calc (y q - g (J q)) / q ≤ (y q - g (J q)) / q.totient :=
            div_le_div_of_nonneg_left hgap0 (by linarith) hφq
        _ ≤ x / M / q.totient := div_le_div_of_nonneg_right hgap (by linarith)
    have h2 : (y q - g (J q)) / q.totient ≤ x / M * (1 / q.totient) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hgap (by linarith)
    have hgrid : |err (g (J q)) q (a q)| ≤ ∑ j ∈ Icc 1 M, |err (g j) q (a q)| := by
      rcases Nat.eq_zero_or_pos (J q) with h0 | hpos
      · have : g (J q) = 0 := by simp only [hg, h0]; simp
        rw [this, err_zero, abs_zero]
        exact sum_nonneg (fun _ _ => abs_nonneg _)
      · exact single_le_sum (f := fun j => |err (g j) q (a q)|)
          (fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨hpos, hJM q⟩)
    have htri : |err (y q) q (a q)| ≤ |err (g (J q)) q (a q)| +
        |err (y q) q (a q) - err (g (J q)) q (a q)| := by
      have := abs_add_le (err (g (J q)) q (a q)) (err (y q) q (a q) - err (g (J q)) q (a q))
      simpa using this
    have hX : 0 ≤ x / M * (1 / q.totient) := by positivity
    show |err (y q) q (a q)| ≤ _
    nlinarith
  have hgrid_bound : ∀ j ∈ Icc 1 M, ∑ q ∈ Icc 1 Q, |err (g j) q (a q)| ≤
      K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4) := by
    intro j hj
    rw [mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hjM : (j : ℝ) ≤ M := by exact_mod_cast hj.2
    have hgx : g j ≤ x := by
      simp only [hg]; rw [div_le_iff₀ hMpos]; nlinarith
    have hgxM : x / M ≤ g j := by
      simp only [hg]; rw [mul_div_assoc]; nlinarith [show 0 ≤ x / M by positivity]
    have hxMs : Real.sqrt x ≤ x / M := by
      rw [le_div_iff₀ hMpos]
      calc Real.sqrt x * M ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_left (hM2.trans hLx) hsx0.le
        _ = x := Real.mul_self_sqrt hx0.le
    have hgs : Real.sqrt x ≤ g j := hxMs.trans hgxM
    have hs2 : 2 ≤ Real.sqrt x := by
      have : L ≤ L ^ (A + 4) := by
        conv_lhs => rw [← Real.rpow_one L]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      linarith
    have hg2 : 2 ≤ g j := by linarith
    have hg0 : 0 < g j := by linarith
    have hlogg : L / 2 ≤ Real.log (g j) := by
      have := Real.log_le_log hsx0 hgs
      rwa [Real.log_sqrt hx0.le] at this
    have hloggx : Real.log (g j) ≤ L := Real.log_le_log hg0 hgx
    have hsub : Icc 1 Q ⊆ Icc 1 ⌊Real.sqrt (g j) / Real.log (g j) ^ B1⌋₊ := by
      apply Icc_subset_Icc_right
      apply Nat.floor_le_floor
      have hlg0 : 0 < Real.log (g j) := by linarith
      have hp1 : Real.log (g j) ^ B1 ≤ L ^ B1 := Real.rpow_le_rpow hlg0.le hloggx hB1.le
      have hp0 : 0 < Real.log (g j) ^ B1 := Real.rpow_pos_of_pos hlg0 B1
      have hsM : Real.sqrt (M : ℝ) ≤ M := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      have hsg : Real.sqrt x / L ^ (A + 4) ≤ Real.sqrt (g j) := by
        have h1 : Real.sqrt (x / M) ≤ Real.sqrt (g j) := Real.sqrt_le_sqrt hgxM
        rw [Real.sqrt_div' x (Nat.cast_nonneg M)] at h1
        refine le_trans ?_ h1
        apply div_le_div_of_nonneg_left hsx0.le (Real.sqrt_pos.mpr hMpos)
        exact hsM.trans hM2
      have hsplit : L ^ (B1 + A + 4) = L ^ (A + 4) * L ^ B1 := by
        rw [show B1 + A + 4 = (A + 4) + B1 by ring, Real.rpow_add hL0]
      rw [hsplit, ← div_div]
      calc Real.sqrt x / L ^ (A + 4) / L ^ B1
          ≤ Real.sqrt (g j) / L ^ B1 := div_le_div_of_nonneg_right hsg (by positivity)
        _ ≤ Real.sqrt (g j) / Real.log (g j) ^ B1 :=
            div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hp0 hp1
    have hmain := hK1 (g j) hg2 a ha
    have hle : ∑ q ∈ Icc 1 Q, |err (g j) q (a q)| ≤
        ∑ q ∈ Icc 1 ⌊Real.sqrt (g j) / Real.log (g j) ^ B1⌋₊,
          |psi (g j) q (a q) - g j / q.totient| :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    refine hle.trans (hmain.trans ?_)
    have hl2 : (L / 2) ^ (2 * A + 4) ≤ Real.log (g j) ^ (2 * A + 4) :=
      Real.rpow_le_rpow (by linarith) hlogg (by linarith)
    have hl2' : (L / 2) ^ (2 * A + 4) = L ^ (2 * A + 4) / 2 ^ (2 * A + 4) :=
      Real.div_rpow hL0.le (by norm_num) _
    have hpos2 : 0 < (L / 2) ^ (2 * A + 4) := Real.rpow_pos_of_pos (by linarith) _
    have h2p : 0 < (2 : ℝ) ^ (2 * A + 4) := Real.rpow_pos_of_pos (by norm_num) _
    have hLp : 0 < L ^ (2 * A + 4) := Real.rpow_pos_of_pos hL0 _
    calc K1 * g j / Real.log (g j) ^ (2 * A + 4) ≤ K1 * x / (L / 2) ^ (2 * A + 4) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hgx hK1nn) hpos2 hl2
      _ = K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4) := by
          rw [hl2']; field_simp
  have hsum1 : ∑ q ∈ Icc 1 Q, |psi (y q) q (a q) - y q / q.totient| ≤
      (∑ j ∈ Icc 1 M, ∑ q ∈ Icc 1 Q, |err (g j) q (a q)|) +
      (x / M * (L + 1)) * (∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient) + 2 * L * Q := by
    refine (sum_le_sum hstep).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_add_distrib, sum_comm, ← mul_sum, sum_const, Nat.card_Icc,
      nsmul_eq_mul]
    simp only [add_tsub_cancel_right]
    ring
  have hA1 : ∑ j ∈ Icc 1 M, ∑ q ∈ Icc 1 Q, |err (g j) q (a q)| ≤ K1 * 2 ^ (2 * A + 4) * x / L ^ A := by
    refine (sum_le_sum hgrid_bound).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, add_tsub_cancel_right]
    have hsplit : L ^ (2 * A + 4) = L ^ (A + 4) * L ^ A := by
      rw [show 2 * A + 4 = (A + 4) + A by ring, Real.rpow_add hL0]
    have hLA4p : 0 < L ^ (A + 4) := Real.rpow_pos_of_pos hL0 _
    have hX : 0 ≤ K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4) := by positivity
    calc (M : ℝ) * (K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4))
        ≤ L ^ (A + 4) * (K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4)) :=
          mul_le_mul_of_nonneg_right hM2 hX
      _ = K1 * 2 ^ (2 * A + 4) * x / L ^ A := by
          rw [hsplit]; field_simp
  have hA2 : (x / M * (L + 1)) * (∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient) ≤ 4 * C * x / L ^ A := by
    have hc := hCsum Q
    have hlogQ : Real.log Q ≤ L := by
      rcases Nat.eq_zero_or_pos Q with h0 | hpos
      · rw [h0]; simp; linarith
      · have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hpos
        have := Real.log_le_log hQ0 (hQx.trans (sqrt_le_self' ?_))
        · exact this
        · nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hx0.le]
    have hxM0 : 0 ≤ x / M * (L + 1) := by positivity
    have hstep1 : (x / M * (L + 1)) * (∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient) ≤
        (x / M * (L + 1)) * (C * (1 + L)) :=
      mul_le_mul_of_nonneg_left (hc.trans (by nlinarith)) hxM0
    refine hstep1.trans ?_
    have hLA3' : L ^ (A + 3) = L ^ A * L ^ 3 := by
      rw [Real.rpow_add hL0]; norm_cast
    have hxM : x / M ≤ x / (L ^ A * L ^ 3) := by
      rw [← hLA3']; exact div_le_div_of_nonneg_left hx0.le (by linarith) hM1
    calc x / M * (L + 1) * (C * (1 + L)) ≤ x / (L ^ A * L ^ 3) * (L + 1) * (C * (1 + L)) := by
          have : 0 ≤ (L + 1) * (C * (1 + L)) := by positivity
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hxM this
      _ ≤ x / (L ^ A * L ^ 3) * (4 * C * L ^ 2) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have e : (L + 1) * (C * (1 + L)) = C * (L + 1) ^ 2 := by ring
          have h4 : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
          rw [e]
          calc C * (L + 1) ^ 2 ≤ C * (4 * L ^ 2) := mul_le_mul_of_nonneg_left h4 hC.le
            _ = 4 * C * L ^ 2 := by ring
      _ = 4 * C * x / L ^ A * (1 / L) := by field_simp
      _ ≤ 4 * C * x / L ^ A := by
          have : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL1
          have : 0 ≤ 4 * C * x / L ^ A := by positivity
          nlinarith
  have hA3 : 2 * L * Q ≤ 2 * x / L ^ A := by
    have hLA1 : L ^ (A + 1) = L ^ A * L := by rw [Real.rpow_add hL0, Real.rpow_one]
    rw [le_div_iff₀ hLA0]
    have h1 : L * Q * L ^ A ≤ L ^ (A + 1) * Real.sqrt x := by
      rw [hLA1]
      have := mul_le_mul_of_nonneg_left hQx (show 0 ≤ L * L ^ A by positivity)
      nlinarith
    have h2 : L ^ (A + 1) * Real.sqrt x ≤ x := by
      calc L ^ (A + 1) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hsxL hsx0.le
        _ = x := Real.mul_self_sqrt hx0.le
    nlinarith
  calc ∑ q ∈ Icc 1 Q, |psi (y q) q (a q) - y q / q.totient|
      ≤ _ := hsum1
    _ ≤ K1 * 2 ^ (2 * A + 4) * x / L ^ A + 4 * C * x / L ^ A + 2 * x / L ^ A := by
        linarith
    _ = (K1 * 2 ^ (2 * A + 4) + 4 * C + 2) * x / L ^ A := by ring

set_option maxHeartbeats 1000000 in
/-- Halupczok page 6, the classical psi maximum with level exponent three A plus fourteen.
Derived from the explicitly supplied Siegel Walfisz statement. -/
theorem bvMax_fixed_of (hSW : LeanLab.HeathBrown1985.SiegelWalfisz) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
      (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ,
      (∀ q, 0 ≤ y q ∧ y q ≤ x) →
        ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ (3 * A + 14)⌋₊,
          |psi (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A := by
  let B := 3 * A + 14
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨K, hK⟩ := bvMax_fixed_eventually_of hSW A hA
  have h1 : ∀ᶠ x in atTop, 2 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 2
  have h2 : ∀ᶠ x in atTop, Real.log x ^ (A + 4) ≤ Real.sqrt x := by
    have ho := (isLittleO_log_rpow_rpow_atTop (A + 4) (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      zero_lt_one
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at hx
    rw [Real.sqrt_eq_rpow]
    exact (le_abs_self _).trans (hx.trans (le_of_eq (abs_of_nonneg (by positivity))))
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (h1.and h2)
  set X1 := max X0 2 with hX1
  have hX12 : 2 ≤ X1 := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set T := ((X1 + 2) * Real.log X1 + X1) * Real.log X1 ^ A / Real.log 2 ^ B with hT
  refine ⟨max K T, ?_⟩
  intro x hx a ha y hy
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hxL : 0 ≤ x / Real.log x ^ A := by positivity
  by_cases hxX : X0 ≤ x
  · refine (hK x hx (hX0 x hxX).1 (hX0 x hxX).2 a ha y hy).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxL
  · push Not at hxX
    have hxX1 : x ≤ X1 := (hxX.le).trans (le_max_left _ _)
    set L := Real.log x with hLdef
    have hLX : L ≤ Real.log X1 := Real.log_le_log hx0 hxX1
    have hlog2L : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
    have hterm : ∀ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊,
        |psi (y q) q (a q) - y q / q.totient| ≤ (x + 2) * L + x := by
      intro q hq
      rw [mem_Icc] at hq
      have hq0 : 0 < q := by omega
      have hd := err_sub_le q (a q) hq0 le_rfl (hy q).1 (hy q).2 (by linarith)
      rw [err_zero, sub_zero, sub_zero] at hd
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
      have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have hy0 := (hy q).1
      have hyx := (hy q).2
      have e1 : y q / q ≤ x := (div_le_self hy0 hq1).trans hyx
      have e2 : y q / q.totient ≤ x := (div_le_self hy0 hφ1).trans hyx
      show |err (y q) q (a q)| ≤ _
      nlinarith
    have hsum := sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul, Nat.card_Icc, add_tsub_cancel_right] at hsum
    have hLB : Real.log 2 ^ B ≤ L ^ B := Real.rpow_le_rpow hlog2.le hlog2L hB.le
    have hl2B : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hlog2 B
    have hQ : (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) ≤ x / Real.log 2 ^ B := by
      refine (Nat.floor_le (by positivity)).trans ?_
      calc Real.sqrt x / L ^ B ≤ x / L ^ B :=
            div_le_div_of_nonneg_right (sqrt_le_self' (by nlinarith)) (by positivity)
        _ ≤ x / Real.log 2 ^ B := div_le_div_of_nonneg_left hx0.le hl2B hLB
    have hW : 0 ≤ (x + 2) * L + x := by positivity
    have hLAX : L ^ A ≤ Real.log X1 ^ A := Real.rpow_le_rpow hL0.le hLX hA.le
    have hWX : (x + 2) * L + x ≤ (X1 + 2) * Real.log X1 + X1 := by
      have : (x + 2) * L ≤ (X1 + 2) * Real.log X1 :=
        mul_le_mul (by linarith) hLX hL0.le (by linarith)
      linarith
    calc _ ≤ _ := hsum
      _ ≤ x / Real.log 2 ^ B * ((x + 2) * L + x) := mul_le_mul_of_nonneg_right hQ hW
      _ ≤ T * x / L ^ A := by
          rw [hT, le_div_iff₀ hLA0]
          have hlX : 0 ≤ Real.log X1 := Real.log_nonneg (by linarith)
          have : x / Real.log 2 ^ B * ((x + 2) * L + x) * L ^ A ≤
              x / Real.log 2 ^ B * (((X1 + 2) * Real.log X1 + X1) * Real.log X1 ^ A) := by
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hWX hLAX hLA0.le (by positivity)
          calc _ ≤ _ := this
            _ = _ := by field_simp
      _ ≤ max K T * x / L ^ A := by
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxL

set_option maxHeartbeats 1000000 in
/-- Halupczok page 6, the theta maximum with the explicit level exponent four A plus fifteen.
Derived from the explicitly supplied Siegel Walfisz statement. -/
theorem theta_fixed_of (hSW : LeanLab.HeathBrown1985.SiegelWalfisz) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
      (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ,
      (∀ q, 0 ≤ y q ∧ y q ≤ x) →
        ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ (4 * A + 15)⌋₊,
          |thetaAP (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A := by
  rw [show 4 * A + 15 = (3 * A + 14) + A + 1 by ring]
  let B0 := 3 * A + 14
  have hB0 : 0 < B0 := by dsimp [B0]; linarith
  obtain ⟨K0, hK0⟩ := bvMax_fixed_of hSW A hA
  set B := B0 + A + 1 with hBdef
  have hB : 0 < B := by linarith
  obtain ⟨T, hT⟩ := small_x_bound A B (Real.exp 1) hA hB
    (by have := Real.add_one_le_exp (1 : ℝ); linarith)
  refine ⟨max (K0 + 2) T, ?_⟩
  intro x hx a ha y hy
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hxL : 0 ≤ x / Real.log x ^ A := by positivity
  by_cases hxe : Real.exp 1 ≤ x
  · set L := Real.log x with hLdef
    have hL1 : 1 ≤ L := by
      rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hBB : L ^ B0 ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hsub : Icc 1 ⌊Real.sqrt x / L ^ B⌋₊ ⊆ Icc 1 ⌊Real.sqrt x / L ^ B0⌋₊ := by
      apply Icc_subset_Icc_right; apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hsx0.le (Real.rpow_pos_of_pos hL0 _) hBB
    have hterm : ∀ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊,
        |thetaAP (y q) q (a q) - y q / q.totient| ≤
          |psi (y q) q (a q) - y q / q.totient| + 2 * Real.sqrt x * L := by
      intro q _
      have h := psi_sub_thetaAP q (a q) (hy q).1 (hy q).2 (by linarith)
      have := abs_sub_abs_le_abs_sub (thetaAP (y q) q (a q) - y q / q.totient)
        (psi (y q) q (a q) - y q / q.totient)
      have e : thetaAP (y q) q (a q) - y q / q.totient - (psi (y q) q (a q) - y q / q.totient) =
        -(psi (y q) q (a q) - thetaAP (y q) q (a q)) := by ring
      rw [e, abs_neg, abs_of_nonneg h.1] at this
      linarith [h.2]
    have hs1 := sum_le_sum hterm
    rw [sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hs1
    have hs2 : ∑ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, |psi (y q) q (a q) - y q / q.totient| ≤
        K0 * x / L ^ A :=
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans
        (hK0 x hx a ha y hy)
    have hQ : (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) ≤ Real.sqrt x / L ^ B :=
      Nat.floor_le (by positivity)
    have hs3 : (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) * (2 * Real.sqrt x * L) ≤ 2 * x / L ^ A := by
      have hLB : L ^ B = L ^ (B0 + A) * L := by
        rw [hBdef, Real.rpow_add hL0, Real.rpow_one]
      have hLA : L ^ A ≤ L ^ (B0 + A) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have hLAp : 0 < L ^ (B0 + A) := Real.rpow_pos_of_pos hL0 _
      calc (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) * (2 * Real.sqrt x * L)
          ≤ Real.sqrt x / L ^ B * (2 * Real.sqrt x * L) :=
            mul_le_mul_of_nonneg_right hQ (by positivity)
        _ = 2 * x / L ^ (B0 + A) := by
            rw [hLB]; field_simp; rw [Real.sq_sqrt hx0.le]
        _ ≤ 2 * x / L ^ A := div_le_div_of_nonneg_left (by positivity) hLA0 hLA
    calc _ ≤ _ := hs1
      _ ≤ K0 * x / L ^ A + 2 * x / L ^ A := add_le_add hs2 hs3
      _ = (K0 + 2) * x / L ^ A := by ring
      _ ≤ max (K0 + 2) T * x / L ^ A := by
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxL
  · push Not at hxe
    refine (hT x hx hxe.le (fun q => |thetaAP (y q) q (a q) - y q / q.totient|)
      (fun _ _ => abs_nonneg _) ?_).trans ?_
    · intro q hq
      · have hb := thetaAP_bounds q (a q) hq (hy q).1 (hy q).2 (by linarith)
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
        have e1 : y q / q ≤ x := (div_le_self (hy q).1 hq1).trans (hy q).2
        have e2 : y q / q.totient ≤ x := (div_le_self (hy q).1 hφ1).trans (hy q).2
        have e3 : 0 ≤ y q / q.totient := div_nonneg (hy q).1 (by linarith)
        rw [abs_le]; constructor <;> nlinarith
    · rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxL

/-- Halupczok page 6, fixed exponent theta discrepancy mean with the lab Siegel Walfisz proof. -/
theorem theta_fixed (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
      (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ,
      (∀ q, 0 ≤ y q ∧ y q ≤ x) →
        ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ (4 * A + 15)⌋₊,
          |thetaAP (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A := by
  exact theta_fixed_of LeanLab.PNTPort.PsiChi.siegelWalfisz A hA

end LeanLab.Tolev2009.QuantitativeBV346
