module

public import LeanLab.VanDerCorput1939.SingLimit
public import LeanLab.VanDerCorput1939.Unweight
public import LeanLab.PNTPort.Vinogradov.TernaryAsymp
public import LeanLab.PNTPort.Vinogradov.SingPos
public import LeanLab.VanDerCorput1939.KBounds

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5704, paper P0067.

# van der Corput 1939, (1): Vinogradov's asymptotic for the number of prime triples

`vinogradov1 : Vinogradov1`, PROVED unconditional: for odd `N → ∞`,
`I(N) = (1 + ε) N² K P(N) / (2 (log N)³)` with `ε → 0`, where `I(N)` counts ordered triples of
primes with sum `N`. Assembled from

* the lab's `PNTPort.Vinogradov.vinogradov_asymptotic`, `|r₃ - J 𝔖_Q| ≤ C N²/log N` at `A = 1`,
  with `Q = ⌊(log N)^14⌋`, ineffective through Siegel-Walfisz;
* `SingLimit.fS_sum_tendsto_KP`, `𝔖_Q(N) → K P(N)` uniformly in odd `N` with `log N ≤ Q`;
* `Unweight.J_self`, `r3_le_I`, `I_le_r3`: `J(N, N) = (N-1)(N-2)/2` and `I(N) log³ N` against
  the von Mangoldt weighted `r₃`.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.VanDerCorput1939

open Real Finset Filter
open LeanLab.PNTPort.Vinogradov (r3 J singP fS vinogradov_asymptotic)

/-- The pure inequality step: from the four estimates to the relative error. -/
theorem assemble_ineq {I r3v Jv S KP L N C δ B : ℝ}
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hB : |S| ≤ B)
    (hasy : |r3v - Jv * S| ≤ C * N ^ 2 / L)
    (hJ : |Jv - N ^ 2 / 2| ≤ 2 * N)
    (hS : |S - KP| ≤ δ)
    (hup : r3v ≤ I * L ^ 3 + δ * N ^ 2)
    (hlo : I * L ^ 3 ≤ (1 + δ) * r3v + δ * N ^ 2)
    (hr3 : 0 ≤ r3v) :
    |I * L ^ 3 - N ^ 2 * KP / 2| ≤
      (δ * (C * N ^ 2 / L + 2 * N * B + N ^ 2 / 2 * (|KP| + δ)) + 2 * δ * N ^ 2 +
        (C * N ^ 2 / L + 2 * N * B + N ^ 2 / 2 * δ)) := by
  -- |r3 - N² KP/2| ≤ C N²/L + 2 N B + N²/2 δ
  have h1 : |r3v - N ^ 2 * KP / 2| ≤ C * N ^ 2 / L + 2 * N * B + N ^ 2 / 2 * δ := by
    have e : r3v - N ^ 2 * KP / 2 =
        (r3v - Jv * S) + (Jv - N ^ 2 / 2) * S + N ^ 2 / 2 * (S - KP) := by ring
    rw [e]
    have hN2 : 0 ≤ N ^ 2 / 2 := by positivity
    calc |(r3v - Jv * S) + (Jv - N ^ 2 / 2) * S + N ^ 2 / 2 * (S - KP)|
        ≤ |r3v - Jv * S| + |(Jv - N ^ 2 / 2) * S| + |N ^ 2 / 2 * (S - KP)| :=
          abs_add_three _ _ _
      _ ≤ C * N ^ 2 / L + 2 * N * B + N ^ 2 / 2 * δ := by
          rw [abs_mul, abs_mul, abs_of_nonneg hN2]
          gcongr
  have hr3le : r3v ≤ C * N ^ 2 / L + 2 * N * B + N ^ 2 / 2 * (|KP| + δ) := by
    have := (abs_le.mp h1).2
    have : N ^ 2 * KP / 2 ≤ N ^ 2 / 2 * |KP| := by
      have := le_abs_self KP; nlinarith [sq_nonneg N]
    nlinarith
  rw [abs_le]
  constructor
  · have := (abs_le.mp h1).1
    nlinarith
  · have := (abs_le.mp h1).2
    nlinarith

/-- `P(N) ≤ 1`: every factor `1 - 1/(p² - 3p + 3)` lies in `[0, 1]`. -/
theorem P_le_one (N : ℕ) : P N ≤ 1 := by
  unfold P
  apply Finset.prod_le_one₀
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hd : 1 ≤ (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
    have : 1 / ((p : ℝ) ^ 2 - 3 * p + 3) ≤ 1 := by rw [div_le_one (by linarith)]; exact hd
    linarith
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hd : 1 ≤ (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
    have : 0 ≤ 1 / ((p : ℝ) ^ 2 - 3 * p + 3) := by positivity
    linarith

set_option maxHeartbeats 1000000 in
/-- **van der Corput 1939, (1)**, Vinogradov's asymptotic for prime triples, unconditional. -/
theorem vinogradov1 : Vinogradov1 := by
  intro ε hε
  set δ : ℝ := min (1 / 4) (ε / 200) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδε : δ ≤ ε / 200 := min_le_right _ _
  obtain ⟨C, N₀', hasy⟩ := vinogradov_asymptotic 1 one_pos
  obtain ⟨P₀, hsing⟩ := fS_sum_tendsto_KP δ hδ0
  obtain ⟨N₁, hup⟩ := r3_le_I δ hδ0
  obtain ⟨N₂, hlo⟩ := I_le_r3 δ hδ0
  have hLtend : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- eventual conditions on L = log N
  have hev : ∀ᶠ N : ℕ in atTop,
      max (max (P₀ : ℝ) 2) (16 * Real.exp 16) + 1 ≤ Real.log N ^ (2 * (1 : ℝ) + 12) ∧
      2 ≤ Real.log N ∧ |C| / δ ≤ Real.log N ∧ N₀' ≤ (N : ℝ) ∧ 32 / δ ≤ (N : ℝ) ∧
      N₁ ≤ N ∧ N₂ ≤ N ∧ 3 ≤ N := by
    have hpow : Tendsto (fun N : ℕ => Real.log N ^ (2 * (1 : ℝ) + 12)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp hLtend
    refine (hpow.eventually_ge_atTop _).and ((hLtend.eventually_ge_atTop 2).and
      ((hLtend.eventually_ge_atTop _).and ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and ((eventually_ge_atTop N₁).and
      ((eventually_ge_atTop N₂).and (eventually_ge_atTop 3)))))))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hev
  refine ⟨N₃, fun N hNodd hN => ?_⟩
  obtain ⟨hQbig, hL2, hLC, hN0', hNδ, hN1, hN2, hN3⟩ := hN₃ N hN
  set L := Real.log N with hLdef
  set Q : ℕ := ⌊L ^ (2 * (1 : ℝ) + 12)⌋₊ with hQdef
  have hL0 : 0 < L := by linarith
  have hQge : max (max (P₀ : ℝ) 2) (16 * Real.exp 16) ≤ Q := by
    have := Nat.sub_one_lt_floor (L ^ (2 * (1 : ℝ) + 12)); rw [← hQdef] at this; linarith
  have hQP₀ : P₀ ≤ Q := by
    have : (P₀ : ℝ) ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQge
    exact_mod_cast this
  have hQ2 : 2 ≤ Q := by
    have : (2 : ℝ) ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQge
    exact_mod_cast this
  have hQe : 16 * Real.exp 16 ≤ (Q : ℝ) := le_trans (le_max_right _ _) hQge
  have hLQ : L ≤ Q := by
    have h1 : L ^ (2 : ℝ) ≤ L ^ (2 * (1 : ℝ) + 12) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : L ^ (2 : ℝ) = L * L := by rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]; ring
    have h3 : L + 1 ≤ L * L := by nlinarith
    have h4 : L + 1 ≤ L ^ (2 * (1 : ℝ) + 12) := by rw [← h2] at h3; exact h3.trans h1
    have h5 := Nat.sub_one_lt_floor (L ^ (2 * (1 : ℝ) + 12))
    have h6 : L ^ (2 * (1 : ℝ) + 12) - 1 < (Q : ℝ) := by rw [hQdef]; exact h5
    have h7 : L + 1 < (Q : ℝ) + 1 := h4.trans_lt (sub_lt_iff_lt_add.mp h6)
    exact ((add_lt_add_iff_right 1).mp h7).le
  -- the singular series
  set S : ℝ := ∑ q ∈ Finset.Icc 1 Q, fS N q with hSdef
  have hSK : |S - K * P N| ≤ δ := hsing Q N hQP₀ hNodd hLQ
  have hSlow : 1 - Real.exp 8 / Real.sqrt Q ≤ S := LeanLab.PNTPort.Vinogradov.singP_fS_ge hNodd hQ2
  have hsq : 4 * Real.exp 8 ≤ Real.sqrt Q := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : (4 * Real.exp 8) ^ 2 = 16 * Real.exp 16 := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    linarith
  have hS34 : 3 / 4 ≤ S := by
    have : Real.exp 8 / Real.sqrt Q ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hKP : 1 / 2 ≤ K * P N := by
    have h := (abs_le.mp hSK).2
    linarith [h, hS34, hδ1]
  have hKPle : K * P N ≤ 2.33 := by
    have h1 := P_le_one N
    have h2 := (P_pos hNodd).le
    have h3 := K_lt
    have h4 := one_le_K
    nlinarith
  have hB : |S| ≤ 4 := by
    rw [abs_le]; constructor
    · linarith
    · have := (abs_le.mp hSK).2; linarith
  -- the asymptotic
  have hasyN := hasy N hN0' N (by omega)
  rw [LeanLab.PNTPort.Vinogradov.singP_eq_fS, ← hQdef, ← hSdef] at hasyN
  have hasyR : |r3 N N - J N N * S| ≤ C * (N : ℝ) ^ 2 / L ^ (1 : ℝ) := by
    have e : ((r3 N N : ℝ) : ℂ) - ((J N N : ℝ) : ℂ) * ((S : ℝ) : ℂ) = ((r3 N N - J N N * S : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hasyN
    exact hasyN
  rw [Real.rpow_one] at hasyR
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hJ : |J N N - (N : ℝ) ^ 2 / 2| ≤ 2 * (N : ℝ) := by
    rw [J_self N hN3, abs_le]; constructor <;> nlinarith
  have hr3 : 0 ≤ r3 N N := by
    unfold r3
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => ?_
    split_ifs
    · exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg) ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  have key := assemble_ineq (I := (I N : ℝ)) (L := L) hN1r hδ0.le hB hasyR hJ hSK
    (hup N hN1) (hlo N hN2) hr3
  -- bound the right side by (ε/4) N²
  have hCL : C * (N : ℝ) ^ 2 / L ≤ δ * N ^ 2 := by
    rw [div_le_iff₀ hL0]
    have : C ≤ δ * L := by
      have := le_abs_self C
      rw [div_le_iff₀ hδ0] at hLC; linarith
    nlinarith [sq_nonneg (N : ℝ)]
  have h2NB : 2 * (N : ℝ) * 4 ≤ δ * N ^ 2 / 4 := by
    rw [div_le_iff₀ hδ0] at hNδ; nlinarith
  have hKPabs : |K * P N| ≤ 2.33 := by rw [abs_of_pos (by linarith)]; exact hKPle
  set KP := K * P N with hKPdef
  have hN2pos : 0 < (N : ℝ) ^ 2 := by positivity
  have hRHS : δ * (C * N ^ 2 / L + 2 * N * 4 + N ^ 2 / 2 * (|KP| + δ)) + 2 * δ * N ^ 2 +
      (C * N ^ 2 / L + 2 * N * 4 + N ^ 2 / 2 * δ) ≤ 25 * δ * N ^ 2 := by
    have : |KP| + δ ≤ 3 := by linarith
    have hc : (N : ℝ) ^ 2 / 2 * (|KP| + δ) ≤ N ^ 2 / 2 * 3 := by
      apply mul_le_mul_of_nonneg_left this (by positivity)
    have hδN : δ * (N : ℝ) ^ 2 ≤ N ^ 2 / 4 := by nlinarith
    have hsum : C * (N : ℝ) ^ 2 / L + 2 * N * 4 + N ^ 2 / 2 * (|KP| + δ) ≤ 2 * N ^ 2 := by
      linarith
    have hm : δ * (C * (N : ℝ) ^ 2 / L + 2 * N * 4 + N ^ 2 / 2 * (|KP| + δ)) ≤ δ * (2 * N ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hδ0.le
    have hd2 : (N : ℝ) ^ 2 / 2 * δ = δ * N ^ 2 / 2 := by ring
    linarith
  have hfin : |(I N : ℝ) * L ^ 3 - N ^ 2 * KP / 2| ≤ ε * (N ^ 2 * KP / 2) := by
    refine key.trans (hRHS.trans ?_)
    have h25 : 25 * δ ≤ ε / 8 := by linarith
    have hm : 25 * δ * (N : ℝ) ^ 2 ≤ ε / 8 * N ^ 2 := mul_le_mul_of_nonneg_right h25 hN2pos.le
    have hm2 : ε / 8 * (N : ℝ) ^ 2 ≤ ε * (N ^ 2 * KP / 2) := by
      have : (N : ℝ) ^ 2 / 4 ≤ N ^ 2 * KP / 2 := by nlinarith
      nlinarith
    linarith
  -- divide by L³
  have hL3 : 0 < L ^ 3 := by positivity
  have e1 : (I N : ℝ) - (N : ℝ) ^ 2 * K * P N / (2 * L ^ 3) =
      ((I N : ℝ) * L ^ 3 - N ^ 2 * KP / 2) / L ^ 3 := by
    rw [hKPdef]; field_simp
  have e2 : ε * ((N : ℝ) ^ 2 * K * P N / (2 * L ^ 3)) = ε * (N ^ 2 * KP / 2) / L ^ 3 := by
    rw [hKPdef]; field_simp
  rw [e1, e2, abs_div, abs_of_pos hL3]
  exact div_le_div_of_nonneg_right hfin hL3.le

end LeanLab.VanDerCorput1939

