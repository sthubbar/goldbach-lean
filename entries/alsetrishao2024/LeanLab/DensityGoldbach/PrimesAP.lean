module

public import LeanLab.HardyLittlewood1923.APPow

/-! AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5907, paper P0047.
Primes in a reduced residue class get at least their share `1/φ(m)` of all primes up to `N`,
asymptotically: `π(N; m, a) ≥ (1 - η) π(N) / φ(m)` for all large `N`.
Route: the lower bound `π(N; m, a) log N ≥ θ(N; m, a) ≥ (1/φ(m) - ε) N` comes from the
`k = 0` case of `ap_sum_pow`, which rests on the lab's Siegel-Walfisz theorem; the upper bound
`(1 - δ) π(N) log N ≤ (1 - δ) (N^(1-δ) + 1) log N + θ(N)` comes from splitting the primes at
`N^(1-δ)`, with `θ(N) ≤ (1 + ε) N` from the `d = 1` case of `ap_sum_pow`.
No cited input beyond what `siegelWalfisz` proves. Binary Goldbach is OPEN. -/

@[expose] public section

open Real Finset Filter

namespace LeanLab.DensityGoldbach

/-- Splitting the primes up to `N` at `N^(1-δ)`. -/
lemma pi_split (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : δ < 1) :
    (1 - δ) * Real.log N * (((range (N + 1)).filter Nat.Prime).card : ℝ) ≤
      (1 - δ) * Real.log N * ((N : ℝ) ^ (1 - δ) + 1) +
        ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p := by
  set P := (range (N + 1)).filter Nat.Prime with hP
  set t : ℝ := (N : ℝ) ^ (1 - δ) with ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have hlogt : Real.log t = (1 - δ) * Real.log N := Real.log_rpow hN0 _
  have h1δ : 0 < 1 - δ := by linarith
  set Ps := P.filter (fun p : ℕ => (p : ℝ) < t)
  set Pb := P.filter (fun p : ℕ => ¬ (p : ℝ) < t)
  have hcard : (P.card : ℝ) = Ps.card + Pb.card := by
    rw [← card_filter_add_card_filter_not (s := P) (fun p : ℕ => (p : ℝ) < t)]; push_cast; rfl
  have hsmall : (Ps.card : ℝ) ≤ t + 1 := by
    have h2 : Ps.card ≤ ⌈t⌉₊ := by
      calc Ps.card ≤ (range ⌈t⌉₊).card := by
            refine card_le_card fun p hp => ?_
            exact mem_range.2 (Nat.lt_ceil.2 (mem_filter.1 hp).2)
        _ = ⌈t⌉₊ := card_range _
    exact le_trans (by exact_mod_cast h2) (Nat.ceil_lt_add_one ht0.le).le
  have hbig : (1 - δ) * Real.log N * Pb.card ≤ ∑ p ∈ P, Real.log p := by
    have e : (1 - δ) * Real.log N * Pb.card = ∑ _p ∈ Pb, (1 - δ) * Real.log N := by
      rw [sum_const, nsmul_eq_mul]; ring
    rw [e]
    refine le_trans (sum_le_sum fun p hp => ?_) (sum_le_sum_of_subset_of_nonneg
      (filter_subset _ P) fun p _ _ => Real.log_natCast_nonneg p)
    have htp : t ≤ p := not_lt.1 (mem_filter.1 hp).2
    exact hlogt ▸ Real.log_le_log ht0 htp
  have hA : 0 ≤ (1 - δ) * Real.log N := mul_nonneg h1δ.le hL
  have := mul_le_mul_of_nonneg_left hsmall hA
  rw [hcard]
  nlinarith

/-- `π(N; m, a) log N ≥ θ(N; m, a)`. -/
lemma theta_ap_le (N m a : ℕ) :
    ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % m = a % m), Real.log p ≤
      (((range (N + 1)).filter (fun p => p.Prime ∧ p % m = a % m)).card : ℝ) * Real.log N := by
  calc ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % m = a % m), Real.log p
      ≤ ∑ _p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % m = a % m), Real.log N := by
        apply sum_le_sum; intro p hp
        rw [mem_filter, mem_range] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
        have hpn : (p : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 hp.1
        exact Real.log_le_log hp0 hpn
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- Primes in a reduced class get at least their share `1/φ(m)` of all primes, asymptotically. -/
theorem pi_ap_lower (m a : ℕ) (hm : 1 ≤ m) (ha : Nat.Coprime a m) : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N →
      (1 - η) / (Nat.totient m : ℝ) * (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤
        (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % m = a % m)).card : ℝ) := by
  intro η hη
  have hφ : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.2 (by omega)
  by_cases hη1 : 1 ≤ η
  · refine ⟨0, fun N _ => ?_⟩
    have : (1 - η) / (Nat.totient m : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hφ.le
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg this (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  push Not at hη1
  set φ : ℝ := (Nat.totient m : ℝ) with hφdef
  set ε : ℝ := η / (2 * (3 + φ)) with hεdef
  have hε : 0 < ε := by positivity
  set δ : ℝ := η / 2 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 m hm ε hε
  obtain ⟨n₁, hn₁⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 1 le_rfl ε hε
  have hev := (LeanLab.HardyLittlewood1923.eventually_log_le ε δ hε hδ).and
    ((LeanLab.HardyLittlewood1923.eventually_log_le ε 1 hε one_pos).and (eventually_ge_atTop 2))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hev
  refine ⟨max n₀ (max n₁ n₂), fun N hN => ?_⟩
  obtain ⟨hl1, hl2, hN2⟩ := hn₂ N (le_of_max_le_right (le_of_max_le_right hN))
  have hS := hn₀ N (le_of_max_le_left hN) a ha
  have hT := hn₁ N (le_of_max_le_left (le_of_max_le_right hN)) 0 (Nat.coprime_zero_left 1 |>.2 rfl)
  simp only [pow_zero, mul_one, zero_add, pow_one, Nat.cast_zero, one_mul, Nat.totient_one,
    Nat.cast_one, div_one, Nat.mod_one, and_true] at hS hT
  rw [Real.rpow_one] at hl2
  set n : ℝ := (N : ℝ) with hndef
  have hn1 : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < n := by linarith
  set L := Real.log n with hLdef
  have hL : 0 < L := Real.log_pos (by rw [hndef]; exact_mod_cast (show 1 < N by omega))
  have hsplit := pi_split N (by omega) δ (by linarith)
  have hlow := theta_ap_le N m a
  set S := ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % m = a % m), Real.log p
  set θ := ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p
  set P : ℝ := (((range (N + 1)).filter Nat.Prime).card : ℝ)
  set A : ℝ := (((range (N + 1)).filter (fun p => p.Prime ∧ p % m = a % m)).card : ℝ)
  rw [abs_le] at hS hT
  rw [← hφdef] at hS
  rw [← hndef, ← hLdef] at hlow
  set t := n ^ (1 - δ) with htdef
  have htn : t * n ^ δ = n := by
    rw [htdef, ← Real.rpow_add hn0]; simp
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0.le _
  have hLt : L * t ≤ ε * n := by
    have := mul_le_mul_of_nonneg_left hl1 ht0
    nlinarith
  -- upper: (1 - δ) L P ≤ (1 + 3ε) n
  have h1δ : 0 < 1 - δ := by rw [hδdef]; linarith
  have hup : (1 - δ) * L * P ≤ (1 + 3 * ε) * n := by
    have : (1 - δ) * L * (t + 1) ≤ L * (t + 1) := by
      have : 0 ≤ L * (t + 1) := by positivity
      nlinarith
    nlinarith
  -- lower: A L ≥ (1/φ - ε) n
  have hS' : n / φ - ε * n ≤ A * L := by linarith
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  -- goal times φ (1 - δ) L
  have key : (1 - η) * ((1 - δ) * L * P) ≤ (1 - δ) * φ * (A * L) := by
    have e1 : (1 - η) * ((1 - δ) * L * P) ≤ (1 - η) * ((1 + 3 * ε) * n) :=
      mul_le_mul_of_nonneg_left hup (by linarith)
    have e2 : (1 - δ) * φ * (n / φ - ε * n) ≤ (1 - δ) * φ * (A * L) :=
      mul_le_mul_of_nonneg_left hS' (by positivity)
    have e3 : (1 - δ) * φ * (n / φ - ε * n) = (1 - δ) * (1 - ε * φ) * n := by
      field_simp
    have hεφ : ε * (3 + φ) = η / 2 := by rw [hεdef]; field_simp
    have e4 : (1 - η) * ((1 + 3 * ε) * n) ≤ (1 - δ) * (1 - ε * φ) * n := by
      have c : (1 - η) * (1 + 3 * ε) ≤ (1 - δ) * (1 - ε * φ) := by
        rw [hδdef]; nlinarith
      have := mul_le_mul_of_nonneg_right c hn0.le
      linarith [show (1 - η) * ((1 + 3 * ε) * n) = (1 - η) * (1 + 3 * ε) * n by ring]
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hφ]
  have hpos : 0 < (1 - δ) * L := mul_pos h1δ hL
  nlinarith

