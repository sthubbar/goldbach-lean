module

public import LeanLab.VanDerCorput1939.Statements
public import LeanLab.PNTPort.Vinogradov.TernaryCircle
public import LeanLab.PNTPort.Vinogradov.TernaryMajor

/-! AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5704, paper P0067.
Unweighting the ternary count. With `L = log N`:
* `J_self`: `J N N = (N - 1)(N - 2)/2` for `N ≥ 3`;
* `r3_le_I`: `r₃(N) ≤ I(N) L³ + ε N²` for large `N`, the prime powers `p^k`, `k ≥ 2`, being few;
* `I_le_r3`: `I(N) L³ ≤ (1 + ε) r₃(N) + ε N²` for large `N`, by cutting the primes at `N / L⁴`.
Known mathematics, no cited input. Checked only by the Lean kernel.
Binary Goldbach is OPEN. -/

@[expose] public section

noncomputable section
namespace LeanLab.VanDerCorput1939

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt

/-! ### Collapsing the third coordinate -/

lemma collapse (N a b : ℕ) (g : ℕ → ℝ) :
    ∑ c ∈ Icc 1 N, (if a + b + c = N then g c else 0) =
      if a + b < N then g (N - a - b) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (N - a - b)]
    · rw [if_pos (by omega)]
    · intro c _ hc; rw [if_neg (by omega)]
    · intro hc; exfalso; apply hc; simp only [Finset.mem_Icc]; omega
  · apply Finset.sum_eq_zero; intro c hc
    simp only [Finset.mem_Icc] at hc
    rw [if_neg (by omega)]

lemma triple_eq (N : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
      if a + b + c = N then f a * f b * f c else 0) =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if a + b < N then f a * f b * f (N - a - b) else 0 := by
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  exact collapse N a b (fun c => f a * f b * f c)

/-! ### `J N N` -/

lemma sum_Icc_sub (N : ℕ) : ∑ x ∈ Icc 1 N, (N - x - 1) = ∑ i ∈ range (N - 1), i := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 : Icc 1 N = Ico 1 (N + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have h2 : N + 1 - 1 = (N - 1) + 1 := by omega
  rw [h2, Finset.sum_range_succ]
  have h3 : N - (1 + (N - 1)) - 1 = 0 := by omega
  rw [h3, add_zero]
  rw [← Finset.sum_range_reflect (fun i => i) (N - 1)]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  omega

theorem J_self (N : ℕ) (hN : 3 ≤ N) :
    LeanLab.PNTPort.Vinogradov.J N N = ((N:ℝ) - 1) * ((N:ℝ) - 2) / 2 := by
  unfold LeanLab.PNTPort.Vinogradov.J
  have h := triple_eq N (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  have h2 : ∀ x ∈ Icc 1 N, (∑ y ∈ Icc 1 N, if x + y < N then (1 : ℝ) else 0) =
      ((N - x - 1 : ℕ) : ℝ) := by
    intro x _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    have : (Icc 1 N).filter (fun y => x + y < N) = Icc 1 (N - x - 1) := by
      ext y; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc]; omega
  rw [sum_congr rfl h2, ← Nat.cast_sum, sum_Icc_sub]
  have h3 := Finset.sum_range_id_mul_two (N - 1)
  have h4 : ((∑ i ∈ range (N - 1), i : ℕ) : ℝ) * 2 = ((N - 1 : ℕ) : ℝ) * ((N - 1 - 1 : ℕ) : ℝ) := by
    exact_mod_cast h3
  have e1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have e2 : ((N - 1 - 1 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [show N - 1 - 1 = N - 2 by omega, Nat.cast_sub (by omega)]; simp
  rw [e1, e2] at h4
  linarith

/-! ### `I N` as a pair sum -/

/-- The prime indicator. -/
def chiP (n : ℕ) : ℝ := if n.Prime then 1 else 0

lemma chiP_nonneg (n : ℕ) : 0 ≤ chiP n := by unfold chiP; split_ifs <;> norm_num

lemma I_eq (N : ℕ) : (I N : ℝ) =
    ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if a + b < N then chiP a * chiP b * chiP (N - a - b) else 0 := by
  set G : ℕ → ℕ → ℝ := fun a b =>
    if a + b < N then chiP a * chiP b * chiP (N - a - b) else 0 with hG
  have hpt : ∀ a b : ℕ, (if (a.Prime ∧ b.Prime ∧ N - a - b ≠ 0 ∧ (N - a - b).Prime ∧ a + b ≤ N)
      then (1 : ℝ) else 0) = G a b := by
    intro a b
    simp only [hG, chiP]
    by_cases ha : a.Prime <;> by_cases hb : b.Prime <;> by_cases hc : (N - a - b).Prime <;>
      simp [ha, hb, hc]
    split_ifs <;> first | rfl | omega
  unfold I
  rw [Finset.natCast_card_filter, Finset.sum_product]
  simp only [hpt]
  have hsub : Icc 1 N ⊆ range (N + 1) := by
    intro x; simp only [mem_Icc, mem_range]; omega
  have hz : ∀ a b, (a = 0 ∨ b = 0) → G a b = 0 := by
    intro a b h
    simp only [hG, chiP]
    rcases h with rfl | rfl <;> simp [Nat.not_prime_zero]
  rw [← Finset.sum_subset hsub]
  · refine sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_subset hsub]
    intro b hb hb'
    apply hz; right; simp only [mem_Icc, mem_range] at hb hb'; omega
  · intro a ha ha'
    apply Finset.sum_eq_zero; intro b _
    apply hz; left; simp only [mem_Icc, mem_range] at ha ha'; omega

/-! ### The counting bound for the exceptional coordinate -/

lemma third_bound (N : ℕ) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) :
    ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a + b < N then s a + s b + s (N - a - b) else 0) ≤
      3 * N * ∑ n ∈ Icc 1 N, s n := by
  set S := ∑ n ∈ Icc 1 N, s n with hS
  have hc : ∀ a, ∑ b ∈ Icc 1 N, (if a + b < N then s (N - a - b) else 0) ≤ S := by
    intro a
    rw [← Finset.sum_filter]
    rw [← Finset.sum_image (g := fun b => N - a - b) (f := s)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [mem_image, mem_filter, mem_Icc] at hn
        obtain ⟨b, ⟨⟨hb1, hb2⟩, hb3⟩, rfl⟩ := hn
        simp only [mem_Icc]; omega
      · intro n _ _; exact hs n
    · intro x hx y hy hxy
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy hxy
      omega
  have hin : ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a + b < N then s a + s b + s (N - a - b) else 0)
      ≤ N * s a + S + S := by
    intro a _
    have h1 : ∀ b ∈ Icc 1 N, (if a + b < N then s a + s b + s (N - a - b) else 0) ≤
        s a + s b + (if a + b < N then s (N - a - b) else 0) := by
      intro b _
      split_ifs
      · exact le_refl _
      · linarith [hs a, hs b]
    calc _ ≤ ∑ b ∈ Icc 1 N, (s a + s b + (if a + b < N then s (N - a - b) else 0)) :=
          sum_le_sum h1
      _ = N * s a + S + ∑ b ∈ Icc 1 N, (if a + b < N then s (N - a - b) else 0) := by
          rw [sum_add_distrib, sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp [hS]
      _ ≤ N * s a + S + S := by linarith [hc a]
  calc _ ≤ ∑ a ∈ Icc 1 N, (N * s a + S + S) := sum_le_sum hin
    _ = N * S + N * S + N * S := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp [hS]
    _ = 3 * N * S := by ring

/-! ### Non-prime prime powers are few -/

/-- Indicator of prime powers that are not prime. -/
def ppNP (n : ℕ) : ℝ := if IsPrimePow n ∧ ¬ n.Prime then 1 else 0

lemma ppNP_nonneg (n : ℕ) : 0 ≤ ppNP n := by unfold ppNP; split_ifs <;> norm_num

lemma card_ppNP (N : ℕ) :
    ∑ n ∈ Icc 1 N, ppNP n ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) := by
  have h1 : ∑ n ∈ Icc 1 N, ppNP n = (((Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ) := by
    rw [Finset.natCast_card_filter]; rfl
  rw [h1]
  have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) ⊆
      ((Icc 1 (Nat.sqrt N)) ×ˢ (Icc 1 (Nat.log 2 N))).image (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, ⟨p, k, hp, hk, rfl⟩, hnp⟩ := hn
    have hp' : p.Prime := hp.nat_prime
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hnp (by simpa using hp')
    simp only [mem_image, mem_product, mem_Icc]
    refine ⟨(p, k), ⟨⟨hp'.one_lt.le, ?_⟩, ⟨by omega, ?_⟩⟩, rfl⟩
    · rw [Nat.le_sqrt']
      calc p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp'.pos hk2
        _ ≤ N := hnN
    · have : 2 ^ k ≤ N := le_trans (Nat.pow_le_pow_left hp'.two_le k) hnN
      exact Nat.le_log_of_pow_le (by norm_num) this
  have := (card_le_card hsub).trans card_image_le
  rw [card_product, Nat.card_Icc, Nat.card_Icc] at this
  simp only [add_tsub_cancel_right] at this
  exact_mod_cast this

lemma natLog_le (N : ℕ) (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h' : ((2 : ℝ)) ^ Nat.log 2 N ≤ (N : ℝ) := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this

lemma eventually_nat {P : ℝ → Prop} (h : ∀ᶠ x in atTop, P x) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P N := by
  have := tendsto_natCast_atTop_atTop.eventually h
  exact eventually_atTop.mp this

/-! ### `r₃ ≤ I L³ + ε N²` -/

lemma pw_upper {N a b c : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) (hb : 1 ≤ b) (hbN : b ≤ N)
    (hc : 1 ≤ c) (hcN : c ≤ N) :
    Λ a * Λ b * Λ c ≤ Real.log N ^ 3 * (chiP a * chiP b * chiP c) +
      Real.log N ^ 3 * (ppNP a + ppNP b + ppNP c) := by
  set L := Real.log N
  have hle : ∀ n : ℕ, 1 ≤ n → n ≤ N → Λ n ≤ L := by
    intro n h1 h2
    refine (ArithmeticFunction.vonMangoldt_le_log).trans ?_
    exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hnn : ∀ n : ℕ, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  have hL : 0 ≤ L := Real.log_natCast_nonneg N
  have hprod : Λ a * Λ b * Λ c ≤ L ^ 3 := by
    have h1 : Λ a * Λ b ≤ L * L :=
      mul_le_mul (hle a ha haN) (hle b hb hbN) (hnn b) hL
    calc Λ a * Λ b * Λ c ≤ (L * L) * L :=
          mul_le_mul h1 (hle c hc hcN) (hnn c) (mul_nonneg hL hL)
      _ = L ^ 3 := by ring
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL 3
  have hX : 0 ≤ L ^ 3 * (chiP a * chiP b * chiP c) :=
    mul_nonneg hL3 (mul_nonneg (mul_nonneg (chiP_nonneg a) (chiP_nonneg b)) (chiP_nonneg c))
  have hsa := ppNP_nonneg a
  have hsb := ppNP_nonneg b
  have hsc := ppNP_nonneg c
  -- a non-prime coordinate either kills `Λ` or is counted by `ppNP`
  have key : ∀ n : ℕ, ¬ n.Prime → Λ n = 0 ∨ ppNP n = 1 := by
    intro n hn
    by_cases hpp : IsPrimePow n
    · right; unfold ppNP; rw [if_pos ⟨hpp, hn⟩]
    · left; exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
  have hprod0 : 0 ≤ Λ a * Λ b * Λ c := mul_nonneg (mul_nonneg (hnn a) (hnn b)) (hnn c)
  by_cases hpa : a.Prime
  · by_cases hpb : b.Prime
    · by_cases hpc : c.Prime
      · have : chiP a * chiP b * chiP c = 1 := by simp [chiP, hpa, hpb, hpc]
        rw [this]; nlinarith
      · rcases key c hpc with h | h
        · rw [h, mul_zero]; nlinarith
        · rw [h]; nlinarith
    · rcases key b hpb with h | h
      · rw [h, mul_zero, zero_mul]; nlinarith
      · rw [h]; nlinarith
  · rcases key a hpa with h | h
    · rw [h, zero_mul, zero_mul]; nlinarith
    · rw [h]; nlinarith

theorem r3_le_I : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    LeanLab.PNTPort.Vinogradov.r3 N N ≤ (I N : ℝ) * Real.log N ^ 3 + ε * (N:ℝ) ^ 2 := by
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := ε * Real.log 2 / 3 with hc
  have hcpos : 0 < c := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hcpos
  obtain ⟨N₀, hN₀⟩ := eventually_nat (ho.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hbd, hN1⟩ := hN₀ N hN
  have hN1' : 1 ≤ N := by exact_mod_cast hN1
  set L := Real.log N with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg N
  have hx0 : (0 : ℝ) ≤ N := by positivity
  -- the log bound: L⁴ ≤ c √N
  have hsq : (N : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt N := (Real.sqrt_eq_rpow _).symm
  have hL4 : L ^ 4 ≤ c * Real.sqrt N := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _), hsq] at hbd
    have : L ^ (4 : ℝ) = L ^ 4 := by exact_mod_cast Real.rpow_natCast L 4
    rw [this] at hbd
    exact (le_abs_self _).trans hbd
  -- r3 as a pair sum, bounded pointwise
  unfold LeanLab.PNTPort.Vinogradov.r3
  rw [triple_eq N (fun n => Λ n)]
  have hpt : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      (if a + b < N then Λ a * Λ b * Λ (N - a - b) else 0) ≤
        L ^ 3 * (if a + b < N then chiP a * chiP b * chiP (N - a - b) else 0) +
        L ^ 3 * (if a + b < N then ppNP a + ppNP b + ppNP (N - a - b) else 0) := by
    intro a ha b hb
    simp only [mem_Icc] at ha hb
    split_ifs with h
    · exact pw_upper ha.1 ha.2 hb.1 hb.2 (by omega) (by omega)
    · simp
  have hsum := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpt a ha b hb
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← I_eq] at hsum
  have h3 := third_bound N ppNP ppNP_nonneg
  have h4 := card_ppNP N
  have h5 := natLog_le N hN1'
  have hsqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hx0
  -- the error: L³ · 3N · √N · log₂ N ≤ ε N²
  have hS : L ^ 3 * (3 * N * ∑ n ∈ Icc 1 N, ppNP n) ≤ ε * (N : ℝ) ^ 2 := by
    have hlog2 : (Nat.log 2 N : ℝ) ≤ L / Real.log 2 := by
      rw [le_div_iff₀ hl2]; exact h5
    have hS1 : ∑ n ∈ Icc 1 N, ppNP n ≤ Real.sqrt N * (L / Real.log 2) := by
      refine h4.trans ?_
      apply mul_le_mul hsqrt hlog2 (by positivity) (Real.sqrt_nonneg _)
    have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, ppNP n := sum_nonneg fun n _ => ppNP_nonneg n
    calc L ^ 3 * (3 * N * ∑ n ∈ Icc 1 N, ppNP n)
        ≤ L ^ 3 * (3 * N * (Real.sqrt N * (L / Real.log 2))) := by gcongr
      _ = 3 * N * Real.sqrt N * L ^ 4 / Real.log 2 := by field_simp
      _ ≤ 3 * N * Real.sqrt N * (c * Real.sqrt N) / Real.log 2 := by gcongr
      _ = ε * (N : ℝ) ^ 2 := by
          rw [hc]; field_simp
          exact Real.sq_sqrt hx0
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL 3
  have := mul_le_mul_of_nonneg_left h3 hL3
  nlinarith

/-! ### `I L³ ≤ (1 + ε) r₃ + ε N²` -/

lemma pw_lower {a b c Y : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hlog : ∀ p : ℕ, p.Prime → Y < p → ℓ ≤ Real.log p) :
    ℓ ^ 3 * (chiP a * chiP b * chiP c) ≤ Λ a * Λ b * Λ c +
      ℓ ^ 3 * ((if a ≤ Y then 1 else 0) + (if b ≤ Y then 1 else 0) + (if c ≤ Y then 1 else 0)) := by
  have hnn : ∀ n : ℕ, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  have hprod0 : 0 ≤ Λ a * Λ b * Λ c := mul_nonneg (mul_nonneg (hnn a) (hnn b)) (hnn c)
  have hℓ3 : 0 ≤ ℓ ^ 3 := pow_nonneg hℓ 3
  have hi : ∀ n : ℕ, (0 : ℝ) ≤ if n ≤ Y then 1 else 0 := fun n => by split_ifs <;> norm_num
  have hia := hi a; have hib := hi b; have hic := hi c
  by_cases hpa : a.Prime
  · by_cases hpb : b.Prime
    · by_cases hpc : c.Prime
      · have h1 : chiP a * chiP b * chiP c = 1 := by simp [chiP, hpa, hpb, hpc]
        rw [h1, mul_one]
        by_cases ya : a ≤ Y
        · rw [if_pos ya]; nlinarith
        by_cases yb : b ≤ Y
        · rw [if_pos yb]; nlinarith
        by_cases yc : c ≤ Y
        · rw [if_pos yc]; nlinarith
        push_neg at ya yb yc
        have la : ℓ ≤ Λ a := by
          rw [ArithmeticFunction.vonMangoldt_apply_prime hpa]; exact hlog a hpa ya
        have lb : ℓ ≤ Λ b := by
          rw [ArithmeticFunction.vonMangoldt_apply_prime hpb]; exact hlog b hpb yb
        have lc : ℓ ≤ Λ c := by
          rw [ArithmeticFunction.vonMangoldt_apply_prime hpc]; exact hlog c hpc yc
        have : ℓ ^ 3 ≤ Λ a * Λ b * Λ c := by
          calc ℓ ^ 3 = ℓ * ℓ * ℓ := by ring
            _ ≤ Λ a * Λ b * Λ c := by
              apply mul_le_mul (mul_le_mul la lb hℓ (hnn a)) lc hℓ
                (mul_nonneg (hnn a) (hnn b))
        nlinarith
      · have : chiP c = 0 := by simp [chiP, hpc]
        rw [this, mul_zero, mul_zero]; nlinarith
    · have : chiP b = 0 := by simp [chiP, hpb]
      rw [this, mul_zero, zero_mul, mul_zero]; nlinarith
  · have : chiP a = 0 := by simp [chiP, hpa]
    rw [this, zero_mul, zero_mul, mul_zero]; nlinarith

lemma card_le_Y (N Y : ℕ) :
    ∑ n ∈ Icc 1 N, (if n ≤ Y then (1 : ℝ) else 0) ≤ Y := by
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have : (Icc 1 N).filter (fun n => n ≤ Y) ⊆ Icc 1 Y := by
    intro n; simp only [mem_filter, mem_Icc]; omega
  have := card_le_card this
  rw [Nat.card_Icc] at this
  exact_mod_cast (by omega : ((Icc 1 N).filter (fun n => n ≤ Y)).card ≤ Y)

theorem I_le_r3 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (I N : ℝ) * Real.log N ^ 3 ≤ (1 + ε) * LeanLab.PNTPort.Vinogradov.r3 N N + ε * (N:ℝ) ^ 2 := by
  intro ε hε
  set δ : ℝ := ε / (3 * (1 + ε)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ < 1 / 3 := by
    rw [hδ, div_lt_iff₀ (by positivity)]; nlinarith
  have hkey : 3 * δ * (1 + ε) = ε := by rw [hδ]; field_simp
  -- eventually: 4 log L ≤ δ L, and L ≥ max 1 (3(1+ε)/ε)
  have ho := Real.isLittleO_log_id_atTop.bound (by positivity : (0 : ℝ) < δ / 4)
  have h1 : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤ δ / 4 * ‖id (Real.log x)‖ :=
    Real.tendsto_log_atTop.eventually ho
  have h2 : ∀ᶠ x : ℝ in atTop, max 1 (3 * (1 + ε) / ε) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_nat ((h1.and h2).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hb1, hb2⟩, hN1⟩ := hN₀ N hN
  have hN1' : 1 ≤ N := by exact_mod_cast hN1
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hb2
  have hLe : 3 * (1 + ε) / ε ≤ L := (le_max_right _ _).trans hb2
  have hLpos : 0 < L := by linarith
  have hlogL : 4 * Real.log L ≤ δ * L := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hLpos] at hb1
    have := (le_abs_self (Real.log L)).trans hb1
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  -- cut point
  set y : ℝ := N / L ^ 4 with hy
  have hypos : 0 < y := by positivity
  set ℓ : ℝ := Real.log y with hℓdef
  have hℓeq : ℓ = L - 4 * Real.log L := by
    rw [hℓdef, hy, Real.log_div hNpos.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hℓlow : (1 - δ) * L ≤ ℓ := by rw [hℓeq]; linarith
  have hℓpos : 0 < ℓ := by nlinarith
  have hℓL : ℓ ≤ L := by
    rw [hℓeq]; have := Real.log_nonneg hL1; linarith
  set Y : ℕ := ⌊y⌋₊ with hY
  have hYy : (Y : ℝ) ≤ y := Nat.floor_le hypos.le
  have hlog : ∀ p : ℕ, p.Prime → Y < p → ℓ ≤ Real.log p := by
    intro p _ hp
    have : y < p := by
      have := Nat.lt_floor_add_one y
      have hp' : (Y : ℝ) + 1 ≤ p := by exact_mod_cast hp
      linarith
    exact Real.log_le_log hypos this.le
  -- pointwise and summed
  have hpt : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      ℓ ^ 3 * (if a + b < N then chiP a * chiP b * chiP (N - a - b) else 0) ≤
        (if a + b < N then Λ a * Λ b * Λ (N - a - b) else 0) +
        ℓ ^ 3 * (if a + b < N then (if a ≤ Y then (1 : ℝ) else 0) + (if b ≤ Y then (1 : ℝ) else 0)
          + (if N - a - b ≤ Y then (1 : ℝ) else 0) else 0) := by
    intro a _ b _
    by_cases h : a + b < N
    · rw [if_pos h, if_pos h, if_pos h]; exact pw_lower hℓpos.le hlog
    · rw [if_neg h, if_neg h, if_neg h]; simp
  have hsum := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpt a ha b hb
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← I_eq] at hsum
  have hr3 : LeanLab.PNTPort.Vinogradov.r3 N N =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if a + b < N then Λ a * Λ b * Λ (N - a - b) else 0 := by
    unfold LeanLab.PNTPort.Vinogradov.r3; exact triple_eq N (fun n => Λ n)
  rw [← hr3] at hsum
  have h3 := third_bound N (fun n => if n ≤ Y then (1 : ℝ) else 0)
    (fun n => by split_ifs <;> norm_num)
  have h4 := card_le_Y N Y
  set E := ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a + b < N then (if a ≤ Y then (1 : ℝ) else 0) +
    (if b ≤ Y then (1 : ℝ) else 0) + (if N - a - b ≤ Y then (1 : ℝ) else 0) else 0) with hEdef
  have hE : E ≤ 3 * N * y := by
    refine h3.trans ?_
    have : (0 : ℝ) ≤ 3 * N := by positivity
    exact mul_le_mul_of_nonneg_left (h4.trans hYy) this
  have hr3nn : 0 ≤ LeanLab.PNTPort.Vinogradov.r3 N N := by
    rw [hr3]; apply sum_nonneg; intro a _; apply sum_nonneg; intro b _
    split_ifs
    · exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg) ArithmeticFunction.vonMangoldt_nonneg
    · exact le_refl _
  have hI0 : (0 : ℝ) ≤ I N := Nat.cast_nonneg _
  -- L³ ≤ (1 + ε) ℓ³
  have hcube : L ^ 3 ≤ (1 + ε) * ℓ ^ 3 := by
    have hb : (1 - 3 * δ) * L ^ 3 ≤ ℓ ^ 3 := by
      have hA : ((1 - δ) * L) ^ 3 ≤ ℓ ^ 3 := by
        apply pow_le_pow_left₀ (by nlinarith) hℓlow
      have hB : (1 - 3 * δ) ≤ (1 - δ) ^ 3 := by nlinarith [sq_nonneg δ]
      have hL3 : 0 ≤ L ^ 3 := by positivity
      calc (1 - 3 * δ) * L ^ 3 ≤ (1 - δ) ^ 3 * L ^ 3 := by nlinarith
        _ = ((1 - δ) * L) ^ 3 := by ring
        _ ≤ ℓ ^ 3 := hA
    have : (1 + ε) * ((1 - 3 * δ) * L ^ 3) = L ^ 3 := by
      have : (1 + ε) * (1 - 3 * δ) = 1 := by nlinarith [hkey]
      calc (1 + ε) * ((1 - 3 * δ) * L ^ 3) = ((1 + ε) * (1 - 3 * δ)) * L ^ 3 := by ring
        _ = L ^ 3 := by rw [this, one_mul]
    nlinarith
  -- error term: (1+ε) ℓ³ · 3 N y ≤ ε N²
  have herr : (1 + ε) * (ℓ ^ 3 * (3 * N * y)) ≤ ε * (N : ℝ) ^ 2 := by
    have hℓ3 : ℓ ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hℓpos.le hℓL 3
    have hyL : L ^ 3 * y = N / L := by
      rw [hy]; field_simp
    have hNL : (1 + ε) * 3 / L ≤ ε := by
      rw [div_le_iff₀ hLpos]
      have := (div_le_iff₀ hε).mp hLe
      linarith
    calc (1 + ε) * (ℓ ^ 3 * (3 * N * y)) ≤ (1 + ε) * (L ^ 3 * (3 * N * y)) := by gcongr
      _ = (1 + ε) * 3 / L * (N : ℝ) ^ 2 := by
          rw [show L ^ 3 * (3 * N * y) = 3 * N * (L ^ 3 * y) by ring, hyL]
          field_simp
      _ ≤ ε * (N : ℝ) ^ 2 := by gcongr
  -- combine: ℓ³ I ≤ r3 + ℓ³ E
  have hmain : ℓ ^ 3 * (I N : ℝ) ≤ LeanLab.PNTPort.Vinogradov.r3 N N + ℓ ^ 3 * (3 * N * y) := by
    have : ℓ ^ 3 * E ≤ ℓ ^ 3 * (3 * N * y) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    linarith
  calc (I N : ℝ) * L ^ 3 ≤ (I N : ℝ) * ((1 + ε) * ℓ ^ 3) := mul_le_mul_of_nonneg_left hcube hI0
    _ = (1 + ε) * (ℓ ^ 3 * (I N : ℝ)) := by ring
    _ ≤ (1 + ε) * (LeanLab.PNTPort.Vinogradov.r3 N N + ℓ ^ 3 * (3 * N * y)) := by gcongr
    _ = (1 + ε) * LeanLab.PNTPort.Vinogradov.r3 N N + (1 + ε) * (ℓ ^ 3 * (3 * N * y)) := by ring
    _ ≤ (1 + ε) * LeanLab.PNTPort.Vinogradov.r3 N N + ε * (N : ℝ) ^ 2 := by linarith

end LeanLab.VanDerCorput1939

