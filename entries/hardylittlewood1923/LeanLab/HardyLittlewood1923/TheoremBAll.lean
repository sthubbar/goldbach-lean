module

public import LeanLab.HardyLittlewood1923.TheoremBRec
public import LeanLab.HardyLittlewood1923.APPow
public import LeanLab.HardyLittlewood1923.EulerR

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5901, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III, Theorem B, (3.32), for every r ≥ 3

Read from `papers/P0004.pdf`, Acta Math. 44, p. 29, Theorem B: if `r ≥ 3` and `n`, `r` have like
parity, then
`ν_r(n) ∼ (2 C_r/(r-1)!) n^{r-1} ∏_{p ∣ n, p odd} ((p-1)^r + (-1)^r (p-1))/((p-1)^r - (-1)^r)`.
`Br r n` and `Cr r` of `TheoremB34.lean` are the product and the constant exactly as printed.

Route: induction on `r` from the lab's `theoremB3`. The step uses
`ν_{r+1}(n) = Σ_p log p · ν_r(n - p)`, `TheoremBRec.lean`; the divisor expansion
`Br r m = Σ_{d ∣ m, d squarefree} g_r(d)` and the Euler product identity
`Σ_{(d, n) = 1} g_r(d)/φ(d) = (C_{r+1}/C_r) Br (r+1) n`, `EulerR.lean`; the prime number theorem in
progressions with weight `(n - p)^{r-1}` for each fixed modulus, from the lab's unconditional
Siegel-Walfisz, and a Brun-Titchmarsh bound uniform in the modulus for the tail, `APPow.lean`.
Hardy and Littlewood assume Hypothesis R; here every case `r ≥ 3` is PROVED with no hypothesis.

Ternary Goldbach is Helfgott's theorem. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- The main term of (3.32), `(2 C_r/(r-1)!) n^{r-1} Br r n`. -/
noncomputable def Mr (r n : ℕ) : ℝ :=
  2 * Cr r / (Nat.factorial (r - 1) : ℝ) * (n : ℝ) ^ (r - 1) * Br r n

/-- **Theorem B, (3.32)**, for one `r`, in the `ε` form of `∼`. -/
def theoremB_stmt (r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n % 2 = r % 2 → n₀ ≤ n →
    |nur r n - Mr r n| ≤ ε * Mr r n

/-! ### Small helpers -/

lemma small_pow_log (s j : ℕ) (c T : ℝ) (hc : 0 ≤ c) (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, c * ((n : ℝ) + 1) ^ s * Real.log n ^ j ≤ T * (n : ℝ) ^ (s + 1) := by
  filter_upwards [ThmE.grow j (2 ^ s * c / T + 1) (by positivity), eventually_ge_atTop 3]
    with n hn h3
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < Real.log n := Real.log_pos hn1
  have hLj : 0 < Real.log n ^ j := pow_pos hL j
  have h1 : Real.log n ^ j * (2 ^ s * c / T + 1) ≤ n := by
    rw [le_div_iff₀ hLj] at hn; linarith
  have h2 : ((n : ℝ) + 1) ^ s ≤ 2 ^ s * (n : ℝ) ^ s := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) s
  have h3' : 2 ^ s * c * Real.log n ^ j ≤ T * n := by
    have : 2 ^ s * c / T * Real.log n ^ j ≤ n := by nlinarith
    have e : 2 ^ s * c * Real.log n ^ j = T * (2 ^ s * c / T * Real.log n ^ j) := by
      field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left this hT.le
  calc c * ((n : ℝ) + 1) ^ s * Real.log n ^ j
      ≤ c * (2 ^ s * (n : ℝ) ^ s) * Real.log n ^ j := by gcongr
    _ = (2 ^ s * c * Real.log n ^ j) * (n : ℝ) ^ s := by ring
    _ ≤ (T * n) * (n : ℝ) ^ s := by gcongr
    _ = T * (n : ℝ) ^ (s + 1) := by ring

lemma small_sqrt (s : ℕ) (c T : ℝ) (hc : 0 ≤ c) (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ s ≤ T * (n : ℝ) ^ (s + 1) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop (c / T), eventually_ge_atTop 1] with n hn h1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = n := by
    rw [← Real.rpow_add' hn0 (by norm_num)]; norm_num
  have hpos : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hn0 _
  have : c ≤ T * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [div_le_iff₀ hT] at hn; linarith
  calc c * (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ s
      ≤ T * (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ s := by gcongr
    _ = T * (n : ℝ) ^ (s + 1) := by rw [mul_assoc T, hsq]; ring

/-- If `d ∣ n - p` for a prime `p ≤ n` and `(d, n) > 1`, then `p ∣ d`. -/
lemma prime_dvd_of_not_coprime {d n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) (hd : 0 < d)
    (hdvd : d ∣ n - p) (hc : ¬ Nat.Coprime d n) : p ≤ d := by
  obtain ⟨q, hq, hqd, hqn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have h1 : q ∣ n - p := hqd.trans hdvd
  have h2 : q ∣ p := by
    have := Nat.dvd_sub hqn h1
    rwa [Nat.sub_sub_self hpn] at this
  have h3 : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h2
  subst h3
  exact Nat.le_of_dvd hd hqd

/-- `p % d = n % d` iff `d ∣ n - p`, for `p ≤ n`. -/
lemma mod_eq_iff_dvd_sub {d n p : ℕ} (hpn : p ≤ n) : p % d = n % d ↔ d ∣ n - p := by
  show Nat.ModEq d p n ↔ _
  exact Nat.modEq_iff_dvd' hpn

/-! ### The divisor expansion of the main term -/

/-- `S_d(n) = Σ_{p ≤ n, p ≡ n mod d} log p (n - p)^s`. -/
noncomputable def Ssum (s d n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d),
    Real.log p * ((n : ℝ) - p) ^ s

lemma Ssum_nonneg (s d n : ℕ) : 0 ≤ Ssum s d n := by
  unfold Ssum
  refine sum_nonneg fun p hp => ?_
  rw [mem_filter, mem_range] at hp
  have h1 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)
  have h2 : (0 : ℝ) ≤ (n : ℝ) - p := by
    have : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
    linarith
  positivity

lemma Mr_succ (s m : ℕ) :
    Mr (s + 1) m = 2 * Cr (s + 1) / (Nat.factorial s : ℝ) * (m : ℝ) ^ s * Br (s + 1) m := by
  simp [Mr]

/-- Pointwise: `(n - p)^s Br (s+1) (n - p) = Σ_{d ≤ n squarefree, d ∣ n - p} g(d) (n - p)^s`. -/
lemma pointwise_expand (s n p : ℕ) (hs : 1 ≤ s) (hpn : p ≤ n) :
    (((n - p : ℕ) : ℝ)) ^ s * Br (s + 1) (n - p) =
      ∑ d ∈ (Finset.range (n + 1)).filter Squarefree,
        if p % d = n % d then gr (s + 1) d * ((n : ℝ) - p) ^ s else 0 := by
  have hcast : (((n - p : ℕ) : ℝ)) = (n : ℝ) - p := by
    rw [Nat.cast_sub hpn]
  rcases Nat.eq_zero_or_pos (n - p) with h0 | hpos
  · have hnp : n = p := by omega
    subst hnp
    simp only [Nat.sub_self, Nat.cast_zero, sub_self]
    rw [zero_pow (by omega), zero_mul]
    refine (sum_eq_zero fun d _ => ?_).symm
    split_ifs <;> simp
  · rw [Br_eq_sum (s + 1) (n - p) hpos (by omega), hcast, mul_sum]
    rw [← sum_filter]
    have hset : ((Finset.range (n + 1)).filter Squarefree).filter (fun d => p % d = n % d) =
        (n - p).divisors.filter Squarefree := by
      ext d
      simp only [mem_filter, mem_range, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, hsq⟩, hmod⟩
        exact ⟨⟨(mod_eq_iff_dvd_sub hpn).mp hmod, by omega⟩, hsq⟩
      · rintro ⟨⟨hdvd, hne⟩, hsq⟩
        refine ⟨⟨?_, hsq⟩, (mod_eq_iff_dvd_sub hpn).mpr hdvd⟩
        have := Nat.le_of_dvd hpos hdvd
        omega
    rw [hset]
    refine sum_congr rfl fun d _ => by ring

/-- The main-term sum as a divisor sum of `S_d(n)`. -/
lemma main_expand (s n : ℕ) (hs : 1 ≤ s) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p * Mr (s + 1) (n - p) =
      2 * Cr (s + 1) / (Nat.factorial s : ℝ) *
        ∑ d ∈ (Finset.range (n + 1)).filter Squarefree, gr (s + 1) d * Ssum s d n := by
  have h1 : ∀ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      Real.log p * Mr (s + 1) (n - p) =
        2 * Cr (s + 1) / (Nat.factorial s : ℝ) *
          ∑ d ∈ (Finset.range (n + 1)).filter Squarefree,
            if p % d = n % d then gr (s + 1) d * (Real.log p * ((n : ℝ) - p) ^ s) else 0 := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    rw [Mr_succ, mul_assoc (2 * Cr (s + 1) / _), pointwise_expand s n p hs (by omega)]
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  rw [sum_congr rfl h1, ← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  unfold Ssum
  rw [mul_sum, sum_filter, sum_filter]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime <;> by_cases hm : p % d = n % d <;> simp [hp, hm]

/-! ### The head: moduli `d ≤ D` -/

lemma Ssum_noncop (s d n D : ℕ) (hd : 0 < d) (hdD : d ≤ D) (hc : ¬ Nat.Coprime d n) :
    Ssum s d n ≤ Real.log 4 * D * (n : ℝ) ^ s := by
  unfold Ssum
  calc ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d),
        Real.log p * ((n : ℝ) - p) ^ s
      ≤ ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d),
        Real.log p * (n : ℝ) ^ s := by
        refine sum_le_sum fun p hp => ?_
        rw [mem_filter, mem_range] at hp
        have h1 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)
        have hp0 : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
        have h2 : (0 : ℝ) ≤ (n : ℝ) - p := by linarith
        have h3 : ((n : ℝ) - p) ^ s ≤ (n : ℝ) ^ s :=
          pow_le_pow_left₀ h2 (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]) s
        exact mul_le_mul_of_nonneg_left h3 h1
    _ ≤ ∑ p ∈ (Finset.range (D + 1)).filter Nat.Prime, Real.log p * (n : ℝ) ^ s := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
        · intro p hp
          rw [mem_filter, mem_range] at hp ⊢
          refine ⟨?_, hp.2.1⟩
          have := prime_dvd_of_not_coprime hp.2.1 (by omega) hd
            ((mod_eq_iff_dvd_sub (by omega)).mp hp.2.2) hc
          omega
        · rw [mem_filter] at hp
          have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
          positivity
    _ = (∑ p ∈ (Finset.range (D + 1)).filter Nat.Prime, Real.log p) * (n : ℝ) ^ s := by
        rw [sum_mul]
    _ ≤ Real.log 4 * D * (n : ℝ) ^ s := by
        gcongr
        exact theta_le D

/-- The head estimate for a fixed `D`. -/
lemma head_estimate (s D : ℕ) (Kg : ℝ) (hKg : ∀ N : ℕ,
      ∑ d ∈ (Finset.range N).filter Squarefree, |gr (s + 1) d| ≤ Kg) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n : ℕ in atTop,
      |∑ d ∈ (Finset.range (D + 1)).filter Squarefree, gr (s + 1) d * Ssum s d n
        - (n : ℝ) ^ (s + 1) / (s + 1) *
          ∑ d ∈ (Finset.range (D + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n),
            gr (s + 1) d / (Nat.totient d : ℝ)| ≤ T * (n : ℝ) ^ (s + 1) := by
  intro T hT
  have hKg0 : 0 ≤ Kg := (sum_nonneg fun _ _ => abs_nonneg _).trans (hKg 0)
  set δ := T / (2 * (Kg + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  -- PNT in progressions for every modulus `1 ≤ d ≤ D` at once
  have hap : ∀ᶠ n : ℕ in atTop, ∀ d ∈ Finset.range (D + 1), 1 ≤ d → Nat.Coprime d n →
      |Ssum s d n - (n : ℝ) ^ (s + 1) / ((s + 1) * (Nat.totient d : ℝ))| ≤
        δ * (n : ℝ) ^ (s + 1) := by
    rw [eventually_all_finset]
    intro d _
    by_cases hd : 1 ≤ d
    · obtain ⟨n₀, hn₀⟩ := ap_sum_pow s d hd δ hδ0
      filter_upwards [eventually_ge_atTop n₀] with n hn _ hc
      have := hn₀ n hn n (Nat.Coprime.symm hc)
      unfold Ssum
      push_cast at this ⊢
      exact this
    · exact Eventually.of_forall fun n h => absurd h hd
  filter_upwards [hap, small_pow_log s 0 (Kg * Real.log 4 * D) (T / 2)
    (by positivity) (by positivity)] with n hn hsmall
  have hn' : Kg * Real.log 4 * D * (n : ℝ) ^ s ≤ T / 2 * (n : ℝ) ^ (s + 1) := by
    have h := hsmall
    simp only [pow_zero, mul_one] at h
    have : (n : ℝ) ^ s ≤ ((n : ℝ) + 1) ^ s :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) s
    have h4 : 0 ≤ Kg * Real.log 4 * D := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h4]
  -- rewrite the difference as one sum over squarefree `d ≤ D`
  have hsplit : (n : ℝ) ^ (s + 1) / (s + 1) *
      ∑ d ∈ (Finset.range (D + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n),
        gr (s + 1) d / (Nat.totient d : ℝ) =
      ∑ d ∈ (Finset.range (D + 1)).filter Squarefree,
        gr (s + 1) d * (if Nat.Coprime d n then
          (n : ℝ) ^ (s + 1) / ((s + 1) * (Nat.totient d : ℝ)) else 0) := by
    rw [mul_sum]
    rw [show (Finset.range (D + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n) =
      ((Finset.range (D + 1)).filter Squarefree).filter (fun d => Nat.Coprime d n) by
        rw [filter_filter]]
    rw [sum_filter]
    refine sum_congr rfl fun d _ => ?_
    split_ifs
    · field_simp
    · simp
  rw [hsplit, ← sum_sub_distrib]
  calc |∑ d ∈ (Finset.range (D + 1)).filter Squarefree,
        (gr (s + 1) d * Ssum s d n - gr (s + 1) d * (if Nat.Coprime d n then
          (n : ℝ) ^ (s + 1) / ((s + 1) * (Nat.totient d : ℝ)) else 0))|
      ≤ ∑ d ∈ (Finset.range (D + 1)).filter Squarefree,
        |gr (s + 1) d| * (δ * (n : ℝ) ^ (s + 1) + Real.log 4 * D * (n : ℝ) ^ s) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
        rw [← mul_sub, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [mem_filter, mem_range] at hd
        have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; exact not_squarefree_zero hd.2)
        have hpos1 : 0 ≤ δ * (n : ℝ) ^ (s + 1) := by positivity
        have hpos2 : 0 ≤ Real.log 4 * D * (n : ℝ) ^ s := by positivity
        split_ifs with hc
        · have := hn d (mem_range.mpr hd.1) hd1 hc
          linarith
        · rw [sub_zero, abs_of_nonneg (Ssum_nonneg s d n)]
          have := Ssum_noncop s d n D hd1 (by omega) hc
          linarith
    _ = (∑ d ∈ (Finset.range (D + 1)).filter Squarefree, |gr (s + 1) d|) *
        (δ * (n : ℝ) ^ (s + 1) + Real.log 4 * D * (n : ℝ) ^ s) := by rw [sum_mul]
    _ ≤ Kg * (δ * (n : ℝ) ^ (s + 1) + Real.log 4 * D * (n : ℝ) ^ s) := by
        gcongr
        exact hKg (D + 1)
    _ ≤ T * (n : ℝ) ^ (s + 1) := by
        have e1 : Kg * δ ≤ T / 2 := by
          rw [hδ]
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have : Kg * (δ * (n : ℝ) ^ (s + 1)) ≤ T / 2 * (n : ℝ) ^ (s + 1) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right e1 (by positivity)
        nlinarith

/-! ### The tail: moduli `D < d ≤ n` -/

lemma Ssum_le (s d n : ℕ) :
    Ssum s d n ≤ (n : ℝ) ^ s *
      ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d), Real.log p := by
  unfold Ssum
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  rw [mem_filter, mem_range] at hp
  have h1 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)
  have hp0 : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
  have h3 : ((n : ℝ) - p) ^ s ≤ (n : ℝ) ^ s :=
    pow_le_pow_left₀ (by linarith) (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]) s
  nlinarith

lemma tail_estimate (s : ℕ) (hs : 2 ≤ s) :
    ∀ T : ℝ, 0 < T → ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∀ᶠ n : ℕ in atTop,
      |∑ d ∈ (Finset.Ioc D n).filter Squarefree, gr (s + 1) d * Ssum s d n| ≤
        T * (n : ℝ) ^ (s + 1) := by
  intro T hT
  obtain ⟨A, B, n₁, hAB⟩ := ap_log_sum_le
  obtain ⟨Kt, hKt⟩ := gr_tail (s + 1) (by omega)
  obtain ⟨Kg, hKg⟩ := gr_sum_bdd (s + 1) (by omega)
  have hKg0 : 0 ≤ Kg := (sum_nonneg fun _ _ => abs_nonneg _).trans (hKg 0)
  have hKt0 : 0 ≤ Kt := by
    have := hKt 1 0 le_rfl
    simp at this
    exact this
  -- choose D₁ with |A| Kt/√D ≤ T/2
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → |A| * (Kt / Real.sqrt D) ≤ T / 2 := by
    have hlim : Tendsto (fun D : ℕ => |A| * (Kt / Real.sqrt D)) atTop (nhds 0) := by
      have h1 : Tendsto (fun D : ℕ => Real.sqrt D) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have h2 := (h1.inv_tendsto_atTop).const_mul Kt
      simpa [div_eq_mul_inv] using h2.const_mul |A|
    obtain ⟨D₁, h⟩ := eventually_atTop.mp (hlim.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < T / 2)))
    exact ⟨D₁, h⟩
  refine ⟨max D₁ 1, fun D hD => ?_⟩
  filter_upwards [eventually_ge_atTop n₁, small_sqrt s (|B| * Kg) (T / 2) (by positivity)
    (by positivity)] with n hn hsq
  have hD1 : 1 ≤ D := le_of_max_le_right hD
  calc |∑ d ∈ (Finset.Ioc D n).filter Squarefree, gr (s + 1) d * Ssum s d n|
      ≤ ∑ d ∈ (Finset.Ioc D n).filter Squarefree, |gr (s + 1) d| *
          ((n : ℝ) ^ s * (|A| * n / (Nat.totient d : ℝ) + |B| * (n : ℝ) ^ ((1 : ℝ) / 2))) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
        rw [abs_mul, abs_of_nonneg (Ssum_nonneg s d n)]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [mem_filter, mem_Ioc] at hd
        refine (Ssum_le s d n).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        refine (hAB n hn d n (by omega)).trans ?_
        have hφ : (0 : ℝ) ≤ Nat.totient d := Nat.cast_nonneg _
        have : A * n / (Nat.totient d : ℝ) ≤ |A| * n / (Nat.totient d : ℝ) := by
          gcongr; exact le_abs_self A
        have : B * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ |B| * (n : ℝ) ^ ((1 : ℝ) / 2) := by
          gcongr; exact le_abs_self B
        linarith
    _ = |A| * (n : ℝ) ^ (s + 1) *
          (∑ d ∈ (Finset.Ioc D n).filter Squarefree, |gr (s + 1) d| / (Nat.totient d : ℝ)) +
        |B| * (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ s *
          (∑ d ∈ (Finset.Ioc D n).filter Squarefree, |gr (s + 1) d|) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun d _ => ?_
        ring
    _ ≤ |A| * (n : ℝ) ^ (s + 1) * (Kt / Real.sqrt D) + |B| * (n : ℝ) ^ ((1 : ℝ) / 2) *
          (n : ℝ) ^ s * Kg := by
        gcongr
        · exact hKt D n hD1
        · refine le_trans ?_ (hKg (n + 1))
          refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _
          intro d hd
          rw [mem_filter, mem_Ioc] at hd
          rw [mem_filter, mem_range]
          exact ⟨by omega, hd.2⟩
    _ ≤ T / 2 * (n : ℝ) ^ (s + 1) + T / 2 * (n : ℝ) ^ (s + 1) := by
        refine add_le_add ?_ ?_
        · have := hD₁ D (le_of_max_le_left hD)
          calc |A| * (n : ℝ) ^ (s + 1) * (Kt / Real.sqrt D)
              = (|A| * (Kt / Real.sqrt D)) * (n : ℝ) ^ (s + 1) := by ring
            _ ≤ T / 2 * (n : ℝ) ^ (s + 1) := by gcongr
        · calc |B| * (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ s * Kg
              = |B| * Kg * (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ s := by ring
            _ ≤ T / 2 * (n : ℝ) ^ (s + 1) := hsq
    _ = T * (n : ℝ) ^ (s + 1) := by ring


/-! ### The error carried from `ν_{s+1}` -/

lemma log_le_log_nat {m n : ℕ} (h : m ≤ n) : Real.log m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

lemma Mr_bounds (s : ℕ) (K : ℝ) (hK : ∀ m : ℕ, 0 ≤ Br (s + 1) m ∧ Br (s + 1) m ≤ K)
    (hcs : 0 ≤ 2 * Cr (s + 1) / (Nat.factorial s : ℝ)) {m n : ℕ} (h : m ≤ n) :
    0 ≤ Mr (s + 1) m ∧
      Mr (s + 1) m ≤ 2 * Cr (s + 1) / (Nat.factorial s : ℝ) * K * (n : ℝ) ^ s := by
  rw [Mr_succ]
  have h0 := (hK m).1
  have h1 : (m : ℝ) ^ s ≤ (n : ℝ) ^ s :=
    pow_le_pow_left₀ (Nat.cast_nonneg m) (by exact_mod_cast h) s
  constructor
  · positivity
  · calc 2 * Cr (s + 1) / (Nat.factorial s : ℝ) * (m : ℝ) ^ s * Br (s + 1) m
        ≤ 2 * Cr (s + 1) / (Nat.factorial s : ℝ) * (n : ℝ) ^ s * K := by
          gcongr; exact (hK m).2
      _ = _ := by ring

lemma err_estimate (s : ℕ) (hs : 2 ≤ s) (IH : theoremB_stmt (s + 1)) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n : ℕ in atTop, n % 2 = (s + 2) % 2 →
      |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
          Real.log p * (nur (s + 1) (n - p) - Mr (s + 1) (n - p))| ≤ T * (n : ℝ) ^ (s + 1) := by
  intro T hT
  obtain ⟨c, K, hc, hBK⟩ := Br_bounds (s + 1) (by omega)
  have hK : ∀ m : ℕ, 0 ≤ Br (s + 1) m ∧ Br (s + 1) m ≤ K :=
    fun m => ⟨hc.le.trans (hBK m).1, (hBK m).2⟩
  have hK0 : 0 ≤ K := (hK 0).1.trans (hK 0).2
  set cs := 2 * Cr (s + 1) / (Nat.factorial s : ℝ) with hcsdef
  have hcs : 0 ≤ cs := by
    have := Cr_pos (s + 1) (by omega); positivity
  set η := T / (4 * (cs * K * Real.log 4 + 1)) with hη
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hη0 : 0 < η := by positivity
  obtain ⟨m₀, hm₀⟩ := IH η hη0
  set C₀ := ((m₀ : ℝ) + 1) ^ s * Real.log m₀ ^ (s + 1) + cs * K * (m₀ : ℝ) ^ s with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    have := Real.log_natCast_nonneg m₀; positivity
  filter_upwards [eventually_ge_atTop 3,
    small_pow_log s 1 (C₀ * m₀) (T / 4) (by positivity) (by positivity),
    small_pow_log s (s + 1) (Real.log 2) (T / 4) (Real.log_nonneg (by norm_num)) (by positivity),
    small_pow_log s 0 (Real.log 2 * (cs * K)) (T / 4) (by positivity) (by positivity)]
    with n hn3 hsm1 hsm2 hsm3 hpar
  set Big := ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 1) + cs * K * (n : ℝ) ^ s with hBig
  have hLn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- a pointwise bound on the error at every `m ≤ n`
  have hgen : ∀ m : ℕ, m ≤ n → |nur (s + 1) m - Mr (s + 1) m| ≤
      ((m : ℝ) + 1) ^ s * Real.log m ^ (s + 1) + cs * K * (m : ℝ) ^ s := by
    intro m hm
    have h1 := nur_le_pow s m
    have h2 := nur_nonneg (s + 1) m
    have h3 := Mr_bounds s K hK hcs (le_refl m)
    rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
  have hpt : ∀ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      Real.log p * |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| ≤
        Real.log p * (η * (cs * K * (n : ℝ) ^ s)) +
        (if n - p < m₀ then Real.log n * C₀ else 0) +
        (if p = 2 then Real.log 2 * Big else 0) := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    have hlpn : Real.log p ≤ Real.log n := log_le_log_nat (by omega)
    have hA : 0 ≤ Real.log p * (η * (cs * K * (n : ℝ) ^ s)) := by positivity
    have hB : 0 ≤ (if n - p < m₀ then Real.log n * C₀ else 0) := by
      split_ifs <;> positivity
    have hC : 0 ≤ (if p = 2 then Real.log 2 * Big else 0) := by
      split_ifs <;> positivity
    by_cases h2 : p = 2
    · subst h2
      rw [if_pos rfl]
      have := hgen (n - 2) (by omega)
      have e1 : ((n - 2 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - 2 ≤ n)
        linarith
      have e2 : Real.log ((n - 2 : ℕ) : ℝ) ≤ Real.log n := log_le_log_nat (by omega)
      have e3 : (((n - 2 : ℕ) : ℝ) + 1) ^ s * Real.log ((n - 2 : ℕ) : ℝ) ^ (s + 1) ≤
          ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 1) := by
        have := Real.log_natCast_nonneg (n - 2)
        gcongr
      have e4 : cs * K * ((n - 2 : ℕ) : ℝ) ^ s ≤ cs * K * (n : ℝ) ^ s := by
        gcongr; exact_mod_cast (by omega : n - 2 ≤ n)
      have : |nur (s + 1) (n - 2) - Mr (s + 1) (n - 2)| ≤ Big := by linarith
      have := mul_le_mul_of_nonneg_left this hlp
      push_cast at this hA ⊢
      linarith
    by_cases hsmall : n - p < m₀
    · rw [if_pos hsmall]
      have := hgen (n - p) (by omega)
      have e1 : ((n - p : ℕ) : ℝ) + 1 ≤ (m₀ : ℝ) + 1 := by
        have : ((n - p : ℕ) : ℝ) ≤ m₀ := by exact_mod_cast hsmall.le
        linarith
      have e2 : Real.log ((n - p : ℕ) : ℝ) ≤ Real.log m₀ := log_le_log_nat hsmall.le
      have e3 : (((n - p : ℕ) : ℝ) + 1) ^ s * Real.log ((n - p : ℕ) : ℝ) ^ (s + 1) ≤
          ((m₀ : ℝ) + 1) ^ s * Real.log m₀ ^ (s + 1) := by
        have := Real.log_natCast_nonneg (n - p)
        gcongr
      have e4 : cs * K * ((n - p : ℕ) : ℝ) ^ s ≤ cs * K * (m₀ : ℝ) ^ s := by
        gcongr
      have h5 : |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| ≤ C₀ := by linarith
      have h6 : Real.log p * |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| ≤ Real.log n * C₀ :=
        mul_le_mul hlpn h5 (abs_nonneg _) hLn
      linarith
    · rw [if_neg hsmall]
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.2.eq_two_or_odd'.resolve_left h2)
      have hm : (n - p) % 2 = (s + 1) % 2 := by omega
      have h5 := hm₀ (n - p) hm (by omega)
      have h6 := (Mr_bounds s K hK hcs (show n - p ≤ n by omega)).2
      have h7 : |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| ≤ η * (cs * K * (n : ℝ) ^ s) :=
        h5.trans (mul_le_mul_of_nonneg_left h6 hη0.le)
      have := mul_le_mul_of_nonneg_left h7 hlp
      linarith
  -- sum the pointwise bounds
  have hcard : #(((Finset.range (n + 1)).filter Nat.Prime).filter (fun p => n - p < m₀)) ≤ m₀ := by
    calc _ ≤ #((Finset.range m₀).image (fun j => n - j)) := by
          refine card_le_card fun p hp => ?_
          rw [mem_filter, mem_filter, mem_range] at hp
          rw [mem_image]
          exact ⟨n - p, mem_range.mpr hp.2, by omega⟩
      _ ≤ #(Finset.range m₀) := card_image_le
      _ = m₀ := card_range m₀
  calc |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        Real.log p * (nur (s + 1) (n - p) - Mr (s + 1) (n - p))|
      ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        Real.log p * |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| := by
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun p hp => ?_))
        rw [mem_filter] at hp
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))]
    _ ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        (Real.log p * (η * (cs * K * (n : ℝ) ^ s)) +
          (if n - p < m₀ then Real.log n * C₀ else 0) +
          (if p = 2 then Real.log 2 * Big else 0)) := sum_le_sum hpt
    _ = (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p) * (η * (cs * K * (n : ℝ) ^ s)) +
        (#(((Finset.range (n + 1)).filter Nat.Prime).filter (fun p => n - p < m₀)) : ℝ) *
          (Real.log n * C₀) + Real.log 2 * Big := by
        rw [sum_add_distrib, sum_add_distrib, sum_mul, ← sum_filter, sum_const, nsmul_eq_mul]
        congr 1
        rw [sum_ite_eq']
        rw [if_pos]
        rw [mem_filter, mem_range]
        exact ⟨by omega, Nat.prime_two⟩
    _ ≤ (Real.log 4 * n) * (η * (cs * K * (n : ℝ) ^ s)) + (m₀ : ℝ) * (Real.log n * C₀) +
        Real.log 2 * Big := by
        gcongr
        exact theta_le n
    _ ≤ T / 4 * (n : ℝ) ^ (s + 1) + T / 4 * (n : ℝ) ^ (s + 1) +
        (T / 4 * (n : ℝ) ^ (s + 1) + T / 4 * (n : ℝ) ^ (s + 1)) := by
        have hns : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ s := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
        refine add_le_add (add_le_add ?_ ?_) ?_
        · have e : (Real.log 4 * n) * (η * (cs * K * (n : ℝ) ^ s)) =
              (η * (cs * K * Real.log 4)) * (n : ℝ) ^ (s + 1) := by ring
          rw [e]
          gcongr
          rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg (mul_nonneg hcs hK0) hl4.le]
        · calc (m₀ : ℝ) * (Real.log n * C₀) = C₀ * m₀ * 1 * Real.log n ^ 1 := by ring
            _ ≤ C₀ * m₀ * ((n : ℝ) + 1) ^ s * Real.log n ^ 1 := by gcongr
            _ ≤ _ := hsm1
        · rw [hBig, mul_add]
          refine add_le_add ?_ ?_
          · calc Real.log 2 * (((n : ℝ) + 1) ^ s * Real.log n ^ (s + 1)) =
                Real.log 2 * ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 1) := by ring
              _ ≤ _ := hsm2
          · have : (n : ℝ) ^ s ≤ ((n : ℝ) + 1) ^ s :=
              pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) s
            calc Real.log 2 * (cs * K * (n : ℝ) ^ s) ≤
                Real.log 2 * (cs * K) * ((n : ℝ) + 1) ^ s * Real.log n ^ 0 := by
                  rw [pow_zero, mul_one]
                  have : 0 ≤ Real.log 2 * (cs * K) := by
                    have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num); positivity
                  nlinarith
              _ ≤ _ := hsm3
    _ = T * (n : ℝ) ^ (s + 1) := by ring

/-! ### The induction step and Theorem B for every `r ≥ 3` -/

lemma split_range (n D : ℕ) (hD : D ≤ n) (f : ℕ → ℝ) :
    ∑ d ∈ (Finset.range (n + 1)).filter Squarefree, f d =
      ∑ d ∈ (Finset.range (D + 1)).filter Squarefree, f d +
        ∑ d ∈ (Finset.Ioc D n).filter Squarefree, f d := by
  rw [sum_filter, sum_filter, sum_filter, ← Finset.sum_range_add_sum_Ico _ (by omega : D + 1 ≤ n + 1)]
  congr 1
  rw [show Finset.Ico (D + 1) (n + 1) = Finset.Ioc D n by
    ext x; simp only [mem_Ico, mem_Ioc]; omega]

theorem theoremB_step (s : ℕ) (hs : 2 ≤ s) (IH : theoremB_stmt (s + 1)) :
    theoremB_stmt (s + 2) := by
  intro ε hε
  obtain ⟨c₂', K₂, hc₂', hB₂⟩ := Br_bounds (s + 2) (by omega)
  have hC1 := Cr_pos (s + 1) (by omega)
  have hC2 := Cr_pos (s + 2) (by omega)
  set cs := 2 * Cr (s + 1) / (Nat.factorial s : ℝ) with hcsdef
  have hcs : 0 < cs := by positivity
  set c₂ := 2 * Cr (s + 2) / (Nat.factorial (s + 1) : ℝ) * c₂' with hc₂def
  have hc₂ : 0 < c₂ := by positivity
  set τ := ε * c₂ / 4 with hτ
  have hτ0 : 0 < τ := by positivity
  obtain ⟨D₁, hD₁⟩ := tail_estimate s hs (τ / cs) (by positivity)
  obtain ⟨D₀, hD₀⟩ := euler_avg_r (s + 1) (by omega) (τ * (s + 1) / cs) (by positivity)
  set D := max D₁ D₀ with hDdef
  obtain ⟨Kg, hKg⟩ := gr_sum_bdd (s + 1) (by omega)
  have hev := ((err_estimate s hs IH τ hτ0).and (hD₁ D (le_max_left _ _))).and
    ((head_estimate s D Kg hKg (τ / cs) (by positivity)).and (eventually_ge_atTop (D + 1)))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀, fun n hpar hn => ?_⟩
  obtain ⟨⟨hErr, hTail⟩, hHead, hnD⟩ := hn₀ n hn
  have hErr := hErr hpar
  have hEu := hD₀ (D + 1) n (by omega) (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the main term
  have hMr : Mr (s + 2) n = cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
      (Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n) := by
    rw [Mr, show s + 2 - 1 = s + 1 by omega, hcsdef, Nat.factorial_succ]
    push_cast
    field_simp
  have hMlow : c₂ * (n : ℝ) ^ (s + 1) ≤ Mr (s + 2) n := by
    rw [Mr, show s + 2 - 1 = s + 1 by omega, hc₂def]
    have := (hB₂ n).1
    have : 0 ≤ 2 * Cr (s + 2) / (Nat.factorial (s + 1) : ℝ) * (n : ℝ) ^ (s + 1) := by positivity
    nlinarith
  -- the decomposition
  set H := ∑ d ∈ (Finset.range (D + 1)).filter Squarefree, gr (s + 1) d * Ssum s d n
  set Tl := ∑ d ∈ (Finset.Ioc D n).filter Squarefree, gr (s + 1) d * Ssum s d n
  set Eu := ∑ d ∈ (Finset.range (D + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n),
    gr (s + 1) d / (Nat.totient d : ℝ)
  set Er := ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
    Real.log p * (nur (s + 1) (n - p) - Mr (s + 1) (n - p))
  have hdec : nur (s + 2) n = cs * (H + Tl) + Er := by
    rw [show s + 2 = (s + 1) + 1 by omega, nur_succ]
    have : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p * nur (s + 1) (n - p) =
        ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p * Mr (s + 1) (n - p) + Er := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun p _ => by ring
    rw [this, main_expand s n (by omega), split_range n D (by omega)]
  have key : nur (s + 2) n - Mr (s + 2) n =
      cs * (H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu) + cs * Tl +
      cs * ((n : ℝ) ^ (s + 1) / (s + 1)) * (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n) +
      Er := by
    rw [hdec, hMr]; ring
  have b1 : |cs * (H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu)| ≤ τ * (n : ℝ) ^ (s + 1) := by
    rw [abs_mul, abs_of_pos hcs]
    calc cs * |H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu| ≤ cs * (τ / cs * (n : ℝ) ^ (s + 1)) := by
          gcongr
      _ = τ * (n : ℝ) ^ (s + 1) := by field_simp
  have b2 : |cs * Tl| ≤ τ * (n : ℝ) ^ (s + 1) := by
    rw [abs_mul, abs_of_pos hcs]
    calc cs * |Tl| ≤ cs * (τ / cs * (n : ℝ) ^ (s + 1)) := by gcongr
      _ = τ * (n : ℝ) ^ (s + 1) := by field_simp
  have b3 : |cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
      (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n)| ≤ τ * (n : ℝ) ^ (s + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc cs * ((n : ℝ) ^ (s + 1) / (s + 1)) * |Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n|
        ≤ cs * ((n : ℝ) ^ (s + 1) / (s + 1)) * (τ * (s + 1) / cs) := by gcongr
      _ = τ * (n : ℝ) ^ (s + 1) := by field_simp
  rw [key]
  calc |cs * (H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu) + cs * Tl +
        cs * ((n : ℝ) ^ (s + 1) / (s + 1)) * (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n) +
        Er|
      ≤ |cs * (H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu)| + |cs * Tl| +
        |cs * ((n : ℝ) ^ (s + 1) / (s + 1)) * (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n)| +
        |Er| := by
        have t1 := abs_add_le (cs * (H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu) + cs * Tl +
          cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
            (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n)) Er
        have t2 := abs_add_le (cs * (H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu) + cs * Tl)
          (cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
            (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n))
        have t3 := abs_add_le (cs * (H - (n : ℝ) ^ (s + 1) / (s + 1) * Eu)) (cs * Tl)
        linarith
    _ ≤ τ * (n : ℝ) ^ (s + 1) + τ * (n : ℝ) ^ (s + 1) + τ * (n : ℝ) ^ (s + 1) +
        τ * (n : ℝ) ^ (s + 1) := by gcongr
    _ = ε * (c₂ * (n : ℝ) ^ (s + 1)) := by rw [hτ]; ring
    _ ≤ ε * Mr (s + 2) n := by gcongr

theorem theoremB_three : theoremB_stmt 3 := by
  intro ε hε
  obtain ⟨n₀, h⟩ := theoremB3 ε hε
  refine ⟨n₀, fun n hpar hn => ?_⟩
  have hodd : Odd n := Nat.odd_iff.mpr (by simpa using hpar)
  have e : Mr 3 n = 2 * Cr 3 / 2 * (n : ℝ) ^ 2 * Br 3 n := by
    simp [Mr]
  rw [e]
  exact h n hodd hn

/-- **Hardy-Littlewood 1923, Theorem B, (3.32), for every `r ≥ 3`**, PROVED with no hypothesis:
if `r ≥ 3` and `n ≡ r mod 2` then
`ν_r(n) ∼ (2 C_r/(r-1)!) n^{r-1} ∏_{p ∣ n, p odd} ((p-1)^r + (-1)^r (p-1))/((p-1)^r - (-1)^r)`. -/
theorem theoremB : ∀ r : ℕ, 3 ≤ r → theoremB_stmt r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact theoremB_three
  | succ r hr ih =>
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    exact theoremB_step s (by omega) ih

end LeanLab.HardyLittlewood1923

