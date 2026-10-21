module

public import LeanLab.HardyLittlewood1923.TheoremC
public import LeanLab.HardyLittlewood1923.TheoremE

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5713, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III, Theorem B, (3.32), cases r = 3 and r = 4

Read from `papers/P0004.pdf`, Acta Math. 44, p. 29, Theorem B: if `r ≥ 3` and `n`, `r` have like
parity, then
`ν_r(n) ∼ (2 C_r/(r-1)!) n^{r-1} ∏_{p ∣ n, p odd} ((p-1)^r + (-1)^r (p-1))/((p-1)^r - (-1)^r)`,
`C_r = ∏_{ϖ ≥ 3} (1 - (-1)^r/(ϖ-1)^r)`. The product and the constant are written below exactly as
in the paper, as `Br r n` and `Cr r`, and identified with the lab's `Pi3`, `Pi4`, `C3`, `C4`.

Route: `ν_r ≈ N_r (log n)^r` by Theorem C; `N_3` differs from `N̄_3` by at most 3 for odd `n`, and
`N_4` from `N̄_4` by at most `12 (n+1)^2` tuples having an entry below 3; then Theorem D and Theorem E,
with the lower bound `Nr_lower` absorbing the counting error. Hardy and Littlewood assume
Hypothesis R; here the cases r = 3, 4 are PROVED with no hypothesis, from the lab's unconditional
Theorems C, D, E.

Ternary Goldbach is Helfgott's theorem. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter
open LeanLab.VanDerCorput1939 (I)

/-- The product in (3.32), over the odd prime divisors of `n`, as written in the paper. -/
noncomputable def Br (r n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (· ≠ 2),
    (((p : ℝ) - 1) ^ r + (-1) ^ r * ((p : ℝ) - 1)) / (((p : ℝ) - 1) ^ r - (-1) ^ r)

/-- The constant `C_r = ∏_{ϖ ≥ 3} (1 - (-1)^r/(ϖ-1)^r)` of (3.32), the factor at `2` set to `1`. -/
noncomputable def Cr (r : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime}, if p = ⟨2, Nat.prime_two⟩ then 1 else 1 - (-1 : ℝ) ^ r / ((p : ℝ) - 1) ^ r

theorem Cr3_eq : Cr 3 = C3 := by
  unfold Cr C3
  refine tprod_congr fun p => ?_
  split_ifs <;> ring

theorem Cr4_eq : Cr 4 = C4 := by
  unfold Cr C4
  refine tprod_congr fun p => ?_
  split_ifs <;> ring

theorem Br3_eq (n : ℕ) (hn : Odd n) : Br 3 n = Pi3 n := by
  unfold Br Pi3
  rw [filter_true_of_mem]
  · refine prod_congr rfl fun p hp => ?_
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hd1 : ((p : ℝ) - 1) ^ 3 - (-1) ^ 3 ≠ 0 := by
      have := pow_pos hq 3; nlinarith
    have hd2 : (p : ℝ) ^ 2 - 3 * p + 3 ≠ 0 := by nlinarith
    rw [div_eq_div_iff hd1 hd2]
    ring
  · intro p hp h
    subst h
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))

theorem Br4_eq (n : ℕ) : Br 4 n = Pi4 n := by
  unfold Br Pi4
  refine prod_congr (by ext; simp) fun p hp => ?_
  rw [mem_filter] at hp
  have hpp := Nat.prime_of_mem_primeFactors hp.1
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hpp hp.2
  have hq : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hd1 : ((p : ℝ) - 1) ^ 4 - (-1) ^ 4 ≠ 0 := by
    have : (16 : ℝ) ≤ ((p : ℝ) - 1) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hq 4; norm_num at this; linarith
    norm_num; linarith
  have hd2 : ((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2) ≠ 0 := by
    apply mul_ne_zero <;> nlinarith
  rw [div_eq_div_iff hd1 hd2]
  ring

/-! ### Counting: `N_3` versus `N̄_3`, `N_4` versus `N̄_4` -/

lemma Nr3_le_I (n : ℕ) : Nr 3 n ≤ I n := by
  rw [Nr_eq]
  unfold I
  apply card_le_card_of_injOn (fun t : Fin 3 → ℕ => (t 0, t 1))
  · intro t ht
    rw [mem_coe, mem_Sr] at ht
    obtain ⟨h1, h2, h3⟩ := ht
    rw [Fin.sum_univ_three] at h3
    have e : n - t 0 - t 1 = t 2 := by omega
    simp only [mem_coe, mem_filter, mem_product, mem_range]
    rw [e]
    exact ⟨⟨h1 0, h1 1⟩, h2 0, h2 1, (h2 2).ne_zero, h2 2, by omega⟩
  · intro t ht u hu h
    rw [mem_coe, mem_Sr] at ht hu
    simp only [Prod.mk.injEq] at h
    have a := ht.2.2
    have b := hu.2.2
    rw [Fin.sum_univ_three] at a b
    funext i
    fin_cases i <;> simp <;> omega

lemma Nr3_sub_N3bar (n : ℕ) (hn : Odd n) : |(Nr 3 n : ℝ) - N3bar n| ≤ 3 := by
  have a : (Nr 3 n : ℝ) ≤ I n := by exact_mod_cast Nr3_le_I n
  have b := I_sub_N3bar_le n hn
  have c : (N3bar n : ℝ) ≤ Nr 3 n := by exact_mod_cast (N3bar_le_I n).trans (I_le_Nr3 n)
  rw [abs_le]
  constructor <;> linarith

lemma N4bar_le_Nr4 (n : ℕ) : N4bar n ≤ Nr 4 n := by
  rw [Nr_eq]
  unfold N4bar
  apply card_le_card_of_injOn
    (fun t : ℕ × ℕ × ℕ => ![t.1, t.2.1, t.2.2, n - t.1 - t.2.1 - t.2.2])
  · intro t ht
    simp only [mem_coe, mem_filter, mem_product, mem_range] at ht
    obtain ⟨⟨h1, h2, h3⟩, p1, p2, p3, hlt, p4, -⟩ := ht
    rw [mem_coe, mem_Sr]
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp <;> omega
    · intro i
      fin_cases i <;> simpa
    · simp [Fin.sum_univ_four]
      omega
  · intro t _ u _ h
    have e1 := congrFun h 0
    have e2 := congrFun h 1
    have e3 := congrFun h 2
    simp at e1 e2 e3
    exact Prod.ext e1 (Prod.ext e2 e3)

lemma Nr4_le (n : ℕ) : Nr 4 n ≤ N4bar n + 12 * (n + 1) ^ 2 := by
  have hs : #((Sr 4 n).filter (fun t => ∃ i, t i < 3)) ≤ 4 * (3 * (n + 1) ^ 2) :=
    card_small_union 2 n 3
  have hsplit := card_filter_add_card_filter_not (s := Sr 4 n) (fun t => ∃ i, t i < 3)
  have hbig : #((Sr 4 n).filter (fun t => ¬ ∃ i, t i < 3)) ≤ N4bar n := by
    unfold N4bar
    apply card_le_card_of_injOn (fun t : Fin 4 → ℕ => (t 0, (t 1, t 2)))
    · intro t ht
      rw [mem_coe, mem_filter, mem_Sr] at ht
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ht
      simp only [not_exists, not_lt] at h4
      rw [Fin.sum_univ_four] at h3
      have hodd : ∀ i, Odd (t i) := fun i =>
        ((h2 i).eq_two_or_odd').resolve_left (by have := h4 i; omega)
      have e : n - t 0 - t 1 - t 2 = t 3 := by omega
      simp only [mem_coe, mem_filter, mem_product, mem_range]
      rw [e]
      exact ⟨⟨h1 0, h1 1, h1 2⟩, h2 0, h2 1, h2 2, by have := h4 3; omega, h2 3,
        hodd 0, hodd 1, hodd 2, hodd 3⟩
    · intro t ht u hu h
      rw [mem_coe, mem_filter, mem_Sr] at ht hu
      simp only [Prod.mk.injEq] at h
      have a := ht.1.2.2
      have b := hu.1.2.2
      rw [Fin.sum_univ_four] at a b
      funext i
      fin_cases i <;> simp <;> omega
  rw [Nr_eq]
  omega

lemma Nr4_sub_N4bar (n : ℕ) : |(Nr 4 n : ℝ) - N4bar n| ≤ 12 * ((n : ℝ) + 1) ^ 2 := by
  have a : (Nr 4 n : ℝ) ≤ N4bar n + 12 * ((n : ℝ) + 1) ^ 2 := by exact_mod_cast Nr4_le n
  have c : (N4bar n : ℝ) ≤ Nr 4 n := by exact_mod_cast N4bar_le_Nr4 n
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Assembly -/

/-- The algebra of the assembly: `A = N_r (log n)^r`, `M` the main term, `E` the counting error. -/
lemma assemble (A nu M E θ η : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hM : 0 ≤ M) (hnu : 0 ≤ nu) (h1 : |A - nu| ≤ θ * nu) (h2 : |A - M| ≤ θ * M + E)
    (h3 : E ≤ η * A) : |nu - M| ≤ (7 * θ + 3 * η) * M := by
  rw [abs_le] at h1 h2
  have hA0 : 0 ≤ A := by nlinarith [mul_le_mul_of_nonneg_right hθ hnu]
  have k1 := mul_le_mul_of_nonneg_right hθ hM
  have k2 := mul_le_mul_of_nonneg_right hη hA0
  have hA : A ≤ 3 * M := by linarith
  have k3 := mul_le_mul_of_nonneg_right hθ hnu
  have hnuM : nu ≤ 6 * M := by linarith
  have k4 := mul_le_mul_of_nonneg_left hnuM hθ0
  have k5 := mul_le_mul_of_nonneg_left hA hη0
  rw [abs_le]
  constructor <;> nlinarith

/-- **Hardy-Littlewood 1923, Theorem B, (3.32), r = 3**, PROVED with no hypothesis. -/
theorem theoremB3 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Odd n → n₀ ≤ n →
    |nur 3 n - 2 * Cr 3 / 2 * (n : ℝ) ^ 2 * Br 3 n| ≤ ε * (2 * Cr 3 / 2 * (n : ℝ) ^ 2 * Br 3 n) := by
  intro ε hε
  set θ := min (ε / 10) (1 / 4) with hθdef
  have hθ0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθ1 : θ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hθε : 7 * θ + 3 * θ ≤ ε := by have := min_le_left (ε / 10) (1 / 4); linarith
  obtain ⟨n₁, hC⟩ := theoremC 3 le_rfl θ hθ0
  obtain ⟨n₂, hD⟩ := theoremD θ hθ0
  obtain ⟨n₃, hlow⟩ := Nr3_lower
  obtain ⟨n₄, hg⟩ := eventually_atTop.mp (ThmE.grow 3 (240 / θ) (by positivity))
  refine ⟨max (max n₁ n₂) (max n₃ (max n₄ 2)), fun n hn hn0 => ?_⟩
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hc := hC n (by omega) (by omega)
  have hd := hD n hn (by omega)
  have hl := hlow n (by omega) hn2
  have hg' := hg n (by omega)
  set L := Real.log n
  have eM : 2 * Cr 3 / 2 * (n : ℝ) ^ 2 * Br 3 n = (C3 * (n : ℝ) ^ 2 / L ^ 3 * Pi3 n) * L ^ 3 := by
    rw [Cr3_eq, Br3_eq n hn]; field_simp
  rw [eM]
  set D := C3 * (n : ℝ) ^ 2 / L ^ 3 * Pi3 n
  have hD0 : 0 ≤ D := by
    have := C3_pos
    have := (ThmE.Pi3_bounds n).1
    positivity
  have k1 : 240 / θ * L ^ 3 ≤ n := (le_div_iff₀ (by positivity)).mp hg'
  have k2 : 240 * L ^ 3 ≤ θ * n := by
    calc 240 * L ^ 3 = θ * (240 / θ * L ^ 3) := by field_simp
      _ ≤ θ * n := mul_le_mul_of_nonneg_left k1 hθ0.le
  have k3 : θ * (n : ℝ) ≤ θ * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hθ0.le
  have k4 := mul_le_mul_of_nonneg_left hl hθ0.le
  have hE : 3 * L ^ 3 ≤ θ * ((Nr 3 n : ℝ) * L ^ 3) := by nlinarith
  have h2 : |(Nr 3 n : ℝ) * L ^ 3 - D * L ^ 3| ≤ θ * (D * L ^ 3) + 3 * L ^ 3 := by
    rw [← sub_mul, abs_mul, abs_of_pos (pow_pos hL 3)]
    have : |(Nr 3 n : ℝ) - D| ≤ θ * D + 3 := by
      calc |(Nr 3 n : ℝ) - D| = |((Nr 3 n : ℝ) - N3bar n) + ((N3bar n : ℝ) - D)| := by ring_nf
        _ ≤ |(Nr 3 n : ℝ) - N3bar n| + |(N3bar n : ℝ) - D| := abs_add_le _ _
        _ ≤ 3 + θ * D := add_le_add (Nr3_sub_N3bar n hn) hd
        _ = θ * D + 3 := by ring
    calc |(Nr 3 n : ℝ) - D| * L ^ 3 ≤ (θ * D + 3) * L ^ 3 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = θ * (D * L ^ 3) + 3 * L ^ 3 := by ring
  have hM : 0 ≤ D * L ^ 3 := by positivity
  have := assemble _ _ _ _ θ θ hθ0.le hθ1 hθ0.le hθ1 hM (nur_nonneg 3 n) hc h2 hE
  exact this.trans (mul_le_mul_of_nonneg_right hθε hM)

/-- **Hardy-Littlewood 1923, Theorem B, (3.32), r = 4**, PROVED with no hypothesis. -/
theorem theoremB4 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n →
    |nur 4 n - 2 * Cr 4 / 6 * (n : ℝ) ^ 3 * Br 4 n| ≤ ε * (2 * Cr 4 / 6 * (n : ℝ) ^ 3 * Br 4 n) := by
  intro ε hε
  set θ := min (ε / 10) (1 / 4) with hθdef
  have hθ0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθ1 : θ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hθε : 7 * θ + 3 * θ ≤ ε := by have := min_le_left (ε / 10) (1 / 4); linarith
  obtain ⟨n₁, hC⟩ := theoremC 4 (by norm_num) θ hθ0
  obtain ⟨n₂, hE4⟩ := theoremE θ hθ0
  obtain ⟨c, hc0, n₃, hlow⟩ := Nr_lower 1
  obtain ⟨n₄, hg⟩ := eventually_atTop.mp (ThmE.grow 4 (48 / (θ * c)) (by positivity))
  refine ⟨max (max n₁ n₂) (max n₃ (max n₄ 2)), fun n hn hn0 => ?_⟩
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hn
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hc := hC n (by omega) (by omega)
  have hd := hE4 n hn (by omega)
  have hl : c * (n : ℝ) ^ 3 ≤ (Nr 4 n : ℝ) * Real.log n ^ 4 := hlow n (by omega) (by omega)
  have hg' := hg n (by omega)
  set L := Real.log n
  have eM : 2 * Cr 4 / 6 * (n : ℝ) ^ 3 * Br 4 n =
      (C4 * (n : ℝ) ^ 3 / (3 * L ^ 4) * Pi4 n) * L ^ 4 := by
    rw [Cr4_eq, Br4_eq n]; field_simp; ring
  rw [eM]
  set D := C4 * (n : ℝ) ^ 3 / (3 * L ^ 4) * Pi4 n
  have hD0 : 0 ≤ D := by
    have := C4_pos
    have : (0 : ℝ) ≤ Pi4 n := by linarith [one_le_Pi4 n]
    positivity
  have k1 : 48 / (θ * c) * L ^ 4 ≤ n := (le_div_iff₀ (by positivity)).mp hg'
  have k2 : 48 * L ^ 4 ≤ θ * c * n := by
    calc 48 * L ^ 4 = θ * c * (48 / (θ * c) * L ^ 4) := by field_simp
      _ ≤ θ * c * n := mul_le_mul_of_nonneg_left k1 (by positivity)
  have k3 : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  have k4 : 12 * ((n : ℝ) + 1) ^ 2 * L ^ 4 ≤ 48 * (n : ℝ) ^ 2 * L ^ 4 := by
    have := pow_pos hL 4; nlinarith
  have k5 : (n : ℝ) ^ 2 * (48 * L ^ 4) ≤ (n : ℝ) ^ 2 * (θ * c * n) :=
    mul_le_mul_of_nonneg_left k2 (by positivity)
  have k6 := mul_le_mul_of_nonneg_left hl hθ0.le
  have hE : 12 * ((n : ℝ) + 1) ^ 2 * L ^ 4 ≤ θ * ((Nr 4 n : ℝ) * L ^ 4) := by nlinarith
  have h2 : |(Nr 4 n : ℝ) * L ^ 4 - D * L ^ 4| ≤ θ * (D * L ^ 4) + 12 * ((n : ℝ) + 1) ^ 2 * L ^ 4 := by
    rw [← sub_mul, abs_mul, abs_of_pos (pow_pos hL 4)]
    have : |(Nr 4 n : ℝ) - D| ≤ θ * D + 12 * ((n : ℝ) + 1) ^ 2 := by
      calc |(Nr 4 n : ℝ) - D| = |((Nr 4 n : ℝ) - N4bar n) + ((N4bar n : ℝ) - D)| := by ring_nf
        _ ≤ |(Nr 4 n : ℝ) - N4bar n| + |(N4bar n : ℝ) - D| := abs_add_le _ _
        _ ≤ 12 * ((n : ℝ) + 1) ^ 2 + θ * D := add_le_add (Nr4_sub_N4bar n) hd
        _ = θ * D + 12 * ((n : ℝ) + 1) ^ 2 := by ring
    calc |(Nr 4 n : ℝ) - D| * L ^ 4 ≤ (θ * D + 12 * ((n : ℝ) + 1) ^ 2) * L ^ 4 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = θ * (D * L ^ 4) + 12 * ((n : ℝ) + 1) ^ 2 * L ^ 4 := by ring
  have hM : 0 ≤ D * L ^ 4 := by positivity
  have := assemble _ _ _ _ θ θ hθ0.le hθ1 hθ0.le hθ1 hM (nur_nonneg 4 n) hc h2 hE
  exact this.trans (mul_le_mul_of_nonneg_right hθε hM)

end LeanLab.HardyLittlewood1923

