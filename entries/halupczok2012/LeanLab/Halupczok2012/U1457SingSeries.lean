module

public import LeanLab.Halupczok2012.U1452MainTermMV

/-!
# P0077 Halupczok 2012, the main term step reduced to Theorem 3 and an elementary input, U-1457

AI wrote the Lean code, Claude, run 20261022T0003Z-15508. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper's main term step, the displays after (10) in the proof of Theorem 2, rests on two
things: Theorem 3 of Perelli-Pintz-Salerno, used through the CRT step `crtStep` of U-1452, and a
purely elementary statement about the singular series, with no primes in it. This file names the
second as `SingSeriesApprox` and proves

* `mainTermMV_of_inputs : Theorem3 → SingSeriesApprox → MainTermMV`. CONDITIONAL ON both.
* `theorem2Zeroed_of_three`: the F-0008 repair, CONDITIONAL ON `Theorem3`, `Theorem5` and
  `SingSeriesApprox`.

`SingSeriesApprox` says: under the hypotheses of Theorem 2 there are a finite set `Z` of moduli
`s ≤ L^D`, `s ≤ X₁`, at most `L^D` of them, and `s`-periodic weights `g_s` bounded by a constant
`K`, such that
(i) TAIL: `∑_{q ≤ Q, (a,q)=1} ∑_{m ∈ (X₁, X₁+Y₁], m ≡ a (q)} log m |𝔖(n - m) - ∑_{s ∈ Z} g_s(m)|
    ≪ Y₁ L^{-A}`, a sum over ALL integers `m`, no primes;
(ii) EULER PRODUCT: `∑_{q ≤ Q, (a,q)=1} |∑_{s ∈ Z} Y₁/φ([q,s]) ∑_{b ∈ G(a,q,s)} g_s(b) - 𝔗(n,q,a) Y₁|
    ≪ Y₁ L^{-A}`.
In the paper `Z` is the squarefree `s ≤ L^C` and `g_s(m) = μ(s)² c_s(n - m)/φ(s)²`, the
Ramanujan expansion of `𝔖`.

Toward proving `SingSeriesApprox`, the local algebra:

* `local_factor_div`, `local_factor_ndiv`: for an odd prime `p`,
  `1 + c_p(r)/(p-1)²` equals `(1 - 1/(p-1)²)(p-1)/(p-2)` if `p ∣ r` and `1 - 1/(p-1)²` if not,
  with `c_p(r) = p - 1` or `-1`. PROVED.
* `euler_expand`: `∏_{p ∈ P} (1 + f p) = ∑_{t ⊆ P} ∏_{p ∈ t} f p`, the squarefree expansion. PROVED.
* `ramanujanP_periodic`: the weight `∏_{p ∈ t} c_p(n - m)` is `∏ t`-periodic in `m`. PROVED.
* `truncS_expand`: the truncated singular series over a finite set `P` of odd primes,
  `∏_{p ∈ P} (1 - 1/(p-1)²) ∏_{p ∈ P, p ∣ r} (p-1)/(p-2)`, equals the sum over `t ⊆ P` of
  `∏_{p ∈ t} c_p(r)/(p-1)²`. PROVED.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-! ### The elementary input -/

/-- The integers `m ∈ (X₁, X₁ + Y₁]`, `m ≤ n`, `m ≡ a (q)`: the window of `P1` without primality. -/
noncomputable def W1 (n : ℕ) (X1 Y1 : ℝ) (q : ℕ) (a : ℤ) : Finset ℕ :=
  (range (n + 1)).filter (fun m => X1 < m ∧ (m : ℝ) ≤ X1 + Y1 ∧ (m : ℤ) ≡ a [ZMOD q])

theorem P1_subset_W1 (n : ℕ) (X1 Y1 : ℝ) (q : ℕ) (a : ℤ) : P1 n X1 Y1 q a ⊆ W1 n X1 Y1 q a := by
  intro p hp
  simp only [P1, W1, mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.2⟩

/-- **The singular series approximation**, a prime free named input. See the module doc. -/
def SingSeriesApprox : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ D : ℝ, 0 ≤ D ∧
  ∀ B : ℝ, 0 < B → ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ,
  ∃ C K Y0 : ℝ, ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 →
    Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
    ∃ (Z : Finset ℕ) (g : ℕ → ℕ → ℝ),
      (∀ s ∈ Z, 0 < s ∧ (s : ℝ) ≤ X1 ∧ (s : ℝ) ≤ Real.log Y2 ^ D) ∧
      ((Z.card : ℝ) ≤ Real.log Y2 ^ D) ∧
      (∀ s ∈ Z, ∀ m, g s m = g s (m % s)) ∧
      (∀ s ∈ Z, ∀ m, |g s m| ≤ K) ∧
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        ∑ m ∈ W1 n X1 Y1 q a, Real.log m * |S (n - m) - ∑ s ∈ Z, g s m|
          ≤ C * Y1 * Real.log Y2 ^ (-A) ∧
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        |∑ s ∈ Z, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b -
          T n q a * Y1| ≤ C * Y1 * Real.log Y2 ^ (-A)

/-! ### Real analysis helpers -/

/-- From `u ≤ k L` to `L^{-B} ≤ k^B u^{-B}`. -/
theorem rpow_neg_le_of_le {u L k B : ℝ} (hu : 0 < u) (hk : 0 < k) (huL : u ≤ k * L)
    (hB : 0 ≤ B) : L ^ (-B) ≤ k ^ B * u ^ (-B) := by
  have hL : 0 < L := by
    by_contra h; push_neg at h; nlinarith
  have h1 : (k * L) ^ (-B) ≤ u ^ (-B) := Real.rpow_le_rpow_of_nonpos hu huL (by linarith)
  rw [Real.mul_rpow hk.le hL.le] at h1
  have hkB : k ^ B * k ^ (-B) = 1 := by
    rw [Real.rpow_neg hk.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hk B).ne']
  have hkB0 : 0 ≤ k ^ B := (Real.rpow_pos_of_pos hk B).le
  calc L ^ (-B) = k ^ B * (k ^ (-B) * L ^ (-B)) := by rw [← mul_assoc, hkB, one_mul]
    _ ≤ k ^ B * u ^ (-B) := mul_le_mul_of_nonneg_left h1 hkB0

theorem rpow_three_D {L A D : ℝ} (hL : 0 < L) :
    L ^ D * (L ^ D) ^ 2 * L ^ (-(A + 3 * D)) = L ^ (-A) := by
  rw [sq, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
  congr 1; ring

/-! ### The main term step, CONDITIONAL ON `Theorem3` and `SingSeriesApprox` -/

theorem mainSum_split (n : ℕ) (X1 Y1 : ℝ) (q : ℕ) (a : ℤ) (Z : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    mainSum n X1 Y1 q a - T n q a * Y1 =
      ∑ p ∈ P1 n X1 Y1 q a, Real.log p * (S (n - p) - ∑ s ∈ Z, g s p) +
      ∑ s ∈ Z, (∑ p ∈ P1 n X1 Y1 q a, Real.log p * g s p -
        Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b) +
      (∑ s ∈ Z, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b -
        T n q a * Y1) := by
  have h1 : ∑ s ∈ Z, ∑ p ∈ P1 n X1 Y1 q a, Real.log p * g s p =
      ∑ p ∈ P1 n X1 Y1 q a, Real.log p * ∑ s ∈ Z, g s p := by
    rw [sum_comm]; simp_rw [mul_sum]
  have h2 : ∑ p ∈ P1 n X1 Y1 q a, Real.log p * (S (n - p) - ∑ s ∈ Z, g s p) =
      ∑ p ∈ P1 n X1 Y1 q a, Real.log p * S (n - p) -
        ∑ p ∈ P1 n X1 Y1 q a, Real.log p * ∑ s ∈ Z, g s p := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro p _; ring
  rw [sum_sub_distrib, mainSum]
  linarith [h1, h2]

/-- **The main term step `MainTermMV`, CONDITIONAL ON `Theorem3` and `SingSeriesApprox`.** -/
theorem mainTermMV_of_inputs (h3 : Theorem3) (hss : SingSeriesApprox) : MainTermMV := by
  classical
  intro A ε ε1 ε2 hA hε hε1 hε2
  obtain ⟨D, hD, hS⟩ := hss A ε ε1 ε2 hA hε hε1 hε2
  set A' := A + 3 * D with hA'
  have hA'0 : 0 < A' := by rw [hA']; linarith
  obtain ⟨B3, hB3, h3'⟩ := crtStep h3 A' ε1 hA'0 hε1
  refine ⟨B3 + D, by linarith, fun c hc c7 hc7 a => ?_⟩
  have c0 := hc 0; have c2 := hc 2; have c3 := hc 3; have c6 := hc 6
  obtain ⟨C1, K, Y01, hS'⟩ := hS (B3 + D) (by linarith) c hc c7 hc7 a
  set kX := 2 * |Real.log (c 3 / c 0)| + 2 with hkX
  set kY := 3 + 3 * |Real.log (c 2)| with hkY
  have hkX0 : 0 < kX := by rw [hkX]; positivity
  have hkY0 : 0 < kY := by rw [hkY]; positivity
  obtain ⟨C3, Y03, hcrt⟩ := h3' (c 0) (c 6 * kX ^ B3) c0 (by positivity)
  refine ⟨2 * C1 + |K * C3| * kY ^ A', max Y01 (max Y03 (Real.exp 1)), ?_⟩
  intro n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ ha
  have hY01 : Y01 ≤ Y1 := le_trans (le_max_left _ _) hY1
  have hY01' : Y01 ≤ Y2 := le_trans (le_max_left _ _) hY2
  have hY03 : Y03 ≤ Y1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY1
  have hYe1 : Real.exp 1 ≤ Y1 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY1
  have hYe2 : Real.exp 1 ≤ Y2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY2
  obtain ⟨Z, g, hZ, hcard, hper, hbd, htail, heul⟩ := hS' n X1 Y1 X2 Y2 Q hY01 hY01' hH hQ ha
  obtain ⟨hn, hYX1, h0, hYX2, h1, h2, h3, hD0, hD1, hD2, hQ1, hQ2⟩ := hH
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hY1pos : 0 < Y1 := by linarith
  have hY2pos : 0 < Y2 := by linarith
  have hL1 : 1 ≤ Real.log Y2 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hYe2
  have hl1 : 1 ≤ Real.log Y1 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hYe1
  have hL0 : 0 < Real.log Y2 := by linarith
  have hX1 : 1 ≤ X1 := by linarith
  have hX1pos : 0 < X1 := by linarith
  have hn' : X1 + Y1 ≤ n := by linarith
  -- `log X₁ ≤ kX L`
  have hlogX : Real.log X1 ≤ kX * Real.log Y2 := by
    have hsq := le_sq_of_rpow c0 hX1 (by linarith) h0
    have hb : X1 ≤ (c 3 / c 0 * Y2) ^ 2 := by
      refine hsq.trans ?_
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ c0]
      calc Y1 ≤ c 3 * Y2 := h3
        _ = c 3 / c 0 * Y2 * c 0 := by field_simp
    have h := Real.log_le_log hX1pos hb
    rw [Real.log_pow, Real.log_mul (by positivity) hY2pos.ne'] at h
    have := le_abs_self (Real.log (c 3 / c 0))
    have : |Real.log (c 3 / c 0)| ≤ |Real.log (c 3 / c 0)| * Real.log Y2 :=
      le_mul_of_one_le_right (abs_nonneg _) hL1
    rw [hkX]; push_cast at h; linarith
  -- `L ≤ kY log Y₁`
  have hlogY : Real.log Y2 ≤ kY * Real.log Y1 := by
    have hpos : 0 < c 2 * Y2 ^ (1 / 3 + ε) := by positivity
    have h := Real.log_le_log hpos h2
    rw [Real.log_mul c2.ne' (by positivity), Real.log_rpow hY2pos] at h
    have := neg_abs_le (Real.log (c 2))
    have : |Real.log (c 2)| ≤ |Real.log (c 2)| * Real.log Y1 :=
      le_mul_of_one_le_right (abs_nonneg _) hl1
    have hεL : 0 ≤ ε * Real.log Y2 := mul_nonneg hε.le hL0.le
    have : (1 / 3) * Real.log Y2 ≤ (1 / 3 + ε) * Real.log Y2 := by linarith
    rw [hkY]; linarith
  have hlogX1 : 0 < Real.log X1 := by
    have : Real.log Y1 ≤ Real.log X1 := Real.log_le_log hY1pos hYX1
    linarith
  -- the moduli bound of Theorem 3
  have hQs : ∀ s ∈ Z, Q * s ≤ c 6 * kX ^ B3 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log X1 ^ (-B3) := by
    intro s hs
    obtain ⟨-, -, hsL⟩ := hZ s hs
    have hQ0 : 0 ≤ Q := by linarith
    have hP : 0 ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) := by positivity
    have e1 : Real.log Y2 ^ (-(B3 + D)) * Real.log Y2 ^ D = Real.log Y2 ^ (-B3) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hlb := rpow_neg_le_of_le hlogX1 hkX0 hlogX hB3.le
    calc Q * s ≤ (c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log Y2 ^ (-(B3 + D))) *
          Real.log Y2 ^ D := mul_le_mul hQ2 hsL (Nat.cast_nonneg _) (by positivity)
      _ = c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log Y2 ^ (-B3) := by rw [mul_assoc, e1]
      _ ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * (kX ^ B3 * Real.log X1 ^ (-B3)) :=
          mul_le_mul_of_nonneg_left hlb hP
      _ = _ := by ring
  -- one modulus
  set l1 := Real.log Y1 ^ (-A') with hl1def
  set LD := Real.log Y2 ^ D with hLD
  have hLD0 : 0 ≤ LD := by positivity
  have hl10 : 0 ≤ l1 := by positivity
  have hl1le : l1 ≤ kY ^ A' * Real.log Y2 ^ (-A') :=
    rpow_neg_le_of_le hL0 hkY0 hlogY hA'0.le
  have hones : ∀ s ∈ Z,
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        |∑ p ∈ P1 n X1 Y1 q a, Real.log p * g s p -
          Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b| ≤
        LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) := by
    intro s hs
    obtain ⟨hs0, hsX, hsL⟩ := hZ s hs
    have h := hcrt n s X1 Y1 Q K a (g s) hY03 hYX1 h0 (hQs s hs) hs0 hsX hn' (hper s hs)
      (hbd s hs)
    have hab : K * C3 * Y1 * l1 ≤ |K * C3| * Y1 * l1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hY1pos.le) hl10
    have hs2 : (s : ℝ) ^ 2 ≤ LD ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hsL 2
    calc _ ≤ (s : ℝ) ^ 2 * K * C3 * Y1 * l1 := h
      _ = (s : ℝ) ^ 2 * (K * C3 * Y1 * l1) := by ring
      _ ≤ (s : ℝ) ^ 2 * (|K * C3| * Y1 * l1) :=
          mul_le_mul_of_nonneg_left hab (sq_nonneg _)
      _ ≤ LD ^ 2 * (|K * C3| * Y1 * l1) :=
          mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ ≤ LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hl1le (by positivity)
  -- all moduli
  set Iq := (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1) with hIq
  have hmid : ∑ q ∈ Iq, ∑ s ∈ Z, |∑ p ∈ P1 n X1 Y1 q a, Real.log p * g s p -
        Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b| ≤
      |K * C3| * kY ^ A' * Y1 * Real.log Y2 ^ (-A) := by
    rw [sum_comm]
    have hP0 : 0 ≤ LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) := by positivity
    calc _ ≤ ∑ s ∈ Z, LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) :=
          sum_le_sum hones
      _ = (Z.card : ℝ) * (LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A')))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ LD * (LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A')))) :=
          mul_le_mul_of_nonneg_right hcard hP0
      _ = |K * C3| * kY ^ A' * Y1 * (LD * LD ^ 2 * Real.log Y2 ^ (-(A + 3 * D))) := by
          rw [hA']; ring
      _ = _ := by rw [hLD, rpow_three_D hL0]
  -- the tail over primes
  have htailP : ∀ q, |∑ p ∈ P1 n X1 Y1 q a, Real.log p * (S (n - p) - ∑ s ∈ Z, g s p)| ≤
      ∑ m ∈ W1 n X1 Y1 q a, Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| := by
    intro q
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hnn : ∀ m : ℕ, 0 ≤ Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| :=
      fun m => mul_nonneg (Real.log_natCast_nonneg m) (abs_nonneg _)
    calc _ = ∑ p ∈ P1 n X1 Y1 q a, Real.log p * |S (n - p) - ∑ s ∈ Z, g s p| := by
          apply sum_congr rfl; intro p _
          rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (P1_subset_W1 n X1 Y1 q a) (fun m _ _ => hnn m)
  -- assemble
  have hper_q : ∀ q ∈ Iq, |mainSum n X1 Y1 q a - T n q a * Y1| ≤
      ∑ m ∈ W1 n X1 Y1 q a, Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| +
      ∑ s ∈ Z, |∑ p ∈ P1 n X1 Y1 q a, Real.log p * g s p -
        Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b| +
      |∑ s ∈ Z, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b -
        T n q a * Y1| := by
    intro q _
    rw [mainSum_split n X1 Y1 q a Z g]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add (htailP q) ?_)) le_rfl
    exact abs_sum_le_sum_abs _ _
  calc _ ≤ ∑ q ∈ Iq, (∑ m ∈ W1 n X1 Y1 q a, Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| +
      ∑ s ∈ Z, |∑ p ∈ P1 n X1 Y1 q a, Real.log p * g s p -
        Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b| +
      |∑ s ∈ Z, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, g s b -
        T n q a * Y1|) := sum_le_sum hper_q
    _ = _ := by rw [sum_add_distrib, sum_add_distrib]
    _ ≤ C1 * Y1 * Real.log Y2 ^ (-A) + |K * C3| * kY ^ A' * Y1 * Real.log Y2 ^ (-A) +
          C1 * Y1 * Real.log Y2 ^ (-A) := add_le_add (add_le_add htail hmid) heul
    _ = _ := by ring

/-- **Theorem 2 in the lab's coprime reading, CONDITIONAL ON `Theorem3`, `Theorem5` and
`SingSeriesApprox`.** -/
theorem theorem2_of_three (h3 : Theorem3) (h5 : Theorem5) (hss : SingSeriesApprox) : Theorem2 :=
  theorem2_of_inputs h5 (mainTermMV_of_inputs h3 hss)

/-- **The F-0008 repair, CONDITIONAL ON `Theorem3`, `Theorem5` and `SingSeriesApprox`.** -/
theorem theorem2Zeroed_of_three (h3 : Theorem3) (h5 : Theorem5) (hss : SingSeriesApprox) :
    Theorem2Zeroed :=
  theorem2Zeroed_of_inputs h5 (mainTermMV_of_inputs h3 hss)

/-! ### Toward `SingSeriesApprox`: the local algebra of the Ramanujan expansion -/

/-- `c_p(r)` for a prime `p`: `p - 1` if `p ∣ r`, else `-1`. -/
noncomputable def cP (p r : ℕ) : ℝ := if p ∣ r then (p : ℝ) - 1 else -1

/-- **Local factor, `p ∣ r`.** -/
theorem local_factor_div {p : ℕ} (hp : 3 ≤ p) :
    1 + ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 =
      (1 - 1 / ((p : ℝ) - 1) ^ 2) * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  have h : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- **Local factor, `p ∤ r`.** -/
theorem local_factor_ndiv (p : ℕ) :
    1 + (-1) / ((p : ℝ) - 1) ^ 2 = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by ring

/-- The local factor in terms of `cP`. -/
theorem local_factor {p : ℕ} (hp : 3 ≤ p) (r : ℕ) :
    1 + cP p r / ((p : ℝ) - 1) ^ 2 =
      (1 - 1 / ((p : ℝ) - 1) ^ 2) * (if p ∣ r then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) := by
  unfold cP
  split_ifs
  · exact local_factor_div hp
  · rw [local_factor_ndiv, mul_one]

/-- **The squarefree expansion of a finite Euler product.** -/
theorem euler_expand {ι : Type*} [DecidableEq ι] (P : Finset ι) (f : ι → ℝ) :
    ∏ p ∈ P, (1 + f p) = ∑ t ∈ P.powerset, ∏ p ∈ t, f p := by
  simp_rw [add_comm (1 : ℝ)]
  rw [prod_add]
  apply sum_congr rfl
  intro t _
  rw [prod_const_one, mul_one]

/-- **The truncated singular series is a finite sum of Ramanujan type terms.** For a finite set
`P` of primes `≥ 3`,
`∏_{p ∈ P} (1 - 1/(p-1)²) ∏_{p ∈ P, p ∣ r} (p-1)/(p-2) = ∑_{t ⊆ P} ∏_{p ∈ t} c_p(r)/(p-1)²`. -/
theorem truncS_expand (P : Finset ℕ) (hP : ∀ p ∈ P, 3 ≤ p) (r : ℕ) :
    (∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
        ∏ p ∈ P.filter (· ∣ r), (((p : ℝ) - 1) / ((p : ℝ) - 2)) =
      ∑ t ∈ P.powerset, ∏ p ∈ t, cP p r / ((p : ℝ) - 1) ^ 2 := by
  rw [← euler_expand, prod_filter, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  rw [local_factor (hP p hp)]

/-- **Periodicity of the weights.** `m ↦ ∏_{p ∈ t} c_p(n - m)` depends only on `m mod ∏ t`,
for `m ≤ n` on both sides; here in the form `c_p(n - m)` with `m ≡ m' (∏ t)`. -/
theorem cP_periodic {p n m m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n) (h : m ≡ m' [MOD p]) :
    cP p (n - m) = cP p (n - m') := by
  unfold cP
  have : p ∣ n - m ↔ p ∣ n - m' := by
    have hd : (p : ℤ) ∣ (m' : ℤ) - m := (Nat.modEq_iff_dvd.mp h)
    have e : ((n : ℤ) - m) = ((n : ℤ) - m') + ((m' : ℤ) - m) := by ring
    rw [← Int.natCast_dvd_natCast, ← Int.natCast_dvd_natCast, Nat.cast_sub hm, Nat.cast_sub hm', e]
    exact dvd_add_left hd
  simp only [this]

theorem ramanujanP_periodic (t : Finset ℕ) {n m m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n)
    (h : m ≡ m' [MOD ∏ p ∈ t, p]) :
    ∏ p ∈ t, cP p (n - m) / ((p : ℝ) - 1) ^ 2 = ∏ p ∈ t, cP p (n - m') / ((p : ℝ) - 1) ^ 2 := by
  apply prod_congr rfl
  intro p hp
  rw [cP_periodic hm hm' (Nat.ModEq.of_dvd (dvd_prod_of_mem _ hp) h)]

/-! ### Vacuity -/

/-- `truncS_expand` is not vacuous: `P = {3, 5}`, `r = 3`, both sides equal `45/32`. -/
theorem truncS_instance :
    (∏ p ∈ ({3, 5} : Finset ℕ), (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
        ∏ p ∈ ({3, 5} : Finset ℕ).filter (· ∣ 3), (((p : ℝ) - 1) / ((p : ℝ) - 2)) = 45 / 32 := by
  rw [show ({3, 5} : Finset ℕ).filter (· ∣ 3) = {3} by decide]
  simp [prod_insert, prod_singleton]
  norm_num

/-! ### Toward `SingSeriesApprox`: the local Euler factor of `𝔗` at a prime modulus -/

/-- The reduced classes mod a prime `p` are `1, …, p - 1`. -/
theorem reduced_mod_prime {p : ℕ} (hp : p.Prime) :
    (range p).filter (fun b => Nat.gcd b p = 1) = Ico 1 p := by
  ext b
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨hb, hg⟩
    refine ⟨?_, hb⟩
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at hg; exact absurd hg hp.one_lt.ne'
    · exact h
  · rintro ⟨h1, hb⟩
    refine ⟨hb, ?_⟩
    rw [Nat.gcd_comm]
    exact hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := Nat.le_of_dvd (by omega) hd; omega)

/-- For `1 ≤ b < p`, `b ≤ n`: `p ∣ n - b` iff `b = n mod p`. -/
theorem dvd_sub_iff_eq_mod {p n b : ℕ} (hb : b < p) (hbn : b ≤ n) :
    p ∣ n - b ↔ b = n % p := by
  rw [← Nat.modEq_iff_dvd' hbn, Nat.ModEq, Nat.mod_eq_of_lt hb]

/-- **The Ramanujan sum over the reduced classes.** For a prime `p ≤ n`,
`∑_{b mod p, (b,p)=1} c_p(n - b) = -(p - 1)` if `p ∣ n` and `1` if not. -/
theorem cP_reduced_sum {p n : ℕ} (hp : p.Prime) (hn : p ≤ n) :
    ∑ b ∈ (range p).filter (fun b => Nat.gcd b p = 1), cP p (n - b) =
      if p ∣ n then -((p : ℝ) - 1) else 1 := by
  rw [reduced_mod_prime hp]
  have hsplit : ∀ b ∈ Ico 1 p, cP p (n - b) = -1 + (if b = n % p then (p : ℝ) else 0) := by
    intro b hb
    rw [mem_Ico] at hb
    unfold cP
    have key := dvd_sub_iff_eq_mod (p := p) (n := n) hb.2 (by omega)
    by_cases h : b = n % p
    · rw [if_pos (key.mpr h), if_pos h]; ring
    · rw [if_neg (fun hh => h (key.mp hh)), if_neg h]; ring
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_const, Nat.card_Ico, sum_ite_eq']
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hmod : n % p < p := Nat.mod_lt n (by omega)
  by_cases hd : p ∣ n
  · have h0 : n % p = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [if_pos hd, if_neg (by rw [mem_Ico, h0]; omega), nsmul_eq_mul]
    push_cast [Nat.cast_sub hp1]; ring
  · have h0 : n % p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    rw [if_neg hd, if_pos (by rw [mem_Ico]; omega), nsmul_eq_mul]
    push_cast [Nat.cast_sub hp1]; ring

/-- **Local factor of `𝔗` at a prime `p ∤ q`**: with `φ([q,p]) = φ(q)(p-1)` and the reduced
classes sum `cP_reduced_sum`, `1 + (1/(p-1)) R/(p-1)²` is the factor of `𝔗(n,q,a)`:
`1 - 1/(p-1)²` if `p ∣ n` and `1 + 1/(p-1)³` if not. -/
theorem local_T_ndvd_q {p n : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hn : p ≤ n) :
    1 + (1 / ((p : ℝ) - 1)) *
        (∑ b ∈ (range p).filter (fun b => Nat.gcd b p = 1), cP p (n - b)) / ((p : ℝ) - 1) ^ 2 =
      if p ∣ n then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  rw [cP_reduced_sum hp hn]
  have h : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  split_ifs
  · field_simp; ring
  · field_simp

/-- **Local factor of `𝔗` at a prime `p ∣ q`**: the single compatible class is `a mod p`, the
modulus `[q,p] = q`, and `1 + c_p(n - a)/(p-1)²` is `p/(p-1)` if `p ∣ n - a`, else
`1 - 1/(p-1)²`. -/
theorem local_T_dvd_q {p : ℕ} (hp3 : 3 ≤ p) (r : ℕ) :
    1 + cP p r / ((p : ℝ) - 1) ^ 2 =
      if p ∣ r then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have h : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold cP
  split_ifs
  · field_simp; ring
  · ring

/-- Vacuity: `p = 5`, `n = 10`: the reduced sum is `-4`; `n = 11`: it is `1`. -/
theorem cP_reduced_sum_instance :
    ∑ b ∈ (range 5).filter (fun b => Nat.gcd b 5 = 1), cP 5 (10 - b) = -4 ∧
    ∑ b ∈ (range 5).filter (fun b => Nat.gcd b 5 = 1), cP 5 (11 - b) = 1 := by
  rw [cP_reduced_sum (by norm_num) (by norm_num), cP_reduced_sum (by norm_num) (by norm_num)]
  norm_num

end LeanLab.Halupczok2012
