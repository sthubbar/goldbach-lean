module

public import LeanLab.Halupczok2012.U1439Thm2Reduction

/-!
# P0077 Halupczok 2012, the main term step: the CRT combination, unit U-1452

AI wrote the Lean code, Claude, run 20261022T0003Z-15508. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper's main term step, the displays after (10) in the proof of Theorem 2, expands
`𝔖(n - p₁)` as a finite sum over squarefree `s ≤ L^C` of functions of `p₁ mod s`, combines
`p₁ ≡ a (q)` with `p₁ ≡ b (s)` by the Chinese remainder theorem into one class mod `[q, s]`, and
applies Theorem 3 of Perelli-Pintz-Salerno at the moduli `[q, s]`. This file proves that
combination step for ONE modulus `s` and ANY `s`-periodic weight `f`, uniformly in `s`:

* `modEq_and_iff_lcm`: `p ≡ a (q) ∧ p ≡ b (s) ↔ p ≡ x ([q, s])` for any common solution `x`. PROVED.
* `crt_exists_iff`: a common solution exists iff `(q, s) ∣ a - b`. PROVED.
* `class_sum_eq_theta`: the primes of `P1` in the class `b mod s` are those of one class mod
  `[q, s]`, a class coprime to `[q, s]`. PROVED.
* `perQ_eq`: for one `q`, `∑_{p ≡ a (q)} log p f(p) - Y/φ([q,s]) ∑_{b ∈ G} f(b)` equals
  `∑_{b ∈ G} f(b) (θ(X, Y; [q, s], x_b) - Y/φ([q, s]))`, `G` the reduced `b mod s` compatible
  with `a mod q`. PROVED.
* `crtStep`: CONDITIONAL ON `Theorem3` only:
  `∑_{q ≤ Q, (a,q)=1} |∑_{p ≡ a (q)} log p f(p) - Y/φ([q,s]) ∑_{b ∈ G} f(b)| ≤ s² M C Y L^{-A}`
  whenever `Q s ≪ Y X^{-1/2} (log X)^{-B}`, `|f| ≤ M`, `s ≤ X`.

NOT done here: the Ramanujan expansion of `𝔖`, the tail `s > L^C`, and the Euler product
identification with `𝔗`. So `MainTermMV` is still NOT derived from `Theorem3`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-! ### The Chinese remainder theorem for two moduli -/

/-- **CRT combination.** -/
theorem modEq_and_iff_lcm {p x a b : ℤ} {q s : ℕ} (hxa : x ≡ a [ZMOD q])
    (hxb : x ≡ b [ZMOD s]) :
    (p ≡ a [ZMOD q] ∧ p ≡ b [ZMOD s]) ↔ p ≡ x [ZMOD (Nat.lcm q s : ℕ)] := by
  constructor
  · rintro ⟨h1, h2⟩
    exact modEq_lcm (h1.trans hxa.symm) (h2.trans hxb.symm)
  · intro h
    refine ⟨(Int.ModEq.of_dvd ?_ h).trans hxa, (Int.ModEq.of_dvd ?_ h).trans hxb⟩
    · exact_mod_cast Nat.dvd_lcm_left q s
    · exact_mod_cast Nat.dvd_lcm_right q s

/-- **Solvability of two congruences.** -/
theorem crt_exists_iff (a b : ℤ) (q s : ℕ) :
    (∃ x : ℤ, x ≡ a [ZMOD q] ∧ x ≡ b [ZMOD s]) ↔ ((Nat.gcd q s : ℕ) : ℤ) ∣ b - a := by
  constructor
  · rintro ⟨x, h1, h2⟩
    have d1 : ((Nat.gcd q s : ℕ) : ℤ) ∣ x - a :=
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q s)).trans h1.symm.dvd
    have d2 : ((Nat.gcd q s : ℕ) : ℤ) ∣ x - b :=
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q s)).trans h2.symm.dvd
    have := dvd_sub d1 d2
    rwa [show x - a - (x - b) = b - a by ring] at this
  · rintro ⟨k, hk⟩
    -- Bezout: gcd q s = q u + s v
    have hb : ((Nat.gcd q s : ℕ) : ℤ) = (q : ℤ) * Nat.gcdA q s + (s : ℤ) * Nat.gcdB q s :=
      Nat.gcd_eq_gcd_ab q s
    refine ⟨a + (q : ℤ) * Nat.gcdA q s * k, ?_, ?_⟩
    · apply Int.ModEq.symm
      apply Int.modEq_of_dvd
      exact ⟨Nat.gcdA q s * k, by ring⟩
    · apply Int.ModEq.symm
      apply Int.modEq_of_dvd
      refine ⟨-(Nat.gcdB q s * k), ?_⟩
      have : b = a + ((Nat.gcd q s : ℕ) : ℤ) * k := by linarith
      rw [this, hb]; ring

/-! ### The compatible reduced classes mod `s` and their representatives mod `[q, s]` -/

open Classical in
/-- `G(a, q, s)`: the `b < s` with `(b, s) = 1` for which `p ≡ a (q)`, `p ≡ b (s)` is solvable. -/
noncomputable def crtG (a : ℤ) (q s : ℕ) : Finset ℕ :=
  (range s).filter (fun b => Nat.gcd b s = 1 ∧ ∃ x : ℤ, x ≡ a [ZMOD q] ∧ x ≡ (b : ℤ) [ZMOD s])

open Classical in
/-- A common solution `x_b` of `x ≡ a (q)`, `x ≡ b (s)`, or `1` if there is none. -/
noncomputable def crtX (a : ℤ) (q s b : ℕ) : ℤ :=
  if h : ∃ x : ℤ, x ≡ a [ZMOD q] ∧ x ≡ (b : ℤ) [ZMOD s] then h.choose else 1

open Classical in
theorem mem_crtG {a : ℤ} {q s b : ℕ} :
    b ∈ crtG a q s ↔ b < s ∧ Nat.gcd b s = 1 ∧
      ∃ x : ℤ, x ≡ a [ZMOD q] ∧ x ≡ (b : ℤ) [ZMOD s] := by
  unfold crtG; rw [mem_filter, mem_range]

theorem crtG_subset (a : ℤ) (q s : ℕ) : crtG a q s ⊆ range s := by
  intro b hb; exact mem_range.mpr (mem_crtG.mp hb).1

theorem crtX_spec {a : ℤ} {q s b : ℕ} (h : ∃ x : ℤ, x ≡ a [ZMOD q] ∧ x ≡ (b : ℤ) [ZMOD s]) :
    crtX a q s b ≡ a [ZMOD q] ∧ crtX a q s b ≡ (b : ℤ) [ZMOD s] := by
  rw [crtX, dif_pos h]; exact h.choose_spec

theorem isCoprime_of_modEq {x a : ℤ} {m : ℕ} (h : x ≡ a [ZMOD m]) (ha : Int.gcd a m = 1) :
    IsCoprime x (m : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, ← Int.gcd_emod, h, Int.gcd_emod]; exact ha

/-- The representative `x_b` is a reduced residue mod `[q, s]`. -/
theorem gcd_crtX {a : ℤ} {q s b : ℕ} (ha : Int.gcd a q = 1) (hbG : b ∈ crtG a q s) :
    Int.gcd (crtX a q s b) ((Nat.lcm q s : ℕ) : ℤ) = 1 := by
  rw [mem_crtG] at hbG
  obtain ⟨-, hb, hex⟩ := hbG
  obtain ⟨h1, h2⟩ := crtX_spec hex
  have c1 := isCoprime_of_modEq h1 ha
  have c2 := isCoprime_of_modEq h2 (by rw [Int.gcd_natCast_natCast]; exact hb)
  have c3 : IsCoprime (crtX a q s b) ((q : ℤ) * (s : ℤ)) := c1.mul_right c2
  have hd : ((Nat.lcm q s : ℕ) : ℤ) ∣ (q : ℤ) * (s : ℤ) := by
    exact_mod_cast Nat.lcm_dvd_mul q s
  exact Int.isCoprime_iff_gcd_eq_one.mp (c3.of_isCoprime_of_dvd_right hd)

/-! ### Splitting the prime sum by the class mod `s` -/

theorem sum_split_mod (W : Finset ℕ) (g f : ℕ → ℝ) {s : ℕ} (hs : 0 < s)
    (hf : ∀ p, f p = f (p % s)) :
    ∑ p ∈ W, g p * f p = ∑ b ∈ range s, f b * ∑ p ∈ W.filter (fun p => p % s = b), g p := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => p % s) (t := range s)
    (fun p _ => mem_range.mpr (Nat.mod_lt p hs))]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [mem_filter] at hp
  rw [hf p, hp.2]; ring

theorem mod_eq_iff_modEq {p b s : ℕ} (hb : b < s) : p % s = b ↔ (p : ℤ) ≡ (b : ℤ) [ZMOD s] := by
  rw [Int.natCast_modEq_iff, Nat.ModEq, Nat.mod_eq_of_lt hb]

/-- **The class `b mod s` of `P1` is one reduced class mod `[q, s]`.** -/
theorem class_sum_eq_theta {n q s b : ℕ} {a : ℤ} {X Y : ℝ} (hn : X + Y ≤ n) (hb : b < s)
    (hex : ∃ x : ℤ, x ≡ a [ZMOD q] ∧ x ≡ (b : ℤ) [ZMOD s]) :
    ∑ p ∈ (P1 n X Y q a).filter (fun p => p % s = b), Real.log p =
      thetaAP X Y (Nat.lcm q s) (crtX a q s b) := by
  obtain ⟨h1, h2⟩ := crtX_spec hex
  unfold thetaAP
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [P1, mem_filter, mem_range]
  rw [mod_eq_iff_modEq hb, ← modEq_and_iff_lcm h1 h2]
  constructor
  · rintro ⟨⟨-, hp, h3, h4, h5⟩, h6⟩
    refine ⟨?_, hp, h3, h4, h5, h6⟩
    have := Nat.le_ceil (X + Y)
    have : p ≤ ⌈X + Y⌉₊ := by exact_mod_cast (h4.trans this)
    omega
  · rintro ⟨-, hp, h3, h4, h5, h6⟩
    refine ⟨⟨?_, hp, h3, h4, h5⟩, h6⟩
    have : (p : ℝ) ≤ n := h4.trans hn
    have : p ≤ n := by exact_mod_cast this
    omega

/-- **The other classes contribute nothing**, once `s ≤ X`. -/
theorem class_sum_eq_zero {n q s b : ℕ} {a : ℤ} {X Y : ℝ} (hsX : (s : ℝ) ≤ X) (hb : b < s)
    (hbG : b ∉ crtG a q s) :
    ∑ p ∈ (P1 n X Y q a).filter (fun p => p % s = b), Real.log p = 0 := by
  apply sum_eq_zero
  intro p hp
  exfalso
  simp only [P1, mem_filter, mem_range] at hp
  obtain ⟨⟨-, hpr, hXp, -, hpa⟩, hpb⟩ := hp
  rw [mem_crtG] at hbG
  have hpb' := (mod_eq_iff_modEq hb).mp hpb
  by_cases hg : Nat.gcd b s = 1
  · exact hbG ⟨hb, hg, ⟨p, hpa, hpb'⟩⟩
  · obtain ⟨d, hd, hdg⟩ := Nat.exists_prime_and_dvd hg
    have hds : d ∣ s := hdg.trans (Nat.gcd_dvd_right b s)
    have hdb : ((d : ℕ) : ℤ) ∣ ((b : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (hdg.trans (Nat.gcd_dvd_left b s))
    have hpd := prime_cong_noncoprime hpr hd hpb' hds hdb
    have hdle : d ≤ s := Nat.le_of_dvd (by omega) hds
    have : (p : ℝ) ≤ s := by rw [hpd]; exact_mod_cast hdle
    linarith

/-- **The main term identity for one `q`.** -/
theorem perQ_eq {n q s : ℕ} {a : ℤ} {X Y : ℝ} (f : ℕ → ℝ) (hs : 0 < s)
    (hf : ∀ p, f p = f (p % s)) (hn : X + Y ≤ n) (hsX : (s : ℝ) ≤ X) :
    ∑ p ∈ P1 n X Y q a, Real.log p * f p -
        Y / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, f b =
      ∑ b ∈ crtG a q s, f b * (thetaAP X Y (Nat.lcm q s) (crtX a q s b) -
        Y / (Nat.totient (Nat.lcm q s) : ℝ)) := by
  rw [sum_split_mod _ _ f hs hf]
  have hsub : crtG a q s ⊆ range s := crtG_subset a q s
  rw [← sum_subset hsub (f := fun b => f b * ∑ p ∈ (P1 n X Y q a).filter (fun p => p % s = b),
    Real.log p)]
  · rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro b hbG
    have hb : b < s := mem_range.mp (hsub hbG)
    have hex : ∃ x : ℤ, x ≡ a [ZMOD q] ∧ x ≡ (b : ℤ) [ZMOD s] := by
      exact (mem_crtG.mp hbG).2.2
    rw [class_sum_eq_theta hn hb hex]; ring
  · intro b hb hbG
    rw [class_sum_eq_zero hsX (mem_range.mp hb) hbG, mul_zero]

/-- `|θ(X, Y; [q,s], x_b) - Y/φ([q,s])|`, the Theorem 3 error at the combined class. -/
noncomputable def crtErr (X Y : ℝ) (a : ℤ) (q s b : ℕ) : ℝ :=
  |thetaAP X Y (Nat.lcm q s) (crtX a q s b) - Y / (Nat.totient (Nat.lcm q s) : ℝ)|

/-- **The bound for one `q`.** -/
theorem perQ_abs_le {n q s : ℕ} {a : ℤ} {X Y M : ℝ} (f : ℕ → ℝ) (hs : 0 < s)
    (hf : ∀ p, f p = f (p % s)) (hn : X + Y ≤ n) (hsX : (s : ℝ) ≤ X) (hM : ∀ b, |f b| ≤ M) :
    |∑ p ∈ P1 n X Y q a, Real.log p * f p -
        Y / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, f b| ≤
      M * ∑ b ∈ crtG a q s, crtErr X Y a q s b := by
  rw [perQ_eq f hs hf hn hsX, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
  rw [abs_mul, crtErr]
  exact mul_le_mul_of_nonneg_right (hM b) (abs_nonneg _)

/-- **Reindexing by `q ↦ [q, s]`**: on the `q` with a fixed `(q, s) = g` the map is injective,
so these errors form part of one Theorem 3 sum at level `Q s` with one reduced residue per modulus. -/
theorem piece_le (X Y Q : ℝ) (a : ℤ) (s b g : ℕ) (hs : 0 < s) (J : Finset ℕ)
    (hJ : ∀ q ∈ J, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ Int.gcd a q = 1 ∧ b ∈ crtG a q s ∧ Nat.gcd q s = g) :
    ∃ a' : ℕ → ℤ, (∀ q, Int.gcd (a' q) q = 1) ∧
      ∑ q ∈ J, crtErr X Y a q s b ≤
        ∑ q ∈ Icc 1 ⌊Q * s⌋₊, |thetaAP X Y q (a' q) - Y / (q.totient : ℝ)| := by
  classical
  have hinj : ∀ q1 ∈ J, ∀ q2 ∈ J, Nat.lcm q1 s = Nat.lcm q2 s → q1 = q2 := by
    intro q1 h1 q2 h2 he
    have e1 := Nat.gcd_mul_lcm q1 s
    have e2 := Nat.gcd_mul_lcm q2 s
    rw [(hJ q1 h1).2.2.2.2, he] at e1
    rw [(hJ q2 h2).2.2.2.2] at e2
    have : q1 * s = q2 * s := by rw [← e1, ← e2]
    exact Nat.eq_of_mul_eq_mul_right hs this
  let a' : ℕ → ℤ := fun q' =>
    if h : ∃ q ∈ J, Nat.lcm q s = q' then crtX a h.choose s b else 1
  have ha'J : ∀ q ∈ J, a' (Nat.lcm q s) = crtX a q s b := by
    intro q hq
    have h : ∃ q0 ∈ J, Nat.lcm q0 s = Nat.lcm q s := ⟨q, hq, rfl⟩
    simp only [a', dif_pos h]
    rw [hinj _ h.choose_spec.1 q hq h.choose_spec.2]
  refine ⟨a', ?_, ?_⟩
  · intro q'
    by_cases h : ∃ q ∈ J, Nat.lcm q s = q'
    · simp only [a', dif_pos h]
      obtain ⟨hq, hl⟩ := h.choose_spec
      have := gcd_crtX (hJ _ hq).2.2.1 (hJ _ hq).2.2.2.1
      rw [hl] at this; exact this
    · simp only [a', dif_neg h]; simp
  · calc ∑ q ∈ J, crtErr X Y a q s b
        = ∑ q ∈ J, |thetaAP X Y (Nat.lcm q s) (a' (Nat.lcm q s)) -
            Y / ((Nat.lcm q s).totient : ℝ)| := by
          apply sum_congr rfl; intro q hq; rw [crtErr, ha'J q hq]
      _ = ∑ q' ∈ J.image (fun q => Nat.lcm q s),
            |thetaAP X Y q' (a' q') - Y / (q'.totient : ℝ)| :=
          (sum_image (f := fun q' => |thetaAP X Y q' (a' q') - Y / (q'.totient : ℝ)|)
            (fun x hx y hy h => hinj x hx y hy h)).symm
      _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
          intro q' hq'
          rw [mem_image] at hq'
          obtain ⟨q, hq, rfl⟩ := hq'
          obtain ⟨h1, hQ, -⟩ := hJ q hq
          rw [mem_Icc]
          refine ⟨Nat.lcm_pos (by omega) hs, Nat.le_floor ?_⟩
          have hle : Nat.lcm q s ≤ q * s :=
            Nat.le_of_dvd (Nat.mul_pos (by omega) hs) (Nat.lcm_dvd_mul q s)
          have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
          calc ((Nat.lcm q s : ℕ) : ℝ) ≤ ((q * s : ℕ) : ℝ) := by exact_mod_cast hle
            _ = (q : ℝ) * s := by push_cast; ring
            _ ≤ Q * s := mul_le_mul_of_nonneg_right hQ hs0

/-- **The CRT step of the main term, CONDITIONAL ON `Theorem3` only.** For one modulus `s`
and an `s`-periodic weight `f` with `|f| ≤ M`, uniformly in `s`, `f`, `a`:
`∑_{q ≤ Q, (a,q)=1} |∑_{p ∈ (X, X+Y], p ≡ a (q)} log p f(p) - Y/φ([q,s]) ∑_{b ∈ G(a,q,s)} f(b)|
  ≤ s² M C Y L^{-A}` when `Q s ≤ c₂ Y X^{-1/2} (log X)^{-B}`, `s ≤ X`. -/
theorem crtStep (h3 : Theorem3) : ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c2 : ℝ, 0 < c1 → 0 < c2 → ∃ C Y0 : ℝ,
    ∀ (n s : ℕ) (X Y Q M : ℝ) (a : ℤ) (f : ℕ → ℝ),
    Y0 ≤ Y → Y ≤ X → c1 * X ^ (3 / 5 + ε) ≤ Y →
    Q * s ≤ c2 * Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B) →
    0 < s → (s : ℝ) ≤ X → X + Y ≤ n → (∀ p, f p = f (p % s)) → (∀ b, |f b| ≤ M) →
    ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |∑ p ∈ P1 n X Y q a, Real.log p * f p -
        Y / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, f b| ≤
      (s : ℝ) ^ 2 * M * C * Y * Real.log Y ^ (-A) := by
  classical
  intro A ε hA hε
  obtain ⟨B, hB, h3'⟩ := h3 A ε hA hε
  refine ⟨B, hB, fun c1 c2 hc1 hc2 => ?_⟩
  obtain ⟨C, Y0, hC⟩ := h3' c1 c2 hc1 hc2
  refine ⟨C, Y0, fun n s X Y Q M a f hY0 hYX hc1Y hQs hs hsX hn hf hM => ?_⟩
  set Iq := (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1) with hIq
  set K := C * Y * Real.log Y ^ (-A) with hKdef
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := by
    have := hC X Y (Q * s) hY0 hYX hc1Y hQs (fun _ => 1) (fun _ => Int.gcd_one_left _)
    exact (sum_nonneg (fun _ _ => abs_nonneg _)).trans this
  have hpiece : ∀ b g : ℕ,
      ∑ q ∈ (Iq.filter (fun q => b ∈ crtG a q s)).filter (fun q => Nat.gcd q s = g),
        crtErr X Y a q s b ≤ K := by
    intro b g
    obtain ⟨a', ha', hle⟩ := piece_le X Y Q a s b g hs
      ((Iq.filter (fun q => b ∈ crtG a q s)).filter (fun q => Nat.gcd q s = g)) (by
      intro q hq
      simp only [hIq, mem_filter, mem_Icc] at hq
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hq
      exact ⟨h1, (Nat.le_floor_iff' (by omega)).mp h2, h3, h4, h5⟩)
    exact hle.trans (hC X Y (Q * s) hY0 hYX hc1Y hQs a' ha')
  have hite : ∀ q, ∑ b ∈ crtG a q s, crtErr X Y a q s b =
      ∑ b ∈ range s, if b ∈ crtG a q s then crtErr X Y a q s b else 0 := by
    intro q
    rw [sum_ite_mem, inter_eq_right.mpr (crtG_subset a q s)]
  have hfib : ∀ b, ∑ q ∈ Iq, (if b ∈ crtG a q s then crtErr X Y a q s b else 0) ≤
      (s.divisors.card : ℝ) * K := by
    intro b
    rw [← sum_filter, ← sum_fiberwise_of_maps_to (g := fun q => Nat.gcd q s) (t := s.divisors)
      (fun q _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hs.ne'⟩)]
    calc _ ≤ ∑ g ∈ s.divisors, K := sum_le_sum (fun g _ => hpiece b g)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hdiv : (s.divisors.card : ℝ) ≤ s := by exact_mod_cast Nat.card_divisors_le_self s
  calc _ ≤ ∑ q ∈ Iq, M * ∑ b ∈ crtG a q s, crtErr X Y a q s b :=
        sum_le_sum (fun q _ => perQ_abs_le f hs hf hn hsX hM)
    _ = M * ∑ b ∈ range s, ∑ q ∈ Iq,
          (if b ∈ crtG a q s then crtErr X Y a q s b else 0) := by
        rw [← mul_sum, sum_congr rfl (fun q _ => hite q), sum_comm]
    _ ≤ M * ∑ b ∈ range s, (s.divisors.card : ℝ) * K :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun b _ => hfib b)) hM0
    _ = M * s * ((s.divisors.card : ℝ) * K) := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ M * s * (s * K) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdiv hK0)
        positivity
    _ = _ := by rw [hKdef]; ring

/-! ### Vacuity -/

/-- The hypotheses of `crtStep` on `s`, `f` can hold: `s = 6`, `f(p) = 1` if `p ≡ 1 (6)`. -/
theorem crtStep_weight_instance :
    (∀ p : ℕ, (fun p : ℕ => if p % 6 = 1 then (1 : ℝ) else 0) p =
      (fun p : ℕ => if p % 6 = 1 then (1 : ℝ) else 0) (p % 6)) ∧
    ∀ b : ℕ, |(fun p : ℕ => if p % 6 = 1 then (1 : ℝ) else 0) b| ≤ 1 := by
  refine ⟨fun p => by simp, fun b => ?_⟩
  simp only; split_ifs <;> simp

/-- The combined class is nonempty in a concrete case: `q = 4`, `s = 6`, `a = 1`, `b = 5`
gives `x = 5` mod `[4, 6] = 12`, and `G(1, 4, 6) = {1, 5}`. -/
theorem crtG_instance : crtG 1 4 6 = {1, 5} := by
  ext b
  simp only [mem_crtG, mem_insert, mem_singleton, crt_exists_iff]
  constructor
  · rintro ⟨hb, hg, hd⟩
    interval_cases b <;> simp_all
  · rintro (rfl | rfl) <;> refine ⟨by norm_num, by norm_num, by decide⟩

end LeanLab.Halupczok2012
