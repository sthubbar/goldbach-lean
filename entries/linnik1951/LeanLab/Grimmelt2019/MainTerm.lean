module

public import LeanLab.Grimmelt2019.Prop21

/-!
P0074 L. Grimmelt, "Goldbach Numbers in Short Intervals: A Nonnegative Model Approach",
arXiv 1910.05187 v2. Unit U-1300, run 20261021T0003Z-5661.

The main term step at the end of the proof of Theorem 1.1, pages 13 and 14, and a check of the
cited bundle `Prop21.Section5Inputs`.

* `not_section5Inputs`, PROVED: the bundle `Prop21.Section5Inputs` of U-6760 is REFUTABLE, since
  it quantifies over every `ε > 0`; at `ε = 1` one has `Y ≥ X`, so the support conditions force
  `ω = 0`, and then the `mainTerm` field asks that about `H/2` even integers number at most
  `K H / log X`. So `Prop21.thm1_1_of_section5` is vacuous as stated. The paper's Lemma 5.1 is
  meant for small `ε`; the repair is to restrict `ε`, for instance to `0 < ε < 1/18`, see
  `Bookkeeping.rough_support`.
* `ΛQ` is defined concretely, `LamQ Q m = ∑_{q ≤ Q} μ(q)/φ(q) c_q(m)`, with the Ramanujan sum
  `c_q(m) = ∑_{a < q, (a,q) = 1} cos(2π a m / q)`, the real part of `∑ e(am/q)`; that sum is
  real, so this is the paper's `ΛQ`. The model is `Tν = cν ΛQ` on `(Y, 2Y]`, as on page 5 and in
  Lemma 4.2.
* `conv_Tnu`, `sum_window_ram`, `conv_Tnu_approx`, PROVED: the exchange of summation and the
  split into residue classes. If `ω` is equidistributed in residue classes mod every `q ≤ Q` on
  the window `n₁ ∈ [n - 2Y, n - Y)` with error `E`, the input `APEquidist`, then
  `|ω * Tν (n) - cν cω Y S_Q(n)| ≤ cν Q² E`, with the truncated singular series `SQ`.
  `APEquidist` is the residue class form of condition (29) of Lemma 5.1: by orthogonality of
  characters mod `q`, and since `ω` lives on `Q`-rough numbers, the classes `r` with
  `(r, q) > 1` carry no mass. That translation is NOT formalized here.
* The paper writes the `n₁` range as `[n - Y, n - 2Y]`; since `Tν` lives on `(Y, 2Y]` the range
  is `n - 2Y ≤ n₁ < n - Y`, which is what `Wn` uses. A typo; it changes nothing.
* `SQ Q n` is written as `∑_{q ≤ Q} μ(q)/φ(q)² ∑_{(r,q)=1} c_q(n - r)`; the inner sum equals
  `μ(q) c_q(n)`, giving the paper's `∑ μ(q)² c_q(n)/φ(q)²`, but that identity is NOT proved here.
* `Sec5ObjectsMT.toSec5`, PROVED: objects with the concrete model, (29) in the form
  `APEquidist`, and the singular series lower bound outside few exceptions give
  `Prop21.Sec5Objects`, so the `mainTerm` field is no longer an input.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves Theorem 1.1; its analytic inputs stay cited.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019.MainTerm
open Real LeanLab.Grimmelt2019 LeanLab.Grimmelt2019.Prop21

attribute [local instance] Classical.propDecidable

/-! ### The bundle `Section5Inputs` is refutable -/

/-- PROVED: `Prop21.Section5Inputs`, quantified over all `ε > 0`, is false. At `ε = 1`,
`Y = X^{61/40} ≥ X`, so `ω` lives on `(X - 3Y, X - Y] ∩ [1, X] = ∅`, hence `ω * T = 0`, and the
`mainTerm` field would bound the number of even integers in `[X - H, X]`, which exceeds
`H/2 - 1`, by `K H / log X`. -/
theorem not_section5Inputs : ¬ Section5Inputs := by
  intro h
  obtain ⟨B, hB⟩ := h 1 one_pos
  obtain ⟨K, c, X0, hK, hc, hobj⟩ := hB 1 one_pos
  set X : ℝ := max X0 (Real.exp (4 * K + 4)) with hXdef
  have hXX0 : X0 ≤ X := le_max_left _ _
  have hXe : Real.exp (4 * K + 4) ≤ X := le_max_right _ _
  have hX4 : 4 ≤ X := by have := Real.add_one_le_exp (4 * K + 4); linarith
  have hXpos : 0 < X := by linarith
  have hlog : 4 * K + 4 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe
  obtain ⟨o⟩ := hobj X hXX0
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hYX : X ≤ X ^ (21 / 40 + (1 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le hX1 (show (1 : ℝ) ≤ 21 / 40 + 1 by norm_num)
    rwa [Real.rpow_one] at this
  set Y := X ^ (21 / 40 + (1 : ℝ)) with hY
  have hY1 : 1 ≤ Y := le_trans hX1 hYX
  have hHY : Y ≤ Y ^ (1 / 9 + 2 * (1 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le hY1 (show (1 : ℝ) ≤ 1 / 9 + 2 * 1 by norm_num)
    rwa [Real.rpow_one] at this
  set H := Y ^ (1 / 9 + 2 * (1 : ℝ)) with hH
  have hH4 : 4 ≤ H := by linarith
  have hω0 : ∀ n, o.ω n = 0 := by
    intro n
    by_contra hne
    have hw := o.omega_window n hne
    have hs : n ∈ supp X := by
      by_contra hn; exact hne (o.omega_supp n hn)
    unfold supp at hs
    rw [Finset.mem_Icc] at hs
    have : (1 : ℝ) ≤ n := by exact_mod_cast hs.1
    linarith [hw.2]
  have hconv : ∀ n, conv (supp X) o.ω o.T n = 0 := by
    intro n; unfold conv; simp [hω0]
  have hmt := o.mainTerm
  have hcY : 0 < c * Y := mul_pos hc (by linarith)
  have hsub : (Finset.Icc ⌈(X - H) / 2⌉ ⌊X / 2⌋).image (fun m : ℤ => 2 * m) ⊆
      (win X H).filter (fun n => Even n ∧ conv (supp X) o.ω o.T n < c * Y) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨m, hm, rfl⟩ := hz
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_filter, hconv]
    refine ⟨?_, ⟨m, by ring⟩, hcY⟩
    unfold win
    rw [Finset.mem_Icc]
    have h1 : (X - H) / 2 ≤ (m : ℝ) := Int.ceil_le.mp hm.1
    have h2 : (m : ℝ) ≤ X / 2 := Int.le_floor.mp hm.2
    constructor
    · rw [Int.ceil_le]; push_cast; linarith
    · rw [Int.le_floor]; push_cast; linarith
  have hinj : Function.Injective (fun m : ℤ => 2 * m) := fun a b hab => by
    simp only at hab; omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Int.card_Icc] at hcard
  have hf1 := Int.floor_le (X / 2)
  have hf2 := Int.lt_floor_add_one (X / 2)
  have hc1 := Int.le_ceil ((X - H) / 2)
  have hc2 := Int.ceil_lt_add_one ((X - H) / 2)
  set d := ⌊X / 2⌋ + 1 - ⌈(X - H) / 2⌉ with hd
  have hdr : H / 2 - 1 < (d : ℝ) := by rw [hd]; push_cast; linarith
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) < d := by linarith
    exact_mod_cast this.le
  have hdcast : ((d.toNat : ℕ) : ℝ) = (d : ℝ) := by
    have : ((d.toNat : ℤ) : ℝ) = (d : ℝ) := by rw [Int.toNat_of_nonneg hd0]
    rw [← this]; push_cast; rfl
  have hlow : H / 2 - 1 < (((win X H).filter
      (fun n => Even n ∧ conv (supp X) o.ω o.T n < c * Y)).card : ℝ) := by
    have : ((d.toNat : ℕ) : ℝ) ≤ (((win X H).filter
        (fun n => Even n ∧ conv (supp X) o.ω o.T n < c * Y)).card : ℝ) := by
      exact_mod_cast hcard
    linarith
  have hlogpos : 0 < Real.log X := by linarith
  have hup : K * H / Real.log X ^ (1 : ℝ) ≤ H / 4 := by
    rw [Real.rpow_one, div_le_div_iff₀ hlogpos (by norm_num)]
    nlinarith
  linarith

/-! ### Ramanujan sums and the concrete `ΛQ` -/

/-- The Ramanujan sum `c_q(m) = ∑_{a < q, (a,q)=1} cos(2π a m / q)`, the real part of
`∑_{a(q)*} e(am/q)`, which is real. -/
noncomputable def ram (q : ℕ) (m : ℤ) : ℝ :=
  ∑ a ∈ (Finset.range q).filter (fun a => q.Coprime a), Real.cos (2 * π * a * m / q)

/-- `ΛQ(m) = ∑_{q ≤ Q} μ(q)/φ(q) c_q(m)`, page 4 of P0074. -/
noncomputable def LamQ (Q : ℕ) (m : ℤ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) * ram q m

/-- The model `Tν = cν ΛQ` on `(Y, 2Y]`, the support of `ν`, zero elsewhere; pages 5 and 11. -/
noncomputable def Tnu (cν Y : ℝ) (Q : ℕ) (m : ℤ) : ℝ :=
  if Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Y then cν * LamQ Q m else 0

/-- The window of `n₁` with `n - n₁ ∈ (Y, 2Y]`, that is `n - 2Y ≤ n₁ < n - Y`; the paper prints
it as `[n - Y, n - 2Y]`, reversed. -/
noncomputable def Wn (X Y : ℝ) (n : ℤ) : Finset ℤ :=
  (supp X).filter (fun m => (n : ℝ) - 2 * Y ≤ m ∧ (m : ℝ) < n - Y)

theorem abs_ram_le (q : ℕ) (m : ℤ) : |ram q m| ≤ (q.totient : ℝ) := by
  unfold ram
  calc |∑ a ∈ (Finset.range q).filter (fun a => q.Coprime a), Real.cos (2 * π * a * m / q)|
        ≤ ∑ a ∈ (Finset.range q).filter (fun a => q.Coprime a),
            |Real.cos (2 * π * a * m / q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ (Finset.range q).filter (fun a => q.Coprime a), (1 : ℝ) :=
        Finset.sum_le_sum fun a _ => Real.abs_cos_le_one _
    _ = (q.totient : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.totient_eq_card_coprime]

theorem ram_add_mul (q : ℕ) (m j : ℤ) : ram q (m + q * j) = ram q m := by
  unfold ram
  apply Finset.sum_congr rfl
  intro a ha
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp at ha
  · have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have e : 2 * π * (a : ℝ) * ((m + q * j : ℤ) : ℝ) / q
        = 2 * π * a * m / q + ((a * j : ℤ) : ℝ) * (2 * π) := by
      push_cast; field_simp; try ring
    rw [e, Real.cos_add_int_mul_two_pi]

theorem ram_emod (q : ℕ) (n m : ℤ) : ram q (n - m) = ram q (n - m % q) := by
  have h : n - m = (n - m % (q : ℤ)) + (q : ℤ) * (-(m / q)) := by
    have := Int.emod_add_ediv_mul m q; linarith
  rw [h, ram_add_mul]

/-! ### The exchange of summation -/

/-- PROVED: `ω * Tν (n) = cν ∑_{q ≤ Q} μ(q)/φ(q) ∑_{n₁ ∈ Wn} ω(n₁) c_q(n - n₁)`. -/
theorem conv_Tnu (X Y cν : ℝ) (Q : ℕ) (ω : ℤ → ℝ) (n : ℤ) :
    conv (supp X) ω (Tnu cν Y Q) n =
      cν * ∑ q ∈ Finset.Icc 1 Q, (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) *
        ∑ m ∈ Wn X Y n, ω m * ram q (n - m) := by
  have h1 : conv (supp X) ω (Tnu cν Y Q) n = ∑ m ∈ Wn X Y n, ω m * (cν * LamQ Q (n - m)) := by
    unfold conv Wn
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    unfold Tnu
    have e : (Y < ((n - m : ℤ) : ℝ) ∧ ((n - m : ℤ) : ℝ) ≤ 2 * Y) ↔
        ((n : ℝ) - 2 * Y ≤ m ∧ (m : ℝ) < n - Y) := by
      push_cast
      constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)
    by_cases h : (n : ℝ) - 2 * Y ≤ m ∧ (m : ℝ) < n - Y
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h, mul_zero]
  rw [h1]
  unfold LamQ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  apply Finset.sum_congr rfl; intro m _
  ring

/-- PROVED: splitting the window sum into residue classes mod `q`, using `q`-periodicity of
`c_q`. -/
theorem sum_window_ram (q : ℕ) (hq : 0 < q) (W : Finset ℤ) (ω : ℤ → ℝ) (n : ℤ) :
    ∑ m ∈ W, ω m * ram q (n - m) =
      ∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * ∑ m ∈ W.filter (fun m => m % q = r), ω m := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rw [← Finset.sum_fiberwise_of_maps_to (s := W) (t := Finset.Ico (0 : ℤ) q)
    (g := fun m => m % (q : ℤ)) (fun m _ => by
      rw [Finset.mem_Ico]; exact ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩)]
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m hm
  rw [Finset.mem_filter] at hm
  rw [ram_emod q n m, hm.2]; ring

/-! ### Condition (29) in residue class form, and the singular series -/

/-- Cited input shape, the residue class form of condition (29) of Lemma 5.1 at `n`: for every
`q ≤ Q` and residue `r`, the mass of `ω` on the window in the class `r mod q` is
`cω Y / φ(q)` for `(r,q) = 1` and `0` otherwise, up to `E`. -/
def APEquidist (X Y : ℝ) (Q : ℕ) (ω : ℤ → ℝ) (cω E : ℝ) (n : ℤ) : Prop :=
  ∀ q ∈ Finset.Icc 1 Q, ∀ r ∈ Finset.Ico (0 : ℤ) q,
    |∑ m ∈ (Wn X Y n).filter (fun m => m % q = r), ω m
      - (if Int.gcd r q = 1 then cω * Y / (q.totient : ℝ) else 0)| ≤ E

/-- The truncated singular series, in the form the computation produces:
`S_Q(n) = ∑_{q ≤ Q} μ(q)/φ(q)² ∑_{r < q, (r,q)=1} c_q(n - r)`; the inner sum is `μ(q) c_q(n)`,
not proved here. -/
noncomputable def SQ (Q : ℕ) (n : ℤ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) ^ 2 *
    ∑ r ∈ (Finset.Ico (0 : ℤ) q).filter (fun r => Int.gcd r q = 1), ram q (n - r)

/-- PROVED: under `APEquidist` at `n`, `|ω * Tν (n) - cν cω Y S_Q(n)| ≤ cν Q² E`. This is the
Ramanujan sum step at the end of the proof of Theorem 1.1, done with residue classes instead
of characters. -/
theorem conv_Tnu_approx {X Y cν cω E : ℝ} {Q : ℕ} {ω : ℤ → ℝ} {n : ℤ} (hcν : 0 ≤ cν)
    (hE : 0 ≤ E) (hap : APEquidist X Y Q ω cω E n) :
    |conv (supp X) ω (Tnu cν Y Q) n - cν * cω * Y * SQ Q n| ≤ cν * (Q : ℝ) ^ 2 * E := by
  set main : ℕ → ℤ → ℝ := fun q r => if Int.gcd r q = 1 then cω * Y / (q.totient : ℝ) else 0
    with hmain
  set D : ℕ → ℤ → ℝ := fun q r =>
    ∑ m ∈ (Wn X Y n).filter (fun m => m % q = r), ω m - main q r with hD
  set R : ℕ → ℝ := fun q => (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) *
    ∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * D q r with hR
  have key : ∀ q ∈ Finset.Icc 1 Q,
      (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) *
        ∑ m ∈ Wn X Y n, ω m * ram q (n - m)
      = cω * Y * ((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) ^ 2 *
          ∑ r ∈ (Finset.Ico (0 : ℤ) q).filter (fun r => Int.gcd r q = 1), ram q (n - r))
        + R q := by
    intro q hq
    have hq0 : 0 < q := by rw [Finset.mem_Icc] at hq; omega
    rw [sum_window_ram q hq0]
    have hs : ∑ r ∈ Finset.Ico (0 : ℤ) q,
          ram q (n - r) * ∑ m ∈ (Wn X Y n).filter (fun m => m % q = r), ω m
        = ∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * main q r
          + ∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * D q r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro r _
      simp only [hD]; ring
    have hm : ∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * main q r
        = cω * Y / (q.totient : ℝ) *
          ∑ r ∈ (Finset.Ico (0 : ℤ) q).filter (fun r => Int.gcd r q = 1), ram q (n - r) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      simp only [hmain]
      split_ifs <;> ring
    rw [hs, hm]
    simp only [hR]
    ring
  have hdiff : conv (supp X) ω (Tnu cν Y Q) n - cν * cω * Y * SQ Q n
      = cν * ∑ q ∈ Finset.Icc 1 Q, R q := by
    rw [conv_Tnu, Finset.sum_congr rfl key, Finset.sum_add_distrib]
    unfold SQ
    rw [← Finset.mul_sum]
    ring
  have hRq : ∀ q ∈ Finset.Icc 1 Q, |R q| ≤ (q : ℝ) * E := by
    intro q hq
    have hq0 : 0 < q := by rw [Finset.mem_Icc] at hq; omega
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hsum : |∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * D q r|
        ≤ (q : ℝ) * (q.totient : ℝ) * E := by
      calc |∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * D q r|
            ≤ ∑ r ∈ Finset.Ico (0 : ℤ) q, |ram q (n - r) * D q r| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r ∈ Finset.Ico (0 : ℤ) q, (q.totient : ℝ) * E := by
              apply Finset.sum_le_sum; intro r hr
              rw [abs_mul]
              exact mul_le_mul (abs_ram_le q _) (hap q hq r hr) (abs_nonneg _) hφ.le
        _ = (q : ℝ) * (q.totient : ℝ) * E := by
              rw [Finset.sum_const, Int.card_Ico, nsmul_eq_mul]
              simp only [sub_zero, Int.toNat_natCast]
              ring
    simp only [hR]
    rw [abs_mul, abs_div, abs_of_pos hφ]
    calc |(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ) *
          |∑ r ∈ Finset.Ico (0 : ℤ) q, ram q (n - r) * D q r|
        ≤ 1 / (q.totient : ℝ) * ((q : ℝ) * (q.totient : ℝ) * E) :=
          mul_le_mul (div_le_div_of_nonneg_right hμ hφ.le) hsum (abs_nonneg _)
            (div_nonneg zero_le_one hφ.le)
      _ = (q : ℝ) * E := by field_simp
  rw [hdiff, abs_mul, abs_of_nonneg hcν, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hcν
  calc |∑ q ∈ Finset.Icc 1 Q, R q| ≤ ∑ q ∈ Finset.Icc 1 Q, |R q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) * E := by
        apply Finset.sum_le_sum; intro q hq
        refine le_trans (hRq q hq) (mul_le_mul_of_nonneg_right ?_ hE)
        rw [Finset.mem_Icc] at hq; exact_mod_cast hq.2
    _ = (Q : ℝ) ^ 2 * E := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        ring

/-- PROVED: the main term exceptions are among the singular series exceptions, once the
budget `c Y ≤ cν cω Y s0 - cν Q² E` holds. -/
theorem mainTerm_count {X Y H cν cω E c s0 : ℝ} {Q : ℕ} {ω : ℤ → ℝ} (hcν : 0 ≤ cν)
    (hcω : 0 ≤ cω) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hap : ∀ n ∈ win X H, APEquidist X Y Q ω cω E n)
    (hbudget : c * Y ≤ cν * cω * Y * s0 - cν * (Q : ℝ) ^ 2 * E) :
    (((win X H).filter (fun n => Even n ∧ conv (supp X) ω (Tnu cν Y Q) n < c * Y)).card : ℝ)
      ≤ ((win X H).filter (fun n => Even n ∧ SQ Q n < s0)).card := by
  have hsub : (win X H).filter (fun n => Even n ∧ conv (supp X) ω (Tnu cν Y Q) n < c * Y) ⊆
      (win X H).filter (fun n => Even n ∧ SQ Q n < s0) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, hn.2.1, ?_⟩
    by_contra hs
    have hs' : s0 ≤ SQ Q n := not_lt.mp hs
    have h := conv_Tnu_approx hcν hE (hap n hn.1)
    have h2 := (abs_le.mp h).1
    have : cν * cω * Y * s0 ≤ cν * cω * Y * SQ Q n :=
      mul_le_mul_of_nonneg_left hs' (mul_nonneg (mul_nonneg hcν hcω) hY)
    linarith [hn.2.2]
  exact_mod_cast Finset.card_le_card hsub

/-! ### Section 5 objects with the concrete model -/

/-- The objects of Section 5 at one scale, with the concrete model `Tν = cν ΛQ` and with the
main term field of `Sec5Objects` replaced by its two sources: condition (29) of Lemma 5.1 in
residue class form, and the truncated singular series lower bound outside few exceptions,
Harman page 208, plus the budget inequality. -/
structure Sec5ObjectsMT (X Y H K B A c : ℝ) where
  ν : ℤ → ℝ
  ω : ℤ → ℝ
  Tp : ℤ → ℝ
  cν : ℝ
  cω : ℝ
  Q : ℕ
  E : ℝ
  s0 : ℝ
  /-- Lemma 5.1. -/
  nu_le : ∀ n, ν n ≤ LamP X n
  omega_le : ∀ n, ω n ≤ LamP X n
  omega_window : ∀ n : ℤ, ω n ≠ 0 → X - 3 * Y < (n : ℝ) ∧ (n : ℝ) ≤ X - Y
  nu_supp : SuppIn (supp X) ν
  omega_supp : SuppIn (supp X) ω
  omega_norm : sqn (supp X) ω ≤ K * Y * Real.log Y ^ B
  /-- Model construction, Lemma 4.2. -/
  T_supp : SuppIn (supp X) (Tnu cν Y Q)
  Tp_supp : SuppIn (supp X) Tp
  Tp_nonneg : ∀ n, 0 ≤ Tp n
  lemma42 : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A))
    (fun n => Tnu cν Y Q n - Tp n)
  cor43 : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A)) (fun n => ν n - Tp n)
  /-- Constants: `cν > 0.05`, `cω > 0.09` in Lemma 5.1. -/
  cnu_nonneg : 0 ≤ cν
  comega_nonneg : 0 ≤ cω
  E_nonneg : 0 ≤ E
  /-- Condition (29) of Lemma 5.1, residue class form, at every `n ∈ [X - H, X]`. -/
  ap29 : ∀ n ∈ win X H, APEquidist X Y Q ω cω E n
  /-- Truncated singular series: `S_Q(n) ≥ s0` for even `n ∈ [X - H, X]` outside
  `K H (log X)^{-A}` exceptions. -/
  singSeries : (((win X H).filter (fun n => Even n ∧ SQ Q n < s0)).card : ℝ)
    ≤ K * H / Real.log X ^ A
  /-- The error `cν Q² E` leaves `c Y` of the main term `cν cω Y s0`. -/
  budget : c * Y ≤ cν * cω * Y * s0 - cν * (Q : ℝ) ^ 2 * E

/-- PROVED: `Sec5ObjectsMT` gives `Prop21.Sec5Objects` with `T = Tν`; the `mainTerm` field is
derived, not assumed. -/
noncomputable def Sec5ObjectsMT.toSec5 {X Y H K B A c : ℝ} (hY : 0 ≤ Y)
    (o : Sec5ObjectsMT X Y H K B A c) : Sec5Objects X Y H K B A c where
  ν := o.ν
  ω := o.ω
  T := Tnu o.cν Y o.Q
  Tp := o.Tp
  nu_le := o.nu_le
  omega_le := o.omega_le
  omega_window := o.omega_window
  nu_supp := o.nu_supp
  omega_supp := o.omega_supp
  omega_norm := o.omega_norm
  T_supp := o.T_supp
  Tp_supp := o.Tp_supp
  Tp_nonneg := o.Tp_nonneg
  lemma42 := o.lemma42
  cor43 := o.cor43
  mainTerm := le_trans (mainTerm_count o.cnu_nonneg o.comega_nonneg hY o.E_nonneg o.ap29 o.budget)
    o.singSeries

end LeanLab.Grimmelt2019.MainTerm
