module

public import LeanLab.PerelliPintz1992.Kernel
public import LeanLab.PNTPort.BV.Helpers
public import LeanLab.HeathBrown1985.SingularSeries

/-!
P0070 Perelli-Pintz 1992, Section 4, pp. 359-362: the major arcs estimate (6), split into
leaf lemmas. Unit U-1519, track T1, run 20261025T1603Z-10248.

The paper's chain, read from the rendered page images:
* (8), p. 359: `∫_𝔐 |S|² e(-2kα) = Σ_{q ≤ L^{B/2}} Σ*_a e(-2ka/q) ∫_{-L^B/qN}^{L^B/qN} |S(a/q+η)|² e(-2kη) dη`.
* p. 360: `|S(a/q+η)|² = μ(q)²/φ(q)² |T(η)|² + O(|R|²) + O(|T R|/φ(q))`,
  `R(η,q,a) = S(a/q+η) - μ(q)/φ(q) T(η)`, `T(η) = Σ_{n=N}^{2N} e(nη)`.
* (9), p. 360: `∫_{-L^B/qN}^{L^B/qN} |T|² e(-2kη) dη = ∫_{-1/2}^{1/2} ... + O(qN L^{-B})`.
  The paper prints the value as `N + O(H + qN L^{-B})`; the exact value of the full integral
  is `N + 1 - 2k`, and (20) uses the main term `𝔖(2k)(N - 2k)`, so the printed `N` is read as
  `N - 2k`. See the QUESTION in STATEMENTS.md. The leaves below use `N + 1 - 2k`.
* (13)-(17), p. 361-362: the character expansion of `R`, partial summation and Siegel-Walfisz
  give `R ≪ N exp(-c √L) + N^{1/2}`. Here the same step is done with residue classes instead of
  characters: `R` is a sum over the reduced residues `b` of Abel sums of
  `Λ(n) 1_{n ≡ b} - 1/φ(q)`, plus the residues with `(b,q) > 1`. Siegel-Walfisz in its
  arithmetic progression form enters as the named hypothesis `hAP`, not proved.
* (19)-(20), p. 362: the singular series `𝔖(2k) = Σ_q μ(q)²/φ(q)² c_q(-2k)` and its tail.
  The tail bound used here is the elementary Rankin type `≪ Q^{-1/2} d(2k)`, weaker than the
  paper's (6.14) of [8], `≪ L^{-B/2} k d(2k)/φ(2k)`, and still enough since `B = 2A + 100`.
  Shiu's Theorem 2 of [12], `Σ_{k=V}^{V+H} d(2k)² ≪ H L^3`, enters as the free sum
  `Σ_{k ∈ K} d(2k)²` in the explicit assembly, not proved.

CODEX task76 proves all thirteen original leaves and discharges their unproved dependencies
in the existing assemblies. R_bound remains CONDITIONAL ON its named hypothesis hAP.
The asymptotic Siegel-Walfisz and Shiu inputs are not proved here.
Proof completions by Codex task76. AI wrote the Lean code.

AI-written Lean code, Claude, unit U-1519. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach and the twin prime conjecture are OPEN.
-/

@[expose] public section

namespace LeanLab.PerelliPintz1992.Decomp1519
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992

/-! ### Definitions, p. 357 and p. 358 -/

/-- `T(η) = Σ_{n=N}^{2N} e(nη)`, p. 357. -/
noncomputable def T (N : ℕ) (η : ℝ) : ℂ := ∑ n ∈ Finset.Icc N (2 * N), e (n * η)

/-- `μ(q)/φ(q)` as a real number. -/
noncomputable def muφ (q : ℕ) : ℝ := ((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ)

/-- `R(η,q,a) = S(a/q + η) - μ(q)/φ(q) T(η)`, p. 357. -/
noncomputable def R (N q a : ℕ) (η : ℝ) : ℂ := S N ((a : ℝ) / q + η) - (muφ q : ℂ) * T N η

/-- The reduced residues `1 ≤ a ≤ q`, `(a,q) = 1`, as in `majorArcs`. -/
def As (q : ℕ) : Finset ℕ := (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)

/-- Ramanujan's sum `c_q(n) = Σ*_a e(an/q)`, p. 358. -/
noncomputable def ram (q : ℕ) (n : ℤ) : ℂ := ∑ a ∈ As q, e ((a : ℝ) * n / q)

/-- The moduli `1 ≤ q ≤ L^{B/2}` of the major arcs. -/
noncomputable def Qs (N : ℕ) (A : ℝ) : Finset ℕ := Finset.Icc 1 ⌊L N ^ (Bexp A / 2)⌋₊

/-- The half width `L^B/(qN)` of the arc `I'_{a/q}`. -/
noncomputable def wq (N : ℕ) (A : ℝ) (q : ℕ) : ℝ := L N ^ Bexp A / (q * N)

/-- The arc `I'_{a/q} = (a/q - L^B/(qN), a/q + L^B/(qN))`. -/
noncomputable def arc (N : ℕ) (A : ℝ) (q a : ℕ) : Set ℝ :=
  Ioo ((a : ℝ) / q - wq N A q) ((a : ℝ) / q + wq N A q)

/-- The truncated singular series `Σ_{q ≤ L^{B/2}} μ(q)²/φ(q)² c_q(-2k)` of (11). -/
noncomputable def Str (N : ℕ) (A : ℝ) (k : ℕ) : ℂ :=
  ∑ q ∈ Qs N A, ((muφ q ^ 2 : ℝ) : ℂ) * ram q (-(2 * k : ℤ))

/-! ### Leaves for (8), p. 359 -/

/-- The arcs `I'_{a/q}`, `q ≤ L^{B/2}`, `(a,q) = 1`, are pairwise disjoint once
`2 L^{3B/2} < N`: distinct reduced fractions are `≥ 1/(qq')` apart and
`L^B/(qN) + L^B/(q'N) < 1/(qq')`. Implicit in (8), p. 359. Unit U-1519. -/
theorem arcs_disjoint {N : ℕ} {A : ℝ} (hA : 0 < A) (hN : 2 ≤ N)
    (hbig : 2 * L N ^ (3 * Bexp A / 2) < N) :
    ∀ q ∈ Qs N A, ∀ q' ∈ Qs N A, ∀ a ∈ As q, ∀ a' ∈ As q', (q, a) ≠ (q', a') →
      Disjoint (arc N A q a) (arc N A q' a') := by
  intro q hq q' hq' a ha a' ha' hne
  obtain ⟨hq1,hq2⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hq'1,hq'2⟩ := Finset.mem_Icc.mp hq'
  obtain ⟨haI, hac⟩ := Finset.mem_filter.mp ha
  obtain ⟨ha'I, ha'c⟩ := Finset.mem_filter.mp ha'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq'pos : (0 : ℝ) < q' := by exact_mod_cast (by omega : 0 < q')
  have hL := L_pos hN
  have hqbound : (q : ℝ) ≤ L N ^ (Bexp A / 2) :=
    (Nat.le_floor_iff (Real.rpow_nonneg hL.le _)).mp hq2
  have hq'bound : (q' : ℝ) ≤ L N ^ (Bexp A / 2) :=
    (Nat.le_floor_iff (Real.rpow_nonneg hL.le _)).mp hq'2
  have hprod : L N ^ Bexp A * L N ^ (Bexp A / 2) = L N ^ (3 * Bexp A / 2) := by
    rw [← Real.rpow_add hL]; congr 1; ring
  have hwidth : L N ^ Bexp A * (q + q') < N := by
    nlinarith [mul_le_mul_of_nonneg_left hqbound (Real.rpow_nonneg hL.le (Bexp A)),
      mul_le_mul_of_nonneg_left hq'bound (Real.rpow_nonneg hL.le (Bexp A))]
  have hcross : a * q' ≠ a' * q := by
    intro he
    have hd1 : q ∣ q' := hac.symm.dvd_mul_left.mp (he ▸ Nat.dvd_mul_left q a')
    have hd2 : q' ∣ q := ha'c.symm.dvd_mul_left.mp (he.symm ▸ Nat.dvd_mul_left q' a)
    have heq : q = q' := Nat.dvd_antisymm hd1 hd2
    subst q'
    have hea : a = a' := Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) he
    exact hne (by simp [hea])
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have htranslate : ∀ r b : ℕ, 0 < (r : ℝ) → x ∈ arc N A r b →
      (b : ℝ) * N - L N ^ Bexp A < x * r * N ∧
      x * r * N < (b : ℝ) * N + L N ^ Bexp A := by
    intro r b hr hx
    have hrN : 0 < (r : ℝ) * N := mul_pos hr hNpos
    have hminus : (b : ℝ) / r - wq N A r = (b * N - L N ^ Bexp A) / (r * N) := by
      unfold wq; field_simp
    have hplus : (b : ℝ) / r + wq N A r = (b * N + L N ^ Bexp A) / (r * N) := by
      unfold wq; field_simp
    rw [arc, mem_Ioo, hminus, hplus] at hx
    exact ⟨by nlinarith [(div_lt_iff₀ hrN).mp hx.1], by nlinarith [(lt_div_iff₀ hrN).mp hx.2]⟩
  obtain ⟨hxl,hxu⟩ := htranslate q a hqpos hx
  obtain ⟨hx'l,hx'u⟩ := htranslate q' a' hq'pos hx'
  rcases lt_or_gt_of_ne hcross with hc | hc
  · have hgap : (a : ℝ) * q' + 1 ≤ a' * q := by exact_mod_cast hc
    nlinarith [mul_pos hq'pos (sub_pos.mpr hxu), mul_pos hqpos (sub_pos.mpr hx'l)]
  · have hgap : (a' : ℝ) * q + 1 ≤ a * q' := by exact_mod_cast hc
    nlinarith [mul_pos hqpos (sub_pos.mpr hx'u), mul_pos hq'pos (sub_pos.mpr hxl)]

/-- The major arcs `𝔐` of p. 357 are the union of the arcs `I'_{a/q}` over `q ∈ Qs`,
`a ∈ As q`. Unit U-1519. -/
theorem majorArcs_eq_iUnion (N : ℕ) {A : ℝ} (hA : 0 < A) :
    majorArcs N A = ⋃ q ∈ Qs N A, ⋃ a ∈ As q, arc N A q a := by
  unfold Qs As arc wq
  have hindex : ∀ q : ℕ, (1 ≤ q ∧ (q : ℝ) ≤ L N ^ (Bexp A / 2)) ↔
      1 ≤ q ∧ q ≤ ⌊L N ^ (Bexp A / 2)⌋₊ := by
    intro q
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩
      have hx : 0 ≤ L N ^ (Bexp A / 2) := Real.rpow_nonneg (Real.log_natCast_nonneg N) _
      exact ⟨h1, (Nat.le_floor_iff hx).mp h2⟩
  ext x
  simp only [majorArcs, mem_iUnion, mem_ofPred_eq, Finset.mem_Icc, Finset.mem_filter]
  simp_rw [hindex]
  aesop

/-- (8), p. 359, given the disjointness of the arcs: `∫_𝔐 |S|² e(-2kα) dα =
Σ_{q ≤ L^{B/2}} Σ*_a e(-2ka/q) ∫_{-L^B/qN}^{L^B/qN} |S(a/q + η)|² e(-2kη) dη`.
Unit U-1519. -/
theorem eq8_of_disjoint (N k : ℕ) (A : ℝ)
    (hdisj : ∀ q ∈ Qs N A, ∀ q' ∈ Qs N A, ∀ a ∈ As q, ∀ a' ∈ As q', (q, a) ≠ (q', a') →
      Disjoint (arc N A q a) (arc N A q' a')) :
    (∫ α in ⋃ q ∈ Qs N A, ⋃ a ∈ As q, arc N A q a,
        ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) =
      ∑ q ∈ Qs N A, ∑ a ∈ As q, e (-(2 * k * ((a : ℝ) / q))) *
        ∫ η in Ioo (-wq N A q) (wq N A q),
          ((‖S N ((a : ℝ) / q + η)‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η)) := by
  have hfi : ∀ q a, IntegrableOn (F N k) (arc N A q a) := by
    intro q a
    exact (continuous_F N k).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  change (∫ α in ⋃ q ∈ Qs N A, ⋃ a ∈ As q, arc N A q a, F N k α) = _
  rw [integral_biUnion_finset (s := fun q => ⋃ a ∈ As q, arc N A q a) (Qs N A)
    (fun q hq => Finset.measurableSet_biUnion (As q) fun a ha => measurableSet_Ioo)
    (by
      intro q hq q' hq' hne
      refine disjoint_iUnion_left.mpr fun a => disjoint_iUnion_left.mpr fun ha => ?_
      refine disjoint_iUnion_right.mpr fun a' => disjoint_iUnion_right.mpr fun ha' => ?_
      exact hdisj q hq q' hq' a ha a' ha' (by intro h; exact hne (Prod.mk.inj h).1))
    (fun q hq => integrableOn_finset_iUnion.mpr (fun a ha => hfi q a))]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_biUnion_finset (s := arc N A q) (As q) (fun a ha => measurableSet_Ioo)
    (by
      intro a ha a' ha' hne
      exact hdisj q hq q hq a ha a' ha' (by intro h; exact hne (Prod.mk.inj h).2))
    (fun a ha => hfi q a)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hp : (fun x : ℝ => (a : ℝ)/q+x) ⁻¹' arc N A q a = Ioo (-wq N A q) (wq N A q) := by
    ext x
    simp only [mem_preimage, arc, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [← (measurePreserving_add_left volume ((a : ℝ)/q)).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft ((a : ℝ)/q)).measurableEmbedding (F N k) (arc N A q a), hp,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with η
  unfold F
  rw [show -(2 * (k : ℝ) * ((a : ℝ)/q+η)) = -(2*k*((a : ℝ)/q)) + -(2*k*η) by ring, e_add]
  ring

/-! ### Leaves for (9) and (10), p. 360 -/

/-- The pointwise expansion before (9), p. 360: with `S(a/q+η) = μ/φ T + R`,
`||S|² - μ²/φ² |T|²| ≤ |R|² + 2 |μ/φ| |T| |R|`. Unit U-1519. -/
theorem normSq_S_sub_le (N q a : ℕ) (η : ℝ) :
    |‖S N ((a : ℝ) / q + η)‖ ^ 2 - muφ q ^ 2 * ‖T N η‖ ^ 2| ≤
      ‖R N q a η‖ ^ 2 + 2 * |muφ q| * ‖T N η‖ * ‖R N q a η‖ := by
  let x := S N ((a : ℝ) / q + η)
  let y := (muφ q : ℂ) * T N η
  have h1 := abs_norm_sub_norm_le x y
  have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by simpa using norm_add_le y (x - y)
  have h3 : |‖x‖ ^ 2 - ‖y‖ ^ 2| = |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) := by
    rw [← abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)), ← abs_mul]
    congr 1; ring
  have h4 : |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ ‖x - y‖ ^ 2 + 2 * ‖y‖ * ‖x - y‖ := by
    rw [h3]
    have := mul_le_mul h1 (show ‖x‖ + ‖y‖ ≤ 2 * ‖y‖ + ‖x - y‖ by linarith)
      (add_nonneg (norm_nonneg x) (norm_nonneg y)) (norm_nonneg (x - y))
    nlinarith
  have hy : ‖y‖ = |muφ q| * ‖T N η‖ := by
    simp only [y, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hy2 : ‖y‖ ^ 2 = muφ q ^ 2 * ‖T N η‖ ^ 2 := by rw [hy, mul_pow, sq_abs]
  rw [hy2, hy] at h4
  simpa only [x, y, R, mul_assoc] using h4

/-- (9), p. 360, the full integral: `∫_{-1/2}^{1/2} |T(η)|² e(-2kη) dη = N + 1 - 2k` for
`2k ≤ N`, the number of `N ≤ m, n ≤ 2N` with `n - m = 2k`. Unit U-1519. -/
theorem T_orth {N k : ℕ} (hk : 2 * k ≤ N) :
    (∫ η in Ioc (-(1 / 2 : ℝ)) (1 / 2), ((‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))) =
      (((N : ℝ) + 1 - 2 * k : ℝ) : ℂ) := by
  have hexpand : ∀ η : ℝ, ((‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η)) =
      ∑ m ∈ Finset.Icc N (2 * N), ∑ n ∈ Finset.Icc N (2 * N),
        e ((((m : ℤ) - n - 2 * k : ℤ) : ℝ) * η) := by
    intro η
    rw [Complex.ofReal_pow, ← Complex.mul_conj', T, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [conj_e, ← e_add, ← e_add]
    congr 1; push_cast; ring
  have horth : ∀ j : ℤ, (∫ η in (-(1/2 : ℝ))..(1/2), e ((j : ℝ) * η)) =
      if j = 0 then 1 else 0 := by
    intro j
    have hi : e (j : ℝ) = 1 := by
      unfold e
      convert Complex.exp_int_mul_two_pi_mul_I j using 1 <;> push_cast <;> ring
    have hp : Function.Periodic (fun η : ℝ => e ((j : ℝ) * η)) 1 := by
      intro η; dsimp only; rw [mul_add, e_add, mul_one, hi, mul_one]
    have hs := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
    norm_num at hs
    rw [hs]
    exact LeanLab.CircleOrth.integral_ee_int j
  rw [← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum (fun m _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun n _ => continuous_e.comp (continuous_const.mul continuous_id))]
  have hci : ∀ j : ℤ, IntervalIntegrable (fun η : ℝ => e ((j : ℝ) * η)) volume (-(1/2 : ℝ)) (1/2) :=
    fun j => (continuous_e.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hin : ∀ m ∈ Finset.Icc N (2*N), (∫ η in (-(1/2 : ℝ))..(1/2),
      ∑ n ∈ Finset.Icc N (2*N), e ((((m : ℤ)-n-2*k : ℤ) : ℝ)*η)) =
      ∑ n ∈ Finset.Icc N (2*N), if (m : ℤ)-n-2*k = 0 then (1 : ℂ) else 0 := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun (n : ℕ) _ => hci ((m : ℤ)-(n : ℤ)-2*k))]
    simp_rw [horth]
  rw [Finset.sum_congr rfl hin, Finset.sum_comm]
  have hcond : ∀ m n : ℕ, ((m : ℤ)-n-2*k = 0) ↔ m = n+2*k := by intros; omega
  simp_rw [hcond, Finset.sum_ite_eq']
  have hsum : (∑ n ∈ Finset.Icc N (2*N), if n+2*k ∈ Finset.Icc N (2*N) then (1 : ℂ) else 0) =
      ∑ n ∈ Finset.Icc N (2*N-2*k), (1 : ℂ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
  have hcount : 2*N-2*k+1-N = N+1-2*k := by omega
  rw [hcount]
  push_cast [Nat.cast_sub (by omega : 2*k ≤ N+1)]
  ring

/-- (9), p. 360, the tail: `∫_{w ≤ |η| ≤ 1/2} |T(η)|² dη ≤ 1/(2w)` for `0 < w ≤ 1/2`,
from `|T(η)| ≤ 1/(2|η|)`. The paper writes `O(qN L^{-B})` with `w = L^B/(qN)`.
Unit U-1519. -/
theorem T_tail (N : ℕ) {w : ℝ} (hw : 0 < w) (hw2 : w ≤ 1 / 2) :
    ∫ η in Ioc (-(1 / 2 : ℝ)) (1 / 2) \ Ioo (-w) w, ‖T N η‖ ^ 2 ≤ 1 / (2 * w) := by
  have hnorm : ∀ η : ℝ, 0 < |η| → |η| ≤ 1/2 → ‖T N η‖ ≤ 1/(2*|η|) := by
    intro η hη hη2
    have heq : T N η = Kk N N (η/2) := by
      unfold T Kk
      rw [show 2*N=N+N by omega]
      apply Finset.sum_congr rfl
      intro n hn; congr 1; ring
    rw [heq]
    have hfar : ∀ j : ℤ, |η|/2 ≤ |η/2-(j : ℝ)/2| := by
      intro j
      have hscale : |η-(j : ℝ)| = 2*|η/2-(j : ℝ)/2| := by
        rw [← abs_of_pos (by norm_num : (0 : ℝ)<2), ← abs_mul]
        congr 1; ring
      by_cases hj : j=0
      · subst j; simp only [Int.cast_zero, sub_zero] at hscale ⊢; linarith
      · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
          rcases (show j ≤ -1 ∨ 1 ≤ j by omega) with hj'|hj'
          · have hjr : (j : ℝ) ≤ -1 := by exact_mod_cast hj'
            linarith [neg_le_abs (j : ℝ)]
          · have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj'
            exact hjr.trans (le_abs_self _)
        have ht := abs_sub_le (j : ℝ) η 0
        simp only [sub_zero, abs_sub_comm] at ht
        linarith
    have hb := kernel_far N N (x := η/2) (δ := |η|/2) (by positivity) hfar
    convert hb using 1 <;> congr 1 <;> ring
  let U : Set ℝ := Ioc (-(1/2 : ℝ)) (1/2) \ Ioo (-w) w
  let g : ℝ → ℝ := fun η => (1/4 : ℝ) * η ^ (-2 : ℤ)
  have hU : U = Ioc (-(1/2 : ℝ)) (-w) ∪ Icc w (1/2) := by
    ext x
    simp only [U, Set.mem_sdiff, mem_Ioc, mem_Ioo, mem_union, mem_Icc]
    constructor
    · rintro ⟨⟨hlo,hhi⟩,hnot⟩
      by_cases hx : x ≤ -w
      · exact Or.inl ⟨hlo,hx⟩
      · exact Or.inr ⟨by by_contra h; apply hnot; constructor <;> linarith, hhi⟩
    · rintro (⟨hlo,hhi⟩ | ⟨hlo,hhi⟩)
      · exact ⟨⟨hlo,by linarith⟩, fun h => by linarith [h.1]⟩
      · exact ⟨⟨by linarith,hhi⟩, fun h => by linarith [h.2]⟩
  have hgi : ∀ a b : ℝ, (∀ x ∈ Icc a b, x ≠ 0) → IntegrableOn g (Icc a b) := by
    intro a b hab
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.mul (continuousOn_id.zpow₀ (-2) (fun x hx => Or.inl (hab x hx)))
  have hneg : IntegrableOn g (Ioc (-(1/2 : ℝ)) (-w)) :=
    (hgi _ _ (by intro x hx; have := hx.2; linarith)).mono_set Ioc_subset_Icc_self
  have hpos : IntegrableOn g (Icc w (1/2)) := hgi _ _ (by intro x hx; have := hx.1; linarith)
  have hgiU : IntegrableOn g U := by
    rw [hU]; exact hneg.union hpos
  have hcont : Continuous (T N) := by
    unfold T
    exact continuous_finsetSum _ fun n _ => continuous_e.comp (continuous_const.mul continuous_id)
  have hfiU : IntegrableOn (fun η => ‖T N η‖^2) U :=
    (hcont.norm.pow 2).integrableOn_Icc.mono_set (sdiff_subset.trans Ioc_subset_Icc_self)
  have hle : (∫ η in U, ‖T N η‖^2) ≤ ∫ η in U, g η := by
    apply setIntegral_mono_on hfiU hgiU (measurableSet_Ioc.diff measurableSet_Ioo)
    intro η hη
    have hηabs : 0 < |η| ∧ |η| ≤ 1/2 := by
      obtain ⟨⟨hlo,hhi⟩,hnot⟩ := hη
      have hgap : η ≤ -w ∨ w ≤ η := by
        by_cases h : η ≤ -w
        · exact Or.inl h
        · right; by_contra h'; apply hnot; constructor <;> linarith
      constructor
      · rw [abs_pos]; intro he; rcases hgap with h|h <;> rw [he] at h <;> linarith
      · rw [abs_le]; constructor <;> linarith
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hnorm η hηabs.1 hηabs.2) 2
    convert hb using 1
    dsimp [g]
    norm_num [div_pow, mul_pow, sq_abs, zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_comm]
  have hdisj : Disjoint (Ioc (-(1/2 : ℝ)) (-w)) (Icc w (1/2)) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'; have := hx.2; have := hx'.1; linarith
  rw [hU, setIntegral_union hdisj measurableSet_Icc hneg hpos,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(1/2 : ℝ) ≤ -w),
    ← intervalIntegral.integral_of_le hw2] at hle
  have hcalc : ∀ a b : ℝ, a ≠ 0 → b ≠ 0 → (0 : ℝ) ∉ Set.uIcc a b →
      (∫ η in a..b, g η) = (1/4 : ℝ)*(1/a-1/b) := by
    intro a b ha hb hab
    rw [show (fun η => g η) = (fun η => (1/4 : ℝ)*η^(-2 : ℤ)) by rfl,
      intervalIntegral.integral_const_mul, integral_zpow (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hab⟩)]
    norm_num
    ring
  rw [hcalc _ _ (by norm_num) (by linarith) (by simp only [uIcc_of_le (by linarith : -(1/2 : ℝ) ≤ -w), mem_Icc]; intro h; linarith [h.2]),
    hcalc _ _ (ne_of_gt hw) (by norm_num) (by simp only [uIcc_of_le hw2, mem_Icc]; intro h; linarith [h.1])] at hle
  rw [← hU] at hle
  have hid : (1/4 : ℝ)*(1/(-(1/2 : ℝ))-1/(-w))+(1/4 : ℝ)*(1/w-1/(1/2 : ℝ)) = 1/(2*w)-1 := by
    field_simp
    <;> ring
  rw [hid] at hle
  exact hle.trans (by linarith)

/-! ### Leaves for (13)-(17), pp. 360-362 -/

/-- The first display of p. 361 in residue form: `S(a/q + η) = Σ_{b < q} e(ab/q)
Σ_{N ≤ n ≤ 2N, n ≡ b (q)} Λ(n) e(nη)`. Unit U-1519. -/
theorem S_split_residues (N q a : ℕ) (hq : 1 ≤ q) (η : ℝ) :
    S N ((a : ℝ) / q + η) = ∑ b ∈ Finset.range q, e ((a : ℝ) * b / q) *
      ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % q = b), (Λ n : ℂ) * e (n * η) := by
  classical
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold S
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.mod_lt n (by omega : 0 < q), ite_true]
  have he : e ((n : ℝ) * ((a : ℝ) / q + η)) = e ((a : ℝ) * ((n % q : ℕ) : ℝ) / q) * e (n * η) := by
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hn : (n : ℝ) = ((n % q : ℕ) : ℝ) + (q : ℝ) * ((n / q : ℕ) : ℝ) := by exact_mod_cast (Nat.mod_add_div n q).symm
    have harg : (n : ℝ) * ((a : ℝ) / q + η) =
        (a : ℝ) * ((n % q : ℕ) : ℝ) / q + n * η + (a * (n / q) : ℕ) := by
      push_cast
      field_simp
      nlinarith [congrArg (fun x : ℝ => x * a) hn]
    rw [harg, e_add, e_add]
    have hi : e ((a * (n / q) : ℕ) : ℝ) = 1 := by
      unfold e
      convert Complex.exp_nat_mul_two_pi_mul_I (a * (n / q)) using 1 <;> push_cast <;> ring
    rw [hi, mul_one]
  rw [he]; ring

/-- Ramanujan's sum at a reduced residue: `Σ_{b < q, (b,q)=1} e(ab/q) = μ(q)` for
`(a,q) = 1`; it turns the reduced residues into the main term `μ(q)/φ(q) T(η)` of `R`,
p. 357 and p. 361. Unit U-1519. -/
theorem ramanujan_coprime {q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), e ((a : ℝ) * b / q) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  let c : ℕ → ℂ := fun n => ∑ b ∈ (Finset.range n).filter (fun b => Nat.Coprime b n), e ((a : ℝ)*b/n)
  have hfiber : ∀ n : ℕ, 0 < n → ∀ d ∈ n.divisors,
      (∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), e ((a : ℝ)*b/n)) = c (n/d) := by
    intro n hn d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
    obtain ⟨r, rfl⟩ := Nat.dvd_of_mem_divisors hd
    rw [Nat.mul_div_cancel_left r hd0]
    dsimp [c]
    symm
    apply Finset.sum_bij (fun b _ => d*b)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨by nlinarith [hb.1], ?_⟩
      rw [Nat.gcd_mul_left, show Nat.gcd r b=1 from hb.2.symm, mul_one]
    · intro b hb b' hb' he
      exact Nat.eq_of_mul_eq_mul_left hd0 he
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      have hdb : d ∣ b := hb.2 ▸ Nat.gcd_dvd_right (d*r) b
      obtain ⟨u, rfl⟩ := hdb
      refine ⟨u, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.mul_lt_mul_left hd0).mp hb.1
      · rw [Nat.gcd_mul_left] at hb
        have hg : Nat.gcd r u = 1 := by nlinarith [hb.2]
        exact (show Nat.Coprime r u from hg).symm
    · intro b hb
      have hr0 : r ≠ 0 := by intro hr; subst r; simp at hn
      push_cast
      field_simp
  have hgroup : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, c d) =
      ∑ b ∈ Finset.range n, e ((a : ℝ)*b/n) := by
    intro n hn
    rw [← Nat.sum_div_divisors n c]
    calc (∑ d ∈ n.divisors, c (n/d)) = ∑ d ∈ n.divisors,
        ∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), e ((a : ℝ)*b/n) := by
          apply Finset.sum_congr rfl
          intro d hd; exact (hfiber n hn d hd).symm
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun b hb => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n b, by omega⟩) _
  have htotal : ∀ n : ℕ, 0 < n → n ∣ q →
      (∑ b ∈ Finset.range n, e ((a : ℝ)*b/n)) = if n=1 then 1 else 0 := by
    intro n hn hnq
    by_cases hn1 : n=1
    · subst n; simp [e]
    · rw [ite_eq_right hn1]
      have hac : Nat.Coprime a n := ha.of_dvd_right hnq
      have hp : IsPrimitiveRoot (e ((a : ℝ)/n)) n := by
        convert Complex.isPrimitiveRoot_exp_of_coprime a n (by omega) hac using 1
        unfold e; push_cast; congr 1
      have hepow : ∀ b : ℕ, e ((a : ℝ)*b/n) = e ((a : ℝ)/n)^b := by
        intro b
        induction b with
        | zero => simp [e]
        | succ b ih => rw [pow_succ, ← ih, ← e_add]; congr 1; push_cast; ring
      simp_rw [hepow]
      exact hp.geom_sum_eq_zero (by omega)
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (f := c) (g := fun n => if n=1 then (1 : ℂ) else 0) {n | n ∣ q}
    (fun m n hmn hn => hmn.trans hn)).mp
      (fun n hn hnq => (hgroup n hn).trans (htotal n hn hnq)) q (by omega) (dvd_refl q)
  rw [Nat.sum_divisorsAntidiagonal (fun d r => ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (if r=1 then 1 else 0))] at hinv
  have hs : (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      (if q/d=1 then 1 else 0)) = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    rw [Finset.sum_eq_single q]
    · rw [Nat.div_self (by omega), ite_eq_left rfl, mul_one]
    · intro d hd hdq
      have hd' := Nat.dvd_of_mem_divisors hd
      have hneq : q/d ≠ 1 := by
        intro h
        have := Nat.div_mul_cancel hd'
        rw [h, one_mul] at this
        exact hdq this
      rw [ite_eq_right hneq, mul_zero]
    · intro h; exact False.elim (h (Nat.mem_divisors_self q (by omega)))
  rw [hs] at hinv
  exact hinv.symm

/-- The residues `(b,q) > 1`, p. 361: `Σ_{N ≤ n ≤ 2N, (n,q) > 1} Λ(n) ≤ 2 q log²(2N)`;
such `n` are powers of the primes dividing `q`. The paper's bound is `≪ N^{1/2}`.
Unit U-1519. -/
theorem nonCoprime_vonMangoldt_le (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) :
    ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n ≤
      2 * q * Real.log (2 * N) ^ 2 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog2 : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : Real.log 2 ≤ Real.log (2*N) := Real.log_le_log (by norm_num) (by linarith)
  by_cases hN1 : N=1
  · subst N
    have hb : ∑ n ∈ (Finset.Icc 1 (2*1)).filter (fun n => ¬ Nat.Coprime n q), Λ n ≤ Real.log 2 := by
      calc _ ≤ ∑ n ∈ Finset.Icc 1 2, Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => vonMangoldt_nonneg)
        _ = Real.log 2 := by norm_num [Finset.sum_Icc_succ_top, vonMangoldt_apply_prime]
    norm_num only [Nat.cast_one, mul_one] at hb ⊢
    nlinarith [mul_nonneg (show 0 ≤ (q : ℝ)-1 by linarith) (sq_nonneg (Real.log 2))]
  have hN2 : 2 ≤ N := by omega
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hL1 : 1 ≤ Real.log (2*N) := by
    have h4 : Real.log (4 : ℝ) ≤ Real.log (2*N) := Real.log_le_log (by norm_num) (by linarith)
    have hlog4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ)=2^2 by norm_num, Real.log_pow]; ring
    linarith
  have hsum : ∑ n ∈ (Finset.Icc N (2*N)).filter (fun n => ¬ Nat.Coprime n q), Λ n ≤
      LeanLab.PNTPort.BV.psiBad (2*N) q := by
    unfold LeanLab.PNTPort.BV.psiBad
    rw [show (2*(N : ℝ)) = ((2*N : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨⟨by omega, hn.1.2⟩,hn.2⟩
    · intro n hn hn'; exact vonMangoldt_nonneg
  have hb := LeanLab.PNTPort.BV.psiBad_le (by linarith : (1 : ℝ) ≤ 2*N) hq
  have hlq : Real.log q ≤ q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hr : Real.log q / Real.log 2 ≤ 2*q := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith
  have h1 : Real.log q / Real.log 2 * Real.log (2*N) ≤ 2*q*Real.log (2*N) :=
    mul_le_mul_of_nonneg_right hr (by linarith)
  have h2 : 2*(q : ℝ)*Real.log (2*N) ≤ 2*q*Real.log (2*N)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2*(q : ℝ) by positivity)
      (show 0 ≤ Real.log (2*N)^2-Real.log (2*N) by nlinarith)]
  exact hsum.trans (hb.trans (h1.trans h2))

/-- Partial summation, (14), p. 361: if every initial sum `|Σ_{n=N}^{N+t} f(n)| ≤ E`,
`t ≤ N`, then `|Σ_{n=N}^{2N} f(n) e(nη)| ≤ (1 + 2π|η|N) E`. Unit U-1519. -/
theorem abel_bound (N : ℕ) (f : ℕ → ℂ) (E η : ℝ)
    (hE : ∀ t ≤ N, ‖∑ n ∈ Finset.Icc N (N + t), f n‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc N (2 * N), f n * e (n * η)‖ ≤ (1 + 2 * π * |η| * N) * E := by
  have hshift : ∀ (t : ℕ) (g : ℕ → ℂ), ∑ n ∈ Finset.Icc N (N+t), g n =
      ∑ i ∈ Finset.range (t+1), g (N+i) := by
    intro t g
    have hi : Finset.Icc N (N+t) = (Finset.range (t+1)).map (addLeftEmbedding N) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply]
      constructor
      · intro hn; exact ⟨n-N, by omega, by omega⟩
      · rintro ⟨i,hi,rfl⟩; omega
    rw [hi, Finset.sum_map]; rfl
  have hE' : ∀ t ≤ N, ‖∑ i ∈ Finset.range (t+1), f (N+i)‖ ≤ E := by
    intro t ht; rw [← hshift]; exact hE t ht
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE' 0 (by omega))
  have hdiff : ∀ i : ℕ, ‖e (((N+i+1 : ℕ) : ℝ)*η) - e (((N+i : ℕ) : ℝ)*η)‖ ≤ 2*π*|η| := by
    intro i
    have he : e (((N+i+1 : ℕ) : ℝ)*η) - e (((N+i : ℕ) : ℝ)*η) =
        e (((N+i : ℕ) : ℝ)*η) * (e η - 1) := by
      rw [show (((N+i+1 : ℕ) : ℝ)*η) = (((N+i : ℕ) : ℝ)*η)+η by push_cast; ring, e_add]
      ring
    rw [he, norm_mul, norm_e, one_mul, norm_e_sub_one]
    have h := Real.abs_sin_le_abs (x := π*η)
    rw [abs_mul, abs_of_pos pi_pos] at h
    linarith
  have hparts := Finset.sum_range_by_parts' (fun i => f (N+i))
    (fun i => e (((N+i : ℕ) : ℝ)*η)) (N+1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hparts
  rw [show 2*N = N+N by omega, hshift, hparts]
  refine (norm_sub_le _ _).trans ?_
  have htop : ‖(∑ i ∈ Finset.range (N+1), f (N+i)) * e (((N+N : ℕ) : ℝ)*η)‖ ≤ E := by
    rw [norm_mul, norm_e, mul_one]; exact hE' N le_rfl
  have hsum : ‖∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), f (N+j)) *
      (e (((N+(i+1) : ℕ) : ℝ)*η) - e (((N+i : ℕ) : ℝ)*η))‖ ≤ N*(E*(2*π*|η|)) := by
    refine (norm_sum_le _ _).trans ?_
    calc (∑ i ∈ Finset.range N, ‖(∑ j ∈ Finset.range (i+1), f (N+j)) *
        (e (((N+(i+1) : ℕ) : ℝ)*η) - e (((N+i : ℕ) : ℝ)*η))‖)
        ≤ ∑ i ∈ Finset.range N, E*(2*π*|η|) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul]
          apply mul_le_mul (hE' i (by simp only [Finset.mem_range] at hi; omega))
          · simpa only [Nat.add_assoc] using hdiff i
          · exact norm_nonneg _
          · exact hE0
      _ = _ := by simp
  nlinarith

/-! ### Leaves for the singular series, p. 362 -/

/-- The squarefree Ramanujan formula used in the singular series on page 362.
This is the elementary identity behind the bound in `norm_ram_le_gcd`. -/
theorem ram_squarefree_nat {q : ℕ} (hq : Squarefree q) (m : ℕ) :
    ram q (m : ℤ) = ((ArithmeticFunction.moebius (q / Nat.gcd q m) : ℤ) : ℂ) *
      (Nat.totient (Nat.gcd q m) : ℂ) := by
  classical
  have hq0 : q ≠ 0 := hq.ne_zero
  let c : ℕ → ℂ := fun n => ∑ b ∈ (Finset.range n).filter (fun b => Nat.Coprime b n), e ((m : ℝ)*b/n)
  have hfiber : ∀ n : ℕ, 0 < n → ∀ d ∈ n.divisors,
      (∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), e ((m : ℝ)*b/n)) = c (n/d) := by
    intro n hn d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
    obtain ⟨r, rfl⟩ := Nat.dvd_of_mem_divisors hd
    rw [Nat.mul_div_cancel_left r hd0]
    dsimp [c]
    symm
    apply Finset.sum_bij (fun b _ => d*b)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨by nlinarith [hb.1], ?_⟩
      rw [Nat.gcd_mul_left, show Nat.gcd r b=1 from hb.2.symm, mul_one]
    · intro b hb b' hb' he
      exact Nat.eq_of_mul_eq_mul_left hd0 he
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      have hdb : d ∣ b := hb.2 ▸ Nat.gcd_dvd_right (d*r) b
      obtain ⟨u, rfl⟩ := hdb
      refine ⟨u, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.mul_lt_mul_left hd0).mp hb.1
      · rw [Nat.gcd_mul_left] at hb
        have hg : Nat.gcd r u = 1 := by nlinarith [hb.2]
        exact (show Nat.Coprime r u from hg).symm
    · intro b hb
      have hr0 : r ≠ 0 := by intro hr; subst r; simp at hn
      push_cast
      field_simp
  have hgroup : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, c d) =
      ∑ b ∈ Finset.range n, e ((m : ℝ)*b/n) := by
    intro n hn
    rw [← Nat.sum_div_divisors n c]
    calc (∑ d ∈ n.divisors, c (n/d)) = ∑ d ∈ n.divisors,
        ∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), e ((m : ℝ)*b/n) := by
          apply Finset.sum_congr rfl
          intro d hd; exact (hfiber n hn d hd).symm
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun b hb => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n b, by omega⟩) _

  have htotal : ∀ r : ℕ, 0 < r →
      (∑ b ∈ Finset.range r, e ((m : ℝ)*b/r)) = if r ∣ m then (r : ℂ) else 0 := by
    intro r hr
    have hone : e ((m : ℝ)/r) = 1 ↔ r ∣ m := by
      convert Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := m) (by omega : r ≠ 0) using 1
      unfold e; push_cast; congr 1; ring
    have hepow : ∀ b : ℕ, e ((m : ℝ)*b/r) = e ((m : ℝ)/r)^b := by
      intro b
      induction b with
      | zero => simp [e]
      | succ b ih => rw [pow_succ, ← ih, ← e_add]; congr 1; push_cast; ring
    by_cases hdiv : r ∣ m
    · simp_rw [hepow, hone.mpr hdiv, one_pow]
      simp [hdiv]
    · rw [ite_eq_right hdiv]
      simp_rw [hepow]
      have hroot : e ((m : ℝ)/r)^r = 1 := by
        rw [← hepow, mul_div_cancel_right₀ _ (by exact_mod_cast (by omega : r ≠ 0))]
        unfold e
        convert Complex.exp_nat_mul_two_pi_mul_I m using 1 <;> push_cast <;> ring
      have hgeom := geom_sum_mul (e ((m : ℝ)/r)) r
      rw [hroot, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr (fun he => hdiv (hone.mp he)))
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := c) (g := fun r => if r ∣ m then (r : ℂ) else 0)).mp
    (fun r hr => (hgroup r hr).trans (htotal r hr)) q (by omega)
  rw [Nat.sum_divisorsAntidiagonal' (fun d r => ((ArithmeticFunction.moebius d : ℤ) : ℂ)*
    (if r ∣ m then (r : ℂ) else 0))] at hinv
  let g := Nat.gcd q m
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hq0
  have hgq : g ∣ q := Nat.gcd_dvd_left q m
  have hfilter : (q.divisors.filter (fun d => d ∣ m)) = g.divisors := by
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq,hq0⟩,hdm⟩
      exact ⟨Nat.dvd_gcd hdq hdm, hg0⟩
    · rintro ⟨hd,hg0⟩
      obtain ⟨hdq,hdm⟩ := Nat.dvd_gcd_iff.mp hd
      exact ⟨⟨hdq,hq0⟩,hdm⟩
  have hformula : c q = ∑ d ∈ g.divisors, ((ArithmeticFunction.moebius (q/d) : ℤ) : ℂ)*(d : ℂ) := by
    rw [← hinv]
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter, hfilter]
  have hc : (q/g).Coprime g := Nat.coprime_of_squarefree_mul (by
    simpa only [Nat.div_mul_cancel hgq] using hq)
  have hmu : ∀ d ∈ g.divisors, ArithmeticFunction.moebius (q/d) =
      ArithmeticFunction.moebius (q/g) * ArithmeticFunction.moebius (g/d) := by
    intro d hd
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdq := hdg.trans hgq
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdg (Nat.pos_of_ne_zero hg0)
    have hquot : q/d = (q/g)*(g/d) := by
      apply Nat.eq_of_mul_eq_mul_right hd0
      rw [Nat.div_mul_cancel hdq, Nat.mul_assoc, Nat.div_mul_cancel hdg, Nat.div_mul_cancel hgq]
    rw [hquot]
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hc.of_dvd_right (Nat.div_dvd_of_dvd hdg))
  have hphi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun r => (Nat.totient r : ℂ)) (g := fun r => (r : ℂ))).mp
    (fun r hr => by exact_mod_cast Nat.sum_totient r) g (Nat.pos_of_ne_zero hg0)
  rw [Nat.sum_divisorsAntidiagonal' (fun d r => ((ArithmeticFunction.moebius d : ℤ) : ℂ)*(r : ℂ))] at hphi
  have hvalue : c q = ((ArithmeticFunction.moebius (q/g) : ℤ) : ℂ) * (Nat.totient g : ℂ) := by
    rw [hformula, ← hphi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hmu d hd, Int.cast_mul, mul_assoc]
  have hrange : ram q (m : ℤ) = c q := by
    by_cases hq1 : q=1
    · subst q
      simp [ram, As, c, e]
      convert Complex.exp_nat_mul_two_pi_mul_I m using 1 <;> push_cast <;> ring
    · have hsets : As q = (Finset.range q).filter (fun b => Nat.Coprime b q) := by
        ext b
        simp only [As, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        by_cases hb0 : b=0
        · subst b; simp [Nat.coprime_zero_left, hq1]
        · by_cases hbq : b=q
          · subst b; simp [Nat.coprime_self, hq1]
          · omega
      unfold ram c
      rw [hsets]
      refine Finset.sum_congr rfl fun b hb => ?_
      congr 1; push_cast; ring
  exact hrange.trans hvalue

/-- For squarefree `q`, `|c_q(n)| ≤ (q, n)`; indeed `c_q(n) = μ(q/(q,n)) φ((q,n))`.
Unit U-1519. -/
theorem norm_ram_le_gcd {q : ℕ} (hq : Squarefree q) (n : ℤ) :
    ‖ram q n‖ ≤ (Nat.gcd q n.natAbs : ℝ) := by
  have hnat : ∀ m : ℕ, ‖ram q (m : ℤ)‖ ≤ (Nat.gcd q m : ℝ) := by
    intro m
    rw [ram_squarefree_nat hq m, norm_mul]
    have hmu1 : ‖((ArithmeticFunction.moebius (q / Nat.gcd q m) : ℤ) : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_intCast] using
        (show (|(ArithmeticFunction.moebius (q / Nat.gcd q m) : ℤ)| : ℝ) ≤ 1 by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q / Nat.gcd q m))
    calc _ ≤ 1 * ‖(Nat.totient (Nat.gcd q m) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hmu1 (norm_nonneg _)
      _ = (Nat.totient (Nat.gcd q m) : ℝ) := by simp
      _ ≤ Nat.gcd q m := by exact_mod_cast Nat.totient_le (Nat.gcd q m)
  cases n with
  | ofNat m => exact hnat m
  | negSucc m =>
    have hconj : ram q (Int.negSucc m) = (starRingEnd ℂ) (ram q ((m+1 : ℕ) : ℤ)) := by
      unfold ram
      rw [map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [conj_e]
      congr 1; push_cast; ring
    rw [hconj, Complex.norm_conj]
    exact hnat (m+1)

open LeanLab.HeathBrown1985 in
/-- The Ramanujan coefficient in the page 362 series equals the existing
HeathBrown1985 Euler product coefficient at a positive natural frequency. -/
theorem ram_term_eq_gm (m q : ℕ) (hm : 1 ≤ m) :
    ((muφ q ^ 2 : ℝ) : ℂ) * ram q (m : ℤ) = (gm m q : ℂ) := by
  classical
  by_cases hsq : Squarefree q
  · let g := Nat.gcd q m
    let r := q/g
    have hgq : g ∣ q := Nat.gcd_dvd_left q m
    have hgm : g ∣ m := Nat.gcd_dvd_right q m
    have hfac : r*g=q := Nat.div_mul_cancel hgq
    have hsqfac : Squarefree (r*g) := by rwa [hfac]
    have hsqr : Squarefree r := hsqfac.of_mul_left
    have hsqg : Squarefree g := hsqfac.of_mul_right
    have hcop : r.Coprime g := Nat.coprime_of_squarefree_mul hsqfac
    have hcopm : r.Coprime m := Nat.coprime_div_gcd_of_squarefree hsq (by omega)
    have hphi : (Nat.totient q : ℝ) = (Nat.totient r : ℝ) * Nat.totient g := by
      rw [← hfac, Nat.totient_mul hcop]; push_cast; rfl
    have hgm_g : gm m g = 1/(Nat.totient g : ℝ) := by
      calc gm m g = ∏ p ∈ g.primeFactors, 1/((p : ℝ)-1) := by
            rw [gm_eq, ite_eq_left hsqg]
            refine Finset.prod_congr rfl fun p hp => ?_
            exact vloc_dvd (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hgm)
        _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_const_one, totient_eq_prod_of_squarefree g hsqg]
    have hmur : ((ArithmeticFunction.moebius r : ℤ) : ℝ) = ∏ p ∈ r.primeFactors, (-1 : ℝ) := by
      rw [← ArithmeticFunction.isMultiplicative_moebius.prod_primeFactors hsqr, Int.cast_prod]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
      norm_num
    have hgm_r : gm m r = ((ArithmeticFunction.moebius r : ℤ) : ℝ)/(Nat.totient r : ℝ)^2 := by
      rw [gm_eq, ite_eq_left hsqr, hmur, totient_eq_prod_of_squarefree r hsqr, ← Finset.prod_pow, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      apply vloc_not_dvd (Nat.prime_of_mem_primeFactors hp)
      intro hpm
      have hd := (Nat.dvd_of_mem_primeFactors hp)
      exact (Nat.prime_of_mem_primeFactors hp).ne_one (Nat.eq_one_of_dvd_coprimes hcopm hd hpm)
    have hgmq : gm m q = ((ArithmeticFunction.moebius r : ℤ) : ℝ)/(Nat.totient r : ℝ)^2 * (1/(Nat.totient g : ℝ)) := by
      rw [← hfac, gm_mul m hcop, hgm_r, hgm_g]
    have hmu : muφ q ^ 2 = 1/(Nat.totient q : ℝ)^2 := by
      unfold muφ
      rw [div_pow]
      have hsqμ : (((ArithmeticFunction.moebius q : ℤ) : ℝ))^2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      rw [hsqμ]
    rw [hmu, ram_squarefree_nat hsq m, hgmq]
    have hgφ : (Nat.totient g : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hsqg.ne_zero.bot_lt).ne'
    have hrφ : (Nat.totient r : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hsqr.ne_zero.bot_lt).ne'
    change ((1 / (Nat.totient q : ℝ)^2 : ℝ) : ℂ) * (↑(ArithmeticFunction.moebius r : ℤ) * ↑(Nat.totient g)) = _
    rw [hphi]
    have hgφc : (Nat.totient g : ℂ) ≠ 0 := by exact_mod_cast hgφ
    have hrφc : (Nat.totient r : ℂ) ≠ 0 := by exact_mod_cast hrφ
    push_cast
    field_simp
  · simp [muφ, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, gm_eq, hsq]

/-- The singular series, p. 362, Vaughan [13] Ch. 3:
`Σ_{q ≥ 1} μ(q)²/φ(q)² c_q(-2k) = 𝔖(2k)` for `k ≥ 1`. Unit U-1519. -/
theorem singSeries_hasSum {k : ℕ} (hk : 1 ≤ k) :
    HasSum (fun q : ℕ => ((muφ q ^ 2 : ℝ) : ℂ) * ram q (-(2 * k : ℤ))) ((S2k k : ℝ) : ℂ) := by
  have hterm : ∀ q : ℕ, ((muφ q ^ 2 : ℝ) : ℂ) * ram q (-(2*k : ℤ)) = (LeanLab.HeathBrown1985.gm (2*k) q : ℂ) := by
    intro q
    have hconj : ram q (-(2*k : ℤ)) = (starRingEnd ℂ) (ram q ((2*k : ℕ) : ℤ)) := by
      unfold ram
      rw [map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [conj_e]; congr 1; push_cast; ring
    calc ((muφ q ^ 2 : ℝ) : ℂ) * ram q (-(2*k : ℤ)) =
          (starRingEnd ℂ) (((muφ q ^ 2 : ℝ) : ℂ)*ram q ((2*k : ℕ) : ℤ)) := by
            rw [map_mul, Complex.conj_ofReal, hconj]
      _ = _ := by rw [ram_term_eq_gm (2*k) q (by omega), Complex.conj_ofReal]
  have hsets : (2*k).primeFactors.filter (2 < ·) = k.primeFactors.filter (2 < ·) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp,hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpp,hpd,hp0⟩ := Nat.mem_primeFactors.mp hp
      refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp,?_,by omega⟩,hp2⟩
      exact (hpp.dvd_mul.mp hpd).resolve_left (fun h => by have := Nat.le_of_dvd (by norm_num : 0 < 2) h; omega)
    · intro hp
      obtain ⟨hp,hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpp,hpd,hp0⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp,hpd.trans (Nat.dvd_mul_left k 2),by omega⟩,hp2⟩
  have hval : LeanLab.HeathBrown1985.singular (2*k) = S2k k := by
    have he : Even (2*k) := ⟨k,by omega⟩
    rw [LeanLab.HeathBrown1985.singular, ite_eq_left he, S2k, hsets]
  simp_rw [hterm]
  rw [← hval]
  exact Complex.hasSum_ofReal.mpr (LeanLab.HeathBrown1985.hasSum_gm (2*k) (by omega))

/-- The tail of the singular series, Rankin's trick, in place of (6.14) of [8], p. 362:
`Σ_{Q < q ≤ Q', q squarefree} (q,n)/φ(q)² ≤ C Q^{-1/2} d(n)`, uniformly in `Q' `.
Unit U-1519. -/
theorem sing_tail_finite : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ Q : ℕ, 1 ≤ Q → ∀ Q' : ℕ,
    ∑ q ∈ (Finset.Ioc Q Q').filter Squarefree, (Nat.gcd q n : ℝ) / (Nat.totient q : ℝ) ^ 2 ≤
      C / Real.sqrt Q * (n.divisors.card : ℝ) := by
  have hphi : ∀ q : ℕ, Squarefree q → 1/(Nat.totient q : ℝ)^2 ≤ 16/((q : ℝ)*√(q : ℝ)) := by
    intro q hsq
    have hpoint : ∀ p ∈ q.primeFactors, (p : ℝ)^3 ≤ LeanLab.HeathBrown1985.bp p ^ 4 * ((p : ℝ)-1)^4 := by
      intro p hp
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      by_cases hp3 : p ≤ 3
      · interval_cases p <;> norm_num [LeanLab.HeathBrown1985.bp]
      · have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (by omega : 4 ≤ p)
        rw [LeanLab.HeathBrown1985.bp, ite_eq_right hp3, one_pow, one_mul]
        let t : ℝ := p-4
        have ht : 0 ≤ t := by dsimp [t]; linarith
        have he : ((p : ℝ)-1)^4-(p : ℝ)^3 = t^4+11*t^3+42*t^2+60*t+17 := by dsimp [t]; ring
        nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]
    have hqprod : (∏ p ∈ q.primeFactors, (p : ℝ)) = q := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hsq)
      push_cast at hh; exact hh
    have hP : (q : ℝ)^3 ≤ (∏ p ∈ q.primeFactors, LeanLab.HeathBrown1985.bp p)^4 * (Nat.totient q : ℝ)^4 := by
      rw [← hqprod, ← Finset.prod_pow, LeanLab.HeathBrown1985.totient_eq_prod_of_squarefree q hsq,
        ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun p hp => by positivity) hpoint
    have hb := LeanLab.HeathBrown1985.prod_bp_le q.primeFactors (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have hb0 : 0 ≤ ∏ p ∈ q.primeFactors, LeanLab.HeathBrown1985.bp p := Finset.prod_nonneg (fun p hp => by unfold LeanLab.HeathBrown1985.bp; split_ifs <;> norm_num)
    have hb4 := pow_le_pow_left₀ hb0 hb 4
    have hP' : (q : ℝ)^3 ≤ 256*(Nat.totient q : ℝ)^4 := by
      have hh := mul_le_mul_of_nonneg_right hb4 (show 0 ≤ (Nat.totient q : ℝ)^4 by positivity)
      norm_num at hh
      exact hP.trans hh
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hsq.ne_zero.bot_lt
    have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hsq.ne_zero.bot_lt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hs : ((q : ℝ)*√(q : ℝ))^2 = (q : ℝ)^3 := by rw [mul_pow, Real.sq_sqrt hq0.le]; ring
    simp only [one_mul]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [hs]
    nlinarith
  have hone : ∀ x : ℝ, 1 ≤ x → 1/(x*√x) ≤ 4/√x-4/√(x+1) := by
    intro x hx
    let a := √x
    let b := √(x+1)
    have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
    have ha2 : a^2=x := Real.sq_sqrt (by linarith)
    have hb2 : b^2=x+1 := Real.sq_sqrt (by linarith)
    have hba : b ≤ 2*a := by nlinarith
    have hineq : b ≤ 4*x*(b-a) := by
      apply (mul_le_mul_iff_of_pos_right (show 0 < b+a by positivity)).mp
      have h1 : b*(b+a) ≤ 4*x := by nlinarith [mul_le_mul_of_nonneg_left hba ha.le]
      have h2 : (4*x*(b-a))*(b+a) = 4*x := by nlinarith
      linarith
    change 1/(x*a) ≤ 4/a-4/b
    rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hineq ha.le]
  have hsum : ∀ V k : ℕ, 1 ≤ V →
      ∑ w ∈ Finset.Ico V (V+k), 1/((w : ℝ)*√(w : ℝ)) ≤ 4/√(V : ℝ)-4/√((V+k : ℕ) : ℝ) := by
    intro V k hV
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have hw : (1 : ℝ) ≤ (V+k : ℕ) := by exact_mod_cast (by omega : 1 ≤ V+k)
      have hh := hone ((V+k : ℕ) : ℝ) hw
      have he : ((V+k+1 : ℕ) : ℝ) = ((V+k : ℕ) : ℝ)+1 := by push_cast; ring
      rw [he]; linarith
  have hsum' : ∀ V M : ℕ, 1 ≤ V →
      ∑ w ∈ Finset.Icc V M, 1/((w : ℝ)*√(w : ℝ)) ≤ 4/√(V : ℝ) := by
    intro V M hV
    by_cases hVM : V ≤ M
    · have he : Finset.Icc V M = Finset.Ico V (V+(M+1-V)) := by ext w; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [he]
      have hh : (0 : ℝ) ≤ 4/√((V+(M+1-V) : ℕ) : ℝ) := by positivity
      exact (hsum V _ hV).trans (by linarith)
    · rw [Finset.Icc_eq_empty (by omega)]; simp; positivity
  have hmult : ∀ Q M d : ℕ, 1 ≤ Q → 1 ≤ d →
      (d : ℝ)*(∑ q ∈ (Finset.Ioc Q M).filter (d ∣ ·), 1/((q : ℝ)*√(q : ℝ))) ≤ 4/√(Q : ℝ) := by
    intro Q M d hQ hd
    let V : ℕ := Q/d+1
    have hsub : (Finset.Ioc Q M).filter (d ∣ ·) ⊆ (Finset.Icc V M).image (d*·) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
      obtain ⟨⟨h1,h2⟩,⟨w,rfl⟩⟩ := hq
      refine Finset.mem_image.mpr ⟨w, Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
      · have hh := (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mpr (by simpa only [Nat.mul_comm] using h1)
        dsimp [V]; omega
      · exact (Nat.le_mul_of_pos_left w (by omega)).trans h2
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hV0 : (0 : ℝ) < V := by exact_mod_cast (Nat.succ_pos (Q/d))
    have hS : (∑ q ∈ (Finset.Ioc Q M).filter (d ∣ ·), 1/((q : ℝ)*√(q : ℝ))) ≤
        (1/((d : ℝ)*√(d : ℝ)))*(4/√(V : ℝ)) := by
      calc _ ≤ ∑ q ∈ (Finset.Icc V M).image (d*·), 1/((q : ℝ)*√(q : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hq' => by positivity)
        _ = ∑ w ∈ Finset.Icc V M, 1/(((d*w : ℕ) : ℝ)*√((d*w : ℕ) : ℝ)) :=
          Finset.sum_image (by intro x hx y hy he; exact Nat.eq_of_mul_eq_mul_left (by omega) he)
        _ = (1/((d : ℝ)*√(d : ℝ)))*∑ w ∈ Finset.Icc V M, 1/((w : ℝ)*√(w : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [Nat.cast_mul, Real.sqrt_mul hd0.le]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hsum' V M (Nat.succ_le_succ (Nat.zero_le _))) (by positivity)
    have hQV : (Q : ℝ) ≤ d*V := by
      have hh : Q < d*V := by
        dsimp [V]
        have hrem := Nat.mod_lt Q (by omega : 0 < d)
        have he := Nat.mod_add_div Q d
        nlinarith
      exact_mod_cast hh.le
    have hsqrt : √(Q : ℝ) ≤ √(d : ℝ)*√(V : ℝ) := by
      rw [← Real.sqrt_mul hd0.le]; exact Real.sqrt_le_sqrt hQV
    have hb : (d : ℝ)*((1/((d : ℝ)*√(d : ℝ)))*(4/√(V : ℝ))) ≤ 4/√(Q : ℝ) := by
      rw [show (d : ℝ)*((1/((d : ℝ)*√(d : ℝ)))*(4/√(V : ℝ))) = 4/(√(d : ℝ)*√(V : ℝ)) by field_simp]
      exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by exact_mod_cast hQ)) hsqrt
    exact (mul_le_mul_of_nonneg_left hS hd0.le).trans hb
  refine ⟨64,by norm_num, fun n hn Q hQ M => ?_⟩
  have hfirst : (∑ q ∈ (Finset.Ioc Q M).filter Squarefree, (Nat.gcd q n : ℝ)/(Nat.totient q : ℝ)^2) ≤
      16*∑ q ∈ Finset.Ioc Q M, (Nat.gcd n q : ℝ)*(1/((q : ℝ)*√(q : ℝ))) := by
    have hterm : ∀ q ∈ (Finset.Ioc Q M).filter Squarefree,
        (Nat.gcd q n : ℝ)/(Nat.totient q : ℝ)^2 ≤
          16*((Nat.gcd n q : ℝ)*(1/((q : ℝ)*√(q : ℝ)))) := by
      intro q hq
      have hh := mul_le_mul_of_nonneg_left (hphi q (Finset.mem_filter.mp hq).2)
        (show (0 : ℝ) ≤ Nat.gcd q n by positivity)
      simpa only [Nat.gcd_comm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_one, one_mul] using hh
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q hq hq' => by positivity)
  have hsecond := LeanLab.HeathBrown1985.sum_gcd_mul_le n hn (Finset.Ioc Q M) (fun q => 1/((q : ℝ)*√(q : ℝ))) (by intros; positivity)
  have hthird : (∑ d ∈ n.divisors, (d : ℝ)*∑ q ∈ (Finset.Ioc Q M).filter (d ∣ ·), 1/((q : ℝ)*√(q : ℝ))) ≤
      (n.divisors.card : ℝ)*(4/√(Q : ℝ)) := by
    have hh := Finset.sum_le_sum (s := n.divisors) (fun d hd =>
      hmult Q M d hQ (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn))
    simpa only [Finset.sum_const, nsmul_eq_mul] using hh
  calc _ ≤ 16*((n.divisors.card : ℝ)*(4/√(Q : ℝ))) :=
      hfirst.trans (mul_le_mul_of_nonneg_left (hsecond.trans hthird) (by norm_num))
    _ = _ := by ring

/-! ### Assemblies with real proofs -/

/-- (8), p. 359, from `arcs_disjoint`, `majorArcs_eq_iUnion` and `eq8_of_disjoint`.
Unit U-1519. -/
theorem eq8 {N : ℕ} {A : ℝ} (k : ℕ) (hA : 0 < A) (hN : 2 ≤ N)
    (hbig : 2 * L N ^ (3 * Bexp A / 2) < N) :
    (∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) =
      ∑ q ∈ Qs N A, ∑ a ∈ As q, e (-(2 * k * ((a : ℝ) / q))) *
        ∫ η in Ioo (-wq N A q) (wq N A q),
          ((‖S N ((a : ℝ) / q + η)‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η)) := by
  rw [majorArcs_eq_iUnion N hA]
  exact eq8_of_disjoint N k A (arcs_disjoint hA hN hbig)

lemma continuous_T (N : ℕ) : Continuous (T N) := by
  unfold T
  exact continuous_finsetSum _ fun n _ => continuous_e.comp (continuous_const.mul continuous_id)

lemma norm_T_le (N : ℕ) (η : ℝ) : ‖T N η‖ ≤ N + 1 := by
  unfold T
  calc ‖∑ n ∈ Finset.Icc N (2 * N), e (n * η)‖
      ≤ ∑ n ∈ Finset.Icc N (2 * N), ‖e (n * η)‖ := norm_sum_le _ _
    _ = N + 1 := by
        rw [Finset.sum_congr rfl (fun n _ => norm_e _), Finset.sum_const, nsmul_eq_mul, mul_one,
          Nat.card_Icc]
        have : 2 * N + 1 - N = N + 1 := by omega
        rw [this]; push_cast; ring

lemma norm_ofReal_mul_e (x y : ℝ) : ‖((x : ℝ) : ℂ) * e y‖ = |x| := by
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The arc integral, (9) and (10) with sup bounds, p. 360, from `normSq_S_sub_le`, `T_orth`
and `T_tail`: if `|R(η,q,a)| ≤ ρ` on `(-w, w)`, `0 < w ≤ 1/2`, `2k ≤ N`, then
`|∫_{-w}^{w} |S(a/q+η)|² e(-2kη) dη - μ²/φ² (N + 1 - 2k)| ≤
μ²/φ² /(2w) + 2w (ρ² + 2 |μ/φ| (N+1) ρ)`. Unit U-1519. -/
theorem arc_integral_bound (N k q a : ℕ) (hk : 2 * k ≤ N) {w ρ : ℝ} (hw : 0 < w)
    (hw2 : w ≤ 1 / 2) (hρ : ∀ η ∈ Ioo (-w) w, ‖R N q a η‖ ≤ ρ) :
    ‖(∫ η in Ioo (-w) w, ((‖S N ((a : ℝ) / q + η)‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))) -
        ((muφ q ^ 2 * ((N : ℝ) + 1 - 2 * k) : ℝ) : ℂ)‖ ≤
      muφ q ^ 2 / (2 * w) + 2 * w * (ρ ^ 2 + 2 * |muφ q| * (N + 1) * ρ) := by
  set m := muφ q
  set U : Set ℝ := Ioc (-(1 / 2 : ℝ)) (1 / 2)
  set W : Set ℝ := Ioo (-w) w
  have hWU : W ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set g : ℝ → ℂ := fun η => ((‖S N ((a : ℝ) / q + η)‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))
  set h : ℝ → ℂ := fun η => ((‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))
  have hce : Continuous fun η : ℝ => e (-(2 * k * η)) :=
    continuous_e.comp (continuous_const.mul continuous_id).neg
  have hg : Continuous g := by
    refine Continuous.mul ?_ hce
    exact Complex.continuous_ofReal.comp
      (((continuous_S N).comp (continuous_const.add continuous_id)).norm.pow 2)
  have hh : Continuous h := by
    refine Continuous.mul ?_ hce
    exact Complex.continuous_ofReal.comp ((continuous_T N).norm.pow 2)
  have hUfin : volume U < ⊤ := by simp [U]
  have hWfin : volume W < ⊤ := by simp [W]
  have hhU : IntegrableOn h U volume := hh.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hhW : IntegrableOn h W volume := hhU.mono_set hWU
  have hgW : IntegrableOn g W volume :=
    (hg.integrableOn_Icc (a := -w) (b := w)).mono_set Ioo_subset_Icc_self
  -- split `∫_U h = ∫_W h + ∫_{U \ W} h`
  have hsplit : (∫ η in U, h η) = (∫ η in W, h η) + ∫ η in U \ W, h η := by
    rw [← setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioc.diff measurableSet_Ioo)
      hhW (hhU.mono_set sdiff_subset), union_sdiff_cancel hWU]
  have horth : (∫ η in U, h η) = (((N : ℝ) + 1 - 2 * k : ℝ) : ℂ) := T_orth hk
  -- tail bound
  have htail : ‖∫ η in U \ W, h η‖ ≤ 1 / (2 * w) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ η, ‖h η‖ = ‖T N η‖ ^ 2 := fun η => by
      simp only [h]; rw [norm_ofReal_mul_e, abs_of_nonneg (sq_nonneg _)]
    simp_rw [this]
    exact T_tail N hw hw2
  -- the `R` part
  have hdiff : ‖∫ η in W, (g η - ((m ^ 2 : ℝ) : ℂ) * h η)‖ ≤
      (ρ ^ 2 + 2 * |m| * (N + 1) * ρ) * volume.real W := by
    refine norm_setIntegral_le_of_norm_le_const hWfin fun η hη => ?_
    have hR := hρ η hη
    have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hR
    have e1 : g η - ((m ^ 2 : ℝ) : ℂ) * h η =
        ((‖S N ((a : ℝ) / q + η)‖ ^ 2 - m ^ 2 * ‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η)) := by
      simp only [g, h]; push_cast; ring
    rw [e1, norm_ofReal_mul_e]
    refine (normSq_S_sub_le N q a η).trans ?_
    have hT := norm_T_le N η
    have hR0 := norm_nonneg (R N q a η)
    have hm0 := abs_nonneg m
    have h1 : ‖R N q a η‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hR0 hR 2
    have h2 : 2 * |m| * ‖T N η‖ * ‖R N q a η‖ ≤ 2 * |m| * (N + 1) * ρ := by
      have := mul_le_mul hT hR hR0 (by positivity)
      nlinarith
    linarith
  have hvol : volume.real W = 2 * w := by
    simp only [W, Measure.real, Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by linarith)]; ring
  rw [hvol] at hdiff
  -- assemble
  have hgsplit : (∫ η in W, g η) = (∫ η in W, (g η - ((m ^ 2 : ℝ) : ℂ) * h η)) +
      ((m ^ 2 : ℝ) : ℂ) * ∫ η in W, h η := by
    rw [integral_sub hgW (hhW.const_mul _), integral_const_mul]; ring
  have hkey : (∫ η in W, g η) - ((m ^ 2 * ((N : ℝ) + 1 - 2 * k) : ℝ) : ℂ) =
      (∫ η in W, (g η - ((m ^ 2 : ℝ) : ℂ) * h η)) -
        ((m ^ 2 : ℝ) : ℂ) * ∫ η in U \ W, h η := by
    rw [hgsplit]
    have : (∫ η in W, h η) = (((N : ℝ) + 1 - 2 * k : ℝ) : ℂ) - ∫ η in U \ W, h η := by
      rw [← horth, hsplit]; ring
    rw [this]; push_cast; ring
  show ‖(∫ η in W, g η) - ((m ^ 2 * ((N : ℝ) + 1 - 2 * k) : ℝ) : ℂ)‖ ≤ _
  rw [hkey]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg m)]
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  have := mul_le_mul_of_nonneg_left htail hm2
  have e2 : m ^ 2 * (1 / (2 * w)) = m ^ 2 / (2 * w) := by ring
  linarith

lemma coprime_mod_iff (n q : ℕ) : Nat.Coprime (n % q) q ↔ Nat.Coprime n q := by
  unfold Nat.Coprime; rw [← Nat.gcd_rec, Nat.gcd_comm]

/-- The bound (17), p. 362, in residue form, from `S_split_residues`, `ramanujan_coprime`,
`abel_bound` and `nonCoprime_vonMangoldt_le`. The hypothesis `hAP` is the Siegel-Walfisz input
(16), p. 361, in arithmetic progression form: for every reduced residue `b` and `t ≤ N`,
`|Σ_{N ≤ n ≤ N+t, n ≡ b} Λ(n) - (t+1)/φ(q)| ≤ E`; it is NOT proved here. Conclusion:
`|R(η,q,a)| ≤ φ(q)(1 + 2π|η|N) E + 2 q log²(2N)`. CONDITIONAL ON `hAP`. Unit U-1519. -/
theorem R_bound (N q a : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (ha : Nat.Coprime a q) (η E : ℝ)
    (hAP : ∀ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), ∀ t ≤ N,
      ‖∑ n ∈ Finset.Icc N (N + t), (((if n % q = b then Λ n else 0 : ℝ) : ℂ) -
        ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ))‖ ≤ E) :
    ‖R N q a η‖ ≤ (Nat.totient q : ℝ) * ((1 + 2 * π * |η| * N) * E) +
      2 * q * Real.log (2 * N) ^ 2 := by
  classical
  set P := (Finset.range q).filter (fun b => Nat.Coprime b q) with hP
  set Pc := (Finset.range q).filter (fun b => ¬ Nat.Coprime b q) with hPc
  set X : ℕ → ℂ := fun b =>
    ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % q = b), (Λ n : ℂ) * e (n * η) with hXdef
  set c : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) with hc
  have hX : ∀ b, X b - c * T N η = ∑ n ∈ Finset.Icc N (2 * N),
      (((if n % q = b then Λ n else 0 : ℝ) : ℂ) - c) * e (n * η) := by
    intro b
    simp only [X, T]
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> push_cast <;> ring
  have hS : S N ((a : ℝ) / q + η) =
      ∑ b ∈ P, e ((a : ℝ) * b / q) * X b + ∑ b ∈ Pc, e ((a : ℝ) * b / q) * X b := by
    rw [S_split_residues N q a hq η, ← Finset.sum_filter_add_sum_filter_not (Finset.range q)
      (fun b => Nat.Coprime b q)]
  have hmu : ((muφ q : ℝ) : ℂ) * T N η = ∑ b ∈ P, e ((a : ℝ) * b / q) * (c * T N η) := by
    rw [← Finset.sum_mul, ramanujan_coprime hq ha, muφ, hc]
    push_cast; ring
  have hR : R N q a η = ∑ b ∈ P, e ((a : ℝ) * b / q) * (X b - c * T N η) +
      ∑ b ∈ Pc, e ((a : ℝ) * b / q) * X b := by
    rw [R, hS, hmu]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]; ring
  rw [hR]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- reduced residues
    refine (norm_sum_le _ _).trans ?_
    have hcard : (P.card : ℝ) = Nat.totient q := by
      rw [Nat.totient_eq_card_coprime]
      congr 2
      exact Finset.filter_congr fun b _ => Nat.coprime_comm
    rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [norm_mul, norm_e, one_mul, hX b]
    exact abel_bound N _ E η (hAP b hb)
  · -- residues with `(b,q) > 1`
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ b ∈ Pc, ‖e ((a : ℝ) * b / q) * X b‖ ≤
        ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % q = b), Λ n := by
      intro b _
      rw [norm_mul, norm_e, one_mul]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
    refine (Finset.sum_le_sum h1).trans ?_
    have h2 : ∑ b ∈ Pc, ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % q = b), Λ n =
        ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_ite_eq]
      have hmem : n % q ∈ Pc ↔ ¬ Nat.Coprime n q := by
        rw [hPc, Finset.mem_filter, Finset.mem_range, coprime_mod_iff]
        exact ⟨fun h => h.2, fun h => ⟨Nat.mod_lt _ (by omega), h⟩⟩
      simp only [hmem]
    rw [h2]
    exact nonCoprime_vonMangoldt_le N q hN hq

/-- The error of one arc in `arc_integral_bound`, with `w = L^B/(qN)`. -/
noncomputable def errB (N : ℕ) (A ρ : ℝ) (q : ℕ) : ℝ :=
  muφ q ^ 2 / (2 * wq N A q) + 2 * wq N A q * (ρ ^ 2 + 2 * |muφ q| * (N + 1) * ρ)

/-- The total error `Σ_{q ≤ L^{B/2}} Σ*_a errB(q)` of (11), `R₁ + R₂ + R₃` in explicit form. -/
noncomputable def E19 (N : ℕ) (A ρ : ℝ) : ℝ := ∑ q ∈ Qs N A, ((As q).card : ℝ) * errB N A ρ q

lemma wq_pos {N : ℕ} {A : ℝ} {q : ℕ} (hN : 2 ≤ N) (hq : 1 ≤ q) : 0 < wq N A q := by
  have hL := L_pos hN
  unfold wq
  have : (0 : ℝ) < q * N := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    positivity
  exact div_pos (Real.rpow_pos_of_pos hL _) this

/-- (19), p. 362, in explicit form, from `eq8` and `arc_integral_bound`:
`|∫_𝔐 |S|² e(-2kα) dα - (N + 1 - 2k) Σ_{q ≤ L^{B/2}} μ²/φ² c_q(-2k)| ≤ E19`,
given `|R| ≤ ρ` on every arc. The bound `ρ` comes from `R_bound` and Siegel-Walfisz.
Unit U-1519. -/
theorem eq19_explicit (N k : ℕ) {A ρ : ℝ} (hA : 0 < A) (hN : 2 ≤ N)
    (hbig : 2 * L N ^ (3 * Bexp A / 2) < N) (hk : 2 * k ≤ N)
    (hw2 : ∀ q ∈ Qs N A, wq N A q ≤ 1 / 2)
    (hρ : ∀ q ∈ Qs N A, ∀ a ∈ As q, ∀ η ∈ Ioo (-wq N A q) (wq N A q), ‖R N q a η‖ ≤ ρ) :
    ‖(∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        (((N : ℝ) + 1 - 2 * k : ℝ) : ℂ) * Str N A k‖ ≤ E19 N A ρ := by
  rw [eq8 k hA hN hbig]
  have hStr : (((N : ℝ) + 1 - 2 * k : ℝ) : ℂ) * Str N A k =
      ∑ q ∈ Qs N A, ∑ a ∈ As q, e (-(2 * k * ((a : ℝ) / q))) *
        ((muφ q ^ 2 * ((N : ℝ) + 1 - 2 * k) : ℝ) : ℂ) := by
    unfold Str ram
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : e ((a : ℝ) * (((-(2 * k : ℤ)) : ℤ) : ℝ) / q) = e (-(2 * k * ((a : ℝ) / q))) := by
      congr 1; push_cast; ring
    rw [this]; push_cast; ring
  rw [hStr, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  unfold E19
  refine Finset.sum_le_sum fun q hq => ?_
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [← mul_sub, norm_mul, norm_e, one_mul]
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  exact arc_integral_bound N k q a hk (wq_pos hN hq1) (hw2 q hq) (hρ q hq a ha)

lemma muφ_zero : muφ 0 = 0 := by simp [muφ]

lemma muφ_sq_le_one {q : ℕ} (hq : 1 ≤ q) : muφ q ^ 2 ≤ 1 := by
  unfold muφ
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [div_pow, div_le_one (by positivity)]
  have : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
  nlinarith

lemma muφ_sq_eq_zero {q : ℕ} (hq : ¬ Squarefree q) : muφ q ^ 2 = 0 := by
  simp [muφ, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

lemma muφ_sq_le {q : ℕ} : muφ q ^ 2 ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
  unfold muφ
  rw [div_pow]
  have : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 := by
    have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [← sq_abs]; nlinarith [abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
  exact div_le_div_of_nonneg_right this (sq_nonneg _)

lemma norm_ram_le_card (q : ℕ) (n : ℤ) : ‖ram q n‖ ≤ q := by
  unfold ram
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_e]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (As q).card ≤ q := by
    unfold As
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast this

/-- The tail of the singular series, from `singSeries_hasSum`, `norm_ram_le_gcd` and
`sing_tail_finite`: `|𝔖(2k) - Σ_{q ≤ Q} μ²/φ² c_q(-2k)| ≤ C Q^{-1/2} d(2k)`.
Unit U-1519. -/
theorem sing_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ Q : ℕ, 1 ≤ Q →
    ‖((S2k k : ℝ) : ℂ) - ∑ q ∈ Finset.Icc 1 Q, ((muφ q ^ 2 : ℝ) : ℂ) * ram q (-(2 * k : ℤ))‖ ≤
      C / Real.sqrt Q * ((2 * k).divisors.card : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := sing_tail_finite
  refine ⟨C, hC0, fun k hk Q hQ => ?_⟩
  set f : ℕ → ℂ := fun q => ((muφ q ^ 2 : ℝ) : ℂ) * ram q (-(2 * k : ℤ)) with hf
  set g : ℕ → ℝ := fun q => if Squarefree q then (Nat.gcd q (2 * k) : ℝ) /
    (Nat.totient q : ℝ) ^ 2 else 0 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => by
    simp only [g]; split_ifs <;> positivity
  have hfg : ∀ q, ‖f q‖ ≤ g q := by
    intro q
    simp only [f, g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    split_ifs with hsq
    · have h1 := norm_ram_le_gcd hsq (-(2 * k : ℤ))
      have h2 : (-(2 * k : ℤ)).natAbs = 2 * k := by
        rw [Int.natAbs_neg]; exact Int.natAbs_natCast (2 * k) |>.trans rfl
      rw [h2] at h1
      calc muφ q ^ 2 * ‖ram q (-(2 * k : ℤ))‖ ≤ 1 / (Nat.totient q : ℝ) ^ 2 * (Nat.gcd q (2 * k)) :=
            mul_le_mul muφ_sq_le h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [muφ_sq_eq_zero hsq, zero_mul]
  have hs := (singSeries_hasSum hk).tendsto_sum_nat
  have hP : ∑ q ∈ Finset.Icc 1 Q, f q = ∑ q ∈ Finset.range (Q + 1), f q := by
    have : Finset.range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [this, Finset.sum_insert (by simp)]
    simp [f, muφ_zero]
  rw [hP]
  set P := ∑ q ∈ Finset.range (Q + 1), f q
  have hlim : Tendsto (fun M => ‖∑ q ∈ Finset.range M, f q - P‖) atTop
      (𝓝 ‖((S2k k : ℝ) : ℂ) - P‖) := (hs.sub_const P).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (Q + 1)] with M hM
  rw [← Finset.sum_Ico_eq_sub _ hM]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun q _ => hfg q).trans ?_
  have hsub : Finset.Ico (Q + 1) M ⊆ Finset.Ioc Q M := by
    intro x hx; simp only [Finset.mem_Ico, Finset.mem_Ioc] at hx ⊢; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hg0 q).trans ?_
  have : ∑ q ∈ Finset.Ioc Q M, g q = ∑ q ∈ (Finset.Ioc Q M).filter Squarefree,
      (Nat.gcd q (2 * k) : ℝ) / (Nat.totient q : ℝ) ^ 2 := by
    rw [Finset.sum_filter]
  rw [this]
  exact hC (2 * k) (by omega) Q hQ M

/-- **(6) in explicit form**, p. 362, the assembly of the major arcs estimate: there is a `C`
such that for all `N ≥ 2`, `A > 0` with `2 L^{3B/2} < N`, `L^B/(qN) ≤ 1/2`, `L^{B/2} ≥ 1`, any
finite set `K` of `1 ≤ k ≤ N/2` and any `ρ` bounding `|R|` on every major arc,
`Σ_{k ∈ K} |∫_𝔐 |S|² e(-2kα) dα - 𝔖(2k)(N - 2k)|² ≤
3 |K| E19² + 3 N² C²/Q₀ Σ_{k ∈ K} d(2k)² + 3 |K| Q₀⁴`, `Q₀ = ⌊L^{B/2}⌋`.
With `ρ ≪ N exp(-c √L)` from `R_bound` and Siegel-Walfisz, and `Σ d(2k)² ≪ H L³` from Shiu,
Theorem 2 of [12], the right side is `≪ H N² L^{-A}` since `B = 2A + 100`; that last
asymptotic step is not done here. Unit U-1519. -/
theorem estimate6_explicit : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (A ρ : ℝ) (K : Finset ℕ),
    0 < A → 2 ≤ N → 2 * L N ^ (3 * Bexp A / 2) < N → (∀ q ∈ Qs N A, wq N A q ≤ 1 / 2) →
    1 ≤ L N ^ (Bexp A / 2) → (∀ k ∈ K, 1 ≤ k ∧ 2 * k ≤ N) →
    (∀ q ∈ Qs N A, ∀ a ∈ As q, ∀ η ∈ Ioo (-wq N A q) (wq N A q), ‖R N q a η‖ ≤ ρ) →
    ∑ k ∈ K, ‖(∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 ≤
      3 * K.card * E19 N A ρ ^ 2 +
      3 * (N : ℝ) ^ 2 * (C ^ 2 / ⌊L N ^ (Bexp A / 2)⌋₊) *
        ∑ k ∈ K, ((2 * k).divisors.card : ℝ) ^ 2 +
      3 * K.card * (⌊L N ^ (Bexp A / 2)⌋₊ : ℝ) ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := sing_tail
  refine ⟨C, hC0, fun N A ρ K hA hN hbig hw2 hL1 hK hρ => ?_⟩
  set Q0 := ⌊L N ^ (Bexp A / 2)⌋₊ with hQ0
  have hQ1 : 1 ≤ Q0 := Nat.le_floor (by exact_mod_cast hL1)
  have hQ0pos : (0 : ℝ) < Q0 := by exact_mod_cast hQ1
  have hQs : Qs N A = Finset.Icc 1 Q0 := rfl
  have hE0 : 0 ≤ E19 N A ρ := by
    have hx : ∀ k ∈ K, 0 ≤ E19 N A ρ := fun k hk =>
      (norm_nonneg _).trans (eq19_explicit N k hA hN hbig (hK k hk).2 hw2 hρ)
    by_cases hKe : K.Nonempty
    · obtain ⟨k, hk⟩ := hKe; exact hx k hk
    · -- with `K` empty the bound is not needed; use `k = 0`
      exact (norm_nonneg _).trans (eq19_explicit N 0 hA hN hbig (by omega) hw2 hρ)
  have hStr_le : ∀ k, ‖Str N A k‖ ≤ (Q0 : ℝ) ^ 2 := by
    intro k
    unfold Str
    rw [hQs]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ q ∈ Finset.Icc 1 Q0, ‖((muφ q ^ 2 : ℝ) : ℂ) * ram q (-(2 * k : ℤ))‖ ≤ Q0 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := muφ_sq_le_one hq1
      have h2 := norm_ram_le_card q (-(2 * k : ℤ))
      have h3 : (q : ℝ) ≤ Q0 := by exact_mod_cast hq2
      have := mul_le_mul h1 (h2.trans h3) (norm_nonneg _) zero_le_one
      linarith
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have : Q0 + 1 - 1 = Q0 := by omega
    rw [this]; ring
  have hper : ∀ k ∈ K, ‖(∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 ≤
      3 * E19 N A ρ ^ 2 + 3 * (N : ℝ) ^ 2 * (C ^ 2 / Q0) * ((2 * k).divisors.card : ℝ) ^ 2 +
        3 * (Q0 : ℝ) ^ 4 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hK k hk
    set I := ∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))
    set x := I - (((N : ℝ) + 1 - 2 * k : ℝ) : ℂ) * Str N A k
    set y := (((N : ℝ) - 2 * k : ℝ) : ℂ) * (Str N A k - ((S2k k : ℝ) : ℂ))
    set z := Str N A k
    have hsplit : I - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ) = x + y + z := by
      simp only [x, y, z]; push_cast; ring
    have hx : ‖x‖ ≤ E19 N A ρ := eq19_explicit N k hA hN hbig hk2 hw2 hρ
    set d : ℝ := ((2 * k).divisors.card : ℝ)
    have hy : ‖y‖ ≤ N * (C / Real.sqrt Q0 * d) := by
      simp only [y]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
      have h1 : |(N : ℝ) - 2 * k| ≤ N := by
        rw [abs_le]
        have : (2 * k : ℝ) ≤ N := by exact_mod_cast hk2
        constructor <;> linarith [show (0 : ℝ) ≤ k by positivity]
      have h2 := hC k hk1 Q0 hQ1
      exact mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
    have hz : ‖z‖ ≤ (Q0 : ℝ) ^ 2 := hStr_le k
    rw [hsplit]
    have hn : ‖x + y + z‖ ≤ E19 N A ρ + N * (C / Real.sqrt Q0 * d) + (Q0 : ℝ) ^ 2 :=
      (norm_add₃_le).trans (by linarith)
    have hb0 : 0 ≤ N * (C / Real.sqrt Q0 * d) := by positivity
    have hsq : (N * (C / Real.sqrt Q0 * d)) ^ 2 = (N : ℝ) ^ 2 * (C ^ 2 / Q0) * d ^ 2 := by
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hQ0pos.le]; ring
    have h3 : ‖x + y + z‖ ^ 2 ≤ (E19 N A ρ + N * (C / Real.sqrt Q0 * d) + (Q0 : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (E19 N A ρ - N * (C / Real.sqrt Q0 * d)),
      sq_nonneg (E19 N A ρ - (Q0 : ℝ) ^ 2), sq_nonneg (N * (C / Real.sqrt Q0 * d) - (Q0 : ℝ) ^ 2)]
  refine (Finset.sum_le_sum hper).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    ← Finset.mul_sum, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-! ### Vacuity checks, real proofs -/

lemma logpow_le_sqrt_div4 (P : ℝ) :
    ∀ᶠ N : ℕ in atTop, L N ^ P ≤ √(N : ℝ) / 4 := by
  have h := (isLittleO_log_rpow_rpow_atTop P (by norm_num : (0 : ℝ) < 1 / 2)).def
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with N hN hN1
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hl : 0 ≤ Real.log N := Real.log_nonneg hx
  simp only [Real.norm_eq_abs] at hN
  rw [abs_of_nonneg (Real.rpow_nonneg hl _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hN
  unfold L; linarith

/-- VACUITY for `estimate6_explicit`, `eq19_explicit` and `eq8`: for every `A > 0` the
size hypotheses `N ≥ 2`, `2 L^{3B/2} < N`, `L^B/(qN) ≤ 1/2` for `q ∈ Qs` and `L^{B/2} ≥ 1`
all hold for every large `N`. Unit U-1519. -/
theorem estimate6_hyps_vacuity {A : ℝ} (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 2 * L N ^ (3 * Bexp A / 2) < N ∧
      (∀ q ∈ Qs N A, wq N A q ≤ 1 / 2) ∧ 1 ≤ L N ^ (Bexp A / 2) := by
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  filter_upwards [logpow_le_sqrt_div4 (3 * Bexp A / 2), eventually_ge_atTop 3] with N h1 h3
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ L N := by
    unfold L
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : Real.log (Real.exp 1) < Real.log N :=
      Real.log_lt_log (Real.exp_pos 1) (by linarith)
    rw [Real.log_exp] at this; linarith
  have hsq : √(N : ℝ) ≤ N := by
    rw [Real.sqrt_le_iff]; constructor <;> nlinarith
  have hP : L N ^ (3 * Bexp A / 2) ≤ N / 4 := by linarith
  refine ⟨by omega, by linarith, fun q hq => ?_, Real.one_le_rpow hL1 (by linarith)⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hLB : L N ^ Bexp A ≤ L N ^ (3 * Bexp A / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  unfold wq
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- VACUITY for `abel_bound`: the zero sequence satisfies its hypothesis with `E = 0`. -/
theorem abel_bound_vacuity (N : ℕ) :
    ∀ t ≤ N, ‖∑ n ∈ Finset.Icc N (N + t), (fun _ : ℕ => (0 : ℂ)) n‖ ≤ 0 := by
  intro t _; simp

/-- VACUITY for `R_bound`, `ramanujan_coprime`, `S_split_residues`: `q = 1`, `a = 1` is
allowed, and `hAP` holds at `q = 1` with `E` the largest initial sum. -/
theorem R_bound_vacuity (N : ℕ) : ∃ E : ℝ,
    ∀ b ∈ (Finset.range 1).filter (fun b => Nat.Coprime b 1), ∀ t ≤ N,
      ‖∑ n ∈ Finset.Icc N (N + t), (((if n % 1 = b then Λ n else 0 : ℝ) : ℂ) -
        ((1 / (Nat.totient 1 : ℝ) : ℝ) : ℂ))‖ ≤ E := by
  refine ⟨∑ t ∈ Finset.range (N + 1), ‖∑ n ∈ Finset.Icc N (N + t),
    (((if n % 1 = 0 then Λ n else 0 : ℝ) : ℂ) - ((1 / (Nat.totient 1 : ℝ) : ℝ) : ℂ))‖,
    fun b hb t ht => ?_⟩
  have hb0 : b = 0 := by simpa using hb
  subst hb0
  exact Finset.single_le_sum (f := fun t => ‖∑ n ∈ Finset.Icc N (N + t),
    (((if n % 1 = 0 then Λ n else 0 : ℝ) : ℂ) - ((1 / (Nat.totient 1 : ℝ) : ℝ) : ℂ))‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))

end LeanLab.PerelliPintz1992.Decomp1519
