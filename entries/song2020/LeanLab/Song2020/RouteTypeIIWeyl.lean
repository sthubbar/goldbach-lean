module

public import LeanLab.Song2020.Characteristic139

/-!
AI wrote the Lean code, 2026-11-15, the Weyl and
van der Corput shift inequality for the Type II sum T(R,S).
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 6 and 7,
"By Lemma 2.5 in [2], we have T(R,S)^2 << (RS)^2/L + (R S^2/L) sum over 1 <= |l| <= L of
max over s of the modulus of the sum over r in I of e(R_b(r(s+l)) - R_b(r s))", which is
Graham and Kolesnik Lemma 2.5 applied to T(R,S).
This new file proves the statement of SPLIT_typeII_per_RS.weyl_shift directly, with the
constant 36. The argument is the classical one: Cauchy over r, the shift of s by k in
[0, L), Cauchy over the shifted variable, expansion of the square, and summation over r
before any modulus is taken, so that the off diagonal terms are the correlations bounded
by the hypothesis. The file defines nothing.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteTypeIIWeyl

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Page 7, the modulus of e(x) is 1, used for the trivial bound of the coefficients of
T(R,S). -/
theorem norm_eC_one (θ : ℝ) : ‖eC θ‖ = 1 := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- Page 7, e(x) times the conjugate of e(y) is e(x - y); this is how the difference
R_b(r(s+l)) - R_b(r s) appears when the square is expanded. -/
theorem eC_mul_conj (x y : ℝ) : eC x * (starRingEnd ℂ) (eC y) = eC (x - y) := by
  unfold eC
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- Page 7, the number of integers in a real interval [A, B) is at most B - A + 1; used
for r ~ R and for the shifted range of s. -/
theorem card_real_interval (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    (((Finset.range N).filter (fun m : ℕ => A ≤ (m : ℝ) ∧ (m : ℝ) < B)).card : ℝ) ≤
      B - A + 1 := by
  have hsub : (Finset.range N).filter (fun m : ℕ => A ≤ (m : ℝ) ∧ (m : ℝ) < B) ⊆
      Finset.Ico ⌈A⌉₊ ⌈B⌉₊ := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_Ico]
    exact ⟨Nat.ceil_le.mpr hm.2.1, Nat.lt_ceil.mpr hm.2.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ico] at h1
  have h2 : ((⌈B⌉₊ - ⌈A⌉₊ : ℕ) : ℝ) ≤ B - A + 1 := by
    have hB := Nat.ceil_lt_add_one (hA.trans hAB)
    have hA' := Nat.le_ceil A
    rcases le_total ⌈A⌉₊ ⌈B⌉₊ with h | h
    · rw [Nat.cast_sub h]; linarith
    · rw [Nat.sub_eq_zero_of_le h]; simp only [Nat.cast_zero]; linarith
  exact (Nat.cast_le.mpr h1).trans h2

/-- Graham and Kolesnik Lemma 2.5 as used on page 7, the abstract shift step. If every
shift k in [0, L) of the inner sum over m reproduces U r, then L^2 times the sum over r of
|U r|^2 is at most the number of m times the sum over pairs of shifts of the modulus of
the correlation, where the correlation is summed over r and m before the modulus. -/
theorem shift_cauchy (Rs M : Finset ℕ) (L : ℕ) (F : ℕ → ℕ → ℕ → ℂ) (U : ℕ → ℂ)
    (hU : ∀ r ∈ Rs, ∀ k ∈ Finset.range L, ∑ m ∈ M, F r m k = U r) :
    (L : ℝ) ^ 2 * ∑ r ∈ Rs, ‖U r‖ ^ 2 ≤
      (M.card : ℝ) * ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ‖∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k')‖ := by
  have h1 : ∀ r ∈ Rs, (L : ℝ) ^ 2 * ‖U r‖ ^ 2 ≤
      (M.card : ℝ) * ∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖ ^ 2 := by
    intro r hr
    have e : (L : ℂ) * U r = ∑ m ∈ M, ∑ k ∈ Finset.range L, F r m k := by
      rw [Finset.sum_comm, Finset.sum_congr rfl (hU r hr)]
      simp
    have e2 : (L : ℝ) ^ 2 * ‖U r‖ ^ 2 = ‖(L : ℂ) * U r‖ ^ 2 := by
      rw [norm_mul, mul_pow]; simp
    rw [e2, e]
    calc ‖∑ m ∈ M, ∑ k ∈ Finset.range L, F r m k‖ ^ 2
        ≤ (∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (M.card : ℝ) * ∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
  have h2 : ((∑ r ∈ Rs, ∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k') := by
    push_cast
    have h3 : ∀ r m, ((‖∑ k ∈ Finset.range L, F r m k‖ : ℂ)) ^ 2 =
        ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
          F r m k * (starRingEnd ℂ) (F r m k') := by
      intro r m
      rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    simp_rw [h3]
    rw [Finset.sum_congr rfl (fun r _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun r _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
  have hX : (∑ r ∈ Rs, ∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖ ^ 2 : ℝ) =
      ‖((∑ r ∈ Rs, ∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc (L : ℝ) ^ 2 * ∑ r ∈ Rs, ‖U r‖ ^ 2 = ∑ r ∈ Rs, (L : ℝ) ^ 2 * ‖U r‖ ^ 2 :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ r ∈ Rs, (M.card : ℝ) * ∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖ ^ 2 :=
        Finset.sum_le_sum h1
    _ = (M.card : ℝ) * ∑ r ∈ Rs, ∑ m ∈ M, ‖∑ k ∈ Finset.range L, F r m k‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [hX, h2]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        exact norm_sum_le _ _

/-- Page 7, the count of pairs of shifts: for a fixed shift k the shifts below it have
differences k - k' that are distinct and lie in [1, L]. -/
theorem sum_below_le (L : ℕ) (B : ℕ → ℝ) (hB : ∀ l, 0 ≤ B l) (k : ℕ) (hk : k < L) :
    ∑ k' ∈ (Finset.range L).filter (fun k' => k' < k), B (k - k') ≤
      ∑ l ∈ Finset.Icc 1 L, B l := by
  have himg : ∑ l ∈ ((Finset.range L).filter (fun k' => k' < k)).image (fun k' => k - k'),
      B l = ∑ k' ∈ (Finset.range L).filter (fun k' => k' < k), B (k - k') := by
    apply Finset.sum_image
    intro x hx z hz hxz
    rw [Finset.mem_coe, Finset.mem_filter] at hx hz
    simp only at hxz
    omega
  rw [← himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hl
    rw [Finset.mem_filter] at hk'
    rw [Finset.mem_Icc]
    omega
  · intro l _ _
    exact hB l

/-- Page 7, the count of pairs of shifts: for a fixed shift k the shifts above it have
differences k' - k that are distinct and lie in [1, L]. -/
theorem sum_above_le (L : ℕ) (B : ℕ → ℝ) (hB : ∀ l, 0 ≤ B l) (k : ℕ) :
    ∑ k' ∈ (Finset.range L).filter (fun k' => k < k'), B (k' - k) ≤
      ∑ l ∈ Finset.Icc 1 L, B l := by
  have himg : ∑ l ∈ ((Finset.range L).filter (fun k' => k < k')).image (fun k' => k' - k),
      B l = ∑ k' ∈ (Finset.range L).filter (fun k' => k < k'), B (k' - k) := by
    apply Finset.sum_image
    intro x hx z hz hxz
    rw [Finset.mem_coe, Finset.mem_filter] at hx hz
    simp only at hxz
    omega
  rw [← himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hl
    rw [Finset.mem_filter, Finset.mem_range] at hk'
    rw [Finset.mem_Icc]
    omega
  · intro l _ _
    exact hB l

/-- Graham and Kolesnik Lemma 2.5 as applied on page 7, with an abstract window W and an
abstract phase phi in place of the window of r s and of R_b(r s). -/
theorem weyl_shift_core (N : ℕ) (R S : ℝ) (W : ℕ → ℕ → Prop) [∀ r s, Decidable (W r s)]
    (φ : ℕ → ℕ → ℝ) (a b : ℕ → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1) (hb : ∀ s, ‖b s‖ ≤ 1)
    (hR : 1 ≤ R) (hS : 1 ≤ S) (L : ℕ) (hL : 1 ≤ L) (hLS : (L : ℝ) ≤ S) (B : ℕ → ℝ)
    (hB : ∀ l, 0 ≤ B l)
    (hyp : ∀ l : ℕ, 1 ≤ l → l ≤ L → ∀ s : ℕ, S ≤ (s : ℝ) → ((s + l : ℕ) : ℝ) < 2 * S →
      ‖∑ r ∈ (Finset.range N).filter (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
        if W r s ∧ W r (s + l) then eC (φ r (s + l) - φ r s) else 0‖ ≤ B l) :
    ‖∑ r ∈ (Finset.range N).filter (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
        ∑ s ∈ (Finset.range N).filter (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
          if W r s then a r * b s * eC (φ r s) else 0‖ ^ 2 ≤
      36 * ((R * S) ^ 2 / L + R * S ^ 2 / L * ∑ l ∈ Finset.Icc 1 L, B l) := by
  obtain ⟨Rs, hRs⟩ : ∃ Rs : Finset ℕ,
      Rs = (Finset.range N).filter (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R) := ⟨_, rfl⟩
  obtain ⟨Ss, hSs⟩ : ∃ Ss : Finset ℕ,
      Ss = (Finset.range N).filter (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Finset ℕ, M = (Finset.range (N + L)).filter
      (fun m : ℕ => S ≤ (m : ℝ) ∧ (m : ℝ) < 2 * S + L) := ⟨_, rfl⟩
  rw [← hRs, ← hSs]
  rw [← hRs] at hyp
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℂ, ∀ r s, c r s =
      if s ∈ Ss then (if W r s then b s * eC (φ r s) else 0) else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → ℕ → ℂ, ∀ r m k, F r m k =
      if k ≤ m then c r (m - k) else 0 := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℕ → ℂ, ∀ r, U r = ∑ s ∈ Ss, c r s := ⟨_, fun _ => rfl⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  -- trivial bounds
  have hcn : ∀ r s, ‖c r s‖ ≤ 1 := by
    intro r s
    rw [hc]
    split_ifs
    · rw [norm_mul, norm_eC_one, mul_one]; exact hb s
    · simp
    · simp
  have hFn : ∀ r m k, ‖F r m k‖ ≤ 1 := by
    intro r m k
    rw [hF]
    split_ifs
    · exact hcn _ _
    · simp
  -- cardinalities
  have hRc : (Rs.card : ℝ) ≤ 2 * R := by
    have := card_real_interval N R (2 * R) (by linarith) (by linarith)
    rw [← hRs] at this
    linarith
  have hMc : (M.card : ℝ) ≤ 3 * S := by
    have := card_real_interval (N + L) S (2 * S + L) (by linarith) (by linarith)
    rw [← hM] at this
    linarith
  -- T as a sum of a r * U r, and Cauchy over r
  have hT : ∑ r ∈ Rs, ∑ s ∈ Ss, (if W r s then a r * b s * eC (φ r s) else 0) =
      ∑ r ∈ Rs, a r * U r := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hUdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hc, ite_eq_left hs]
    split_ifs
    · ring
    · simp
  have hT2 : ‖∑ r ∈ Rs, a r * U r‖ ^ 2 ≤ (Rs.card : ℝ) * ∑ r ∈ Rs, ‖U r‖ ^ 2 := by
    calc ‖∑ r ∈ Rs, a r * U r‖ ^ 2 ≤ (∑ r ∈ Rs, ‖U r‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          rw [norm_mul]
          calc ‖a r‖ * ‖U r‖ ≤ 1 * ‖U r‖ := by gcongr; exact ha r
            _ = ‖U r‖ := one_mul _
      _ ≤ (Rs.card : ℝ) * ∑ r ∈ Rs, ‖U r‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  -- every shift reproduces U r
  have hU : ∀ r ∈ Rs, ∀ k ∈ Finset.range L, ∑ m ∈ M, F r m k = U r := by
    intro r _ k hk
    rw [Finset.mem_range] at hk
    have e1 : ∑ s ∈ Ss, c r s = ∑ m ∈ Ss.image (fun s => s + k), F r m k := by
      rw [Finset.sum_image (by intro x _ z _ hxz; simpa using hxz)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hF]
      simp
    rw [hUdef, e1]
    symm
    apply Finset.sum_subset
    · intro m hm
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hm
      rw [hSs, Finset.mem_filter, Finset.mem_range] at hs
      rw [hM, Finset.mem_filter, Finset.mem_range]
      have hkL : (k : ℝ) < L := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      refine ⟨by omega, by linarith, by linarith⟩
    · intro m _ hmn
      rw [hF]
      split_ifs with hkm
      · rw [hc, ite_eq_right]
        intro hs
        exact hmn (Finset.mem_image.2 ⟨m - k, hs, Nat.sub_add_cancel hkm⟩)
      · rfl
  have hshift := shift_cauchy Rs M L F U hU
  -- the correlation for a positive difference l
  have hcorr : ∀ s l : ℕ, 1 ≤ l → l ≤ L →
      ‖∑ r ∈ Rs, c r (s + l) * (starRingEnd ℂ) (c r s)‖ ≤ B l := by
    intro s l hl1 hl2
    by_cases hs : s ∈ Ss ∧ s + l ∈ Ss
    · have e : ∀ r ∈ Rs, c r (s + l) * (starRingEnd ℂ) (c r s) =
          (b (s + l) * (starRingEnd ℂ) (b s)) *
            (if W r s ∧ W r (s + l) then eC (φ r (s + l) - φ r s) else 0) := by
        intro r _
        rw [hc, hc, ite_eq_left hs.1, ite_eq_left hs.2]
        by_cases h1 : W r s <;> by_cases h2 : W r (s + l)
        · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left ⟨h1, h2⟩, ← eC_mul_conj, map_mul]
          ring
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum, norm_mul, norm_mul, RCLike.norm_conj]
      have hs1 := hs.1
      have hs2 := hs.2
      rw [hSs, Finset.mem_filter] at hs1 hs2
      have h3 := hyp l hl1 hl2 s hs1.2.1 hs2.2.2
      have h4 := hb (s + l)
      have h5 := hb s
      have h6 : ‖b (s + l)‖ * ‖b s‖ ≤ 1 := by
        calc ‖b (s + l)‖ * ‖b s‖ ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul _
      calc ‖b (s + l)‖ * ‖b s‖ * _ ≤ 1 * B l := by
            apply mul_le_mul h6 h3 (norm_nonneg _) zero_le_one
        _ = B l := one_mul _
    · have e : ∀ r ∈ Rs, c r (s + l) * (starRingEnd ℂ) (c r s) = 0 := by
        intro r _
        rw [hc, hc]
        by_cases h1 : s ∈ Ss
        · have h2 : s + l ∉ Ss := fun h2 => hs ⟨h1, h2⟩
          simp [h2]
        · simp [h1]
      rw [Finset.sum_congr rfl e]
      simpa using hB l
  have hcorr' : ∀ s l : ℕ, 1 ≤ l → l ≤ L →
      ‖∑ r ∈ Rs, c r s * (starRingEnd ℂ) (c r (s + l))‖ ≤ B l := by
    intro s l hl1 hl2
    have e : ∑ r ∈ Rs, c r s * (starRingEnd ℂ) (c r (s + l)) =
        (starRingEnd ℂ) (∑ r ∈ Rs, c r (s + l) * (starRingEnd ℂ) (c r s)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul, Complex.conj_conj, mul_comm]
    rw [e, RCLike.norm_conj]
    exact hcorr s l hl1 hl2
  -- the correlations of shifts
  have hGdiag : ∀ k k' : ℕ,
      ‖∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k')‖ ≤
        (Rs.card : ℝ) * M.card := by
    intro k k'
    have hterm : ∀ r m, ‖F r m k * (starRingEnd ℂ) (F r m k')‖ ≤ 1 := by
      intro r m
      rw [norm_mul, RCLike.norm_conj]
      calc ‖F r m k‖ * ‖F r m k'‖ ≤ 1 * 1 := by
            apply mul_le_mul (hFn _ _ _) (hFn _ _ _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    calc ‖∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k')‖
        ≤ ∑ r ∈ Rs, ∑ m ∈ M, (1 : ℝ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => hterm r m)
      _ = (Rs.card : ℝ) * M.card := by simp
  have hGup : ∀ k k' : ℕ, k < k' → k' < L →
      ‖∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k')‖ ≤
        (M.card : ℝ) * B (k' - k) := by
    intro k k' hkk hk'L
    rw [Finset.sum_comm]
    have hm : ∀ m ∈ M, ‖∑ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k')‖ ≤ B (k' - k) := by
      intro m _
      by_cases hk'm : k' ≤ m
      · have e : ∀ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k') =
            c r ((m - k') + (k' - k)) * (starRingEnd ℂ) (c r (m - k')) := by
          intro r _
          rw [hF, hF, ite_eq_left hk'm, ite_eq_left (by omega)]
          have : m - k = (m - k') + (k' - k) := by omega
          rw [this]
        rw [Finset.sum_congr rfl e]
        exact hcorr _ _ (by omega) (by omega)
      · have e : ∀ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k') = 0 := by
          intro r _
          rw [hF r m k', ite_eq_right hk'm]
          simp
        rw [Finset.sum_congr rfl e]
        simpa using hB (k' - k)
    calc ‖∑ m ∈ M, ∑ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k')‖
        ≤ ∑ m ∈ M, B (k' - k) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hm)
      _ = (M.card : ℝ) * B (k' - k) := by simp
  have hGdown : ∀ k k' : ℕ, k' < k → k < L →
      ‖∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k')‖ ≤
        (M.card : ℝ) * B (k - k') := by
    intro k k' hkk hkL
    rw [Finset.sum_comm]
    have hm : ∀ m ∈ M, ‖∑ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k')‖ ≤ B (k - k') := by
      intro m _
      by_cases hkm : k ≤ m
      · have e : ∀ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k') =
            c r (m - k) * (starRingEnd ℂ) (c r ((m - k) + (k - k'))) := by
          intro r _
          rw [hF, hF, ite_eq_left hkm, ite_eq_left (by omega)]
          have : m - k' = (m - k) + (k - k') := by omega
          rw [this]
        rw [Finset.sum_congr rfl e]
        exact hcorr' _ _ (by omega) (by omega)
      · have e : ∀ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k') = 0 := by
          intro r _
          rw [hF r m k, ite_eq_right hkm]
          simp
        rw [Finset.sum_congr rfl e]
        simpa using hB (k - k')
    calc ‖∑ m ∈ M, ∑ r ∈ Rs, F r m k * (starRingEnd ℂ) (F r m k')‖
        ≤ ∑ m ∈ M, B (k - k') :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hm)
      _ = (M.card : ℝ) * B (k - k') := by simp
  -- the sum over k' for a fixed k
  have hSig0 : 0 ≤ ∑ l ∈ Finset.Icc 1 L, B l := Finset.sum_nonneg fun l _ => hB l
  have hrow : ∀ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
      ‖∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k')‖ ≤
        (Rs.card : ℝ) * M.card + 2 * ((M.card : ℝ) * ∑ l ∈ Finset.Icc 1 L, B l) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hpt : ∀ k' ∈ Finset.range L,
        ‖∑ r ∈ Rs, ∑ m ∈ M, F r m k * (starRingEnd ℂ) (F r m k')‖ ≤
          (if k' = k then (Rs.card : ℝ) * M.card else 0) +
            (if k' < k then (M.card : ℝ) * B (k - k') else 0) +
            (if k < k' then (M.card : ℝ) * B (k' - k) else 0) := by
      intro k' hk'
      rw [Finset.mem_range] at hk'
      rcases lt_trichotomy k' k with h | h | h
      · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right (by omega)]
        simpa using hGdown k k' h hk
      · rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_right (by omega)]
        simpa using hGdiag k k'
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
        simpa using hGup k k' h hk'
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range L) k,
      ite_eq_left (Finset.mem_range.2 hk), ← Finset.sum_filter, ← Finset.sum_filter,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := sum_below_le L B hB k hk
    have h2 := sum_above_le L B hB k
    have hM0 : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 hM0, mul_le_mul_of_nonneg_left h2 hM0]
  have htot : (L : ℝ) ^ 2 * ∑ r ∈ Rs, ‖U r‖ ^ 2 ≤
      (M.card : ℝ) * ((L : ℝ) * ((Rs.card : ℝ) * M.card +
        2 * ((M.card : ℝ) * ∑ l ∈ Finset.Icc 1 L, B l))) := by
    refine hshift.trans ?_
    gcongr
    refine (Finset.sum_le_sum hrow).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- arithmetic
  rw [hT]
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ r ∈ Rs, ‖U r‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Sg, hSig⟩ : ∃ Sg : ℝ, Sg = ∑ l ∈ Finset.Icc 1 L, B l := ⟨_, rfl⟩
  rw [← hX] at hT2 htot
  rw [← hSig] at htot hSig0 ⊢
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hRc0 : (0 : ℝ) ≤ Rs.card := Nat.cast_nonneg _
  have hMc0 : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
  have hLX : (L : ℝ) * X ≤ (M.card : ℝ) * ((Rs.card : ℝ) * M.card + 2 * ((M.card : ℝ) * Sg)) := by
    have : (L : ℝ) * ((L : ℝ) * X) ≤
        (L : ℝ) * ((M.card : ℝ) * ((Rs.card : ℝ) * M.card + 2 * ((M.card : ℝ) * Sg))) := by
      nlinarith [htot]
    exact le_of_mul_le_mul_left this hLpos
  have hK : (M.card : ℝ) * ((Rs.card : ℝ) * M.card + 2 * ((M.card : ℝ) * Sg)) ≤
      (3 * S) * ((2 * R) * (3 * S) + 2 * ((3 * S) * Sg)) := by
    gcongr
  have hXb : X ≤ (3 * S) * ((2 * R) * (3 * S) + 2 * ((3 * S) * Sg)) / L := by
    rw [le_div_iff₀ hLpos]
    linarith
  calc ‖∑ r ∈ Rs, a r * U r‖ ^ 2 ≤ (Rs.card : ℝ) * X := hT2
    _ ≤ (2 * R) * ((3 * S) * ((2 * R) * (3 * S) + 2 * ((3 * S) * Sg)) / L) := by
        gcongr
    _ = 36 * ((R * S) ^ 2 / L + R * S ^ 2 / L * Sg) := by
        field_simp
        ring

/-- Song 2020, page 7, "By Lemma 2.5 in [2], we have T(R,S)^2 << (RS)^2/L +
(R S^2/L) sum over 1 <= |l| <= L of max over S < s, s + l <= 2S of the modulus of the sum
over r in I of e(R_b(r(s+l)) - R_b(r s))". Graham and Kolesnik Lemma 2.5 applied to
T(R,S) with 1 <= L <= S, proved here with the constant 36. The statement is that of
SPLIT_typeII_per_RS.weyl_shift. -/
theorem weyl_shift_route :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y α t γ : ℝ) (h : ℤ) (a b : ℕ → ℂ),
      (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖b s‖ ≤ 1) → ∀ R S : ℝ, 1 ≤ R → 1 ≤ S →
        ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ S → ∀ B : ℕ → ℝ, (∀ l, 0 ≤ B l) →
          (∀ l : ℕ, 1 ≤ l → l ≤ L → ∀ s : ℕ, S ≤ (s : ℝ) → ((s + l : ℕ) : ℝ) < 2 * S →
            ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              if (|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) ∧
                  (|((r * (s + l) : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧
                    ((r * (s + l) : ℕ) : ℝ) ≤ t) then
                eC ((α * ((r * (s + l) : ℕ) : ℝ) + h * ((r * (s + l) : ℕ) : ℝ) ^ γ) -
                  (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ))
              else 0‖ ≤ B l) →
          ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
                if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
                  a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
                else 0‖ ^ 2 ≤
            C * ((R * S) ^ 2 / L + R * S ^ 2 / L * ∑ l ∈ Finset.Icc 1 L, B l) := by
  refine ⟨36, by norm_num, ?_⟩
  intro n y α t γ h a b ha hb R S hR hS L hL hLS B hB hyp
  exact weyl_shift_core (Nat.ceil ((n : ℝ) / 3 + y) + 1) R S
    (fun r s => |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t)
    (fun r s => α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
    a b ha hb hR hS L hL hLS B hB hyp

end

end LeanLab.Song2020.RouteTypeIIWeyl
