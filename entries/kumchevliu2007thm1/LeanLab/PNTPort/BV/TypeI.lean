module

public import LeanLab.PNTPort.BV.Decomp
public import LeanLab.PNTPort.BV.PolyaVinogradov

/-!
# Type I bounds for the Vaughan sums S₁, S₂, S₃

Lab proof, AI wrote this file, known mathematics, no cited input.

For a primitive character `χ` modulo `q > 1`, `x ≥ 2` and `u, v ≥ 1`,

  `‖S₁‖ + ‖S₂‖ + ‖S₃‖ ≤ (log 4 + 4) u + 3 (u v + v) log x · √q (1 + log q)`.

Route: `S₁` by Chebyshev's bound `ψ(u) ≤ (log 4 + 4) u`; `S₂` and `S₃` by rearranging the
Dirichlet convolution into `∑_t c_t χ(t) ∑_{r ≤ N/t} a_r χ(r)` and applying Pólya–Vinogradov,
with Abel summation for the `log` weights in `S₃`. In fact `‖S₂‖ ≤ u v log x · PV` and
`‖S₃‖ ≤ 2 v log x · PV`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Rearranging a sum over `n ≤ N` and factorisations `n = t r`. -/
lemma sum_Icc_divisorsAntidiagonal {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, f p =
      ∑ t ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / t), f (t, r) := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2.1, x.2.2⟩) (fun y _ => ⟨y.1 * y.2, (y.1, y.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, a, b⟩ hx
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨h1, h2⟩, hab, hn⟩ := hx
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)
    refine ⟨⟨ha, ?_⟩, hb, ?_⟩
    · nlinarith
    · rw [Nat.le_div_iff_mul_le ha]; nlinarith
  · rintro ⟨t, r⟩ hy
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
    rw [Nat.le_div_iff_mul_le (by omega)] at h4
    refine ⟨⟨?_, ?_⟩, trivial, ?_⟩
    · nlinarith
    · nlinarith
    · positivity
  · rintro ⟨n, a, b⟩ hx
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨_, hab, _⟩ := hx
    subst hab
    rfl
  · rintro ⟨t, r⟩ _
    rfl
  · rintro ⟨n, a, b⟩ _
    rfl

/-- The convolution sums `S₂`, `S₃` in factored form. -/
lemma sum_conv_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (F : ℕ × ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((∑ p ∈ n.divisorsAntidiagonal, F p : ℝ) : ℂ) * χ (n : ZMod q) =
      ∑ t ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / t),
        (F (t, r) : ℂ) * χ (t : ZMod q) * χ (r : ZMod q) := by
  rw [← sum_Icc_divisorsAntidiagonal (fun p => (F p : ℂ) * χ (p.1 : ZMod q) * χ (p.2 : ZMod q))]
  refine sum_congr rfl fun n _ => ?_
  rw [Complex.ofReal_sum, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [(Nat.mem_divisorsAntidiagonal.1 hp).1.symm, Nat.cast_mul, map_mul, mul_assoc]

lemma sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (Y : ℕ) :
    ∑ h ∈ Icc 1 Y, f h = ∑ h ∈ range Y, f (h + 1) := by
  induction Y with
  | zero => simp
  | succ Y ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- Abel summation identity. -/
lemma abel_range (a : ℕ → ℝ) (c : ℕ → ℂ) (Y : ℕ) :
    ∑ h ∈ range Y, (a (h + 1) : ℂ) * c (h + 1) =
      (a Y : ℂ) * (∑ j ∈ range Y, c (j + 1)) -
        ∑ h ∈ range Y, ((a (h + 1) - a h : ℝ) : ℂ) * (∑ j ∈ range h, c (j + 1)) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ (fun h => ((a (h + 1) - a h : ℝ) : ℂ) *
      (∑ j ∈ range h, c (j + 1)))]
    push_cast
    ring

lemma log_nat_mono (h : ℕ) : Real.log (h : ℝ) ≤ Real.log ((h + 1 : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · exact Real.log_le_log (by exact_mod_cast hh) (by push_cast; linarith)

/-- Abel summation bound for `∑_{h ≤ Y} χ(h) log h`. -/
lemma norm_sum_log_le {q : ℕ} (χ : DirichletCharacter ℂ q) (B : ℝ)
    (hB : ∀ k : ℕ, ‖∑ h ∈ Icc 1 k, χ (h : ZMod q)‖ ≤ B) (Y : ℕ) :
    ‖∑ h ∈ Icc 1 Y, (Real.log h : ℂ) * χ (h : ZMod q)‖ ≤ 2 * Real.log Y * B := by
  have hB' : ∀ k : ℕ, ‖∑ j ∈ range k, χ ((j + 1 : ℕ) : ZMod q)‖ ≤ B := fun k => by
    rw [← sum_Icc_one_eq_range (fun h => χ (h : ZMod q))]; exact hB k
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hlog : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  rw [sum_Icc_one_eq_range (fun h => (Real.log h : ℂ) * χ (h : ZMod q))]
  have e := abel_range (fun h => Real.log (h : ℝ)) (fun h => χ (h : ZMod q)) Y
  beta_reduce at e
  rw [e]
  calc _ ≤ ‖(Real.log (Y : ℝ) : ℂ) * ∑ j ∈ range Y, χ ((j + 1 : ℕ) : ZMod q)‖ +
        ‖∑ h ∈ range Y, ((Real.log ((h + 1 : ℕ) : ℝ) - Real.log (h : ℝ) : ℝ) : ℂ) *
          ∑ j ∈ range h, χ ((j + 1 : ℕ) : ZMod q)‖ := norm_sub_le _ _
    _ ≤ Real.log Y * B + ∑ h ∈ range Y,
          (Real.log ((h + 1 : ℕ) : ℝ) - Real.log (h : ℝ)) * B := by
        refine add_le_add ?_ ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
          exact mul_le_mul_of_nonneg_left (hB' Y) hlog
        · refine (norm_sum_le _ _).trans (sum_le_sum fun h _ => ?_)
          have hm := sub_nonneg.2 (log_nat_mono h)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm]
          exact mul_le_mul_of_nonneg_left (hB' h) hm
    _ = 2 * Real.log Y * B := by
        rw [← sum_mul, sum_range_sub (fun h : ℕ => Real.log (h : ℝ))]
        simp only [Nat.cast_zero, Real.log_zero, sub_zero]
        ring

lemma sum_ite_le (N K : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ t ∈ Icc 1 N, (if t ≤ K then c else 0) ≤ K * c := by
  rw [← sum_filter]
  calc _ ≤ ∑ t ∈ Icc 1 K, c := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hc
        intro t ht
        simp only [mem_filter, mem_Icc] at ht ⊢
        omega
    _ = K * c := by simp

lemma log_nat_le {x : ℝ} (hx : 1 ≤ x) {Y : ℕ} (hY : (Y : ℝ) ≤ x) :
    Real.log (Y : ℝ) ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos Y with rfl | hh
  · simpa using Real.log_nonneg hx
  · exact Real.log_le_log (by exact_mod_cast hh) hY

theorem norm_S1_le {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (u : ℕ) :
    ‖S1 x u χ‖ ≤ (Real.log 4 + 4) * u := by
  unfold S1
  calc _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (if n ≤ u then vonMangoldt n else 0) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
        have h0 : 0 ≤ (if n ≤ u then vonMangoldt n else 0) := by
          split_ifs <;> simp [vonMangoldt_nonneg]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
        exact mul_le_of_le_one_right h0 (χ.norm_le_one _)
    _ ≤ ∑ n ∈ Icc 1 u, vonMangoldt n := by
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
        intro t ht
        simp only [mem_filter, mem_Icc] at ht ⊢
        omega
    _ = Chebyshev.psi u := by
        rw [Chebyshev.psi, Nat.floor_natCast]
        rfl
    _ ≤ _ := Chebyshev.psi_le_const_mul_self (by positivity)

theorem norm_S2_le {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {x : ℝ} (hx : 1 ≤ x) (u v : ℕ) :
    ‖S2 x u v χ‖ ≤ (u * v : ℕ) * Real.log x * (Real.sqrt q * (1 + Real.log q)) := by
  set P := Real.sqrt q * (1 + Real.log q)
  set N := ⌊x⌋₊
  have hP : 0 ≤ P := le_trans (norm_nonneg _) (polya_vinogradov_Icc hq hχ 0)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  set g : ℕ → ℝ := fun t => ∑ y ∈ t.divisorsAntidiagonal,
    (if y.1 ≤ u ∧ y.2 ≤ v then vonMangoldt y.1 * (μ y.2 : ℝ) else 0)
  have hg : ∀ t ∈ Icc 1 N, |g t| ≤ if t ≤ u * v then Real.log x else 0 := by
    intro t ht
    have ht' := mem_Icc.1 ht
    split_ifs with htuv
    · calc |g t| ≤ ∑ y ∈ t.divisorsAntidiagonal,
            |(if y.1 ≤ u ∧ y.2 ≤ v then vonMangoldt y.1 * (μ y.2 : ℝ) else 0)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ y ∈ t.divisorsAntidiagonal, vonMangoldt y.1 := by
            refine sum_le_sum fun y _ => ?_
            split_ifs
            · rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
              refine mul_le_of_le_one_right vonMangoldt_nonneg ?_
              exact_mod_cast abs_moebius_le_one
            · simp [vonMangoldt_nonneg]
        _ = Real.log t := by
            rw [Nat.sum_divisorsAntidiagonal (fun a _ => vonMangoldt a), vonMangoldt_sum]
        _ ≤ Real.log x := log_nat_le hx (le_trans (by exact_mod_cast ht'.2) hNx)
    · have : g t = 0 := by
        refine sum_eq_zero fun y hy => ?_
        have hy' := (Nat.mem_divisorsAntidiagonal.1 hy).1
        split_ifs with h12
        · exact absurd (hy' ▸ Nat.mul_le_mul h12.1 h12.2) htuv
        · rfl
      simp [this]
  unfold S2
  rw [sum_conv_eq χ (fun p => g p.1) N]
  calc _ ≤ ∑ t ∈ Icc 1 N, |g t| * P := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun t _ => ?_)
        simp only
        rw [← mul_sum, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul ?_ (polya_vinogradov_Icc hq hχ _) (norm_nonneg _) (abs_nonneg _)
        exact mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)
    _ ≤ ∑ t ∈ Icc 1 N, (if t ≤ u * v then Real.log x * P else 0) := by
        refine sum_le_sum fun t ht => ?_
        have := mul_le_mul_of_nonneg_right (hg t ht) hP
        split_ifs at this ⊢ <;> simpa using this
    _ ≤ _ := by
        rw [mul_assoc]
        exact sum_ite_le N (u * v) (mul_nonneg hlx hP)

theorem norm_S3_le {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {x : ℝ} (hx : 1 ≤ x) (v : ℕ) :
    ‖S3 x v χ‖ ≤ v * (2 * Real.log x * (Real.sqrt q * (1 + Real.log q))) := by
  set P := Real.sqrt q * (1 + Real.log q)
  set N := ⌊x⌋₊
  have hP : 0 ≤ P := le_trans (norm_nonneg _) (polya_vinogradov_Icc hq hχ 0)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  unfold S3
  rw [sum_conv_eq χ (fun p => if p.1 ≤ v then (μ p.1 : ℝ) * Real.log p.2 else 0) N]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (sum_le_sum fun d _ => ?_) (sum_ite_le N v (by positivity : 0 ≤ 2 * Real.log x * P))
  simp only
  split_ifs with hd
  · have e : ∑ r ∈ Icc 1 (N / d), (((μ d : ℝ) * Real.log r : ℝ) : ℂ) * χ (d : ZMod q) *
        χ (r : ZMod q) = ((μ d : ℝ) : ℂ) * χ (d : ZMod q) *
          ∑ r ∈ Icc 1 (N / d), (Real.log r : ℂ) * χ (r : ZMod q) := by
      rw [mul_sum]
      refine sum_congr rfl fun r _ => ?_
      push_cast
      ring
    rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(μ d : ℝ)| * ‖χ (d : ZMod q)‖ ≤ 1 := by
      have := mul_le_mul (by exact_mod_cast abs_moebius_le_one : |(μ d : ℝ)| ≤ 1)
        (χ.norm_le_one (d : ZMod q)) (norm_nonneg _) zero_le_one
      simpa using this
    have h2 := norm_sum_log_le χ P (polya_vinogradov_Icc hq hχ) (N / d)
    have h3 : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log x :=
      log_nat_le hx (le_trans (by exact_mod_cast Nat.div_le_self N d) hNx)
    calc _ ≤ 1 * (2 * Real.log ((N / d : ℕ) : ℝ) * P) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ ≤ 2 * Real.log x * P := by
          rw [one_mul]; gcongr
  · simp

/-- **Type I bound** for the Vaughan sums `S₁`, `S₂`, `S₃`. -/
theorem typeI_bound {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {x : ℝ} (hx : 2 ≤ x) (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ‖S1 x u χ‖ + ‖S2 x u v χ‖ + ‖S3 x v χ‖ ≤
      (Real.log 4 + 4) * u + 3 * ((u * v + v : ℕ) : ℝ) * Real.log x *
        (Real.sqrt q * (1 + Real.log q)) := by
  have h1 := norm_S1_le χ x u
  have h2 := norm_S2_le hq hχ (by linarith : (1 : ℝ) ≤ x) u v
  have h3 := norm_S3_le hq hχ (by linarith : (1 : ℝ) ≤ x) v
  have hP : 0 ≤ Real.sqrt q * (1 + Real.log q) :=
    le_trans (norm_nonneg _) (polya_vinogradov_Icc hq hχ 0)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hLP := mul_nonneg hlx hP
  push_cast at h2 ⊢
  have huv : (0 : ℝ) ≤ u * v := by positivity
  nlinarith [mul_nonneg huv hLP, mul_nonneg (Nat.cast_nonneg v : (0 : ℝ) ≤ v) hLP]


end LeanLab.PNTPort.BV
