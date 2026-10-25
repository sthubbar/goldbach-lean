module

public import LeanLab.DensityGoldbach.U1467Prop31

/-!
U-1467, run 20261022T0403Z-7595, P0047 Alsetri and Shao 2024, arXiv 2405.18576v2, Section 3,
Lemma 3.2, the Bohr set approximant, reduced to the Bohr set size bound.

The paper's proof: `R = {r : |f̂(r)| ≥ ε}` has `|R| ≤ (M/ε)^p`; the Bohr set
`B = {x : |e_N(xr) - 1| ≤ ε for r ∈ R}` has `|B| ≥ κ N` with `κ` depending on `ε` and `|R|` only,
Tao and Vu, Additive Combinatorics, Lemma 4.20; then `g = E_{b₁,b₂ ∈ B} f(n + b₁ - b₂)`.
Here `g = f * K` with `K(x) = (N/|B|²) #{(b₁, b₂) ∈ B² : b₁ - b₂ = x}`, `K̂(r) = |Σ_{b∈B} e(rb)|²/|B|²`.

The Bohr set size bound is stated as the named Prop `BohrLower`, a standard pigeonhole fact. All
else is PROVED: `as_lemma32_of_bohr : BohrLower → AS_Lemma32` and the headline
`alsetriShao_1_2_of_bohr : BohrLower → Green62 → Green66 → AlsetriShao12`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical ComplexConjugate

noncomputable section
namespace LeanLab.DensityGoldbach.U1467
open LeanLab.DensityGoldbach.U1446 LeanLab.DensityGoldbach.U1448

/-- **Bohr set size bound**, Tao and Vu, Additive Combinatorics, Cambridge 2006, Lemma 4.20, by
pigeonhole: for `ε > 0` and `k` there is `κ > 0` with `|{x : |e_N(rx) - 1| ≤ ε for all r ∈ R}|
≥ κ N` for every `N` and every frequency set `R ⊆ Z_N` with `|R| ≤ k`. -/
def BohrLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, ∀ [NeZero N], ∀ R : Finset (ZMod N),
    R.card ≤ k → κ * N ≤
      ((univ.filter (fun x : ZMod N => ∀ r ∈ R, ‖(ZMod.stdAddChar (r * x) : ℂ) - 1‖ ≤ ε)).card : ℝ)

variable {N : ℕ} [NeZero N]

/-- The Fourier transform of a convolution is the product. -/
lemma hatE_conv (f K : ZMod N → ℝ) (r : ZMod N) :
    hatE N (convE N f K) r = hatE N f r * hatE N K r := by
  unfold hatE convE
  push_cast
  have e1 : ∀ n m : ZMod N, ZMod.stdAddChar (-(r * n)) =
      ZMod.stdAddChar (-(r * m)) * ZMod.stdAddChar (-(r * (n - m))) := by
    intro n m; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have h1 : ∑ n : ZMod N, (1 / (N : ℂ)) * (∑ m : ZMod N, (f m : ℂ) * (K (n - m) : ℂ)) *
      ZMod.stdAddChar (-(r * n)) = (1 / (N : ℂ)) * ∑ m : ZMod N, (f m : ℂ) *
        ZMod.stdAddChar (-(r * m)) * ∑ n : ZMod N, (K (n - m) : ℂ) *
          ZMod.stdAddChar (-(r * (n - m))) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [e1 n m]; ring
  rw [h1]
  have h2 : ∀ m : ZMod N, ∑ n : ZMod N, (K (n - m) : ℂ) * ZMod.stdAddChar (-(r * (n - m))) =
      ∑ n : ZMod N, (K n : ℂ) * ZMod.stdAddChar (-(r * n)) := fun m =>
    Equiv.sum_comp (Equiv.subRight m) (fun n => (K n : ℂ) * ZMod.stdAddChar (-(r * n)))
  simp_rw [h2, ← Finset.sum_mul]
  ring

/-- The Bohr kernel `K(x) = (N/|B|²) #{(b₁, b₂) ∈ B² : b₁ - b₂ = x}`. -/
def kerB (B : Finset (ZMod N)) (x : ZMod N) : ℝ :=
  (N : ℝ) / (B.card : ℝ) ^ 2 * ∑ b₁ ∈ B, ∑ b₂ ∈ B, if b₁ - b₂ = x then 1 else 0

/-- `S(r) = Σ_{b ∈ B} e(rb)`. -/
def sB (B : Finset (ZMod N)) (r : ZMod N) : ℂ := ∑ b ∈ B, ZMod.stdAddChar (r * b)

lemma kerB_nonneg (B : Finset (ZMod N)) (x : ZMod N) : 0 ≤ kerB B x := by
  unfold kerB
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_)
  split_ifs <;> norm_num

lemma hatE_kerB (B : Finset (ZMod N)) (r : ZMod N) :
    hatE N (kerB B) r = ((‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2 : ℝ) : ℂ) := by
  unfold hatE kerB
  push_cast
  simp only [apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one, Complex.ofReal_zero]
  have h1 : ∑ x : ZMod N, ((N : ℂ) / (B.card : ℂ) ^ 2 * ∑ b₁ ∈ B, ∑ b₂ ∈ B,
      (if b₁ - b₂ = x then (1 : ℂ) else 0)) * ZMod.stdAddChar (-(r * x)) =
      (N : ℂ) / (B.card : ℂ) ^ 2 * ∑ b₁ ∈ B, ∑ b₂ ∈ B, ZMod.stdAddChar (-(r * (b₁ - b₂))) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    rw [Finset.sum_eq_single (b₁ - b₂)]
    · simp
    · intro x _ hx; rw [if_neg (Ne.symm hx)]; simp
    · simp
  rw [show (∑ x : ZMod N, ((N : ℂ) / (B.card : ℂ) ^ 2 * ∑ b₁ ∈ B, ∑ b₂ ∈ B,
      (if b₁ - b₂ = x then (1 : ℂ) else 0)) * ZMod.stdAddChar (-(r * x))) = _ from h1]
  have h2 : ∑ b₁ ∈ B, ∑ b₂ ∈ B, ZMod.stdAddChar (-(r * (b₁ - b₂))) = conj (sB B r) * sB B r := by
    unfold sB
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]; congr 1; ring
  rw [h2, mul_comm (conj _), Complex.mul_conj']
  field_simp [hN]
  rw [mul_div_mul_left _ _ hN]

lemma kerB_hat_le_one (B : Finset (ZMod N)) (hB : B.Nonempty) (r : ZMod N) :
    ‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2 ≤ 1 := by
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  rw [div_le_one (by positivity)]
  have : ‖sB B r‖ ≤ B.card := by
    unfold sB
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_e]
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

/-- `Σ_r K̂(r) = K(0) = N/|B|`. -/
lemma sum_hat_kerB (B : Finset (ZMod N)) (hB : B.Nonempty) :
    ∑ r : ZMod N, ‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2 = N / B.card := by
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have h : (((∑ r : ZMod N, ‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2 : ℝ)) : ℂ) = ((N / B.card : ℝ) : ℂ) := by
    push_cast
    have e : ∀ r : ZMod N, ((‖sB B r‖ : ℂ) ^ 2 / (B.card : ℂ) ^ 2) = hatE N (kerB B) r := by
      intro r; rw [hatE_kerB]; push_cast; ring
    simp_rw [e]
    unfold hatE
    rw [← Finset.mul_sum, Finset.sum_comm]
    have e2 : ∀ x : ZMod N, ∑ r : ZMod N, ((kerB B x : ℝ) : ℂ) * ZMod.stdAddChar (-(r * x)) =
        (kerB B x : ℂ) * (if -x = 0 then (N : ℂ) else 0) := by
      intro x
      rw [← orth, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 2; ring
    simp_rw [e2]
    rw [Finset.sum_eq_single 0]
    · simp only [neg_zero, if_true]
      unfold kerB
      have : ∑ b₁ ∈ B, ∑ b₂ ∈ B, (if b₁ - b₂ = 0 then (1 : ℝ) else 0) = B.card := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun b₁ hb₁ => ?_
        rw [Finset.sum_eq_single b₁]
        · simp
        · intro b₂ _ hb; rw [if_neg]; intro h; exact hb (sub_eq_zero.1 h).symm
        · intro h; exact absurd hb₁ h
      rw [this]
      push_cast
      field_simp [hN]
    · intro x _ hx; rw [if_neg (neg_ne_zero.2 hx), mul_zero]
    · simp
  exact_mod_cast h

/-- On a Bohr frequency, `K̂(r) ≥ (1 - ε)²`. -/
lemma hat_kerB_ge (B : Finset (ZMod N)) (hB : B.Nonempty) (r : ZMod N) (ε : ℝ) (hε1 : ε ≤ 1)
    (h : ∀ b ∈ B, ‖(ZMod.stdAddChar (r * b) : ℂ) - 1‖ ≤ ε) :
    (1 - ε) ^ 2 ≤ ‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2 := by
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have h1 : ‖sB B r - B.card‖ ≤ ε * B.card := by
    have : sB B r - B.card = ∑ b ∈ B, ((ZMod.stdAddChar (r * b) : ℂ) - 1) := by
      unfold sB; rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ B, ‖(ZMod.stdAddChar (r * b) : ℂ) - 1‖ ≤ ∑ _b ∈ B, ε := Finset.sum_le_sum h
      _ = ε * B.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have h2 : (1 - ε) * B.card ≤ ‖sB B r‖ := by
    have := norm_sub_norm_le (B.card : ℂ) (sB B r)
    rw [norm_sub_rev, Complex.norm_natCast] at this
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have h0 : 0 ≤ (1 - ε) * B.card := mul_nonneg (by linarith) hc.le
  nlinarith [pow_le_pow_left₀ h0 h2 2]

/-- **Alsetri-Shao Lemma 3.2, CONDITIONAL ON `BohrLower`.** -/
theorem as_lemma32_of_bohr (HB : BohrLower) : AS_Lemma32 := by
  intro δ hδ hδ1 ε hε p hp hp4 Mc hM
  set ε' := min (ε / 4) (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hε'4 : ε' ≤ ε / 4 := min_le_left _ _
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hp0 : 0 < p := by linarith
  set k := ⌊Mc ^ p / ε' ^ p⌋₊ with hk
  obtain ⟨κ, hκ, hBohr⟩ := HB ε' hε'0 (2 * k)
  refine ⟨min 1 (δ * κ / 10), lt_min one_pos (by positivity), 0,
    fun N _ hNp _ f₁ f₂ ν₁ ν₂ h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  -- large spectra
  have hspec : ∀ f : ZMod N → ℝ, lpHat N p f ≤ Mc →
      (univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖)).card ≤ k := by
    intro f hf
    apply Nat.le_floor
    have hS := sum_pow_le f p Mc hp0 hf
    have hR : ((univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖)).card : ℝ) * ε' ^ p ≤
        ∑ r : ZMod N, ‖hatE N f r‖ ^ p := by
      calc ((univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖)).card : ℝ) * ε' ^ p
          = ∑ r ∈ univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖), ε' ^ p := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ r ∈ univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖), ‖hatE N f r‖ ^ p :=
            Finset.sum_le_sum fun r hr =>
              Real.rpow_le_rpow hε'0.le (mem_filter.1 hr).2 hp0.le
        _ ≤ ∑ r : ZMod N, ‖hatE N f r‖ ^ p :=
            Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              fun r _ _ => Real.rpow_nonneg (norm_nonneg _) _
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hε'0 p)]
    linarith
  set R := univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f₁ r‖) ∪
    univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f₂ r‖) with hR
  have hRk : R.card ≤ 2 * k := by
    have := card_union_le (univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f₁ r‖))
      (univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f₂ r‖))
    have := hspec f₁ h4; have := hspec f₂ h5; rw [hR]; omega
  set B := univ.filter (fun x : ZMod N => ∀ r ∈ R, ‖(ZMod.stdAddChar (r * x) : ℂ) - 1‖ ≤ ε')
    with hBdef
  have hBsize : κ * N ≤ B.card := hBohr N R hRk
  have hBpos : (0 : ℝ) < B.card := lt_of_lt_of_le (by positivity) hBsize
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hBpos
  have hNB : (N : ℝ) / B.card ≤ 1 / κ := by
    rw [div_le_div_iff₀ hBpos hκ]; linarith
  set K := kerB B
  have hK0 := kerB_nonneg B
  set kk : ZMod N → ℝ := fun r => ‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2 with hkk
  have hkk0 : ∀ r, 0 ≤ kk r := fun r => by positivity
  have hkk1 : ∀ r, kk r ≤ 1 := kerB_hat_le_one B hB
  have hKhat : ∀ r, hatE N K r = (kk r : ℂ) := hatE_kerB B
  have hkk_zero : kk 0 = 1 := by
    have h := (hatE_zero N K).symm.trans (hKhat 0)
    -- avg K = 1 from `Σ_r K̂ e(0)`: compute directly instead
    have hS0 : sB B 0 = B.card := by simp [sB]
    simp only [kk, hS0, Complex.norm_natCast]
    field_simp
  -- averages of `ν_i`
  have havgν : ∀ ν : ZMod N → ℝ, (∀ r, ‖hatE N ν r - (if r = 0 then 1 else 0)‖ ≤
      min 1 (δ * κ / 10)) → avg N ν ≤ 2 := by
    intro ν hν
    have := hν 0
    rw [if_pos rfl, hatE_zero] at this
    rw [show ((avg N ν : ℂ) - 1) = ((avg N ν - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at this
    have := (le_abs_self _).trans this
    linarith [min_le_left 1 (δ * κ / 10)]
  -- the construction for one function
  have build : ∀ f ν : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ ν n) → lpHat N p f ≤ Mc →
      (∀ r, ‖hatE N ν r - (if r = 0 then 1 else 0)‖ ≤ min 1 (δ * κ / 10)) →
      (∀ r, ε' ≤ ‖hatE N f r‖ → r ∈ R) →
      (∀ n, 0 ≤ convE N f K n ∧ convE N f K n ≤ 1 + δ / 10) ∧
      avg N (convE N f K) = avg N f ∧ (∀ r, ‖hatE N f r - hatE N (convE N f K) r‖ ≤ ε) ∧
      lpHat N p (convE N f K) ≤ Mc := by
    intro f ν hf hl hν hfR
    have hghat : ∀ r, hatE N (convE N f K) r = hatE N f r * (kk r : ℂ) := fun r => by
      rw [hatE_conv, hKhat]
    have hfavg : avg N f ≤ 2 := (avg_mono _ _ fun n => (hf n).2).trans (havgν ν hν)
    refine ⟨fun n => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · unfold convE
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => mul_nonneg (hf m).1 (hK0 _))
    · -- `f * K ≤ ν * K ≤ 1 + c N/|B|`
      have hle : convE N f K n ≤ convE N ν K n := by
        unfold convE
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_right (hf m).2 (hK0 _)) (by positivity)
      refine hle.trans ?_
      have hinv := conv_inv ν K n
      have hsplit : ∑ r : ZMod N, hatE N ν r * hatE N K r * ZMod.stdAddChar (r * n) =
          ∑ r : ZMod N, (hatE N ν r - (if r = 0 then 1 else 0)) * (kk r : ℂ) *
            ZMod.stdAddChar (r * n) + 1 := by
        have : ∑ r : ZMod N, (if r = 0 then (1 : ℂ) else 0) * (kk r : ℂ) *
            ZMod.stdAddChar (r * n) = 1 := by
          rw [Finset.sum_eq_single 0]
          · simp [hkk_zero]
          · intro r _ hr; simp [hr]
          · simp
        have hs2 : ∑ r : ZMod N, hatE N ν r * hatE N K r * ZMod.stdAddChar (r * n) =
            ∑ r : ZMod N, ((hatE N ν r - (if r = 0 then 1 else 0)) * (kk r : ℂ) *
              ZMod.stdAddChar (r * n) + (if r = 0 then (1 : ℂ) else 0) * (kk r : ℂ) *
              ZMod.stdAddChar (r * n)) :=
          Finset.sum_congr rfl fun r _ => by rw [hKhat]; ring
        rw [hs2, Finset.sum_add_distrib, this]
      rw [hsplit] at hinv
      have hnorm : ‖∑ r : ZMod N, (hatE N ν r - (if r = 0 then 1 else 0)) * (kk r : ℂ) *
          ZMod.stdAddChar (r * n)‖ ≤ δ * κ / 10 * (N / B.card) := by
        refine (norm_sum_le _ _).trans ?_
        rw [← sum_hat_kerB B hB, Finset.mul_sum]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hkk0 r)]
        exact mul_le_mul_of_nonneg_right ((hν r).trans (min_le_right _ _)) (hkk0 r)
      have hre : convE N ν K n ≤ ‖((convE N ν K n : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
      rw [hinv] at hre
      have h3 := (hre.trans (norm_add_le _ _)).trans (add_le_add hnorm (le_of_eq norm_one))
      have h4 : δ * κ / 10 * (N / B.card) ≤ δ / 10 := by
        calc δ * κ / 10 * (N / B.card) ≤ δ * κ / 10 * (1 / κ) :=
              mul_le_mul_of_nonneg_left hNB (by positivity)
          _ = δ / 10 := by field_simp
      linarith
    · have h := hghat 0
      rw [hatE_zero, hatE_zero, hkk_zero] at h
      push_cast at h
      exact_mod_cast (by simpa using h)
    · intro r
      rw [hghat, show hatE N f r - hatE N f r * (kk r : ℂ) = hatE N f r * ((1 - kk r : ℝ) : ℂ) by
        push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hkk1 r])]
      have hfr : ‖hatE N f r‖ ≤ 2 := (norm_hatE_le f (fun n => (hf n).1) r).trans hfavg
      by_cases hr : ε' ≤ ‖hatE N f r‖
      · have hrR := hfR r hr
        have hge := hat_kerB_ge B hB r ε' (by linarith)
          (fun b hb => (mem_filter.1 hb).2 r hrR)
        have : 1 - kk r ≤ 2 * ε' := by simp only [kk]; nlinarith
        calc ‖hatE N f r‖ * (1 - kk r) ≤ 2 * (2 * ε') :=
              mul_le_mul hfr this (by linarith [hkk1 r]) (by norm_num)
          _ ≤ ε := by linarith
      · push Not at hr
        calc ‖hatE N f r‖ * (1 - kk r) ≤ ε' * 1 :=
              mul_le_mul hr.le (by linarith [hkk0 r]) (by linarith [hkk1 r]) hε'0.le
          _ ≤ ε := by linarith
    · refine le_trans ?_ hl
      unfold lpHat
      apply Real.rpow_le_rpow (Finset.sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _)
        _ (by positivity)
      refine Finset.sum_le_sum fun r _ => Real.rpow_le_rpow (norm_nonneg _) ?_ hp0.le
      rw [hghat, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hkk0 r)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hkk1 r)
  obtain ⟨a1, a2, a3, a4⟩ := build f₁ ν₁ h1 h4 h6
    (fun r hr => mem_union_left _ (mem_filter.2 ⟨mem_univ _, hr⟩))
  obtain ⟨b1, b2, b3, b4⟩ := build f₂ ν₂ h2 h5 h7
    (fun r hr => mem_union_right _ (mem_filter.2 ⟨mem_univ _, hr⟩))
  exact ⟨convE N f₁ K, convE N f₂ K, a1, b1, a2, b2, a3, b3, a4, b4⟩

/-- Proposition 3.1, CONDITIONAL ON `BohrLower` only. -/
theorem as_prop31_of_bohr (HB : BohrLower) : AS_Prop31 :=
  as_prop31_of_lemma32 (as_lemma32_of_bohr HB)

/-- **Alsetri-Shao 2024, Theorem 1.2, CONDITIONAL ON `BohrLower`, `Green62`, `Green66`.** -/
theorem alsetriShao_1_2_of_bohr (HB : BohrLower) (H62 : Green62) (H66 : Green66) :
    AlsetriShao12 :=
  alsetriShao_1_2_of_lemma32 (as_lemma32_of_bohr HB) H62 H66

end LeanLab.DensityGoldbach.U1467

