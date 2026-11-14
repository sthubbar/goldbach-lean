module

public import LeanLab.Linnik.U1447Display30

/-!
Li-Liu, arXiv 2610.15784, Lemma 4.2, display (29), from Lemma 4.1, display (28), Lemma 3.1,
display (18), the limit (20) and Proposition 3.2. Read by WebFetch on the unversioned
arxiv.org/html/2610.15784, 2026-10-22.

The paper's proof of Lemma 4.2. Lemma 4.1 gives, for each `ε > 0`, a fixed integer `c_ε` and
`O_ε(1)` moduli `r_ℓ = r_ℓ(N)` whose odd squarefree part tends to infinity, with
`|R₁(h) - N𝔖(h)| ≤ εN𝔖(h)` for even `0 < |h| ≤ 3·2^L` with `r_ℓ ∤ c_ε h` for all `ℓ`, and
`|R₁(h)| ≪_ε N𝔖(h)` for all even `0 < |h| ≤ 3·2^L`. The exceptional `h` have `q_ℓ | h` with
`q_ℓ = ∏_{p | r_ℓ, p ∤ 2c_ε} p → ∞`, odd, so (18) makes their contribution `o(NL^{i+j})`. The rest
is `N ∑_{h ≠ 0} r_{i,j}(h)𝔖(h) (1 + O(ε))`, and (20) with Proposition 3.2 gives
`∑_{h ≠ 0} r_{i,j}(h)𝔖(h) = 2L^{i+j}(1 + A_{ij} + o(1))`.

Contents.
* `oddRad`, `qRad`; `qRad_tendsto`, `qRad_odd`, `qRad_dvd`. PROVED.
* `Lemma41 κ P ε`: Lemma 4.1, (28) and the bound `|R₁(h)| ≪ N𝔖(h)`, CITED.
* `Lemma31_18`: display (18), CITED. `Display20 B`: the limit (20), CITED.
  `Prop32 B A`: `B_{ij} = 1 + A_{ij}`, CITED.
* `lemma42_of`: `Lemma42 κ P A e₀` for every `e₀ > 0`, PROVED, CONDITIONAL ON the four.
* `singSum20_of`: the lab's `SingSum20 CR` from `Display20` and `Prop32` with `A₁₁ = CR - 1`.
* `r6_lower6`: `r₆''(N) ≫ NL⁶` with `Lemma42` and `SingSum20` replaced by the above.

Unit U-1458, run 20261022T0003Z-15508. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1458Lemma42

open Set Real MeasureTheory Filter Finset Topology
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U7203Display33
open LeanLab.Linnik.U7205Display34
open LeanLab.Linnik.U1447Display30
open LeanLab.Linnik.U1434Lemma21 (sv sv_le sv_even)

/-! ### The moduli of Lemma 4.1 -/

/-- The odd squarefree part of `r`: the product of the odd primes dividing `r`. -/
def oddRad (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors.filter (· ≠ 2), p

/-- `q_ℓ = ∏_{p | r_ℓ, p ∤ 2c} p`, the modulus in the proof of Lemma 4.2. -/
def qRad (c r : ℕ) : ℕ := ∏ p ∈ (r.primeFactors.filter (· ≠ 2)).filter (fun p => ¬ p ∣ 2 * c), p

lemma oddRad_le (c r : ℕ) (hc : 0 < c) : oddRad r ≤ qRad c r * (2 * c) := by
  unfold oddRad qRad
  rw [← Finset.prod_filter_mul_prod_filter_not (r.primeFactors.filter (· ≠ 2))
    (fun p => ¬ p ∣ 2 * c)]
  refine Nat.mul_le_mul_left _ ?_
  have h2c : 2 * c ≠ 0 := by omega
  calc ∏ p ∈ (r.primeFactors.filter (· ≠ 2)).filter (fun p => ¬ ¬ p ∣ 2 * c), p
      ≤ ∏ p ∈ (2 * c).primeFactors, p := by
        refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Nat.mem_primeFactors, not_not] at hp
          exact Nat.mem_primeFactors.mpr ⟨hp.1.1.1, hp.2, h2c⟩
        · intro p hp _
          exact (Nat.prime_of_mem_primeFactors hp).one_lt.le
    _ ≤ 2 * c := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)

/-- `q_ℓ → ∞` when the odd squarefree part of `r_ℓ` tends to infinity. -/
lemma qRad_tendsto (c : ℕ) (hc : 0 < c) (r : ℕ → ℕ)
    (hr : Tendsto (fun N => oddRad (r N)) atTop atTop) :
    Tendsto (fun N => qRad c (r N)) atTop atTop := by
  rw [tendsto_atTop] at hr ⊢
  intro b
  filter_upwards [hr (b * (2 * c))] with N hN
  have := (hN.trans (oddRad_le c (r N) hc))
  exact Nat.le_of_mul_le_mul_right this (by omega)

lemma qRad_odd (c r : ℕ) : Odd (qRad c r) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h
  obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finset_prod_iff Nat.prime_two.prime _).mp h
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.1.1.1).mp h2p
  exact hp.1.2 this.symm

/-- If `r | c h` then `q | h`. -/
lemma qRad_dvd (c r : ℕ) (h : ℤ) (hrh : (r : ℤ) ∣ (c : ℤ) * h) : (qRad c r : ℤ) ∣ h := by
  rw [Int.natCast_dvd]
  have hr : r ∣ c * h.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hrh
    simpa [Int.natAbs_mul] using this
  refine Finset.prod_primes_dvd _ (fun p hp => ?_) (fun p hp => ?_)
  · simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact hp.1.1.1.prime
  · simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
    have hpc : p ∣ c * h.natAbs := (hp.1.1.2.1).trans hr
    rcases (Nat.Prime.dvd_mul hp.1.1.1).mp hpc with h1 | h1
    · exact absurd (h1.trans (Dvd.intro_left 2 rfl)) hp.2
    · exact h1

/-! ### The singular series is nonnegative -/

lemma C0_nonneg : 0 ≤ C0 := by
  unfold C0
  refine tprod_nonneg fun p => ?_
  have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast p.2.2
  have h1 : (1 : ℝ) ≤ ((p.1 : ℝ) - 1) ^ 2 := by nlinarith
  have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by linarith)]; exact h1
  linarith

lemma singS_nonneg (h : ℤ) : 0 ≤ singS h := by
  unfold singS
  split_ifs
  · refine mul_nonneg (mul_nonneg (by norm_num) C0_nonneg) (Finset.prod_nonneg fun p hp => ?_)
    simp only [Finset.mem_filter] at hp
    have : (2 : ℝ) < p := by exact_mod_cast hp.2
    exact div_nonneg (by linarith) (by linarith)
  · exact le_refl 0

/-! ### Cited inputs -/

/-- **Lemma 4.1, CITED, a named Prop**, for one `ε > 0`. First claim, display (28): there are
`O_ε(1)` moduli `r_ℓ(N)`, `ℓ < m`, whose odd squarefree part tends to infinity, and a fixed positive
integer `c_ε`, such that for large `N`, `|R₁(h) - N𝔖(h)| ≤ εN𝔖(h)` for every even `h` with
`0 < |h| ≤ 3·2^L` and `r_ℓ ∤ c_ε h` for all `ℓ`. Second claim: `|R₁(h)| ≤ K N𝔖(h)` for every even
`h` with `0 < |h| ≤ 3·2^L`. -/
def Lemma41 (κ : ℝ) (P : ℕ → ℝ) (ε : ℝ) : Prop :=
  (∃ m c : ℕ, 0 < c ∧ ∃ r : Fin m → ℕ → ℕ,
    (∀ ℓ, Tendsto (fun N => oddRad (r ℓ N)) atTop atTop) ∧
    ∀ᶠ N : ℕ in atTop, ∀ h : ℤ, h ≠ 0 → |h| ≤ 3 * 2 ^ Lfun N → Even h →
      (∀ ℓ, ¬ ((r ℓ N : ℤ) ∣ (c : ℤ) * h)) →
      ‖R1h κ P N h - ((N * singS h : ℝ) : ℂ)‖ ≤ ε * N * singS h) ∧
  (∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ h : ℤ, h ≠ 0 → |h| ≤ 3 * 2 ^ Lfun N → Even h →
      ‖R1h κ P N h‖ ≤ K * N * singS h)

/-- `∑_{h ≠ 0, q | h} r_{i,j}(h)𝔖(h)`, written over exponent tuples `1 ≤ ν, μ ≤ L`; `q = 0` is
not used. -/
noncomputable def SOffQ (q L i j : ℕ) : ℝ :=
  ∑ ν : Fin i → Fin L, ∑ μ : Fin j → Fin L,
    if sv ν = sv μ then 0 else
      if (q : ℤ) ∣ ((sv ν : ℤ) - sv μ) then singS ((sv ν : ℤ) - sv μ) else 0

/-- `∑_{h ≠ 0} r_{i,j}(h)𝔖(h)` over exponent tuples. -/
noncomputable def SOff (L i j : ℕ) : ℝ :=
  ∑ ν : Fin i → Fin L, ∑ μ : Fin j → Fin L,
    if sv ν = sv μ then 0 else singS ((sv ν : ℤ) - sv μ)

/-- **Lemma 3.1, display (18), CITED, a named Prop**: for `1 ≤ i, j ≤ 3` and odd `q = q(N) → ∞`,
`∑_{h ≠ 0, q | h} r_{i,j}(h)𝔖(h) = o(L^{i+j})`. -/
def Lemma31_18 : Prop :=
  ∀ i j : Fin 3, ∀ q : ℕ → ℕ, (∀ N, Odd (q N)) → Tendsto q atTop atTop →
    ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      SOffQ (q N) (Lfun N) ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ δ * (Lfun N : ℝ) ^ ((i : ℕ) + j + 2)

/-- **Display (20), CITED, a named Prop**: `(1/2L^{i+j}) ∑_{h ≠ 0} r_{i,j}(h)𝔖(h) → B_{ij}`. -/
def Display20 (B : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ i j : Fin 3, Tendsto (fun L : ℕ => SOff L ((i : ℕ) + 1) ((j : ℕ) + 1) /
    (2 * (L : ℝ) ^ ((i : ℕ) + j + 2))) atTop (𝓝 (B i j))

/-- **Proposition 3.2, CITED, a named Prop**: `B_{ij} = 1 + A_{ij}`. -/
def Prop32 (B A : Fin 3 → Fin 3 → ℝ) : Prop := ∀ i j, B i j = 1 + A i j

/-! ### The pointwise bound -/

lemma re_sub_le (z : ℂ) (x : ℝ) : |z.re - x| ≤ ‖z - (x : ℂ)‖ := by
  have := Complex.abs_re_le_norm (z - (x : ℂ))
  simpa using this

lemma abs_h_le {i j L : ℕ} (hi : i ≤ 3) (hj : j ≤ 3) (ν : Fin i → Fin L) (μ : Fin j → Fin L) :
    |((sv ν : ℤ) - sv μ)| ≤ 3 * 2 ^ L := by
  have h1 := sv_le ν
  have h2 := sv_le μ
  have a1 : (sv ν : ℤ) ≤ 3 * 2 ^ L := by
    have : i * 2 ^ L ≤ 3 * 2 ^ L := Nat.mul_le_mul_right _ hi
    exact_mod_cast h1.trans this
  have a2 : (sv μ : ℤ) ≤ 3 * 2 ^ L := by
    have : j * 2 ^ L ≤ 3 * 2 ^ L := Nat.mul_le_mul_right _ hj
    exact_mod_cast h2.trans this
  have b1 : (0 : ℤ) ≤ sv ν := Nat.cast_nonneg _
  have b2 : (0 : ℤ) ≤ sv μ := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith

lemma even_h {i j L : ℕ} (ν : Fin i → Fin L) (μ : Fin j → Fin L) :
    Even ((sv ν : ℤ) - sv μ) := by
  have e1 : Even (sv ν) := Nat.even_iff.mpr (sv_even ν)
  have e2 : Even (sv μ) := Nat.even_iff.mpr (sv_even μ)
  exact (Int.even_coe_nat _ |>.mpr e1).sub (Int.even_coe_nat _ |>.mpr e2)

/-- **The comparison step of Lemma 4.2, PROVED from Lemma 4.1**: for large `N`,
`|∑_{h≠0} r R₁(h) - N ∑_{h≠0} r 𝔖(h)| ≤ εN ∑ r𝔖 + (|K| + 1) N ∑_ℓ ∑_{q_ℓ | h} r𝔖`. -/
theorem compare_of_41 {κ ε : ℝ} {P : ℕ → ℝ} (hε : 0 ≤ ε) {m c : ℕ} (hc : 0 < c)
    {r : Fin m → ℕ → ℕ} {K : ℝ} {N : ℕ} {i j : ℕ} (hi : i ≤ 3) (hj : j ≤ 3)
    (h1 : ∀ h : ℤ, h ≠ 0 → |h| ≤ 3 * 2 ^ Lfun N → Even h →
      (∀ ℓ, ¬ ((r ℓ N : ℤ) ∣ (c : ℤ) * h)) →
      ‖R1h κ P N h - ((N * singS h : ℝ) : ℂ)‖ ≤ ε * N * singS h)
    (h2 : ∀ h : ℤ, h ≠ 0 → |h| ≤ 3 * 2 ^ Lfun N → Even h → ‖R1h κ P N h‖ ≤ K * N * singS h) :
    |Off κ P N i j - N * SOff (Lfun N) i j| ≤
      ε * N * SOff (Lfun N) i j +
        (|K| + 1) * N * ∑ ℓ : Fin m, SOffQ (qRad c (r ℓ N)) (Lfun N) i j := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- pointwise
  have hpt : ∀ (ν : Fin i → Fin (Lfun N)) (μ : Fin j → Fin (Lfun N)),
      |(if sv ν = sv μ then 0 else (R1h κ P N ((sv ν : ℤ) - sv μ)).re) -
        N * (if sv ν = sv μ then 0 else singS ((sv ν : ℤ) - sv μ))| ≤
      ε * N * (if sv ν = sv μ then 0 else singS ((sv ν : ℤ) - sv μ)) +
        (|K| + 1) * N * ∑ ℓ : Fin m, (if sv ν = sv μ then 0 else
          if (qRad c (r ℓ N) : ℤ) ∣ ((sv ν : ℤ) - sv μ) then singS ((sv ν : ℤ) - sv μ) else 0) := by
    intro ν μ
    by_cases hs : sv ν = sv μ
    · simp [hs]
    simp only [if_neg hs]
    set h : ℤ := (sv ν : ℤ) - sv μ with hhdef
    have hh0 : h ≠ 0 := by omega
    have hhr := abs_h_le hi hj ν μ
    have hhe := even_h ν μ
    have hS := singS_nonneg h
    have hQ : 0 ≤ ∑ ℓ : Fin m, (if (qRad c (r ℓ N) : ℤ) ∣ h then singS h else 0) :=
      Finset.sum_nonneg fun ℓ _ => by split_ifs <;> simp [hS]
    have hεS : 0 ≤ ε * N * singS h := by positivity
    by_cases hex : ∀ ℓ, ¬ ((r ℓ N : ℤ) ∣ (c : ℤ) * h)
    · have := (re_sub_le _ _).trans (h1 h hh0 hhr hhe hex)
      have : 0 ≤ (|K| + 1) * N * ∑ ℓ : Fin m, (if (qRad c (r ℓ N) : ℤ) ∣ h then singS h else 0) :=
        by positivity
      linarith
    · push Not at hex
      obtain ⟨ℓ, hℓ⟩ := hex
      have hq := qRad_dvd c (r ℓ N) h hℓ
      have hone : singS h ≤ ∑ ℓ : Fin m, (if (qRad c (r ℓ N) : ℤ) ∣ h then singS h else 0) := by
        have := Finset.single_le_sum (f := fun ℓ : Fin m =>
          if (qRad c (r ℓ N) : ℤ) ∣ h then singS h else 0)
          (fun ℓ _ => by split_ifs <;> simp [hS]) (Finset.mem_univ ℓ)
        simpa [hq] using this
      have hR := h2 h hh0 hhr hhe
      have hre : |(R1h κ P N h).re| ≤ K * N * singS h :=
        (Complex.abs_re_le_norm _).trans hR
      have hK : K * N * singS h ≤ |K| * N * singS h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hN) hS
      have e1 : |(R1h κ P N h).re - N * singS h| ≤ (|K| + 1) * N * singS h := by
        have := abs_sub (R1h κ P N h).re (N * singS h)
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ N * singS h)] at this
        nlinarith
      have e2 : (|K| + 1) * N * singS h ≤ (|K| + 1) * N *
          ∑ ℓ : Fin m, (if (qRad c (r ℓ N) : ℤ) ∣ h then singS h else 0) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
      linarith
  unfold Off SOff SOffQ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun ℓ ν => ∑ μ : Fin j → Fin (Lfun N), _),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ν _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun ℓ (μ : Fin j → Fin (Lfun N)) => if sv ν = sv μ then (0 : ℝ) else
      if (qRad c (r ℓ N) : ℤ) ∣ ((sv ν : ℤ) - sv μ) then singS ((sv ν : ℤ) - sv μ) else 0),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun μ _ => hpt ν μ

/-! ### Lemma 4.2 -/

/-- **Lemma 4.2, display (29), for all `1 ≤ i, j ≤ 3`, PROVED, CONDITIONAL ON** the cited
Lemma 4.1 for every `ε > 0`, display (18), the limit (20) and Proposition 3.2: `Lemma42 κ P A e₀`
for every `e₀ > 0`. -/
theorem lemma42_of {κ : ℝ} {P : ℕ → ℝ} {A B : Fin 3 → Fin 3 → ℝ}
    (h41 : ∀ ε > 0, Lemma41 κ P ε) (h18 : Lemma31_18) (h20 : Display20 B) (h32 : Prop32 B A) :
    ∀ e0 > 0, Lemma42 κ P A e0 := by
  intro e0 he0 i j δ hδ
  set M := 1 + A i j with hM
  set ε := e0 / (|M| + 1) with hεdef
  have hM1 : 0 < |M| + 1 := by positivity
  have hε : 0 < ε := by positivity
  have hεM : ε * (|M| + 1) = e0 := by rw [hεdef]; field_simp
  obtain ⟨⟨m, c, hc, r, hr, hev1⟩, ⟨K, hev2⟩⟩ := h41 ε hε
  set K1 := |K| + 1 with hK1
  have hK1 : 0 < K1 := by positivity
  set η := min 1 (δ / 2) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ δ / 2 := min_le_right _ _
  set η' := δ / (K1 * m + 1) with hη'def
  have hη' : 0 < η' := by positivity
  have hK1η : K1 * m * η' ≤ δ := by
    rw [hη'def, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]; nlinarith
  -- (20) along `L = Lfun N`
  have hlim := (h20 i j).comp Lfun_tendsto
  rw [h32 i j] at hlim
  have hnear : ∀ᶠ N : ℕ in atTop, |SOff (Lfun N) ((i : ℕ) + 1) ((j : ℕ) + 1) /
      (2 * (Lfun N : ℝ) ^ ((i : ℕ) + j + 2)) - M| ≤ η := by
    have := (Metric.tendsto_nhds.mp hlim) η hη
    filter_upwards [this] with N hN
    exact (le_of_lt (by simpa [Real.dist_eq] using hN))
  -- (18) for each `q_ℓ`
  have hq : ∀ᶠ N : ℕ in atTop, ∀ ℓ : Fin m,
      SOffQ (qRad c (r ℓ N)) (Lfun N) ((i : ℕ) + 1) ((j : ℕ) + 1) ≤
        η' * (Lfun N : ℝ) ^ ((i : ℕ) + j + 2) := by
    rw [eventually_all]; intro ℓ
    exact h18 i j (fun N => qRad c (r ℓ N)) (fun N => qRad_odd _ _)
      (qRad_tendsto c hc _ (hr ℓ)) η' hη'
  have hLpos : ∀ᶠ N : ℕ in atTop, 1 ≤ Lfun N := Lfun_tendsto.eventually_ge_atTop 1
  filter_upwards [hev1, hev2, hnear, hq, hLpos] with N hN1 hN2 hNn hNq hL1
  set L := Lfun N with hLdef
  set k := (i : ℕ) + j + 2 with hk
  have hi3 : (i : ℕ) + 1 ≤ 3 := by omega
  have hj3 : (j : ℕ) + 1 ≤ 3 := by omega
  have hcmp := compare_of_41 hε.le hc hi3 hj3 hN1 hN2
  set X := SOff L ((i : ℕ) + 1) ((j : ℕ) + 1) with hX
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    positivity
  have hY : 0 < 2 * (L : ℝ) ^ k := by positivity
  -- `|X - 2L^k M| ≤ 2 L^k η`
  have hXM : |X - 2 * (L : ℝ) ^ k * M| ≤ 2 * (L : ℝ) ^ k * η := by
    have e : X - 2 * (L : ℝ) ^ k * M = 2 * (L : ℝ) ^ k * (X / (2 * (L : ℝ) ^ k) - M) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hY]
    exact mul_le_mul_of_nonneg_left hNn hY.le
  have hXup : X ≤ 2 * (L : ℝ) ^ k * (|M| + 1) := by
    have := (abs_le.mp hXM).2
    have : M ≤ |M| := le_abs_self M
    nlinarith
  have hQsum : ∑ ℓ : Fin m, SOffQ (qRad c (r ℓ N)) L ((i : ℕ) + 1) ((j : ℕ) + 1) ≤
      m * (η' * (L : ℝ) ^ k) := by
    calc _ ≤ ∑ _ℓ : Fin m, η' * (L : ℝ) ^ k := Finset.sum_le_sum fun ℓ _ => hNq ℓ
      _ = _ := by simp
  -- assemble
  have t1 : ε * N * X ≤ 2 * N * (L : ℝ) ^ k * e0 := by
    have := mul_le_mul_of_nonneg_left hXup (by positivity : 0 ≤ ε * N)
    calc ε * N * X ≤ ε * N * (2 * (L : ℝ) ^ k * (|M| + 1)) := this
      _ = 2 * N * (L : ℝ) ^ k * (ε * (|M| + 1)) := by ring
      _ = _ := by rw [hεM]
  have t2 : K1 * N * ∑ ℓ : Fin m, SOffQ (qRad c (r ℓ N)) L ((i : ℕ) + 1) ((j : ℕ) + 1) ≤
      2 * N * (L : ℝ) ^ k * (δ / 2) := by
    have := mul_le_mul_of_nonneg_left hQsum (by positivity : 0 ≤ K1 * N)
    have h3 : K1 * N * (m * (η' * (L : ℝ) ^ k)) = N * (L : ℝ) ^ k * (K1 * m * η') := by ring
    have h4 : N * (L : ℝ) ^ k * (K1 * m * η') ≤ N * (L : ℝ) ^ k * δ :=
      mul_le_mul_of_nonneg_left hK1η (by positivity)
    linarith
  have t3 : |N * X - 2 * N * (L : ℝ) ^ k * (1 + A i j)| ≤ 2 * N * (L : ℝ) ^ k * (δ / 2) := by
    have e : N * X - 2 * N * (L : ℝ) ^ k * (1 + A i j) = N * (X - 2 * (L : ℝ) ^ k * M) := by
      rw [hM]; ring
    rw [e, abs_mul, abs_of_nonneg hN0]
    have := mul_le_mul_of_nonneg_left hXM hN0
    have h5 : N * (2 * (L : ℝ) ^ k * η) ≤ N * (2 * (L : ℝ) ^ k * (δ / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hη2 hY.le) hN0
    nlinarith
  have tri := abs_sub_le (Off κ P N ((i : ℕ) + 1) ((j : ℕ) + 1)) (N * X)
    (2 * N * (L : ℝ) ^ k * (1 + A i j))
  have : 2 * N * (L : ℝ) ^ k * (e0 + δ) =
      2 * N * (L : ℝ) ^ k * e0 + 2 * N * (L : ℝ) ^ k * (δ / 2) + 2 * N * (L : ℝ) ^ k * (δ / 2) := by
    ring
  rw [this]
  linarith

/-! ### `SingSum20` from (20) -/

lemma SOff11_eq (L : ℕ) : SOff L 1 1 = ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
    (if ν = μ then 0 else singS ((2 : ℤ) ^ ν - 2 ^ μ)) := by
  unfold SOff
  rw [sum_fin1]
  simp_rw [sum_fin1 (L := L)]
  have hsv : ∀ x : Fin L, sv (fun _ : Fin 1 => x) = 2 ^ ((x : ℕ) + 1) := by
    intro x; simp [sv]
  simp_rw [hsv]
  rw [← fin_shift]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← fin_shift L (fun m => if (x : ℕ) + 1 = m then 0 else
    singS ((2 : ℤ) ^ ((x : ℕ) + 1) - 2 ^ m))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hiff : (2 : ℕ) ^ ((x : ℕ) + 1) = 2 ^ ((y : ℕ) + 1) ↔ (x : ℕ) + 1 = (y : ℕ) + 1 :=
    ⟨fun h => Nat.pow_right_injective le_rfl h, fun h => by rw [h]⟩
  by_cases h : (x : ℕ) + 1 = (y : ℕ) + 1
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    push_cast; rfl

/-- **`SingSum20 CR` from (20) and Proposition 3.2, PROVED, CONDITIONAL ON** `Display20 B` and
`Prop32 B A` with `A₁₁ = CR - 1`. -/
theorem singSum20_of {A B : Fin 3 → Fin 3 → ℝ} {CR : ℝ} (h20 : Display20 B) (h32 : Prop32 B A)
    (hA : A 0 0 = CR - 1) : SingSum20 CR := by
  intro δ hδ
  have hlim := h20 0 0
  rw [h32 0 0, hA] at hlim
  simp only [Fin.val_zero, zero_add, add_sub_cancel] at hlim
  have := (Metric.tendsto_nhds.mp hlim) δ hδ
  filter_upwards [this, eventually_ge_atTop 1] with L hL hL1
  rw [Real.dist_eq] at hL
  rw [← SOff11_eq]
  have hY : 0 < 2 * (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    positivity
  have h1 : SOff L 1 1 / (2 * (L : ℝ) ^ 2) ≤ CR + δ := by
    have := (abs_lt.mp hL).2; linarith
  rw [div_le_iff₀ hY] at h1
  linarith

/-! ### The Section 6 conclusion -/

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON** the cited Lemma 4.1 `Lemma41 κ P ε` for every `ε > 0`,
display (18) `Lemma31_18`, the limit (20) `Display20 B`, Proposition 3.2 `Prop32 B (A_* + T)`, the
cited (31) `Display31 6.7814`, `MinorSup1924 P`, the conditions (24) on `P` and the cited constants
of `k6_wired`. This is `U1447Display30.r6_lower5` with `Lemma42` and `SingSum20` discharged. -/
theorem r6_lower6 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814)
    (h18 : Lemma31_18) (h20 : Display20 B)
    (h32 : Prop32 B (fun i j => (LiLiu.Astar i j : ℝ) + T i j)) :
    ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      (∀ ε > 0, Lemma41 κ P ε) →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  have h20' : SingSum20 CR := singSum20_of h20 h32 hA11
  obtain ⟨e1, he1, h⟩ := r6_lower5 T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 h20'
  intro κ hκ P hP11 hPup hP2 hMS h41
  exact h (e1 / 2) (by positivity) (by linarith) hκ P hP11 hPup hP2 hMS
    (lemma42_of h41 h18 h20 h32 (e1 / 2) (by positivity))

/-! ### Vacuity of the arithmetic side -/

/-- `q_ℓ` for `r = 3·5·7 = 105`, `c = 5`: the primes `3, 7`, so `q = 21`; and `105 | 5h` gives
`21 | h` at `h = 42`. -/
theorem qRad_instance : qRad 5 105 = 21 ∧ oddRad 105 = 105 ∧ (21 : ℤ) ∣ 42 := by
  refine ⟨?_, ?_, by norm_num⟩
  · unfold qRad
    have : (105 : ℕ).primeFactors = {3, 5, 7} := by
      rw [show (105 : ℕ) = 3 * 5 * 7 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.Prime.primeFactors (by norm_num),
        Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
      decide
    rw [this]; decide
  · unfold oddRad
    have : (105 : ℕ).primeFactors = {3, 5, 7} := by
      rw [show (105 : ℕ) = 3 * 5 * 7 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.Prime.primeFactors (by norm_num),
        Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
      decide
    rw [this]; decide

end LeanLab.Linnik.U1458Lemma42

