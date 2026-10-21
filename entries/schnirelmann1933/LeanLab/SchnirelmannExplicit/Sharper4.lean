module

public import LeanLab.SchnirelmannExplicit.Sharper3

/-!
Explicit Schnirelmann constant, fourth sharpening, unit U-0311, I-0063.
Every integer `n ≥ 2` is a sum of at most `H₄ = 10752072` primes, about `1.08 · 10^7`,
down from `H₃ = 42075180` in Sharper3.lean.
The change is in the first moment of S3. Sharper3 used `∑_{n ≤ N} r n ≥ π(N/2)^2`, about
`N^2 / (4 log^2 N)`. Here all ordered prime pairs with `p + q ≤ N` are counted:
`∑_{n ≤ N} r n ≥ ∑_{p ≤ N} π(N - p)` and `∑_{p ≤ N} (N - p) = ∑_{t < N} π t`, which with
Chebyshev's `π t ≥ 0.69 t / log t` for `t ≥ 10^4` gives about `0.499 · 0.69^2 N^2 / log^2 N`,
twice as much, so four times the density.
S1u, constant 347 for `N ≥ 5.92 · 10^9`, S2 with `2.52`, the prime floor in S4 and Dyson's basis
step are as in Sharper3.lean. No cited input, unconditional.
KNOWN mathematics and far weaker than the literature, Klimov 55, Vaughan 27, Riesel-Vaughan 19,
Ramaré 7, Tao 5 for odd numbers. Goldbach itself is open.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1302Z-30907. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit.Sharper4

open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannExplicit LeanLab.SchnirelmannExplicit.Sharper
open LeanLab.SchnirelmannExplicit.DysonBasis LeanLab.SchnirelmannExplicit.Sharper3

/-- Primes up to `N` as a filter of `range (N + 1)`. -/
lemma primeCounting_eq (N : ℕ) : Nat.primeCounting N = #((range (N + 1)).filter Nat.Prime) := by
  rw [show Nat.primeCounting N = Nat.primeCounting' (N + 1) from rfl,
    ← Nat.primesBelow_card_eq_primeCounting']
  rfl

/-- `∑_{p ≤ N} π(N - p) ≤ ∑_{n ≤ N} r n`, counting ordered prime pairs with `p + q ≤ N`. -/
lemma sum_pi_le_sum_r (N : ℕ) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, Nat.primeCounting (N - p) ≤ ∑ n ∈ Icc 1 N, r n := by
  rw [Finset.sum_congr rfl (fun p _ => primeCounting_eq (N - p))]
  unfold r
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun x => ⟨x.1 + x.2, x.1⟩)
  · intro x hx
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_range] at hx
    obtain ⟨⟨h1, hp⟩, h2, hq⟩ := hx
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Icc, mem_filter, mem_range]
    refine ⟨⟨by have := hp.two_le; omega, by omega⟩, by have := hq.two_le; omega, hp, ?_⟩
    simpa using hq
  · intro a _ b _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : a.1 = b.1 := by simpa using h2
    have h3 : a.2 = b.2 := by omega
    exact Sigma.ext h2' (heq_of_eq h3)

/-- `∑_{p ≤ y} (y - p) = ∑_{t < y} π t`. -/
lemma sum_sub_eq (y : ℕ) :
    ∑ p ∈ (range (y + 1)).filter Nat.Prime, (y - p) = ∑ t ∈ range y, Nat.primeCounting t := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [Finset.sum_range_succ, ← ih, primeCounting_eq y, Finset.range_add_one (n := y + 1),
      Finset.filter_insert]
    have hsum : ∑ p ∈ (range (y + 1)).filter Nat.Prime, (y + 1 - p) =
        ∑ p ∈ (range (y + 1)).filter Nat.Prime, (y - p) + #((range (y + 1)).filter Nat.Prime) := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [mem_filter, mem_range] at hp
      omega
    split_ifs with hpr
    · rw [Finset.sum_insert (by simp), Nat.sub_self, zero_add, hsum]
    · exact hsum

lemma sum_range_cast (y : ℕ) : ∑ t ∈ range y, (t : ℝ) = y * (y - 1) / 2 := by
  induction y with
  | zero => simp
  | succ y ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Pointwise Chebyshev in the shifted form `π s ≥ (c/L)(s - m₀)`, valid for every `s ≤ N`. -/
lemma pi_shift (c : ℝ) (hc : 0 < c) (m₀ N : ℕ) (hm₀ : 3 ≤ m₀)
    (hm : ∀ m : ℕ, m₀ ≤ m → c * m / Real.log m ≤ (Nat.primeCounting m : ℝ))
    (s : ℕ) (hs : s ≤ N) :
    c / Real.log N * ((s : ℝ) - m₀) ≤ Nat.primeCounting s := by
  rcases Nat.lt_or_ge s m₀ with hlt | hge
  · have hsm : (s : ℝ) - m₀ < 0 := by
      have : (s : ℝ) < m₀ := by exact_mod_cast hlt
      linarith
    have hNR : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
    have : c / Real.log N * ((s : ℝ) - m₀) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hsm.le
    exact this.trans (Nat.cast_nonneg _)
  · have hsR : (3 : ℝ) ≤ s := by exact_mod_cast (le_trans hm₀ hge)
    have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
    have hsN : (s : ℝ) ≤ N := by exact_mod_cast hs
    have hlogle : Real.log s ≤ Real.log N := Real.log_le_log (by linarith) hsN
    have hlogN : 0 < Real.log N := lt_of_lt_of_le hlogs hlogle
    refine le_trans ?_ (hm s hge)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hlogN hlogs]
    have hm0 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
    have h1 : c * ((s : ℝ) - m₀) ≤ c * s := by nlinarith
    have h2 : c * ((s : ℝ) - m₀) * Real.log s ≤ c * s * Real.log s :=
      mul_le_mul_of_nonneg_right h1 hlogs.le
    have h3 : c * s * Real.log s ≤ c * s * Real.log N :=
      mul_le_mul_of_nonneg_left hlogle (by positivity)
    linarith

/-- **First moment, all pairs.** With `L = log N`,
`∑_{n ≤ N} r n ≥ (c/L) ((c/L)(N(N - 1)/2 - m₀ N) - m₀ N)`. -/
theorem first_moment (c : ℝ) (hc : 0 < c) (m₀ N : ℕ) (hm₀ : 3 ≤ m₀) (hN : 3 ≤ N)
    (hm : ∀ m : ℕ, m₀ ≤ m → c * m / Real.log m ≤ (Nat.primeCounting m : ℝ)) :
    c / Real.log N * (c / Real.log N * ((N : ℝ) * (N - 1) / 2 - m₀ * N) - m₀ * N) ≤
      ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by
  set L := Real.log N
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < L := Real.log_pos (by linarith)
  have hk : 0 ≤ c / L := by positivity
  set Pn := (range (N + 1)).filter Nat.Prime
  -- step 1: ∑ r ≥ ∑_p π(N - p) ≥ (c/L) ∑_p ((N - p) - m₀)
  have h1 : ((∑ p ∈ Pn, Nat.primeCounting (N - p) : ℕ) : ℝ) ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by
    exact_mod_cast sum_pi_le_sum_r N
  have h2 : ∑ p ∈ Pn, c / L * (((N - p : ℕ) : ℝ) - m₀) ≤
      ((∑ p ∈ Pn, Nat.primeCounting (N - p) : ℕ) : ℝ) := by
    push_cast
    apply Finset.sum_le_sum
    intro p _
    exact pi_shift c hc m₀ N hm₀ hm (N - p) (Nat.sub_le N p)
  have h3 : ∑ p ∈ Pn, c / L * (((N - p : ℕ) : ℝ) - m₀) =
      c / L * (((∑ p ∈ Pn, (N - p) : ℕ) : ℝ) - m₀ * #Pn) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    push_cast
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  -- step 2: ∑_p (N - p) = ∑_{t < N} π t ≥ (c/L)(N(N - 1)/2 - m₀ N)
  have h4 : ((∑ p ∈ Pn, (N - p) : ℕ) : ℝ) = ((∑ t ∈ range N, Nat.primeCounting t : ℕ) : ℝ) := by
    rw [sum_sub_eq N]
  have h5 : c / L * ((N : ℝ) * (N - 1) / 2 - m₀ * N) ≤
      ((∑ t ∈ range N, Nat.primeCounting t : ℕ) : ℝ) := by
    push_cast
    have : ∑ t ∈ range N, c / L * ((t : ℝ) - m₀) = c / L * ((N : ℝ) * (N - 1) / 2 - m₀ * N) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_range_cast, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    rw [← this]
    apply Finset.sum_le_sum
    intro t ht
    simp only [mem_range] at ht
    exact pi_shift c hc m₀ N hm₀ hm t ht.le
  -- step 3: #Pn ≤ N
  have h6 : (#Pn : ℝ) ≤ N := by
    have : #Pn ≤ N := by
      have hsub : Pn ⊆ (range (N + 1)).erase 0 := by
        intro p hp
        simp only [Pn, mem_filter, mem_range] at hp
        simp only [mem_erase, mem_range]
        exact ⟨hp.2.ne_zero, hp.1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by simp), Finset.card_range] at this
      omega
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
  calc c / L * (c / L * ((N : ℝ) * (N - 1) / 2 - m₀ * N) - m₀ * N)
      ≤ c / L * (((∑ p ∈ Pn, (N - p) : ℕ) : ℝ) - m₀ * #Pn) := by
        apply mul_le_mul_of_nonneg_left _ hk
        rw [h4]
        nlinarith [mul_le_mul_of_nonneg_left h6 hm0]
    _ = ∑ p ∈ Pn, c / L * (((N - p : ℕ) : ℝ) - m₀) := h3.symm
    _ ≤ _ := h2.trans h1

lemma exp7_ge : (1000 : ℝ) ≤ Real.exp 7 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (1000 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
    _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h.le 7

lemma exp19_ge : (100000000 : ℝ) ≤ Real.exp 19 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 19 = Real.exp 1 ^ 19 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (100000000 : ℝ) ≤ 2.7182818283 ^ 19 := by norm_num
    _ ≤ Real.exp 1 ^ 19 := pow_le_pow_left₀ (by norm_num) h.le 19

/-- Chebyshev, `π m ≥ 0.69 m / log m` for `m ≥ 10^4`, from `Chebyshev.pi_ge`. -/
theorem pi_lower_069 : ∀ m : ℕ, 10 ^ 4 ≤ m →
    (69 / 100 : ℝ) * m / Real.log m ≤ (Nat.primeCounting m : ℝ) := by
  intro m hm
  have hl2 := Real.log_two_gt_d9
  have hm' : (10 ^ 4 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  refine le_trans ?_ (Chebyshev.pi_ge m)
  apply div_le_div_of_nonneg_right _ hlogm.le
  have h1 : Real.log ((m + 1) / 1000) ≤ (m + 1) / 1000 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  have h3 : Real.log (1000 : ℝ) ≤ 7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact exp7_ge
  nlinarith

/-- `log N ≤ 18 + N / 10^8`. -/
lemma log_le_lin (N : ℝ) (hN : 0 < N) : Real.log N ≤ 18 + N / 100000000 := by
  have h1 : Real.log (N / 100000000) ≤ N / 100000000 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hN.ne' (by norm_num)] at h1
  have h3 : Real.log (100000000 : ℝ) ≤ 19 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact exp19_ge
  linarith

/-- The new S3 density constant `β^2 c^4 / (C^2 D)`, `β = 0.499`, `c = 0.69`, `C = 347`,
`D = 2.52`. -/
noncomputable def α₄ : ℝ := (499 / 1000 : ℝ) ^ 2 * (69 / 100) ^ 4 / (347 ^ 2 * 2.52)

/-- **S3, fourth sharpening.** For `N ≥ N₁ = 5920000000`, at least `α₄ N` integers in `[1, N]`
are Goldbach sums, `α₄ ≈ 1.86 · 10^-7`. -/
theorem S3_sharp4 : ∀ N ≥ N₁, α₄ * N ≤ #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN
  have hNR : (5920000000 : ℝ) ≤ N := by unfold N₁ at hN; exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hLlin : L ≤ 18 + N / 100000000 := log_le_lin N hNpos
  set c : ℝ := 69 / 100
  set β : ℝ := 499 / 1000
  -- first moment
  have hfm := first_moment c (by norm_num) (10 ^ 4) N (by norm_num) (by unfold N₁ at hN; omega)
    pi_lower_069
  push_cast at hfm
  have hfm' : c / L * (c / L * ((N : ℝ) * (N - 1) / 2 - 10000 * N) - 10000 * N) ≤
      ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by push_cast; exact hfm
  have hS1 : β * c ^ 2 * N ^ 2 / L ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by
    refine le_trans ?_ hfm'
    rw [div_le_iff₀ (by positivity)]
    have e : c / L * (c / L * ((N : ℝ) * (N - 1) / 2 - 10000 * N) - 10000 * N) * L ^ 2 =
        c ^ 2 * ((N : ℝ) * (N - 1) / 2 - 10000 * N) - c * 10000 * N * L := by
      field_simp
    rw [e]
    have hkey : c * 10000 * L ≤ c ^ 2 * ((1 / 2 - β) * N - 1 / 2 - 10000) := by
      simp only [c, β]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hkey hNpos.le]
  -- second moment
  have hR2 : ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (347 * N / L ^ 2) ^ 2 * (2.52 * N) := by
    have hpt : ∀ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (347 * N / L ^ 2) ^ 2 * singProd n ^ 2 := by
      intro n hn
      have h' : (r n : ℝ) ≤ 347 * N / L ^ 2 * singProd n := S1u_sharp N hN n hn
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h' 2
    calc ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2
        ≤ ∑ n ∈ Icc 1 N, (347 * N / L ^ 2) ^ 2 * singProd n ^ 2 := Finset.sum_le_sum hpt
      _ = (347 * N / L ^ 2) ^ 2 * ∑ n ∈ Icc 1 N, singProd n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (347 * N / L ^ 2) ^ 2 * (2.52 * N) := by
          gcongr
          exact S2_sharp N (by unfold N₁ at hN; omega)
  have hCS := cauchy_schwarz_r N
  set K : ℝ := ((#{n ∈ Icc 1 N | n ∈ G} : ℕ) : ℝ) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hcomb : (β * c ^ 2 * N ^ 2 / L ^ 2) ^ 2 ≤ K * ((347 * N / L ^ 2) ^ 2 * (2.52 * N)) := by
    calc (β * c ^ 2 * N ^ 2 / L ^ 2) ^ 2 ≤ (((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hS1 2
      _ ≤ K * ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 := hCS
      _ ≤ K * ((347 * N / L ^ 2) ^ 2 * (2.52 * N)) := by gcongr
  have e1 : (β * c ^ 2 * N ^ 2 / L ^ 2) ^ 2 = β ^ 2 * c ^ 4 * N ^ 4 / L ^ 4 := by
    field_simp
  have e2 : K * ((347 * N / L ^ 2) ^ 2 * (2.52 * N)) = K * (347 ^ 2 * 2.52 * N ^ 3) / L ^ 4 := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at hcomb
  have hL4 : 0 < L ^ 4 := by positivity
  have hN3 : 0 < (N : ℝ) ^ 3 := by positivity
  have h' : β ^ 2 * c ^ 4 * N ^ 4 ≤ K * (347 ^ 2 * 2.52 * N ^ 3) :=
    le_of_mul_le_mul_right hcomb hL4
  have h'' : β ^ 2 * c ^ 4 * N * N ^ 3 ≤ (K * (347 ^ 2 * 2.52)) * N ^ 3 := by
    nlinarith
  have h3 : β ^ 2 * c ^ 4 * N ≤ K * (347 ^ 2 * 2.52) := le_of_mul_le_mul_right h'' hN3
  unfold α₄
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
  simp only [c, β] at h3
  linarith

lemma α₄_pos : 0 < α₄ := by unfold α₄; positivity

lemma α₄_le_density : α₄ ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  apply S4_floor α₄ α₄_pos.le N₁ 100000 S3_sharp4
  · norm_num [α₄]
  · refine le_trans ?_ pi_1e5
    norm_num [α₄, N₁]

/-- `K₄ = ⌈1 / α₄⌉`. -/
def K₄ : ℕ := 5376035

lemma one_le_α₄_mul_K₄ : 1 ≤ α₄ * (K₄ : ℝ) := by
  norm_num [α₄, K₄]

/-- The new explicit Schnirelmann constant. -/
def H₄ : ℕ := 2 * K₄ + 2

lemma H₄_eq : H₄ = 10752072 := by norm_num [H₄, K₄]

/-- **Schnirelmann's theorem, fourth explicit form.** Every integer `n ≥ 2` is a sum of at most
`H₄ = 10752072` primes. Unconditional. -/
theorem schnirelmann_bounded_primes_H₄ :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₄, SumOfPrimes k n := by
  have hh : K₄ • ({0, 1} ∪ G : Set ℕ) = Set.univ :=
    nsmul_eq_univ_dyson ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) α₄
      (by convert α₄_le_density) K₄ one_le_α₄_mul_K₄
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num [H₄], [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num [H₄], [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ K₄ • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ K₄ (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by unfold H₄; omega, hs⟩

/-- Against Sharper3: `3 H₄ < H₃`. -/
lemma H₄_lt_H₃ : 3 * H₄ < H₃ := by norm_num [H₄, K₄, H₃, K₃]

end LeanLab.SchnirelmannExplicit.Sharper4
