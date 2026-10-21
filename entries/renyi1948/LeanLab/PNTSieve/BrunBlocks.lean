module

public import LeanLab.PNTSieve.BrunTwoBlock

/-!
# Brun's sieve with any number of blocks of primes

Unit U-5504, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics, Brun 1920;
the engine of the fundamental lemma of sieve theory, IDEAS I-5051.

A sieve weight on a finset `Ω` of primes is a coefficient function `c : Finset ℕ → ℝ`, read on
`a` as `wEval Ω c a = Σ_{S ⊆ Ω} c(S) [∏S ∣ a]`; its main term is `wMain Ω c x = Σ_{S ⊆ Ω} c(S) ∏_S x_p`.
For disjoint `P, Q` the tensor `tens P Q c d (S) = c(S ∩ P) d(S ∩ Q)` multiplies both.
A list of blocks `(B, re, ro)` gives the upper weight `cU`, a product of even truncations, and the
lower weight `cL` by Brun's recursion `L = u L' + l U' - u U'`.

* `blocks_pointwise`: `wEval cL ≤ [no prime of Ω divides a] ≤ wEval cU`, and `0 ≤ wEval cU`;
* `blocks_sum`: `Σ_{a ∈ A} wEval Ω cL a ≤ S(A, Ω)`;
* `blocks_main`: `S(A, Ω) ≥ X (V_Ω - errL) - Σ_S |cL(S)| |R_S|`, with `errL` the explicit
  recursion of the block errors `(Σ_B x_p)^{r+1}/(r+1)!`.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

/-- `[∏S ∣ a]` as a real number. -/
noncomputable def ind (S : Finset ℕ) (a : ℕ) : ℝ := if (∏ p ∈ S, p) ∣ a then 1 else 0

/-- A sieve weight read at `a`. -/
noncomputable def wEval (Ω : Finset ℕ) (c : Finset ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ S ∈ Ω.powerset, c S * ind S a

/-- The main term of a sieve weight. -/
noncomputable def wMain (Ω : Finset ℕ) (c : Finset ℕ → ℝ) (x : ℕ → ℝ) : ℝ :=
  ∑ S ∈ Ω.powerset, c S * ∏ p ∈ S, x p

/-- The tensor of two weights on disjoint blocks. -/
def tens (P Q : Finset ℕ) (c d : Finset ℕ → ℝ) : Finset ℕ → ℝ := fun S => c (S ∩ P) * d (S ∩ Q)

/-- Splitting a sum over subsets of a disjoint union. -/
lemma sum_powerset_union {P Q : Finset ℕ} (h : Disjoint P Q) (f : Finset ℕ → Finset ℕ → ℝ) :
    ∑ S ∈ (P ∪ Q).powerset, f (S ∩ P) (S ∩ Q) =
      ∑ T ∈ P.powerset, ∑ T' ∈ Q.powerset, f T T' := by
  rw [← sum_product']
  apply sum_nbij' (fun S => (S ∩ P, S ∩ Q)) (fun p => p.1 ∪ p.2)
  · intro S hS
    simp only [coe_powerset, Set.mem_preimage, mem_coe, mem_product, mem_powerset] at hS ⊢
    exact ⟨inter_subset_right, inter_subset_right⟩
  · intro p hp
    simp only [mem_coe, mem_product, mem_powerset] at hp ⊢
    exact union_subset_union hp.1 hp.2
  · intro S hS
    simp only [mem_coe, mem_powerset] at hS
    simp only
    rw [← inter_union_distrib_left, inter_eq_left.mpr hS]
  · intro p hp
    simp only [mem_coe, mem_product, mem_powerset] at hp
    obtain ⟨T, T'⟩ := p
    simp only at hp ⊢
    have h1 : (T ∪ T') ∩ P = T := by
      rw [union_inter_distrib_right, inter_eq_left.mpr hp.1,
        disjoint_iff_inter_eq_empty.mp (h.symm.mono_left hp.2), union_empty]
    have h2 : (T ∪ T') ∩ Q = T' := by
      rw [union_inter_distrib_right, inter_eq_left.mpr hp.2,
        disjoint_iff_inter_eq_empty.mp (h.mono_left hp.1), empty_union]
    rw [h1, h2]
  · intro S _; rfl

lemma ind_union {P Q T T' : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hPQ : Disjoint P Q) (hT : T ⊆ P) (hT' : T' ⊆ Q) (a : ℕ) :
    ind (T ∪ T') a = ind T a * ind T' a := by
  have hd : Disjoint T T' := hPQ.mono hT hT'
  have hcop := coprime_prod_of_disjoint hP hQ hPQ hT hT'
  unfold ind
  rw [prod_union hd]
  by_cases h1 : (∏ p ∈ T, p) ∣ a <;> by_cases h2 : (∏ p ∈ T', p) ∣ a
  · rw [if_pos (hcop.mul_dvd_of_dvd_of_dvd h1 h2), if_pos h1, if_pos h2]; ring
  · rw [if_neg (fun h => h2 ((dvd_mul_left _ _).trans h)), if_neg h2]; ring
  · rw [if_neg (fun h => h1 ((dvd_mul_right _ _).trans h)), if_neg h1]; ring
  · rw [if_neg (fun h => h1 ((dvd_mul_right _ _).trans h)), if_neg h1]; ring

lemma split_union {P Q S : Finset ℕ} (hS : S ⊆ P ∪ Q) : S = S ∩ P ∪ S ∩ Q := by
  rw [← inter_union_distrib_left, inter_eq_left.mpr hS]

lemma wEval_tens {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hPQ : Disjoint P Q) (c d : Finset ℕ → ℝ) (a : ℕ) :
    wEval (P ∪ Q) (tens P Q c d) a = wEval P c a * wEval Q d a := by
  unfold wEval tens
  have : ∀ S ∈ (P ∪ Q).powerset, c (S ∩ P) * d (S ∩ Q) * ind S a =
      c (S ∩ P) * d (S ∩ Q) * (ind (S ∩ P) a * ind (S ∩ Q) a) := by
    intro S hS
    rw [mem_powerset] at hS
    have e : ind S a = ind (S ∩ P ∪ S ∩ Q) a := by rw [← split_union hS]
    rw [e, ind_union hP hQ hPQ inter_subset_right inter_subset_right]
  rw [sum_congr rfl this,
    sum_powerset_union hPQ (fun T T' => c T * d T' * (ind T a * ind T' a)), sum_mul_sum]
  refine sum_congr rfl (fun T _ => sum_congr rfl (fun T' _ => ?_))
  ring

lemma wMain_tens {P Q : Finset ℕ} (hPQ : Disjoint P Q) (c d : Finset ℕ → ℝ) (x : ℕ → ℝ) :
    wMain (P ∪ Q) (tens P Q c d) x = wMain P c x * wMain Q d x := by
  unfold wMain tens
  have : ∀ S ∈ (P ∪ Q).powerset, c (S ∩ P) * d (S ∩ Q) * ∏ p ∈ S, x p =
      c (S ∩ P) * d (S ∩ Q) * ((∏ p ∈ S ∩ P, x p) * ∏ p ∈ S ∩ Q, x p) := by
    intro S hS
    rw [mem_powerset] at hS
    have e : ∏ p ∈ S, x p = ∏ p ∈ S ∩ P ∪ S ∩ Q, x p := by rw [← split_union hS]
    rw [e, prod_union (hPQ.mono inter_subset_right inter_subset_right)]
  rw [sum_congr rfl this,
    sum_powerset_union hPQ (fun T T' => c T * d T' * ((∏ p ∈ T, x p) * ∏ p ∈ T', x p)),
    sum_mul_sum]
  refine sum_congr rfl (fun T _ => sum_congr rfl (fun T' _ => ?_))
  ring

lemma wEval_add (Ω : Finset ℕ) (c d : Finset ℕ → ℝ) (a : ℕ) :
    wEval Ω (fun S => c S + d S) a = wEval Ω c a + wEval Ω d a := by
  unfold wEval; rw [← sum_add_distrib]; exact sum_congr rfl (fun S _ => by ring)

lemma wEval_sub (Ω : Finset ℕ) (c d : Finset ℕ → ℝ) (a : ℕ) :
    wEval Ω (fun S => c S - d S) a = wEval Ω c a - wEval Ω d a := by
  unfold wEval; rw [← sum_sub_distrib]; exact sum_congr rfl (fun S _ => by ring)

lemma wMain_add (Ω : Finset ℕ) (c d : Finset ℕ → ℝ) (x : ℕ → ℝ) :
    wMain Ω (fun S => c S + d S) x = wMain Ω c x + wMain Ω d x := by
  unfold wMain; rw [← sum_add_distrib]; exact sum_congr rfl (fun S _ => by ring)

lemma wMain_sub (Ω : Finset ℕ) (c d : Finset ℕ → ℝ) (x : ℕ → ℝ) :
    wMain Ω (fun S => c S - d S) x = wMain Ω c x - wMain Ω d x := by
  unfold wMain; rw [← sum_sub_distrib]; exact sum_congr rfl (fun S _ => by ring)

/-- The truncated Möbius coefficient of one block. -/
noncomputable def tc (r : ℕ) : Finset ℕ → ℝ := fun T => if T.card ≤ r then (-1 : ℝ) ^ T.card else 0

lemma wEval_tc (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r a : ℕ) :
    wEval P (tc r) a = (trunc (P.filter (· ∣ a)) r : ℝ) := by
  rw [← pointwise P hP r a]
  unfold wEval tc ind
  push_cast
  rw [sum_filter]
  refine sum_congr rfl (fun T _ => ?_)
  split_ifs <;> simp

lemma wMain_tc (P : Finset ℕ) (r : ℕ) (x : ℕ → ℝ) : wMain P (tc r) x = msum P x r := by
  unfold wMain tc msum
  rw [sum_filter]
  refine sum_congr rfl (fun T _ => ?_)
  split_ifs <;> simp

/-- Summing a weight over `A`: `Σ_a wEval Ω c a = X wMain Ω c x + Σ_S c(S) R_S`. -/
lemma sum_wEval (A Ω : Finset ℕ) (c : Finset ℕ → ℝ) (x : ℕ → ℝ) (X : ℝ) :
    ∑ a ∈ A, wEval Ω c a = X * wMain Ω c x + ∑ S ∈ Ω.powerset, c S * rem A x X S := by
  unfold wEval wMain rem cnt ind
  rw [sum_comm, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun S _ => ?_)
  rw [← mul_sum, sum_boole]
  ring

/-! ### The block recursion -/

/-- A block: a finset of primes with an even and an odd truncation level. -/
abbrev Block := Finset ℕ × ℕ × ℕ

/-- The union of the blocks. -/
def univB : List Block → Finset ℕ
  | [] => ∅
  | b :: Bs => b.1 ∪ univB Bs

/-- The weight `[S = ∅]`, value 1 on every `a`. -/
noncomputable def unitW : Finset ℕ → ℝ := fun S => if S = ∅ then 1 else 0

/-- The upper weight: the product of the even truncations. -/
noncomputable def cU : List Block → Finset ℕ → ℝ
  | [] => unitW
  | b :: Bs => tens b.1 (univB Bs) (tc b.2.1) (cU Bs)

/-- The lower weight, Brun's recursion `L = u L' + l U' - u U'`. -/
noncomputable def cL : List Block → Finset ℕ → ℝ
  | [] => unitW
  | b :: Bs => fun S => tens b.1 (univB Bs) (tc b.2.1) (cL Bs) S +
      tens b.1 (univB Bs) (tc b.2.2) (cU Bs) S - tens b.1 (univB Bs) (tc b.2.1) (cU Bs) S

/-- Blocks of primes, pairwise disjoint, with even first and odd second level. -/
def Good : List Block → Prop
  | [] => True
  | b :: Bs => (∀ p ∈ b.1, p.Prime) ∧ Disjoint b.1 (univB Bs) ∧ Even b.2.1 ∧ Odd b.2.2 ∧ Good Bs

lemma univB_prime : ∀ Bs : List Block, Good Bs → ∀ p ∈ univB Bs, p.Prime
  | [], _, p, hp => by simp [univB] at hp
  | b :: Bs, hG, p, hp => by
    rw [univB, mem_union] at hp
    rcases hp with h | h
    · exact hG.1 p h
    · exact univB_prime Bs hG.2.2.2.2 p h

/-- `[no prime of Ω divides a]`. -/
noncomputable def xind (Ω : Finset ℕ) (a : ℕ) : ℝ := if Ω.filter (· ∣ a) = ∅ then 1 else 0

lemma xind_union (P Q : Finset ℕ) (a : ℕ) : xind (P ∪ Q) a = xind P a * xind Q a := by
  unfold xind
  rw [filter_union]
  by_cases h1 : P.filter (· ∣ a) = ∅ <;> by_cases h2 : Q.filter (· ∣ a) = ∅ <;>
    simp [h1, h2, union_eq_empty]

lemma wEval_unit (a : ℕ) : wEval ∅ unitW a = 1 := by
  simp [wEval, unitW, ind]

lemma wMain_unit (x : ℕ → ℝ) : wMain ∅ unitW x = 1 := by
  simp [wMain, unitW]

lemma two_block_pointwise_real {x y u l u' l' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hlx : l ≤ x)
    (hxu : x ≤ u) (hly : l' ≤ y) (hyu : y ≤ u') : u * l' + l * u' - u * u' ≤ x * y := by
  have h1 : 0 ≤ (u - x) * (u' - y) := mul_nonneg (by linarith) (by linarith)
  have h2 : u * l' ≤ u * y := mul_le_mul_of_nonneg_left hly (by linarith)
  have h3 : l * u' ≤ x * u' := mul_le_mul_of_nonneg_right hlx (by linarith)
  nlinarith

lemma xind_nonneg (Ω : Finset ℕ) (a : ℕ) : 0 ≤ xind Ω a := by
  unfold xind; split_ifs <;> norm_num

/-- The one-block Bonferroni bounds for the truncation weights. -/
lemma tc_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {re ro : ℕ} (hre : Even re) (hro : Odd ro)
    (a : ℕ) : wEval P (tc ro) a ≤ xind P a ∧ xind P a ≤ wEval P (tc re) a := by
  rw [wEval_tc P hP, wEval_tc P hP]
  unfold xind
  constructor
  · have := bonferroni_odd (P.filter (· ∣ a)) hro
    have h : ((trunc (P.filter (· ∣ a)) ro : ℤ) : ℝ) ≤
        (((if P.filter (· ∣ a) = ∅ then 1 else 0 : ℤ)) : ℝ) := by exact_mod_cast this
    split_ifs at h ⊢ <;> simpa using h
  · have := bonferroni_even (P.filter (· ∣ a)) hre
    have h : (((if P.filter (· ∣ a) = ∅ then 1 else 0 : ℤ)) : ℝ) ≤
        ((trunc (P.filter (· ∣ a)) re : ℤ) : ℝ) := by exact_mod_cast this
    split_ifs at h ⊢ <;> simpa using h

/-- **The n-block Brun inequality, pointwise.** -/
theorem blocks_pointwise : ∀ Bs : List Block, Good Bs → ∀ a : ℕ,
    wEval (univB Bs) (cL Bs) a ≤ xind (univB Bs) a ∧ xind (univB Bs) a ≤ wEval (univB Bs) (cU Bs) a
  | [], _, a => by
    simp only [univB, cL, cU, wEval_unit]
    simp [xind]
  | b :: Bs, hG, a => by
    obtain ⟨hP, hD, hre, hro, hG'⟩ := hG
    have hQ := univB_prime Bs hG'
    obtain ⟨ihL, ihU⟩ := blocks_pointwise Bs hG' a
    obtain ⟨hl, hu⟩ := tc_bounds b.1 hP hre hro a
    simp only [univB, cL, cU]
    rw [wEval_sub, wEval_add, wEval_tens hP hQ hD, wEval_tens hP hQ hD, wEval_tens hP hQ hD,
      xind_union]
    have hx := xind_nonneg b.1 a
    have hy := xind_nonneg (univB Bs) a
    constructor
    · have := two_block_pointwise_real hx hy hl hu ihL ihU
      linarith
    · exact mul_le_mul hu ihU hy (hx.trans hu)

/-- **The n-block Brun sieve, summed**: `Σ_{a ∈ A} wEval Ω cL a ≤ S(A, Ω)`. -/
theorem blocks_sum (A : Finset ℕ) (Bs : List Block) (hG : Good Bs) :
    ∑ a ∈ A, wEval (univB Bs) (cL Bs) a ≤ (sifted A (univB Bs) : ℝ) := by
  rw [sifted_eq]
  push_cast
  refine sum_le_sum (fun a _ => ?_)
  have := (blocks_pointwise Bs hG a).1
  unfold xind at this
  split_ifs at this ⊢ <;> simpa using this

/-- The upper error recursion: `eU (b :: Bs) = E_re (1 + eU Bs) + eU Bs`. -/
noncomputable def eU (x : ℕ → ℝ) : List Block → ℝ
  | [] => 0
  | b :: Bs => truncErr b.1 x b.2.1 * (1 + eU x Bs) + eU x Bs

/-- The lower error recursion: `eL (b :: Bs) = eL Bs + E_ro (1 + eU Bs) + E_re (eL Bs + eU Bs)`. -/
noncomputable def eL (x : ℕ → ℝ) : List Block → ℝ
  | [] => 0
  | b :: Bs => eL x Bs + truncErr b.1 x b.2.2 * (1 + eU x Bs) +
      truncErr b.1 x b.2.1 * (eL x Bs + eU x Bs)

/-- **Main terms of the block weights**, within `eU`, `eL` of `V = ∏_Ω (1 - x_p)`. -/
theorem blocks_main_dev (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) :
    ∀ Bs : List Block, Good Bs →
      |wMain (univB Bs) (cU Bs) x - ∏ p ∈ univB Bs, (1 - x p)| ≤ eU x Bs ∧
      |wMain (univB Bs) (cL Bs) x - ∏ p ∈ univB Bs, (1 - x p)| ≤ eL x Bs
  | [], _ => by simp [univB, cU, cL, eU, eL, wMain_unit]
  | b :: Bs, hG => by
    obtain ⟨hP, hD, hre, hro, hG'⟩ := hG
    obtain ⟨ihU, ihL⟩ := blocks_main_dev x hx0 hx1 Bs hG'
    simp only [univB, cL, cU, eU, eL]
    rw [wMain_sub, wMain_add, wMain_tens hD, wMain_tens hD, wMain_tens hD,
      wMain_tc, wMain_tc, prod_union hD]
    set V := ∏ p ∈ b.1, (1 - x p)
    set V' := ∏ p ∈ univB Bs, (1 - x p)
    set MU := wMain (univB Bs) (cU Bs) x
    set ML := wMain (univB Bs) (cL Bs) x
    set Ee := truncErr b.1 x b.2.1
    set Eo := truncErr b.1 x b.2.2
    have he : |msum b.1 x b.2.1 - V| ≤ Ee := main_dev b.1 x hx0 hx1 _
    have ho : |msum b.1 x b.2.2 - V| ≤ Eo := main_dev b.1 x hx0 hx1 _
    have hV0 : 0 ≤ V := prod_nonneg (fun p _ => by linarith [hx1 p])
    have hV1 : V ≤ 1 :=
      prod_le_one₀ (fun p _ => by linarith [hx1 p]) (fun p _ => by linarith [hx0 p])
    have hV'0 : 0 ≤ V' := prod_nonneg (fun p _ => by linarith [hx1 p])
    have hV'1 : V' ≤ 1 :=
      prod_le_one₀ (fun p _ => by linarith [hx1 p]) (fun p _ => by linarith [hx0 p])
    have hEe : 0 ≤ Ee := (abs_nonneg _).trans he
    have hEo : 0 ≤ Eo := (abs_nonneg _).trans ho
    have hMU : |MU| ≤ 1 + eU x Bs := by
      have := abs_add_le (MU - V') V'
      rw [sub_add_cancel, abs_of_nonneg hV'0] at this
      linarith
    have hVabs : |V| ≤ 1 := by rw [abs_of_nonneg hV0]; exact hV1
    constructor
    · have hid : msum b.1 x b.2.1 * MU - V * V' = (msum b.1 x b.2.1 - V) * MU + V * (MU - V') := by
        ring
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 := mul_le_mul he hMU (abs_nonneg _) hEe
      have h2 := mul_le_mul hVabs ihU (abs_nonneg _) zero_le_one
      linarith
    · have hid : msum b.1 x b.2.1 * ML + msum b.1 x b.2.2 * MU - msum b.1 x b.2.1 * MU - V * V' =
          V * (ML - V') + (msum b.1 x b.2.2 - V) * MU + (msum b.1 x b.2.1 - V) * (ML - MU) := by
        ring
      rw [hid]
      have hLU : |ML - MU| ≤ eL x Bs + eU x Bs := by
        have := abs_sub_le ML V' MU
        rw [abs_sub_comm V' MU] at this
        linarith
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [abs_mul]
        have := mul_le_mul hVabs ihL (abs_nonneg _) zero_le_one
        linarith
      · rw [abs_mul]; exact mul_le_mul ho hMU (abs_nonneg _) hEo
      · rw [abs_mul]; exact mul_le_mul he hLU (abs_nonneg _) hEe

/-- **The n-block Brun sieve, lower bound with main term.** For good blocks, densities
`0 ≤ x_p ≤ 1` and `X ≥ 0`: `S(A, Ω) ≥ X (∏_Ω (1 - x_p) - eL) - Σ_{S ⊆ Ω} |cL(S)| |R_S|`. -/
theorem blocks_main (A : Finset ℕ) (Bs : List Block) (hG : Good Bs) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (X : ℝ) (hX : 0 ≤ X) :
    X * (∏ p ∈ univB Bs, (1 - x p) - eL x Bs) -
      ∑ S ∈ (univB Bs).powerset, |cL Bs S| * |rem A x X S| ≤ (sifted A (univB Bs) : ℝ) := by
  have h1 := blocks_sum A Bs hG
  rw [sum_wEval A (univB Bs) (cL Bs) x X] at h1
  have h2 := (blocks_main_dev x hx0 hx1 Bs hG).2
  rw [abs_le] at h2
  have h3 : -∑ S ∈ (univB Bs).powerset, |cL Bs S| * |rem A x X S| ≤
      ∑ S ∈ (univB Bs).powerset, cL Bs S * rem A x X S := by
    rw [← sum_neg_distrib]
    refine sum_le_sum (fun S _ => ?_)
    rw [← abs_mul]
    exact neg_abs_le _
  have h4 := mul_le_mul_of_nonneg_left h2.1 hX
  nlinarith

/-- Coefficient bounds: `|cU(S)| ≤ 1` and `|cL(S)| ≤ 3^{#blocks}`. -/
theorem coeff_bounds : ∀ Bs : List Block, ∀ S : Finset ℕ,
    |cU Bs S| ≤ 1 ∧ |cL Bs S| ≤ 3 ^ Bs.length
  | [], S => by
    simp only [cU, cL, unitW, List.length_nil, pow_zero]
    constructor <;> split_ifs <;> simp
  | b :: Bs, S => by
    have htc : ∀ r T, |tc r T| ≤ 1 := by
      intro r T; unfold tc; split_ifs <;> simp
    obtain ⟨hU, hL⟩ := coeff_bounds Bs (S ∩ univB Bs)
    simp only [cU, cL, tens, List.length_cons]
    have hU' : |tc b.2.1 (S ∩ b.1) * cU Bs (S ∩ univB Bs)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (htc _ _) hU (abs_nonneg _) zero_le_one).trans (by norm_num)
    have hU'' : |tc b.2.2 (S ∩ b.1) * cU Bs (S ∩ univB Bs)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (htc _ _) hU (abs_nonneg _) zero_le_one).trans (by norm_num)
    have hL' : |tc b.2.1 (S ∩ b.1) * cL Bs (S ∩ univB Bs)| ≤ 3 ^ Bs.length := by
      rw [abs_mul]
      exact (mul_le_mul (htc _ _) hL (abs_nonneg _) zero_le_one).trans (by rw [one_mul])
    refine ⟨hU', ?_⟩
    have h3 : (1 : ℝ) ≤ 3 ^ Bs.length := one_le_pow₀ (by norm_num)
    calc |tc b.2.1 (S ∩ b.1) * cL Bs (S ∩ univB Bs) + tc b.2.2 (S ∩ b.1) * cU Bs (S ∩ univB Bs) -
          tc b.2.1 (S ∩ b.1) * cU Bs (S ∩ univB Bs)|
        ≤ |tc b.2.1 (S ∩ b.1) * cL Bs (S ∩ univB Bs) + tc b.2.2 (S ∩ b.1) * cU Bs (S ∩ univB Bs)| +
          |tc b.2.1 (S ∩ b.1) * cU Bs (S ∩ univB Bs)| := abs_sub _ _
      _ ≤ 3 ^ Bs.length + 1 + 1 := by
          have := abs_add_le (tc b.2.1 (S ∩ b.1) * cL Bs (S ∩ univB Bs))
            (tc b.2.2 (S ∩ b.1) * cU Bs (S ∩ univB Bs))
          linarith
      _ ≤ 3 ^ (Bs.length + 1) := by rw [pow_succ]; linarith

end LeanLab.PNTSieve.Bonferroni

