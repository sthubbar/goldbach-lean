module

public import LeanLab.Linnik.U7205Display34

/-!
Li-Liu, arXiv 2610.15784, Section 4, display (30) from Lemma 4.2 for all 1 ≤ i, j ≤ 3, and the
diagonal bound (19). Read by WebFetch on the unversioned arxiv.org/html/2610.15784, 2026-10-21.

The paper's argument. With `F(z) = z³ - aLz² - bL²z`, `F(G) = ∑_{i=1}^{3} v_i L^{3-i} G^i` with
`v = (-b, -a, 1)`, so
  `∫_𝔐 |S F(G)|² = ∑_{i,j} v_i v_j L^{6-i-j} ∑_h r_{i,j}(h) R₁(h)`.
Lemma 4.2, display (29), gives `∑_{h ≠ 0} r_{i,j}(h) R₁(h) = 2NL^{i+j}(1 + A_{ij} + O(ε) + o(1))`;
the `h = 0` terms are `r_{1,1}(0) = L`, giving `b² L⁵ R₁(0)`, and `r_{i,j}(0) ≤ 2L^{i+j-2}` for
`i + j ≥ 3`, display (19), giving `O(L⁴ R₁(0)) = o(NL⁶)`.

Contents.
* `pow_pair`: `2^a + 2^b = 2^c + 2^d` forces `{a, b} = {c, d}`. PROVED.
* `Dc`: `r_{i,j}(0)`, the number of pairs of exponent tuples with equal power sums;
  `Dc_one_one`: `r_{1,1}(0) = L`; `Dc_rec`; `Dc_bound`: `r_{i,j}(0) ≤ 3L^{i+j-2}` for
  `i + j ≥ 3`, the lab's constant 3 in place of the paper's 2 in (19). PROVED.
* `Off`: `∑_{h ≠ 0} r_{i,j}(h) Re R₁(h)` written over tuples; `Lemma42`: display (29) for all
  `1 ≤ i, j ≤ 3`, two sided, CITED, a named Prop.
* `integral_major_SFG`: `∫_𝔐 |S F(G)|² = ∑_{k,l} w_k w_l (r(0) R₁(0) + Off)`. PROVED.
* `display30Upper_of`: `Display30Upper κ P V (2e₀)` from `Lemma42 κ P A e₀`. PROVED,
  CONDITIONAL ON the cited Lemma 4.2 only.
* `lemma42Lower11_of`: `Lemma42Lower11 κ P A₁₁ (2e₀)` from `Lemma42 κ P A e₀`.
* `r6_lower5`: r₆''(N) ≫ N L⁶, CONDITIONAL ON `Lemma42` for all i, j, the cited (31), (20),
  `MinorSup1924 P`, conditions (24) and the cited constants of `k6_wired`; `Display30Upper` and
  `Lemma42Lower11` are gone, replaced by the single cited `Lemma42`.

Unit U-1447, PC run 20261021T2003Z-599. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1447Display30

open Set Real MeasureTheory Filter Finset
open LeanLab.Linnik.U1412Display53 (eC continuous_eC)
open LeanLab.Linnik.LiLiuDisplay37 (primesIn logw)
open LeanLab.Linnik.LiLiuLemma43 (SA)
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U7203Display33
open LeanLab.Linnik.U7205Display34
open LeanLab.Linnik.U1434Lemma21 (sv Gs_pow eC_add)

/-! ### The diagonal count (19) -/

lemma pow_key (a b c d : ℕ) (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) (hab : a ≤ b) (hcd : c ≤ d) :
    a = c ∧ b = d := by
  have hac : a = c := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨s, rfl⟩ : ∃ s, c = a + s + 1 := ⟨c - a - 1, by omega⟩
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hcd
      have h2 : 2 ^ a * (1 + 2 ^ t) = 2 ^ a * (2 ^ s * 2 + 2 ^ s * 2 * 2 ^ u) :=
        calc _ = 2 ^ a + 2 ^ (a + t) := by ring
          _ = _ := h
          _ = _ := by ring
      have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
      have hs : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      have hu : 1 ≤ 2 ^ u := Nat.one_le_two_pow
      rcases t with _ | t
      · simp at h3; nlinarith
      · rw [pow_succ] at h3
        have hd : 2 ∣ 1 + 2 ^ t * 2 := by rw [h3]; exact ⟨2 ^ s + 2 ^ s * 2 ^ u, by ring⟩
        omega
    · obtain ⟨s, rfl⟩ : ∃ s, a = c + s + 1 := ⟨a - c - 1, by omega⟩
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hcd
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hab
      have h2 : 2 ^ c * (1 + 2 ^ t) = 2 ^ c * (2 ^ s * 2 + 2 ^ s * 2 * 2 ^ u) :=
        calc _ = 2 ^ c + 2 ^ (c + t) := by ring
          _ = _ := h.symm
          _ = _ := by ring
      have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
      have hs : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      have hu : 1 ≤ 2 ^ u := Nat.one_le_two_pow
      rcases t with _ | t
      · simp at h3; nlinarith
      · rw [pow_succ] at h3
        have hd : 2 ∣ 1 + 2 ^ t * 2 := by rw [h3]; exact ⟨2 ^ s + 2 ^ s * 2 ^ u, by ring⟩
        omega
  subst hac
  have hbd : 2 ^ b = 2 ^ d := by omega
  exact ⟨rfl, Nat.pow_right_injective le_rfl hbd⟩

lemma pow_pair (a b c d : ℕ) (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have e1 : 2 ^ a + 2 ^ b = 2 ^ min a b + 2 ^ max a b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, add_comm]
  have e2 : 2 ^ c + 2 ^ d = 2 ^ min c d + 2 ^ max c d := by
    rcases le_total c d with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, add_comm]
  have := pow_key _ _ _ _ (e1.symm.trans (h.trans e2)) (min_le_max) (min_le_max)
  omega


/-- `r_{i,j}(0)`: the number of pairs of tuples with equal power sums. -/
noncomputable def Dc (i j L : ℕ) : ℝ :=
  ∑ ν : Fin i → Fin L, ∑ μ : Fin j → Fin L, if sv ν = sv μ then (1 : ℝ) else 0

lemma sv_cons {j L : ℕ} (x : Fin L) (ν : Fin j → Fin L) :
    sv (Fin.cons x ν : Fin (j + 1) → Fin L) = 2 ^ ((x : ℕ) + 1) + sv ν := by
  unfold sv; rw [Fin.sum_univ_succ]; simp

lemma sum_cons {j L : ℕ} (f : (Fin (j + 1) → Fin L) → ℝ) :
    ∑ ν : Fin (j + 1) → Fin L, f ν = ∑ x : Fin L, ∑ ν : Fin j → Fin L, f (Fin.cons x ν) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin L) _ _ (fun _ => rfl)).symm

lemma sv_pos {j L : ℕ} (ν : Fin (j + 1) → Fin L) : 0 < sv ν := by
  unfold sv; rw [Fin.sum_univ_succ]; positivity

lemma sv_zero {L : ℕ} (ν : Fin 0 → Fin L) : sv ν = 0 := by simp [sv]

lemma Dc_succ_zero (i L : ℕ) : Dc (i + 1) 0 L = 0 := by
  unfold Dc; refine sum_eq_zero fun ν _ => sum_eq_zero fun μ _ => ?_
  rw [if_neg]; rw [sv_zero]; exact (sv_pos ν).ne'

lemma Dc_zero_succ (j L : ℕ) : Dc 0 (j + 1) L = 0 := by
  unfold Dc; refine sum_eq_zero fun ν _ => sum_eq_zero fun μ _ => ?_
  rw [if_neg]; rw [sv_zero]; exact (sv_pos μ).ne

lemma Dc_zero_zero (L : ℕ) : Dc 0 0 L = 1 := by
  simp [Dc, sv_zero]

/-- With `A ≠ B`, at most one pair `(x, y)` solves `2^{x+1} + A = 2^{y+1} + B`. -/
lemma inner_le_one (L A B : ℕ) (hAB : A ≠ B) :
    ∑ x : Fin L, ∑ y : Fin L, (if 2 ^ ((x : ℕ) + 1) + A = 2 ^ ((y : ℕ) + 1) + B then (1 : ℝ) else 0)
      ≤ 1 := by
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun p : Fin L × Fin L =>
      2 ^ ((p.1 : ℕ) + 1) + A = 2 ^ ((p.2 : ℕ) + 1) + B).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have hpair : 2 ^ ((x : ℕ) + 1) + 2 ^ ((y' : ℕ) + 1) = 2 ^ ((y : ℕ) + 1) + 2 ^ ((x' : ℕ) + 1) := by
      omega
    rcases pow_pair _ _ _ _ hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; rw [h1] at hp; omega
    · ext <;> simp <;> omega
  exact_mod_cast this

lemma inner_eq (L A : ℕ) :
    ∑ x : Fin L, ∑ y : Fin L, (if 2 ^ ((x : ℕ) + 1) + A = 2 ^ ((y : ℕ) + 1) + A then (1 : ℝ) else 0)
      = L := by
  have : ∀ x y : Fin L, (2 ^ ((x : ℕ) + 1) + A = 2 ^ ((y : ℕ) + 1) + A) ↔ x = y := by
    intro x y
    constructor
    · intro h
      have h' : 2 ^ ((x : ℕ) + 1) = 2 ^ ((y : ℕ) + 1) := by omega
      exact Fin.ext (by have := Nat.pow_right_injective le_rfl h'; omega)
    · rintro rfl; rfl
  simp_rw [this]
  simp

lemma Dc_split (i j L : ℕ) : Dc (i + 1) (j + 1) L = ∑ ν : Fin i → Fin L, ∑ μ : Fin j → Fin L,
    ∑ x : Fin L, ∑ y : Fin L,
      (if 2 ^ ((x : ℕ) + 1) + sv ν = 2 ^ ((y : ℕ) + 1) + sv μ then (1 : ℝ) else 0) := by
  unfold Dc
  rw [sum_cons]
  simp only [sv_cons]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun ν _ => ?_
  have h : ∀ x : Fin L, (∑ μ' : Fin (j + 1) → Fin L,
      if 2 ^ ((x : ℕ) + 1) + sv ν = sv μ' then (1 : ℝ) else 0) = ∑ y : Fin L, ∑ μ : Fin j → Fin L,
      (if 2 ^ ((x : ℕ) + 1) + sv ν = 2 ^ ((y : ℕ) + 1) + sv μ then (1 : ℝ) else 0) := fun x => by
    rw [sum_cons]; simp only [sv_cons]
  rw [sum_congr rfl fun x _ => h x, sum_congr rfl fun x _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma Dc_rec (i j L : ℕ) : Dc (i + 1) (j + 1) L ≤ (L : ℝ) ^ (i + j) + L * Dc i j L := by
  rw [Dc_split]
  calc _ ≤ ∑ ν : Fin i → Fin L, ∑ μ : Fin j → Fin L,
        (1 + (L : ℝ) * (if sv ν = sv μ then (1 : ℝ) else 0)) := by
        refine sum_le_sum fun ν _ => sum_le_sum fun μ _ => ?_
        by_cases h : sv ν = sv μ
        · rw [h, inner_eq]; simp
        · rw [if_neg h]; simpa using inner_le_one L _ _ h
    _ = _ := by
        simp only [sum_add_distrib, Dc, mul_sum]
        simp [Finset.card_univ, pow_add]

lemma Dc_one_one (L : ℕ) : Dc 1 1 L = L := by
  rw [Dc_split]; simp [sv_zero, Fin.val_inj]

theorem Dc_bound (i j : Fin 3) (L : ℕ) (hij : ¬ (i = 0 ∧ j = 0)) :
    Dc ((i : ℕ) + 1) ((j : ℕ) + 1) L ≤ 3 * (L : ℝ) ^ ((i : ℕ) + j) := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have r10 := Dc_rec 1 0 L
  have r01 := Dc_rec 0 1 L
  have r20 := Dc_rec 2 0 L
  have r02 := Dc_rec 0 2 L
  have r11 := Dc_rec 1 1 L
  have r21 := Dc_rec 2 1 L
  have r12 := Dc_rec 1 2 L
  have r22 := Dc_rec 2 2 L
  have e10 := Dc_succ_zero 0 L
  have e20 := Dc_succ_zero 1 L
  have e01 := Dc_zero_succ 0 L
  have e02 := Dc_zero_succ 1 L
  have e11 := Dc_one_one L
  simp only [e10, e20, e01, e02, e11, mul_zero, add_zero] at r10 r01 r20 r02 r11 r21 r12 r22
  norm_num at r10 r01 r20 r02 r11 r21 r12 r22
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hL3 : (0 : ℝ) ≤ (L : ℝ) ^ 3 := by positivity
  have hL4 : (0 : ℝ) ≤ (L : ℝ) ^ 4 := by positivity
  have m10 := mul_le_mul_of_nonneg_left r10 hL
  have m01 := mul_le_mul_of_nonneg_left r01 hL
  have m11 := mul_le_mul_of_nonneg_left r11 hL
  have hL1 : (L : ℝ) * L ≤ L ^ 3 ∧ (L : ℝ) * L ^ 2 ≤ L ^ 3 ∧ (L : ℝ) ^ 2 ≤ L ^ 4 ∧ (L : ℝ) ^ 3 ≤ L ^ 4 := by
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · subst h0; norm_num
    · have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hpos
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  obtain ⟨hA, hB, hC, hD⟩ := hL1
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith

/-! ### Expanding |S F(G)|² over the major arcs -/

/-- The coefficient of `G^{k+1}` in `F(G)`: `w_k = v_k L^{2-k}`, `v = (-b, -a, 1)`. -/
noncomputable def wv (L : ℕ) (k : Fin 3) : ℝ := (LiLiu.v k : ℝ) * (L : ℝ) ^ (2 - (k : ℕ))

lemma Gs_zero (α : ℝ) : Gs 0 α = 0 := by simp [Gs]

lemma FG_expand (L : ℕ) (α : ℝ) :
    FG (1 / 4) (1 / 16) L α = ∑ k : Fin 3, (wv L k : ℂ) * Gs L α ^ ((k : ℕ) + 1) := by
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · subst h0; simp [FG, Gs_zero, Fin.sum_univ_three, wv]
  · have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    simp only [Fin.sum_univ_three, wv, LiLiu.v, FG, Qc]
    push_cast
    simp
    field_simp
    ring

lemma conj_eC' (t : ℝ) : (starRingEnd ℂ) (eC t) = eC (-t) := conj_eC t

lemma normSq_sum3 (c : Fin 3 → ℝ) (z : Fin 3 → ℂ) :
    ‖∑ k, (c k : ℂ) * z k‖ ^ 2 = ∑ k, ∑ l, c k * c l * (z k * (starRingEnd ℂ) (z l)).re := by
  have h : ((‖∑ k, (c k : ℂ) * z k‖ ^ 2 : ℝ) : ℂ) =
      (∑ k, (c k : ℂ) * z k) * (starRingEnd ℂ) (∑ k, (c k : ℂ) * z k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : (∑ k, (c k : ℂ) * z k) * (starRingEnd ℂ) (∑ k, (c k : ℂ) * z k) =
      ∑ k, ∑ l, ((c k * c l : ℝ) : ℂ) * (z k * (starRingEnd ℂ) (z l)) := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  have h3 := congrArg Complex.re (h.trans h2)
  rw [Complex.ofReal_re] at h3
  rw [h3, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun l _ => Complex.re_ofReal_mul _ _

lemma Gpow_conj (i j L : ℕ) (α : ℝ) :
    Gs L α ^ i * (starRingEnd ℂ) (Gs L α ^ j) =
      ∑ ν : Fin i → Fin L, ∑ μ : Fin j → Fin L, eC (((sv ν : ℝ) - sv μ) * α) := by
  rw [Gs_pow, Gs_pow, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
  rw [conj_eC', ← eC_add]
  congr 1; ring

lemma eC_re_neg (x : ℝ) : (eC (-x)).re = (eC x).re := by
  rw [← conj_eC', Complex.conj_re]

/-- `Off_{i,j} = ∑_{h ≠ 0} r_{i,j}(h) Re R₁(h)`, written over the tuples
`1 ≤ ν₁, …, ν_i, μ₁, …, μ_j ≤ L` with `h = 2^{ν₁} + ⋯ + 2^{ν_i} - 2^{μ₁} - ⋯ - 2^{μ_j} ≠ 0`. -/
noncomputable def Off (κ : ℝ) (P : ℕ → ℝ) (N i j : ℕ) : ℝ :=
  ∑ ν : Fin i → Fin (Lfun N), ∑ μ : Fin j → Fin (Lfun N),
    if sv ν = sv μ then 0 else (R1h κ P N ((sv ν : ℤ) - sv μ)).re

/-- **Lemma 4.2, display (29), for all `1 ≤ i, j ≤ 3`, CITED, a named Prop**:
`∑_{h ≠ 0} r_{i,j}(h) R₁(h) = 2NL^{i+j}(1 + A_{ij} + O(ε) + o(1))`, with `e₀` the `O(ε)` and the
index `k : Fin 3` standing for `i = k + 1`. -/
def Lemma42 (κ : ℝ) (P : ℕ → ℝ) (A : Fin 3 → Fin 3 → ℝ) (e0 : ℝ) : Prop :=
  ∀ i j : Fin 3, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
    |Off κ P N ((i : ℕ) + 1) ((j : ℕ) + 1) -
        2 * N * (Lfun N : ℝ) ^ ((i : ℕ) + j + 2) * (1 + A i j)| ≤
      2 * N * (Lfun N : ℝ) ^ ((i : ℕ) + j + 2) * (e0 + δ)

lemma R1h_re (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) (h : ℤ) :
    (R1h κ P N h).re = ∫ α in LiLiuLemma43Int.majorArcs (P N) N,
      ‖Sm (N1f κ N) N α‖ ^ 2 * (eC (-(h : ℝ) * α)).re :=
  (integral_term κ P N (-(h : ℝ))).symm

lemma R1h_zero (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) : (R1h κ P N 0).re = R1 κ P N := by
  rw [R1h_re]
  simp only [Int.cast_zero, neg_zero, zero_mul, U1412Display53.eC, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, Complex.one_re, mul_one]
  rfl

lemma intOn (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) (c : ℝ) : IntegrableOn
    (fun α => ‖Sm (N1f κ N) N α‖ ^ 2 * (eC (c * α)).re)
    (LiLiuLemma43Int.majorArcs (P N) N) :=
  integrableOn_major (((continuous_SA _ _).norm.pow 2).mul
    (Complex.continuous_re.comp (continuous_eC.comp (continuous_const.mul continuous_id)))) (P N) N

/-- The inner block: `∫_𝔐 |S|² Re(G^i conj G^j) = r_{i,j}(0) R₁(0) + Off_{i,j}`. -/
lemma block (κ : ℝ) (P : ℕ → ℝ) (N i j : ℕ) :
    ∫ α in LiLiuLemma43Int.majorArcs (P N) N, ‖Sm (N1f κ N) N α‖ ^ 2 *
      (Gs (Lfun N) α ^ i * (starRingEnd ℂ) (Gs (Lfun N) α ^ j)).re =
      Dc i j (Lfun N) * R1 κ P N + Off κ P N i j := by
  have hpt : ∀ α, ‖Sm (N1f κ N) N α‖ ^ 2 *
      (Gs (Lfun N) α ^ i * (starRingEnd ℂ) (Gs (Lfun N) α ^ j)).re =
      ∑ ν : Fin i → Fin (Lfun N), ∑ μ : Fin j → Fin (Lfun N), ‖Sm (N1f κ N) N α‖ ^ 2 *
        (eC (-(((sv ν : ℤ) - sv μ : ℤ) : ℝ) * α)).re := fun α => by
    rw [Gpow_conj, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [neg_mul, eC_re_neg]
    push_cast; rfl
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun ν _ => integrable_finsetSum _ fun μ _ => intOn κ P N _)]
  simp_rw [integral_finsetSum _ (fun μ _ => intOn κ P N _), ← R1h_re]
  unfold Dc Off
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases h : sv ν = sv μ
  · rw [if_pos h, if_pos h, h, sub_self, R1h_zero]; ring
  · rw [if_neg h, if_neg h]; ring

lemma SFG_expand (κ : ℝ) (N : ℕ) (α : ℝ) :
    SFG κ N α = ∑ k : Fin 3, ∑ l : Fin 3, wv (Lfun N) k * wv (Lfun N) l *
      (‖Sm (N1f κ N) N α‖ ^ 2 * (Gs (Lfun N) α ^ ((k : ℕ) + 1) *
        (starRingEnd ℂ) (Gs (Lfun N) α ^ ((l : ℕ) + 1))).re) := by
  unfold SFG
  rw [norm_mul, mul_pow, FG_expand, normSq_sum3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The major arc expansion behind (30), PROVED unconditional**:
`∫_𝔐 |S F(G)|² = ∑_{k,l} w_k w_l (r_{k+1,l+1}(0) R₁(0) + Off_{k+1,l+1})`. -/
theorem integral_major_SFG (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) :
    ∫ α in LiLiuLemma43Int.majorArcs (P N) N, SFG κ N α =
      ∑ k : Fin 3, ∑ l : Fin 3, wv (Lfun N) k * wv (Lfun N) l *
        (Dc ((k : ℕ) + 1) ((l : ℕ) + 1) (Lfun N) * R1 κ P N + Off κ P N ((k : ℕ) + 1) ((l : ℕ) + 1)) := by
  have hint : ∀ i j : ℕ, IntegrableOn (fun α => ‖Sm (N1f κ N) N α‖ ^ 2 *
      (Gs (Lfun N) α ^ i * (starRingEnd ℂ) (Gs (Lfun N) α ^ j)).re)
      (LiLiuLemma43Int.majorArcs (P N) N) := fun i j =>
    integrableOn_major (((continuous_SA _ _).norm.pow 2).mul (Complex.continuous_re.comp
      (((continuous_Gs _).pow i).mul (Complex.continuous_conj.comp ((continuous_Gs _).pow j)))))
      (P N) N
  simp_rw [SFG_expand]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => (hint _ _).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ (fun l _ => (hint _ _).const_mul _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, block]

/-! ### From Lemma 4.2 to the upper half of (30) -/

lemma R1_nonneg (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) : 0 ≤ R1 κ P N := by
  unfold R1 LiLiuLemma43Int.R10
  exact setIntegral_nonneg (measurableSet_majorArcs _ _) fun _ _ => by positivity

/-- `R₁(0) ≤ R(0) = ∑_{N₁ < p ≤ N} log² p`, the second half of (27), by Parseval. -/
lemma R1_le_sum (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) :
    R1 κ P N ≤ ∑ p ∈ primesIn (N1f κ N) N, Real.log p ^ 2 := by
  unfold R1 LiLiuLemma43Int.R10
  have hc : Continuous fun α => ‖SA (primesIn (N1f κ N) N) logw α‖ ^ 2 :=
    (continuous_SA _ _).norm.pow 2
  calc _ ≤ ∫ α in Icc (0 : ℝ) 1, ‖SA (primesIn (N1f κ N) N) logw α‖ ^ 2 :=
        setIntegral_mono_set hc.integrableOn_Icc (ae_of_all _ fun _ => by positivity)
          (majorArcs_sub _ _).eventuallyLE
    _ = _ := parseval _ (fun n => Real.log n)

lemma Dc_nonneg (i j L : ℕ) : 0 ≤ Dc i j L :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- One term of the expansion against the two sided (29). -/
lemma term_le {c D R O M E B : ℝ} (hO : |O - M| ≤ E) (hD0 : 0 ≤ D) (hDB : D ≤ B) (hR : 0 ≤ R) :
    c * (D * R + O) ≤ c * M + |c| * E + |c| * B * R := by
  have h1 : c * (O - M) ≤ |c| * E :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hO (abs_nonneg c))
  have h2 : c * (D * R) ≤ |c| * B * R :=
    calc c * (D * R) ≤ |c| * (D * R) := mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (B * R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDB hR) (abs_nonneg c)
      _ = _ := by ring
  have h3 : c * (D * R + O) = c * (D * R) + c * (O - M) + c * M := by ring
  linarith

lemma term_le00 {c L R O M E : ℝ} (hO : |O - M| ≤ E) :
    c * (L * R + O) ≤ c * M + |c| * E + c * L * R := by
  have h1 : c * (O - M) ≤ |c| * E :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hO (abs_nonneg c))
  have h3 : c * (L * R + O) = c * L * R + c * (O - M) + c * M := by ring
  linarith

lemma wv_mul (L : ℕ) (k l : Fin 3) :
    wv L k * wv L l = ((LiLiu.v k : ℝ) * LiLiu.v l) * ((L : ℝ) ^ (2 - (k : ℕ)) * L ^ (2 - (l : ℕ))) := by
  unfold wv; ring

lemma pow_six (L : ℕ) (k l : Fin 3) :
    (L : ℝ) ^ (2 - (k : ℕ)) * L ^ (2 - (l : ℕ)) * L ^ ((k : ℕ) + l + 2) = L ^ 6 := by
  rw [← pow_add, ← pow_add]; congr 1; omega

lemma pow_four (L : ℕ) (k l : Fin 3) :
    (L : ℝ) ^ (2 - (k : ℕ)) * L ^ (2 - (l : ℕ)) * L ^ ((k : ℕ) + l) = L ^ 4 := by
  rw [← pow_add, ← pow_add]; congr 1; omega

lemma abs_wv_mul (L : ℕ) (k l : Fin 3) :
    |wv L k * wv L l| = |(LiLiu.v k : ℝ) * LiLiu.v l| * ((L : ℝ) ^ (2 - (k : ℕ)) * L ^ (2 - (l : ℕ))) := by
  rw [wv_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ (2 - (k : ℕ)) * L ^ (2 - (l : ℕ)) by
    positivity)]

lemma sum_vv : ∑ k : Fin 3, ∑ l : Fin 3, ((LiLiu.v k : ℝ) * LiLiu.v l) = (1 - 1 / 4 - 1 / 16) ^ 2 := by
  simp [Fin.sum_univ_three, LiLiu.v]; norm_num

lemma sum_abs_vv : ∑ k : Fin 3, ∑ l : Fin 3, |(LiLiu.v k : ℝ) * LiLiu.v l| = 441 / 256 := by
  simp [Fin.sum_univ_three, LiLiu.v, abs_mul]; norm_num

/-- The `h = 0` weights: `G₀₀ = w₀² L` exactly, and `|w_k w_l| · 3L^{k+l}` otherwise. -/
noncomputable def Gw (L : ℕ) (k l : Fin 3) : ℝ :=
  if k = 0 ∧ l = 0 then wv L k * wv L l * L else |wv L k * wv L l| * (3 * (L : ℝ) ^ ((k : ℕ) + l))

lemma sum_Gw (L : ℕ) : ∑ k : Fin 3, ∑ l : Fin 3, Gw L k l =
    (1 / 16) ^ 2 * (L : ℝ) ^ 5 + 3 * (440 / 256) * (L : ℝ) ^ 4 := by
  have h : ∀ k l : Fin 3, ¬ (k = 0 ∧ l = 0) → Gw L k l = 3 * |(LiLiu.v k : ℝ) * LiLiu.v l| * (L : ℝ) ^ 4 := by
    intro k l hkl
    rw [Gw, if_neg hkl, abs_wv_mul, ← pow_four L k l]; ring
  have h00 : Gw L 0 0 = (1 / 16) ^ 2 * (L : ℝ) ^ 5 := by
    simp [Gw, wv, LiLiu.v]; ring
  simp only [Fin.sum_univ_three]
  rw [h00, h 0 1 (by decide), h 0 2 (by decide), h 1 0 (by decide), h 1 1 (by decide),
    h 1 2 (by decide), h 2 0 (by decide), h 2 1 (by decide), h 2 2 (by decide)]
  simp [LiLiu.v, abs_mul]
  ring

/-- **The upper half of (30) from Lemma 4.2, PROVED, CONDITIONAL ON the cited `Lemma42` only**:
with `V = vᵀAv`, `Display30Upper κ P V (2e₀)`. -/
theorem display30Upper_of {κ e0 : ℝ} {P : ℕ → ℝ} {A : Fin 3 → Fin 3 → ℝ} (he0 : 0 ≤ e0)
    (h42 : Lemma42 κ P A e0) :
    Display30Upper κ P (∑ i, ∑ j, (LiLiu.v i : ℝ) * A i j * (LiLiu.v j : ℝ)) (2 * e0) := by
  intro δ hδ
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i j : Fin 3,
      |Off κ P N ((i : ℕ) + 1) ((j : ℕ) + 1) -
        2 * N * (Lfun N : ℝ) ^ ((i : ℕ) + j + 2) * (1 + A i j)| ≤
      2 * N * (Lfun N : ℝ) ^ ((i : ℕ) + j + 2) * (e0 + δ / 4) := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact h42 i j (δ / 4) (by positivity)
  filter_upwards [hall, diag_small κ one_pos, Lfun_tendsto.eventually_ge_atTop ⌈12 / δ⌉₊]
    with N hN hdiag hLbig
  set L := Lfun N with hLdef
  set R := R1 κ P N with hRdef
  have hR0 : 0 ≤ R := R1_nonneg κ P N
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [integral_major_SFG]
  have hterm : ∀ k l : Fin 3, wv L k * wv L l *
      (Dc ((k : ℕ) + 1) ((l : ℕ) + 1) L * R + Off κ P N ((k : ℕ) + 1) ((l : ℕ) + 1)) ≤
      wv L k * wv L l * (2 * N * (L : ℝ) ^ ((k : ℕ) + l + 2) * (1 + A k l)) +
        |wv L k * wv L l| * (2 * N * (L : ℝ) ^ ((k : ℕ) + l + 2) * (e0 + δ / 4)) +
        Gw L k l * R := by
    intro k l
    by_cases hkl : k = 0 ∧ l = 0
    · obtain ⟨rfl, rfl⟩ := hkl
      have h := term_le00 (c := wv L 0 * wv L 0) (L := (L : ℝ)) (R := R) (hN 0 0)
      simp only [Fin.val_zero, zero_add, Dc_one_one, Gw, and_self, if_true] at h ⊢
      linarith
    · have h := term_le (c := wv L k * wv L l) (hN k l) (Dc_nonneg _ _ L)
        (Dc_bound k l L hkl) hR0
      rw [Gw, if_neg hkl]
      linarith
  refine (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l).trans ?_
  simp only [Finset.sum_add_distrib]
  have hS1 : ∑ k : Fin 3, ∑ l : Fin 3,
      wv L k * wv L l * (2 * N * (L : ℝ) ^ ((k : ℕ) + l + 2) * (1 + A k l)) =
      2 * (N * (L : ℝ) ^ 6) * ((1 - 1 / 4 - 1 / 16) ^ 2 +
        ∑ i, ∑ j, (LiLiu.v i : ℝ) * A i j * (LiLiu.v j : ℝ)) := by
    rw [← sum_vv, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [wv_mul, ← pow_six L k l]; ring
  have hS2 : ∑ k : Fin 3, ∑ l : Fin 3,
      |wv L k * wv L l| * (2 * N * (L : ℝ) ^ ((k : ℕ) + l + 2) * (e0 + δ / 4)) =
      2 * (N * (L : ℝ) ^ 6) * (e0 + δ / 4) * (441 / 256) := by
    rw [← sum_abs_vv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [abs_wv_mul, ← pow_six L k l]; ring
  have hS3 : ∑ k : Fin 3, ∑ l : Fin 3, Gw L k l * R =
      ((1 / 16) ^ 2 * (L : ℝ) ^ 5 + 3 * (440 / 256) * (L : ℝ) ^ 4) * R := by
    rw [← sum_Gw, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
  rw [hS1, hS2, hS3]
  -- the error terms
  have hX : 0 ≤ (N : ℝ) * (L : ℝ) ^ 6 := by positivity
  have hLR : (L : ℝ) * R ≤ N * (L : ℝ) ^ 2 * (Real.log 2 + 1) :=
    (mul_le_mul_of_nonneg_left (R1_le_sum κ P N) hL0).trans hdiag
  have hl2 : Real.log 2 + 1 ≤ 2 := by linarith [Real.log_two_lt_d9]
  have hL4R : (L : ℝ) ^ 4 * R ≤ 2 * (N * (L : ℝ) ^ 5) := by
    calc (L : ℝ) ^ 4 * R = (L : ℝ) ^ 3 * (L * R) := by ring
      _ ≤ (L : ℝ) ^ 3 * (N * (L : ℝ) ^ 2 * (Real.log 2 + 1)) :=
          mul_le_mul_of_nonneg_left hLR (by positivity)
      _ ≤ (L : ℝ) ^ 3 * (N * (L : ℝ) ^ 2 * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl2 (by positivity)) (by positivity)
      _ = _ := by ring
  have h12 : 12 ≤ δ * L := by
    have h1 : 12 / δ ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hLbig)
    rw [div_le_iff₀ hδ] at h1; linarith
  have hL5 : 12 * (N * (L : ℝ) ^ 5) ≤ δ * (N * (L : ℝ) ^ 6) := by
    have : 0 ≤ N * (L : ℝ) ^ 5 := by positivity
    calc 12 * (N * (L : ℝ) ^ 5) ≤ (δ * L) * (N * (L : ℝ) ^ 5) := mul_le_mul_of_nonneg_right h12 this
      _ = _ := by ring
  have hE : 2 * (N * (L : ℝ) ^ 6) * (e0 + δ / 4) * (441 / 256) ≤
      2 * (N * (L : ℝ) ^ 6) * (2 * e0 + δ / 2) := by
    have : (e0 + δ / 4) * (441 / 256) ≤ 2 * e0 + δ / 2 := by linarith
    nlinarith
  nlinarith

/-- `Off_{1,1}` is the sum of `Lemma42Lower11`, over `1 ≤ ν ≠ μ ≤ L`. -/
lemma fin_shift (L : ℕ) (g : ℕ → ℝ) : ∑ x : Fin L, g ((x : ℕ) + 1) = ∑ n ∈ Finset.Icc 1 L, g n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1)) L]
  have : Finset.Icc 1 L = (range L).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [this, sum_map]
  rfl

lemma sum_fin1 {L : ℕ} (F : (Fin 1 → Fin L) → ℝ) :
    ∑ ν : Fin 1 → Fin L, F ν = ∑ x : Fin L, F (fun _ => x) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin L)) _ _ fun ν => by
    congr 1; funext i; rw [Subsingleton.elim i default]; rfl

lemma Off11_eq (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) :
    Off κ P N 1 1 = ∑ ν ∈ Finset.Icc 1 (Lfun N), ∑ μ ∈ Finset.Icc 1 (Lfun N),
      (if ν = μ then 0 else (R1h κ P N ((2 : ℤ) ^ ν - 2 ^ μ)).re) := by
  unfold Off
  rw [sum_fin1]
  simp_rw [sum_fin1 (L := Lfun N)]
  have hsv : ∀ x : Fin (Lfun N), sv (fun _ : Fin 1 => x) = 2 ^ ((x : ℕ) + 1) := by
    intro x; simp [sv]
  simp_rw [hsv]
  rw [← fin_shift]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← fin_shift (Lfun N) (fun m => if (x : ℕ) + 1 = m then 0 else
    (R1h κ P N ((2 : ℤ) ^ ((x : ℕ) + 1) - 2 ^ m)).re)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hiff : (2 : ℕ) ^ ((x : ℕ) + 1) = 2 ^ ((y : ℕ) + 1) ↔ (x : ℕ) + 1 = (y : ℕ) + 1 :=
    ⟨fun h => Nat.pow_right_injective le_rfl h, fun h => by rw [h]⟩
  by_cases h : (x : ℕ) + 1 = (y : ℕ) + 1
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    push_cast; rfl

/-- `Lemma42Lower11 κ P A₁₁ (2e₀)` from the two sided `Lemma42 κ P A e₀`. -/
theorem lemma42Lower11_of {κ e0 : ℝ} {P : ℕ → ℝ} {A : Fin 3 → Fin 3 → ℝ} (he0 : 0 ≤ e0)
    (h42 : Lemma42 κ P A e0) : Lemma42Lower11 κ P (A 0 0) (2 * e0) := by
  intro δ hδ
  filter_upwards [h42 0 0 δ hδ] with N hN
  rw [← Off11_eq]
  simp only [Fin.val_zero, zero_add] at hN
  have h1 := (abs_le.mp hN).1
  have hX : 0 ≤ 2 * (N : ℝ) * (Lfun N : ℝ) ^ 2 * e0 := by positivity
  nlinarith

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON the cited Lemma 4.2 for all `1 ≤ i, j ≤ 3` `Lemma42` with
`A = A_* + T`, the cited (31) `Display31 6.7814`, the cited (20) `SingSum20 CR`, `MinorSup1924 P`,
the conditions (24) on `P`, and the cited constants of `k6_wired`**. This is
`U7205Display34.r6_lower4` with `Display30Upper` and `Lemma42Lower11` both discharged from
`Lemma42`. -/
theorem r6_lower5 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814) (h20 : SingSum20 CR) :
    ∃ e1 > 0, ∀ e0 : ℝ, 0 ≤ e0 → e0 < e1 → ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      Lemma42 κ P (fun i j => (LiLiu.Astar i j : ℝ) + T i j) e0 →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  obtain ⟨e1, he1, h⟩ := r6_lower4 T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 h20
  refine ⟨e1 / 2, by positivity, fun e0 he0 he01 κ hκ P hP11 hPup hP2 hMS h42 => ?_⟩
  exact h (2 * e0) (by positivity) (by linarith) hκ P hP11 hPup hP2 hMS
    (display30Upper_of he0 h42) (lemma42Lower11_of he0 h42)

/-- Vacuity of the combinatorial side: `r_{1,1}(0) = L` and the bound of (19) hold at `L = 5`. -/
theorem Dc_instance : Dc 1 1 5 = 5 ∧ Dc 3 3 5 ≤ 3 * (5 : ℝ) ^ 4 :=
  ⟨by rw [Dc_one_one]; norm_num, by simpa using Dc_bound 2 2 5 (by decide)⟩

end LeanLab.Linnik.U1447Display30

