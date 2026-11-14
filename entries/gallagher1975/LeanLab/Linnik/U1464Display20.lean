module

public import LeanLab.Linnik.U1458Lemma42

/-!
Li-Liu, arXiv 2610.15784, Section 3: display (15), Lemma 3.1 display (17), and the limit (20).
Read by WebFetch on the unversioned arxiv.org/html/2610.15784, 2026-10-22.

The paper's route to (20). By (15), `𝔖(h)/(2C₀) = ∑'_{d | h} 1/∏_{p | d}(p-2)`, the primed sum over
odd squarefree `d`. So `∑_{h ≠ 0} r_{i,j}(h)𝔖(h)` splits at a level `D` into
`2C₀ ∑'_{d ≤ D} w(d) #{tuples : h ≠ 0, d | h}` plus `2C₀` times the sum of display (17). For fixed
odd `d`, `2^t mod d` has period `ε(d)`, the order of `2` mod `d`, so the tuples with `d | h` are
counted residue class by residue class: the count over `L^{i+j}` tends to
`P_d(i,j) = #{t, s mod ε(d) : ∑ 2^{t_a} ≡ ∑ 2^{s_b} mod d} / ε(d)^{i+j}`. Display (17) makes the
part `d > D` uniformly small, and this gives (20):
`(1/2L^{i+j}) ∑_{h ≠ 0} r_{i,j}(h)𝔖(h) → B_{ij} = C₀ ∑'_d P_d(i,j)/∏_{p | d}(p-2)`.

Contents.
* `wt`, `eps`: the weight `1/∏_{p|d}(p-2)` on odd squarefree `d`, zero elsewhere, and `ε(d)`.
* `singS_expand`: display (15), first identity, PROVED.
* `soff_split`: the finite-`L` counting identity, PROVED.
* `cntRes_tendsto`, `cntAll_eq`, `cnt_tendsto`: the per-`d` equidistribution count, PROVED.
* `Display17`: Lemma 3.1, display (17), CITED. `display17_lim`: its `N → ∞, D → ∞` form, PROVED
  from `Display17`.
* `display20_of`: `Display20 Bdef`, PROVED, CONDITIONAL ON `Display17`.
* `r6_lower7`: `U1458Lemma42.r6_lower6` with the hypothesis `Display20` removed.

Here `P_d(i,j)` is defined by the residue count. The paper writes it as
`(1/d) ∑_{a mod d} z_d(a)^i conj(z_d(a))^j`; the two agree by orthogonality of additive characters
mod `d`, which is not formalised here. It does not matter for the chain: the paper defines `B_{ij}`
as the limit (20), so the cited Proposition 3.2 is about the same number `Bdef`.

Unit U-1464, run 20261022T0403Z-7595. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1464Display20

open Set Real Filter Finset Topology
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U7203Display33
open LeanLab.Linnik.U7205Display34
open LeanLab.Linnik.U1447Display30
open LeanLab.Linnik.U1458Lemma42
open LeanLab.Linnik.U1434Lemma21 (sv sv_le sv_even)

/-! ### The weight and the order of 2 -/

/-- `1/∏_{p | d}(p-2)` for odd squarefree `d`, and `0` otherwise: the primed sums of the paper
are sums of `wt` over all `d`. -/
noncomputable def wt (d : ℕ) : ℝ :=
  if Odd d ∧ Squarefree d then ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) else 0

/-- `ε(d)`, the order of `2` modulo `d`; `ε(1) = 1`. -/
noncomputable def eps (d : ℕ) : ℕ := orderOf (2 : ZMod d)

lemma three_le_of_mem {d p : ℕ} (hd : Odd d) (hp : p ∈ d.primeFactors) : 3 ≤ p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have h2 := hpp.two_le
  have : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hpd)
  omega

lemma wt_nonneg (d : ℕ) : 0 ≤ wt d := by
  unfold wt; split_ifs with h
  · refine prod_nonneg fun p hp => ?_
    have : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem h.1 hp
    exact div_nonneg zero_le_one (by linarith)
  · exact le_refl 0

lemma eps_pos {d : ℕ} (hd : Odd d) : 0 < eps d := by
  have hd0 : d ≠ 0 := by rintro rfl; exact absurd hd (by decide)
  have h1 : (2 : ZMod d) ^ Nat.totient d = 1 := by
    have := Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hd)
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr this
    simpa using this
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨_, Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0), h1⟩)

/-! ### Display (15) -/

/-- `g(p) = 1/(p-2)` for `p > 2`, `g(2) = 0`. -/
noncomputable def gp (p : ℕ) : ℝ := if 2 < p then 1 / ((p : ℝ) - 2) else 0

lemma sq_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => by
      simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
    fun p hp => (hs p hp).squarefree

lemma wt_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) : wt (∏ p ∈ s, p) = ∏ p ∈ s, gp p := by
  have hpf : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod hs
  by_cases h2 : 2 ∈ s
  · have hev : ¬ Odd (∏ p ∈ s, p) := by
      rw [Nat.not_odd_iff_even, even_iff_two_dvd]
      exact Finset.dvd_prod_of_mem _ h2
    rw [wt, if_neg (fun h => hev h.1)]
    symm; exact Finset.prod_eq_zero h2 (by simp [gp])
  · have hodd : Odd (∏ p ∈ s, p) := by
      refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => ?_)
      obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finset_prod_iff Nat.prime_two.prime _).mp h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hs p hp)).mp h2p
      exact h2 (this ▸ hp)
    rw [wt, if_pos ⟨hodd, sq_prod hs⟩, hpf]
    refine prod_congr rfl fun p hp => ?_
    have h2p : 2 < p := by
      have := (hs p hp).two_le
      have : p ≠ 2 := fun h => h2 (h ▸ hp)
      omega
    simp [gp, h2p]

lemma prod_expand {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2) =
      ∑ d ∈ n.divisors, wt d := by
  rw [Finset.prod_filter]
  have h1 : ∀ p ∈ n.primeFactors,
      (if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) = 1 + gp p := by
    intro p _
    unfold gp
    split_ifs with h
    · have : (p : ℝ) - 2 ≠ 0 := by
        have : (2 : ℝ) < p := by exact_mod_cast h
        linarith
      field_simp; ring
    · simp
  rw [prod_congr rfl h1, Finset.prod_one_add]
  have h2 : ∑ d ∈ n.divisors, wt d = ∑ d ∈ n.divisors.filter Squarefree, wt d := by
    rw [Finset.sum_filter_of_ne]
    intro d _ hd
    by_contra hsq
    exact hd (by simp [wt, hsq])
  rw [h2]
  refine Finset.sum_nbij' (fun t => ∏ p ∈ t, p) (fun d => d.primeFactors) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have ht' : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    have hs : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht' hp)
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hn⟩, sq_prod hs⟩
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors (fun p => p) ht').trans
      (Nat.prod_primeFactors_dvd n)
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono hd.1.1 hn)
  · intro t ht
    have ht' : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (ht' hp)
  · intro d hd
    simp only [Finset.mem_filter] at hd
    exact Nat.prod_primeFactors_of_squarefree hd.2
  · intro t ht
    have ht' : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    exact (wt_prod fun p hp => Nat.prime_of_mem_primeFactors (ht' hp)).symm

/-- **Display (15), first identity, PROVED**: for nonzero even `h`,
`𝔖(h) = 2C₀ ∑'_{d | h} 1/∏_{p | d}(p-2)`. -/
theorem singS_expand (h : ℤ) (h0 : h ≠ 0) (he : Even h) :
    singS h = 2 * C0 * ∑ d ∈ h.natAbs.divisors, wt d := by
  unfold singS
  rw [if_pos ⟨h0, he⟩, prod_expand (Int.natAbs_ne_zero.mpr h0)]

/-! ### The finite-`L` counting identity -/

/-- `#{(ν, μ) : h ≠ 0, d | h}` with `h = ∑ 2^{ν_a} - ∑ 2^{μ_b}`, exponents in `[1, L]`. -/
noncomputable def cnt (I J L d : ℕ) : ℝ :=
  ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L,
    if sv ν = sv μ then 0 else if (d : ℤ) ∣ ((sv ν : ℤ) - sv μ) then 1 else 0

/-- `#{(ν, μ) : d | h}`, the diagonal `h = 0` included. -/
noncomputable def cntAll (I J L d : ℕ) : ℝ :=
  ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L, if (d : ℤ) ∣ ((sv ν : ℤ) - sv μ) then 1 else 0

/-- `∑_{h ≠ 0} r_{I,J}(h) ∑'_{d > D, d | h} 1/∏_{p | d}(p-2)`, over exponent tuples. -/
noncomputable def T17 (I J L D : ℕ) : ℝ :=
  ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L,
    if sv ν = sv μ then 0 else
      ∑ d ∈ ((sv ν : ℤ) - sv μ).natAbs.divisors.filter (fun d => D < d), wt d

/-- The left side of display (17): `T17 / L^{I+J}`. -/
noncomputable def Lhs17 (I J L D : ℕ) : ℝ := T17 I J L D / (L : ℝ) ^ (I + J)

lemma T17_nonneg (I J L D : ℕ) : 0 ≤ T17 I J L D := by
  unfold T17
  refine sum_nonneg fun ν _ => sum_nonneg fun μ _ => ?_
  split_ifs
  · exact le_refl 0
  · exact sum_nonneg fun d _ => wt_nonneg d

lemma split_tuple (D : ℕ) (h : ℤ) (h0 : h ≠ 0) :
    ∑ d ∈ h.natAbs.divisors, wt d =
      ∑ d ∈ range (D + 1), wt d * (if (d : ℤ) ∣ h then 1 else 0) +
        ∑ d ∈ h.natAbs.divisors.filter (fun d => D < d), wt d := by
  rw [← Finset.sum_filter_add_sum_filter_not h.natAbs.divisors (fun d => D < d), add_comm]
  congr 1
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_range, Int.natCast_dvd, not_lt]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨by omega, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2, Int.natAbs_ne_zero.mpr h0⟩, by omega⟩

/-- **The finite-`L` counting identity, PROVED**: for every level `D`,
`∑_{h ≠ 0} r_{I,J}(h)𝔖(h) = 2C₀ (∑'_{d ≤ D} w(d) #{h ≠ 0, d | h} + T17)`. -/
theorem soff_split (I J L D : ℕ) :
    SOff L I J = 2 * C0 * (∑ d ∈ range (D + 1), wt d * cnt I J L d + T17 I J L D) := by
  have hpt : ∀ (ν : Fin I → Fin L) (μ : Fin J → Fin L),
      (if sv ν = sv μ then (0 : ℝ) else singS ((sv ν : ℤ) - sv μ)) =
      ∑ d ∈ range (D + 1), 2 * C0 * (wt d * (if sv ν = sv μ then 0 else
          if (d : ℤ) ∣ ((sv ν : ℤ) - sv μ) then 1 else 0)) +
        2 * C0 * (if sv ν = sv μ then 0 else
          ∑ d ∈ ((sv ν : ℤ) - sv μ).natAbs.divisors.filter (fun d => D < d), wt d) := by
    intro ν μ
    by_cases hs : sv ν = sv μ
    · simp [hs]
    simp only [if_neg hs]
    have h0 : ((sv ν : ℤ) - sv μ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hs)
    rw [singS_expand _ h0 (even_h ν μ), split_tuple D _ h0, ← Finset.mul_sum, mul_add]
  unfold SOff cnt T17
  simp_rw [hpt]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]

/-! ### Equidistribution of `2^t` modulo `d` -/

/-- `#{0 ≤ x < L : x ≡ c mod e}`. -/
noncomputable def cntRes (L e c : ℕ) : ℝ := ∑ x : Fin L, if (x : ℕ) % e = c then 1 else 0

lemma cntRes_eq {L e c : ℕ} (he : 0 < e) (hc : c < e) :
    cntRes L e c = ((L / e + if c < L % e then 1 else 0 : ℕ) : ℝ) := by
  have h := Nat.count_modEq_card (b := L) he c
  rw [Nat.mod_eq_of_lt hc] at h
  rw [← h, Nat.count_eq_card_filter_range, cntRes]
  rw [Fin.sum_univ_eq_sum_range (fun x => if x % e = c then (1 : ℝ) else 0) L]
  rw [Finset.sum_boole]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Nat.ModEq, Nat.mod_eq_of_lt hc]

lemma cntRes_bounds {L e c : ℕ} (he : 0 < e) (hc : c < e) :
    (L : ℝ) / e - 1 ≤ cntRes L e c ∧ cntRes L e c ≤ (L : ℝ) / e + 1 := by
  rw [cntRes_eq he hc]
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hL : (L : ℝ) = e * (L / e : ℕ) + (L % e : ℕ) := by exact_mod_cast (Nat.div_add_mod L e).symm
  have hr : ((L % e : ℕ) : ℝ) < e := by exact_mod_cast Nat.mod_lt L he
  have hr0 : (0 : ℝ) ≤ (L % e : ℕ) := Nat.cast_nonneg _
  have hdiv : (L : ℝ) / e = (L / e : ℕ) + ((L % e : ℕ) : ℝ) / e := by
    rw [hL]; field_simp
  have hq : ((L % e : ℕ) : ℝ) / e < 1 := (div_lt_one heR).mpr hr
  have hq0 : 0 ≤ ((L % e : ℕ) : ℝ) / e := div_nonneg hr0 heR.le
  push_cast
  rw [hdiv]
  split_ifs <;> constructor <;> push_cast <;> linarith

lemma cntRes_tendsto {e c : ℕ} (he : 0 < e) (hc : c < e) :
    Tendsto (fun L : ℕ => cntRes L e c / L) atTop (𝓝 (1 / (e : ℝ))) := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hlo : Tendsto (fun L : ℕ => 1 / (e : ℝ) - 1 / (L : ℝ)) atTop (𝓝 (1 / (e : ℝ))) := by
    have := (tendsto_const_nhds (x := 1 / (e : ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    rwa [sub_zero] at this
  have hhi : Tendsto (fun L : ℕ => 1 / (e : ℝ) + 1 / (L : ℝ)) atTop (𝓝 (1 / (e : ℝ))) := by
    have := (tendsto_const_nhds (x := 1 / (e : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have := (cntRes_bounds (L := L) he hc).1
    rw [le_div_iff₀ hLR]
    have e1 : (1 / (e : ℝ) - 1 / L) * L = L / e - 1 := by field_simp
    linarith
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have := (cntRes_bounds (L := L) he hc).2
    rw [div_le_iff₀ hLR]
    have e1 : (1 / (e : ℝ) + 1 / L) * L = L / e + 1 := by field_simp
    linarith

/-- Summing a function of the residues `ν_a mod e` over all tuples `ν`. -/
lemma sum_fiber {n L e : ℕ} (he : 0 < e) (g : (Fin n → ℕ) → ℝ) :
    ∑ ν : Fin n → Fin L, g (fun a => (ν a : ℕ) % e) =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin n => range e), g t * ∏ a, cntRes L e (t a) := by
  have h1 : ∀ ν : Fin n → Fin L, g (fun a => (ν a : ℕ) % e) =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin n => range e),
        g t * ∏ a, (if (ν a : ℕ) % e = t a then (1 : ℝ) else 0) := by
    intro ν
    have hmem : (fun a => (ν a : ℕ) % e) ∈ Fintype.piFinset (fun _ : Fin n => range e) :=
      Fintype.mem_piFinset.mpr fun a => Finset.mem_range.mpr (Nat.mod_lt _ he)
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · rw [Finset.prod_eq_one (fun a _ => if_pos rfl), mul_one]
    · intro t _ ht
      have : ∃ a, (ν a : ℕ) % e ≠ t a := by
        by_contra hc
        push_neg at hc
        exact ht (funext hc).symm
      obtain ⟨a, ha⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha), mul_zero]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold cntRes
  exact (Fintype.prod_sum (fun a (x : Fin L) => if (x : ℕ) % e = t a then (1 : ℝ) else 0)).symm

/-- The residue condition `∑_a 2^{t_a + 1} = ∑_b 2^{s_b + 1}` in `ZMod d`. -/
def good (d : ℕ) {I J : ℕ} (t : Fin I → ℕ) (s : Fin J → ℕ) : Prop :=
  ∑ a, (2 : ZMod d) ^ (t a + 1) = ∑ b, (2 : ZMod d) ^ (s b + 1)

instance (d : ℕ) {I J : ℕ} (t : Fin I → ℕ) (s : Fin J → ℕ) : Decidable (good d t s) := by
  unfold good; infer_instance

/-- `d | h` depends only on the exponents modulo `ε(d)`. -/
lemma dvd_iff_good {I J L : ℕ} (d : ℕ) (ν : Fin I → Fin L) (μ : Fin J → Fin L) :
    (d : ℤ) ∣ ((sv ν : ℤ) - sv μ) ↔
      good d (fun a => (ν a : ℕ) % eps d) (fun b => (μ b : ℕ) % eps d) := by
  have key : ∀ x : ℕ, (2 : ZMod d) ^ (x % eps d + 1) = 2 ^ (x + 1) := by
    intro x; rw [pow_succ, pow_succ, eps, pow_mod_orderOf]
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, good]
  simp only [key, sv]
  push_cast
  exact eq_comm

/-- **The residue count, PROVED**: `#{(ν, μ) : d | h}` as a sum over residue tuples mod `ε(d)`. -/
lemma cntAll_eq (I J L d : ℕ) (he : 0 < eps d) :
    cntAll I J L d = ∑ t ∈ Fintype.piFinset (fun _ : Fin I => range (eps d)),
      ∑ s ∈ Fintype.piFinset (fun _ : Fin J => range (eps d)),
        (if good d t s then (1 : ℝ) else 0) * (∏ b, cntRes L (eps d) (s b)) *
          (∏ a, cntRes L (eps d) (t a)) := by
  unfold cntAll
  simp_rw [dvd_iff_good d]
  have hin : ∀ ν : Fin I → Fin L, (∑ μ : Fin J → Fin L,
      if good d (fun a => (ν a : ℕ) % eps d) (fun b => (μ b : ℕ) % eps d) then (1 : ℝ) else 0) =
      ∑ s ∈ Fintype.piFinset (fun _ : Fin J => range (eps d)),
        (if good d (fun a => (ν a : ℕ) % eps d) s then (1 : ℝ) else 0) *
          ∏ b, cntRes L (eps d) (s b) :=
    fun ν => sum_fiber he (fun s => if good d (fun a => (ν a : ℕ) % eps d) s then (1 : ℝ) else 0)
  simp_rw [hin]
  rw [sum_fiber he (fun t => ∑ s ∈ Fintype.piFinset (fun _ : Fin J => range (eps d)),
        (if good d t s then (1 : ℝ) else 0) * ∏ b, cntRes L (eps d) (s b))]
  simp_rw [Finset.sum_mul]

/-- `P_d(I, J) = #{t, s mod ε(d) : ∑ 2^{t_a} ≡ ∑ 2^{s_b} mod d} / ε(d)^{I+J}`. -/
noncomputable def Pd (d I J : ℕ) : ℝ :=
  ∑ t ∈ Fintype.piFinset (fun _ : Fin I => range (eps d)),
    ∑ s ∈ Fintype.piFinset (fun _ : Fin J => range (eps d)),
      (if good d t s then (1 : ℝ) else 0) * (∏ _b : Fin J, 1 / (eps d : ℝ)) *
        (∏ _a : Fin I, 1 / (eps d : ℝ))

lemma Pd_nonneg (d I J : ℕ) : 0 ≤ Pd d I J := by
  unfold Pd
  refine sum_nonneg fun t _ => sum_nonneg fun s _ => ?_
  have h1 : (0 : ℝ) ≤ 1 / (eps d : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun _ _ => h1))
    (prod_nonneg fun _ _ => h1)

/-- **Equidistribution, PROVED**: for odd `d`, `#{(ν, μ) : d | h}/L^{I+J} → P_d(I, J)`. -/
theorem cntAll_tendsto {d : ℕ} (hd : Odd d) (I J : ℕ) :
    Tendsto (fun L : ℕ => cntAll I J L d / (L : ℝ) ^ (I + J)) atTop (𝓝 (Pd d I J)) := by
  have he := eps_pos hd
  have hres : ∀ c ∈ range (eps d),
      Tendsto (fun L : ℕ => cntRes L (eps d) c / L) atTop (𝓝 (1 / (eps d : ℝ))) :=
    fun c hc => cntRes_tendsto he (Finset.mem_range.mp hc)
  have key : Tendsto (fun L : ℕ => ∑ t ∈ Fintype.piFinset (fun _ : Fin I => range (eps d)),
      ∑ s ∈ Fintype.piFinset (fun _ : Fin J => range (eps d)),
        (if good d t s then (1 : ℝ) else 0) * (∏ b, (cntRes L (eps d) (s b) / L)) *
          (∏ a, (cntRes L (eps d) (t a) / L))) atTop (𝓝 (Pd d I J)) := by
    unfold Pd
    refine tendsto_finset_sum _ fun t ht => tendsto_finset_sum _ fun s hs => ?_
    refine (tendsto_const_nhds.mul (tendsto_finset_prod _ fun b _ => hres _ ?_)).mul
      (tendsto_finset_prod _ fun a _ => hres _ ?_)
    · exact Fintype.mem_piFinset.mp hs b
    · exact Fintype.mem_piFinset.mp ht a
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  rw [cntAll_eq I J L d he, Finset.sum_div]
  refine sum_congr rfl fun t _ => ?_
  rw [Finset.sum_div]
  refine sum_congr rfl fun s _ => ?_
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_add]
  field_simp

lemma cnt_le_cntAll (I J L d : ℕ) : cnt I J L d ≤ cntAll I J L d := by
  unfold cnt cntAll
  refine sum_le_sum fun ν _ => sum_le_sum fun μ _ => ?_
  split_ifs <;> norm_num

lemma cntAll_le (I J L d : ℕ) : cntAll I J L d ≤ cnt I J L d + Dc I J L := by
  unfold cnt cntAll Dc
  rw [← Finset.sum_add_distrib]
  refine sum_le_sum fun ν _ => ?_
  rw [← Finset.sum_add_distrib]
  refine sum_le_sum fun μ _ => ?_
  split_ifs <;> norm_num

lemma Dc_le (i j : Fin 3) (L : ℕ) (hL : 1 ≤ L) :
    Dc ((i : ℕ) + 1) ((j : ℕ) + 1) L ≤ 3 * (L : ℝ) ^ ((i : ℕ) + j + 1) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij
    simp only [Fin.val_zero, zero_add, Dc_one_one, pow_one]
    linarith
  · have h1 := Dc_bound i j L hij
    have h2 : (L : ℝ) ^ ((i : ℕ) + j) ≤ (L : ℝ) ^ ((i : ℕ) + j + 1) :=
      pow_le_pow_right₀ hL1 (by omega)
    linarith

/-- **The per-`d` count, PROVED**: for odd `d` and `1 ≤ i, j ≤ 3`,
`#{(ν, μ) : h ≠ 0, d | h}/L^{i+j} → P_d(i, j)`. -/
theorem cnt_tendsto (i j : Fin 3) {d : ℕ} (hd : Odd d) :
    Tendsto (fun L : ℕ => cnt ((i : ℕ) + 1) ((j : ℕ) + 1) L d /
      (L : ℝ) ^ (((i : ℕ) + 1) + ((j : ℕ) + 1))) atTop (𝓝 (Pd d ((i : ℕ) + 1) ((j : ℕ) + 1))) := by
  set I := (i : ℕ) + 1 with hI
  set J := (j : ℕ) + 1 with hJ
  have hA := cntAll_tendsto hd I J
  have hlo : Tendsto (fun L : ℕ => cntAll I J L d / (L : ℝ) ^ (I + J) - 3 * (1 / (L : ℝ))) atTop
      (𝓝 (Pd d I J)) := by
    simpa using hA.sub (tendsto_one_div_atTop_nhds_zero_nat.const_mul 3)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hA ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hLk : (0 : ℝ) < (L : ℝ) ^ (I + J) := by positivity
    have e : cntAll I J L d / (L : ℝ) ^ (I + J) - 3 * (1 / (L : ℝ)) =
        (cntAll I J L d - 3 * (L : ℝ) ^ ((i : ℕ) + j + 1)) / (L : ℝ) ^ (I + J) := by
      have : (L : ℝ) ^ (I + J) = (L : ℝ) ^ ((i : ℕ) + j + 1) * L := by
        rw [← pow_succ]; congr 1; omega
      rw [this]; field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hLk.le
    have := cntAll_le I J L d
    have := Dc_le i j L hL
    linarith
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    exact div_le_div_of_nonneg_right (cnt_le_cntAll I J L d) (by positivity)

/-! ### Display (17) and the limit (20) -/

/-- The tail `∑'_{d > D} 1/(ε(d)∏_{p | d}(p-2))` of `R₀` in (15). -/
noncomputable def R0tail (D : ℕ) : ℝ := ∑' n : ℕ, wt (n + (D + 1)) / (eps (n + (D + 1)) : ℝ)

/-- **Lemma 3.1, display (17), CITED, a named Prop**: for `1 ≤ i, j ≤ 3` and fixed `D ≥ 1`,
`(1/L^{i+j}) ∑_{h ≠ 0} r_{i,j}(h) ∑'_{d > D, d | h} 1/∏_{p | d}(p-2)
  ≤ ∑'_{d > D} 1/(ε(d)∏_{p | d}(p-2)) + O(log L / L)`. -/
def Display17 : Prop :=
  ∀ i j : Fin 3, ∀ D : ℕ, 1 ≤ D → ∃ C : ℝ, ∀ L : ℕ, 2 ≤ L →
    Lhs17 ((i : ℕ) + 1) ((j : ℕ) + 1) L D ≤ R0tail D + C * (Real.log L / L)

/-- The form of (17) used in the proof of (20): `lim_{D → ∞} limsup_{L → ∞}` of the left side is
`0`. -/
def Display17lim : Prop :=
  ∀ i j : Fin 3, ∀ η > 0, ∃ D : ℕ, ∀ᶠ L : ℕ in atTop, Lhs17 ((i : ℕ) + 1) ((j : ℕ) + 1) L D ≤ η

/-- **`Display17lim` from `Display17`, PROVED, CONDITIONAL ON `Display17`**: the tail of the
series tends to `0` and `log L / L → 0`. -/
theorem display17_lim (h17 : Display17) : Display17lim := by
  intro i j η hη
  have ht : Tendsto R0tail atTop (𝓝 0) := by
    have := tendsto_sum_nat_add (fun d : ℕ => wt d / (eps d : ℝ))
    exact this.comp (tendsto_add_atTop_nat 1)
  obtain ⟨D, hD⟩ := ((ht.eventually (gt_mem_nhds (half_pos hη))).and
    (eventually_ge_atTop 1)).exists
  obtain ⟨C, hC⟩ := h17 i j D hD.2
  refine ⟨D, ?_⟩
  have hlog : Tendsto (fun L : ℕ => C * (Real.log L / L)) atTop (𝓝 0) := by
    have := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
    simpa using this.const_mul C
  filter_upwards [hlog.eventually (gt_mem_nhds (half_pos hη)), eventually_ge_atTop 2] with L h1 h2
  have := hC L h2
  have := hD.1
  linarith

/-- `B_{ij} = C₀ ∑'_d P_d(i,j)/∏_{p | d}(p-2)`, the right side of (20). -/
noncomputable def Bdef (i j : Fin 3) : ℝ := C0 * ∑' d : ℕ, wt d * Pd d ((i : ℕ) + 1) ((j : ℕ) + 1)

lemma sum_cnt_le_T17 (I J L D : ℕ) (S : Finset ℕ) (hS : ∀ d ∈ S, D < d) :
    ∑ d ∈ S, wt d * cnt I J L d ≤ T17 I J L D := by
  unfold cnt T17
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_le_sum fun ν _ => ?_
  rw [Finset.sum_comm]
  refine sum_le_sum fun μ _ => ?_
  by_cases hs : sv ν = sv μ
  · simp [hs]
  simp only [if_neg hs, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have h0 : ((sv ν : ℤ) - sv μ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hs)
  refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => wt_nonneg d)
  simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd] at hd ⊢
  exact ⟨⟨hd.2, Int.natAbs_ne_zero.mpr h0⟩, hS d hd.1⟩

lemma split_div (I J L D : ℕ) (hL : 1 ≤ L) :
    SOff L I J / (2 * (L : ℝ) ^ (I + J)) =
      C0 * (∑ d ∈ range (D + 1), wt d * (cnt I J L d / (L : ℝ) ^ (I + J)) + Lhs17 I J L D) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hk : (L : ℝ) ^ (I + J) ≠ 0 := by positivity
  rw [soff_split I J L D, Lhs17]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp

/-- **The limit (20), PROVED, CONDITIONAL ON** the `N → ∞, D → ∞` form of display (17):
`(1/2L^{i+j}) ∑_{h ≠ 0} r_{i,j}(h)𝔖(h) → C₀ ∑'_d P_d(i,j)/∏_{p | d}(p-2)`. The convergence of the
series is part of the conclusion. -/
theorem display20_of (h17 : Display17lim) : Display20 Bdef := by
  intro i j
  have hk : (i : ℕ) + j + 2 = ((i : ℕ) + 1) + ((j : ℕ) + 1) := by omega
  simp only [hk]
  set I := (i : ℕ) + 1 with hI
  set J := (j : ℕ) + 1 with hJ
  set f : ℕ → ℝ := fun d => wt d * Pd d I J with hf
  have hf0 : ∀ d, 0 ≤ f d := fun d => mul_nonneg (wt_nonneg d) (Pd_nonneg d I J)
  have hterm : ∀ d, Tendsto (fun L : ℕ => wt d * (cnt I J L d / (L : ℝ) ^ (I + J))) atTop
      (𝓝 (f d)) := by
    intro d
    by_cases hd : Odd d
    · exact tendsto_const_nhds.mul (cnt_tendsto i j hd)
    · have : wt d = 0 := by simp [wt, hd]
      simp only [hf, this, zero_mul]
      exact tendsto_const_nhds
  have hfin : ∀ η D, (∀ᶠ L : ℕ in atTop, Lhs17 I J L D ≤ η) → ∀ S : Finset ℕ,
      (∀ d ∈ S, D < d) → ∑ d ∈ S, f d ≤ η := by
    intro η D hev S hS
    refine le_of_tendsto (tendsto_finset_sum S fun d _ => hterm d) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with L hL hL1
    refine le_trans ?_ hL
    have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have hpos : (0 : ℝ) < (L : ℝ) ^ (I + J) := by positivity
    rw [Lhs17, le_div_iff₀ hpos, Finset.sum_mul]
    calc ∑ d ∈ S, wt d * (cnt I J L d / (L : ℝ) ^ (I + J)) * (L : ℝ) ^ (I + J)
        = ∑ d ∈ S, wt d * cnt I J L d := by
          refine sum_congr rfl fun d _ => ?_
          field_simp
      _ ≤ T17 I J L D := sum_cnt_le_T17 I J L D S hS
  have hsum : Summable f := by
    obtain ⟨D1, hD1⟩ := h17 i j 1 one_pos
    refine summable_of_sum_range_le hf0 (c := ∑ d ∈ range (D1 + 1), f d + 1) fun n => ?_
    rw [← Finset.sum_filter_add_sum_filter_not (range n) (fun d => D1 < d)]
    have h1 := hfin 1 D1 hD1 ((range n).filter (fun d => D1 < d))
      (fun d hd => (Finset.mem_filter.mp hd).2)
    have h2 : ∑ d ∈ (range n).filter (fun d => ¬ D1 < d), f d ≤ ∑ d ∈ range (D1 + 1), f d :=
      sum_le_sum_of_subset_of_nonneg (fun d hd => by
        simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢; omega) (fun d _ _ => hf0 d)
    linarith
  have htail : ∀ η D, (∀ᶠ L : ℕ in atTop, Lhs17 I J L D ≤ η) → ∑' n, f (n + (D + 1)) ≤ η := by
    intro η D hev
    refine Real.tsum_le_of_sum_range_le (fun n => hf0 _) fun m => ?_
    have := hfin η D hev ((range m).map (addRightEmbedding (D + 1))) (fun d hd => by
      simp only [Finset.mem_map, Finset.mem_range, addRightEmbedding_apply] at hd
      obtain ⟨n, _, rfl⟩ := hd; omega)
    rwa [Finset.sum_map] at this
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hC0 := C0_nonneg
  set η := δ / (4 * (C0 + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨D, hD⟩ := h17 i j η hηpos
  have hfinlim : Tendsto (fun L : ℕ => ∑ d ∈ range (D + 1), wt d * (cnt I J L d / (L : ℝ) ^ (I + J)))
      atTop (𝓝 (∑ d ∈ range (D + 1), f d)) := tendsto_finset_sum _ fun d _ => hterm d
  have hnear := (Metric.tendsto_nhds.mp hfinlim) η hηpos
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.mp (hnear.and (hD.and (eventually_ge_atTop 1)))
  refine ⟨L0, fun L hL => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hL0 L hL
  rw [Real.dist_eq] at h1 ⊢
  rw [split_div I J L D h3]
  have hT := htail η D hD
  have hT0 : 0 ≤ ∑' n, f (n + (D + 1)) := tsum_nonneg fun n => hf0 _
  have hB : Bdef i j = C0 * (∑ d ∈ range (D + 1), f d + ∑' n, f (n + (D + 1))) := by
    rw [hsum.sum_add_tsum_nat_add]; rfl
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast h3
  have hL17 : 0 ≤ Lhs17 I J L D := div_nonneg (T17_nonneg _ _ _ _) (by positivity)
  rw [hB, ← mul_sub, abs_mul, abs_of_nonneg hC0]
  have h1' := abs_lt.mp h1
  have hbd : |∑ d ∈ range (D + 1), wt d * (cnt I J L d / (L : ℝ) ^ (I + J)) + Lhs17 I J L D -
      (∑ d ∈ range (D + 1), f d + ∑' n, f (n + (D + 1)))| ≤ 3 * η := by
    rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2]
  calc C0 * |∑ d ∈ range (D + 1), wt d * (cnt I J L d / (L : ℝ) ^ (I + J)) + Lhs17 I J L D -
      (∑ d ∈ range (D + 1), f d + ∑' n, f (n + (D + 1)))| ≤ C0 * (3 * η) :=
        mul_le_mul_of_nonneg_left hbd hC0
    _ < δ := by
        rw [hη]
        have : 0 < C0 + 1 := by linarith
        rw [show C0 * (3 * (δ / (4 * (C0 + 1)))) = δ * (3 * C0 / (4 * (C0 + 1))) by
          field_simp]
        have : 3 * C0 / (4 * (C0 + 1)) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        nlinarith

/-- **The limit (20) from the cited display (17), PROVED, CONDITIONAL ON `Display17`.** -/
theorem display20_of_17 (h17 : Display17) : Display20 Bdef := display20_of (display17_lim h17)

/-! ### The Section 6 conclusion -/

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON** the cited Lemma 4.1 `Lemma41 κ P ε` for every `ε > 0`,
display (18) `Lemma31_18`, display (17) `Display17`, Proposition 3.2 `Prop32 Bdef (A_* + T)`, the
cited (31) `Display31 6.7814`, `MinorSup1924 P`, the conditions (24) on `P` and the cited constants
of `k6_wired`. This is `U1458Lemma42.r6_lower6` with `Display20` discharged and `B = Bdef`. -/
theorem r6_lower7 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814)
    (h18 : Lemma31_18) (h17 : Display17)
    (h32 : Prop32 Bdef (fun i j => (LiLiu.Astar i j : ℝ) + T i j)) :
    ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      (∀ ε > 0, Lemma41 κ P ε) →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) :=
  r6_lower6 T Bdef hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 h18 (display20_of_17 h17) h32

/-! ### Vacuity -/

/-- `w(15) = 1/((3-2)(5-2)) = 1/3`, and `ε(15) = 4` since `2⁴ = 16 ≡ 1 mod 15`. -/
theorem wt_eps_instance : wt 15 = 1 / 3 ∧ eps 15 = 4 := by
  have hpf : (15 : ℕ).primeFactors = {3, 5} := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    decide
  refine ⟨?_, ?_⟩
  · have hsq : Squarefree (15 : ℕ) := by
      rw [show (15 : ℕ) = ∏ p ∈ ({3, 5} : Finset ℕ), p by decide]
      exact sq_prod (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    rw [wt, if_pos ⟨by decide, hsq⟩, hpf]
    norm_num
  · unfold eps
    rw [orderOf_eq_iff (by norm_num)]
    exact ⟨by decide, by decide⟩

end LeanLab.Linnik.U1464Display20
