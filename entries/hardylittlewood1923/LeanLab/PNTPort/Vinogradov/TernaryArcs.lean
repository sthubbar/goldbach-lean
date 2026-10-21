module

public import LeanLab.PNTPort.Vinogradov.TernaryMajor

/-!
# The major arcs on `ZMod M` as a disjoint union

Lab proof, unit U-5254. AI wrote this file. Known mathematics, no cited input.

* `arcSet M Q q a`: the `k` with `‖k/M - a/q‖ ≤ 1/(q(Q + 1))`.
* `majIdx P`: the reduced `a/q`, `1 ≤ q ≤ P`, `0 ≤ a < q`, `(a, q) = 1`.
* `nonminor_eq`: the frequencies outside `minorSet P Q M` are exactly the union of the arcs;
  `arcs_disjoint`: the arcs are pairwise disjoint when `2/(Q + 1) < 1/P²`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ZMod
open LeanLab.PNTPort.LargeSieve

noncomputable def arcSet (M Q q a : ℕ) [NeZero M] : Finset (ZMod M) :=
  univ.filter (fun k => dist0 ((k.val : ℝ) / M - (a : ℝ) / q) ≤ 1 / ((q : ℝ) * (Q + 1)))

def majIdx (P : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 P ×ˢ range P).filter (fun p => p.2 < p.1 ∧ Nat.Coprime p.2 p.1)

lemma dist0_add_le (u v : ℝ) : dist0 (u + v) ≤ dist0 u + dist0 v := by
  have h := dist0_le_abs_sub_int (u + v) (round u + round v)
  unfold dist0 at *
  push_cast at h
  calc |u + v - round (u + v)| ≤ |u + v - (round u + round v)| := h
    _ = |(u - round u) + (v - round v)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

lemma frac_sep {P q a q' a' : ℕ} (h : (q, a) ∈ majIdx P) (h' : (q', a') ∈ majIdx P)
    (hne : (q, a) ≠ (q', a')) : 1 / ((q : ℝ) * q') ≤ dist0 ((a : ℝ) / q - (a' : ℝ) / q') := by
  simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range] at h h'
  obtain ⟨⟨⟨hq1, _⟩, _⟩, haq, hcop⟩ := h
  obtain ⟨⟨⟨hq1', _⟩, _⟩, haq', hcop'⟩ := h'
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  set r := round ((a : ℝ) / q - (a' : ℝ) / q')
  set m : ℤ := (a : ℤ) * q' - (a' : ℤ) * q - r * q * q' with hm
  have hx : (a : ℝ) / q - (a' : ℝ) / q' - r = (m : ℝ) / (q * q') := by
    rw [hm]; push_cast; field_simp
  have hm0 : m ≠ 0 := by
    intro h0
    apply hne
    have e1 : (a : ℤ) * q' = q * ((a' : ℤ) + r * q') := by rw [hm] at h0; linarith
    have e2 : (a' : ℤ) * q = q' * ((a : ℤ) - r * q) := by rw [hm] at h0; linarith
    have d1 : (q : ℤ) ∣ (q' : ℤ) * a := ⟨_, by rw [mul_comm]; exact e1⟩
    have d2 : (q' : ℤ) ∣ (q : ℤ) * a' := ⟨_, by rw [mul_comm]; exact e2⟩
    have c1 : IsCoprime (q : ℤ) (a : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast (Nat.Coprime.symm hcop)
    have c2 : IsCoprime (q' : ℤ) (a' : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast (Nat.Coprime.symm hcop')
    have f1 : (q : ℤ) ∣ q' := c1.dvd_of_dvd_mul_right d1
    have f2 : (q' : ℤ) ∣ q := c2.dvd_of_dvd_mul_right d2
    have hqq : q = q' := by
      have := Int.dvd_antisymm (by positivity) (by positivity) f1 f2
      exact_mod_cast this
    subst hqq
    have e3 : (a : ℤ) - a' = r * q := by
      have : (q : ℤ) * ((a : ℤ) - a' - r * q) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · omega
      · linarith
    have hq0 : (1 : ℤ) ≤ q := by exact_mod_cast hq1
    have ha1 : (a : ℤ) < q := by exact_mod_cast haq
    have ha2 : (a' : ℤ) < q := by exact_mod_cast haq'
    have ha3 : (0 : ℤ) ≤ a := by positivity
    have ha4 : (0 : ℤ) ≤ a' := by positivity
    have : r = 0 := by
      rcases lt_trichotomy r 0 with h | h | h
      · exfalso; have : r ≤ -1 := by omega
        nlinarith
      · exact h
      · exfalso; have : 1 ≤ r := by omega
        nlinarith
    rw [this] at e3
    have : a = a' := by omega
    rw [this]
  unfold dist0
  rw [hx, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
  exact_mod_cast this

theorem arcs_disjoint {M P Q : ℕ} [NeZero M] (hPQ : 2 / ((Q : ℝ) + 1) < 1 / (P : ℝ) ^ 2) :
    Set.PairwiseDisjoint (majIdx P : Set (ℕ × ℕ)) (fun p => arcSet M Q p.1 p.2) := by
  rintro ⟨q, a⟩ hp ⟨q', a'⟩ hp' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro k hk hk'
  simp only [arcSet, mem_filter, mem_univ, true_and] at hk hk'
  have hsep := frac_sep hp hp' hne
  simp only [majIdx, mem_coe, mem_filter, mem_product, mem_Icc, mem_range] at hp hp'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hp.1.1.1
  have hq1' : (1 : ℝ) ≤ q' := by exact_mod_cast hp'.1.1.1
  have hqP : (q : ℝ) ≤ P := by exact_mod_cast hp.1.1.2
  have hqP' : (q' : ℝ) ≤ P := by exact_mod_cast hp'.1.1.2
  have hQ : (0 : ℝ) < Q + 1 := by positivity
  have htri := dist0_add_le ((k.val : ℝ) / M - (a' : ℝ) / q') (-((k.val : ℝ) / M - (a : ℝ) / q))
  rw [dist0_neg] at htri
  have e1 : (k.val : ℝ) / M - (a' : ℝ) / q' + -((k.val : ℝ) / M - (a : ℝ) / q) =
      (a : ℝ) / q - (a' : ℝ) / q' := by ring
  rw [e1] at htri
  have b1 : 1 / ((q : ℝ) * (Q + 1)) ≤ 1 / (Q + 1) :=
    one_div_le_one_div_of_le hQ (by nlinarith)
  have b2 : 1 / ((q' : ℝ) * (Q + 1)) ≤ 1 / (Q + 1) :=
    one_div_le_one_div_of_le hQ (by nlinarith)
  have b3 : 1 / (P : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') :=
    one_div_le_one_div_of_le (by positivity) (by rw [sq]; exact mul_le_mul hqP hqP' (by linarith) (by linarith))
  have : 2 / ((Q : ℝ) + 1) = 1 / (Q + 1) + 1 / (Q + 1) := by ring
  linarith

/-- A non-minor `α` lies on a reduced arc. -/
lemma reduce_arc {P Q : ℕ} {α : ℝ} (h : ¬ MinorAt P Q α) :
    ∃ p ∈ majIdx P, dist0 (α - (p.2 : ℝ) / p.1) ≤ 1 / ((p.1 : ℝ) * (Q + 1)) := by
  unfold MinorAt at h
  push_neg at h
  obtain ⟨a, q, hq1, hqP, hle⟩ := h
  set g : ℕ := Int.gcd a q with hg
  have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_right a (by exact_mod_cast (show q ≠ 0 by omega))
  obtain ⟨a1, ha1⟩ := Int.gcd_dvd_left a (q : ℤ)
  obtain ⟨q1z, hq1z⟩ := Int.gcd_dvd_right a (q : ℤ)
  rw [← hg] at ha1 hq1z
  have hq1pos : 0 < q1z := by
    rcases lt_or_ge 0 q1z with h | h
    · exact h
    · exfalso
      have : (g : ℤ) * q1z ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      omega
  set q1 : ℕ := q1z.toNat with hq1def
  have hq1c : (q1 : ℤ) = q1z := Int.toNat_of_nonneg hq1pos.le
  have hcop1 : Int.gcd a1 q1z = 1 := by
    have := Int.gcd_div_gcd_div_gcd (i := a) (j := (q : ℤ)) (by omega)
    rw [← hg] at this
    have e1 : a / (g : ℤ) = a1 := by rw [ha1]; exact Int.mul_ediv_cancel_left _ (by omega)
    have e2 : (q : ℤ) / (g : ℤ) = q1z := by rw [hq1z]; exact Int.mul_ediv_cancel_left _ (by omega)
    rwa [e1, e2] at this
  have hq1q : q1 ≤ q := by
    have : (g : ℤ) * q1z = q := hq1z.symm
    have h1 : (1 : ℤ) ≤ g := by exact_mod_cast hg0
    have : q1z ≤ q := by nlinarith
    omega
  have hq1one : 1 ≤ q1 := by omega
  set r : ℕ := (a1 % q1z).toNat with hrdef
  have hr0 : 0 ≤ a1 % q1z := Int.emod_nonneg _ hq1pos.ne'
  have hrc : (r : ℤ) = a1 % q1z := Int.toNat_of_nonneg hr0
  have hrlt : r < q1 := by
    have := Int.emod_lt_of_pos a1 hq1pos; omega
  refine ⟨(q1, r), ?_, ?_⟩
  · simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range]
    refine ⟨⟨⟨hq1one, by omega⟩, by omega⟩, hrlt, ?_⟩
    have : Int.gcd (r : ℤ) (q1 : ℤ) = 1 := by
      rw [hrc, hq1c, Int.gcd_emod]; exact hcop1
    exact_mod_cast this
  · simp only
    have hqr1 : (0 : ℝ) < q1 := by exact_mod_cast hq1one
    have hdiv := Int.mul_ediv_add_emod a1 q1z
    have hfrac : (a : ℝ) / q = (a1 : ℝ) / q1 := by
      have hq' : (q : ℝ) = (g : ℝ) * q1 := by
        have : (q : ℤ) = g * q1 := by rw [hq1c]; exact hq1z
        exact_mod_cast this
      have ha' : (a : ℝ) = (g : ℝ) * a1 := by exact_mod_cast ha1
      have hg0r : (0 : ℝ) < g := by exact_mod_cast hg0
      rw [hq', ha']; field_simp
    have h1 : α - (r : ℝ) / q1 - ((a1 / q1z : ℤ) : ℝ) = α - (a : ℝ) / q := by
      rw [hfrac]
      have : (a1 : ℝ) = (r : ℝ) + (q1 : ℝ) * ((a1 / q1z : ℤ) : ℝ) := by
        have : (a1 : ℤ) = (r : ℤ) + q1 * (a1 / q1z) := by rw [hrc, hq1c]; linarith
        exact_mod_cast this
      rw [this]; field_simp; ring
    have h2 := dist0_le_abs_sub_int (α - (r : ℝ) / q1) (a1 / q1z)
    rw [h1] at h2
    refine h2.trans (hle.trans ?_)
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hq1q) (by positivity)

/-- The non-minor frequencies are the union of the arcs. -/
theorem nonminor_eq {M P Q : ℕ} [NeZero M] :
    univ.filter (fun k : ZMod M => k ∉ minorSet P Q M) =
      (majIdx P).biUnion (fun p => arcSet M Q p.1 p.2) := by
  ext k
  have hmk : k ∈ minorSet P Q M ↔ MinorAt P Q ((k.val : ℝ) / M) := by
    constructor
    · intro h; simp only [minorSet, Finset.mem_filter] at h; exact h.2
    · intro h; simp only [minorSet, Finset.mem_filter]; exact ⟨mem_univ _, h⟩
  have hak : ∀ q a : ℕ, k ∈ arcSet M Q q a ↔
      dist0 ((k.val : ℝ) / M - (a : ℝ) / q) ≤ 1 / ((q : ℝ) * (Q + 1)) := by
    intro q a
    constructor
    · intro h; simp only [arcSet, Finset.mem_filter] at h; exact h.2
    · intro h; simp only [arcSet, Finset.mem_filter]; exact ⟨mem_univ _, h⟩
  rw [mem_filter, mem_biUnion]
  constructor
  · rintro ⟨_, h⟩
    obtain ⟨p, hp, hd⟩ := reduce_arc (fun hm => h (hmk.2 hm))
    exact ⟨p, hp, (hak p.1 p.2).2 hd⟩
  · rintro ⟨⟨q, a⟩, hp, hk⟩
    refine ⟨mem_univ _, fun hm => ?_⟩
    have hmin := hmk.1 hm
    have hk' := (hak q a).1 hk
    simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range] at hp
    apply absurd (hmin (a + q * round ((k.val : ℝ) / M - (a : ℝ) / q)) q hp.1.1.1 hp.1.1.2)
    rw [not_lt]
    have hq : (0 : ℝ) < q := by exact_mod_cast hp.1.1.1
    have : (k.val : ℝ) / M - (((a + q * round ((k.val : ℝ) / M - (a : ℝ) / q) : ℤ) : ℝ)) / q =
        (k.val : ℝ) / M - (a : ℝ) / q - round ((k.val : ℝ) / M - (a : ℝ) / q) := by
      push_cast; field_simp; ring
    rw [this]; exact hk'

end LeanLab.PNTPort.Vinogradov

