module

public import LeanLab.LanguascoPintzZaccagnini2007.Lemma61

/-!
# P0045 Lemma 6.2, the arithmetic inputs

Lab proof, unit U-5606, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics.
Binary Goldbach is OPEN.

* `xi_odd`: for odd `d ≥ 1`, `1 ≤ ξ(d)` and `d ∣ 2^ξ(d) - 1`.
* `xi_dvd`: `d ∣ 2^μ - 1` forces `ξ(d) ∣ μ`.
* `xi_mono`: `d ∣ e`, `e` odd, gives `ξ(d) ≤ ξ(e)`.
* `log_lt_xi`: `log₂ r < ξ(r)`.
* `card_nu_le`: `#{ν ∈ [1, K] : 2^ν < m, e ∣ m - 2^ν} ≤ K/ξ(e) + 1` for odd `e`.
* `H n = ∏_{p ∣ n, p > 2} (1 + 1/(p - 2))` and `sing_le_two_H`: `𝔖(n) ≤ 2 H(n)` for `n ≥ 1`.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

lemma xi_odd {d : ℕ} (hd : Odd d) (hd0 : 0 < d) : 1 ≤ xi d ∧ d ∣ 2 ^ xi d - 1 := by
  have hcop : Nat.Coprime 2 d := Nat.coprime_two_left.2 hd
  have hmem : d.totient ∈ {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]} :=
    ⟨Nat.totient_pos.2 hd0, Nat.ModEq.pow_totient hcop⟩
  have hs := Nat.sInf_mem ⟨_, hmem⟩
  exact ⟨hs.1, (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 hs.2.symm⟩

lemma xi_le_of {d μ : ℕ} (hμ : 1 ≤ μ) (h : d ∣ 2 ^ μ - 1) : xi d ≤ μ := by
  refine Nat.sInf_le ⟨hμ, ?_⟩
  exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 h).symm

lemma xi_dvd {d μ : ℕ} (hd : Odd d) (hd0 : 0 < d) (h : d ∣ 2 ^ μ - 1) : xi d ∣ μ := by
  rcases Nat.eq_zero_or_pos μ with h0 | hμ
  · rw [h0]; exact dvd_zero _
  obtain ⟨h1, h2⟩ := xi_odd hd hd0
  have hg := Nat.dvd_gcd h2 h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have hg0 : 0 < Nat.gcd (xi d) μ := Nat.gcd_pos_of_pos_left _ h1
  have hle : xi d ≤ Nat.gcd (xi d) μ := xi_le_of hg0 hg
  have hge : Nat.gcd (xi d) μ ≤ xi d := Nat.le_of_dvd h1 (Nat.gcd_dvd_left _ _)
  have : Nat.gcd (xi d) μ = xi d := le_antisymm hge hle
  rw [← this]; exact Nat.gcd_dvd_right _ _

lemma xi_mono {d e : ℕ} (he : Odd e) (he0 : 0 < e) (hde : d ∣ e) : xi d ≤ xi e := by
  obtain ⟨h1, h2⟩ := xi_odd he he0
  exact xi_le_of h1 (hde.trans h2)

lemma log_lt_xi {r : ℕ} (hr : Odd r) (hr0 : 0 < r) : Nat.log 2 r < xi r := by
  obtain ⟨h1, h2⟩ := xi_odd hr hr0
  have hpos : 0 < 2 ^ xi r - 1 := by
    have : 2 ≤ 2 ^ xi r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ xi r := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hle : r ≤ 2 ^ xi r - 1 := Nat.le_of_dvd hpos h2
  exact Nat.log_lt_of_lt_pow hr0.ne' (by omega)

/-- Two admissible `ν` differ by a multiple of `ξ(e)`. -/
lemma xi_dvd_sub {e m a b : ℕ} (he : Odd e) (he0 : 0 < e) (hab : a ≤ b) (hb : 2 ^ b < m)
    (ha' : e ∣ m - 2 ^ a) (hb' : e ∣ m - 2 ^ b) : xi e ∣ b - a := by
  apply xi_dvd he he0
  have hpa : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
  have hdiff : e ∣ 2 ^ b - 2 ^ a := by
    have := Nat.dvd_sub ha' hb'
    have e1 : m - 2 ^ a - (m - 2 ^ b) = 2 ^ b - 2 ^ a := by omega
    rwa [e1] at this
  have hsplit : 2 ^ b - 2 ^ a = 2 ^ a * (2 ^ (b - a) - 1) := by
    have : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.mul_sub_one]
  rw [hsplit] at hdiff
  have hcop : Nat.Coprime e (2 ^ a) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 he)
  exact hcop.dvd_of_dvd_mul_left hdiff

/-- At most `K/ξ(e) + 1` exponents `ν ∈ [1, K]` with `2^ν < m` and `e ∣ m - 2^ν`. -/
theorem card_nu_le {e : ℕ} (he : Odd e) (he0 : 0 < e) (K m : ℕ) :
    #{ν ∈ Icc 1 K | 2 ^ ν < m ∧ e ∣ m - 2 ^ ν} ≤ K / xi e + 1 := by
  set V := (Icc 1 K).filter (fun ν => 2 ^ ν < m ∧ e ∣ m - 2 ^ ν) with hV
  rcases V.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  set ν₀ := V.min' h
  have hν₀ : ν₀ ∈ V := V.min'_mem h
  have hξ := (xi_odd he he0).1
  refine le_trans (card_le_card_of_injOn (fun ν => (ν - ν₀) / xi e) (t := range (K / xi e + 1))
    (fun ν hν => ?_) (fun a ha b hb hab => ?_)) (by simp)
  · rw [mem_coe, mem_filter, mem_Icc] at hν
    rw [mem_coe, mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  · have ha0 : ν₀ ≤ a := V.min'_le a ha
    have hb0 : ν₀ ≤ b := V.min'_le b hb
    rw [mem_coe, mem_filter] at ha hb
    rw [mem_filter] at hν₀
    have hda := xi_dvd_sub he he0 ha0 ha.2.1 hν₀.2.2 ha.2.2
    have hdb := xi_dvd_sub he he0 hb0 hb.2.1 hν₀.2.2 hb.2.2
    simp only at hab
    have e1 := Nat.div_mul_cancel hda
    have e2 := Nat.div_mul_cancel hdb
    have : a - ν₀ = b - ν₀ := by rw [← e1, ← e2, hab]
    omega

/-- `H(n) = ∏_{p ∣ n, p > 2} (1 + 1/(p - 2))`. -/
def H (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))

lemma one_le_H (n : ℕ) : 1 ≤ H n := by
  unfold H
  calc (1 : ℝ) = ∏ _p ∈ n.primeFactors.filter (fun p => 2 < p), (1 : ℝ) := by simp
    _ ≤ _ := by
      refine prod_le_prod₀ (fun _ _ => zero_le_one) fun p hp => ?_
      have : 2 < p := (mem_filter.1 hp).2
      have : (3 : ℝ) ≤ p := by exact_mod_cast this
      have : 0 < (p : ℝ) - 2 := by linarith
      have : 0 ≤ 1 / ((p : ℝ) - 2) := by positivity
      linarith

/-- The factor of `𝔖` at `p`. -/
def singF (n : ℕ) (p : {p : ℕ // p.Prime}) : ℝ :=
  if p.1 ∣ n then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

/-- `G''(q) = 2` at `q = 2`, `1 + 1/(q - 2)` otherwise. -/
def G2 (q : ℕ) : ℝ := if q = 2 then 2 else 1 + 1 / ((q : ℝ) - 2)

lemma one_le_G2 {q : ℕ} (hq : 2 ≤ q) : 1 ≤ G2 q := by
  unfold G2
  split_ifs with h
  · norm_num
  · have : (3 : ℝ) ≤ q := by exact_mod_cast (by omega : 3 ≤ q)
    have : 0 < (q : ℝ) - 2 := by linarith
    have : 0 ≤ 1 / ((q : ℝ) - 2) := by positivity
    linarith

/-- Every finite partial product of `𝔖(n)` is at most `2 H(n)`, `n ≥ 1`. -/
lemma partial_le_two_H {n : ℕ} (hn : n ≠ 0) (S : Finset {p : ℕ // p.Prime}) :
    ∏ p ∈ S, singF n p ≤ 2 * H n := by
  set G' : ℕ → ℝ := fun q => if q ∣ n then G2 q else 1 with hG'
  have hG'1 : ∀ q, 2 ≤ q → 1 ≤ G' q := by
    intro q hq; simp only [hG']; split_ifs
    · exact one_le_G2 hq
    · exact le_rfl
  have hF0 : ∀ p : {p : ℕ // p.Prime}, 0 ≤ singF n p := by
    intro p
    have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
    unfold singF
    split_ifs
    · exact div_nonneg (by linarith) (by linarith)
    · have : 1 ≤ ((p.1 : ℝ) - 1) ^ 2 := by nlinarith
      have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
  have hFG : ∀ p : {p : ℕ // p.Prime}, singF n p ≤ G' p.1 := by
    intro p
    have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
    simp only [hG']
    unfold singF G2
    split_ifs with h1 h3
    · rw [h3]; norm_num
    · have h3' : (3 : ℝ) ≤ p.1 := by
        have := p.2.two_le
        exact_mod_cast (by omega : 3 ≤ p.1)
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 < (p.1 : ℝ) - 2 := by linarith
      have e : (1 + 1 / ((p.1 : ℝ) - 2)) * ((p.1 : ℝ) - 1) =
          (p.1 - 1) + (p.1 - 1) / (p.1 - 2) := by ring
      rw [e]
      have : 1 ≤ ((p.1 : ℝ) - 1) / ((p.1 : ℝ) - 2) := by rw [le_div_iff₀ h0]; linarith
      linarith
    · have : 0 ≤ 1 / ((p.1 : ℝ) - 1) ^ 2 := by positivity
      linarith
  set S' := S.map (Function.Embedding.subtype _) with hS'
  have hS'p : ∀ q ∈ S', q.Prime := by
    intro q hq
    rw [hS', Finset.mem_map] at hq
    obtain ⟨p, _, rfl⟩ := hq
    exact p.2
  have hpf2 : ∀ q ∈ n.primeFactors, 2 ≤ q := fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le
  calc ∏ p ∈ S, singF n p ≤ ∏ p ∈ S, G' p.1 := prod_le_prod₀ (fun p _ => hF0 p) fun p _ => hFG p
    _ = ∏ q ∈ S', G' q := by rw [hS', prod_map]; rfl
    _ ≤ ∏ q ∈ S' ∪ n.primeFactors, G' q := by
        refine prod_le_prod_of_subset_of_one_le₀ subset_union_left
          (fun q hq => le_trans zero_le_one (hG'1 q (hS'p q hq).two_le)) fun q hq _ => ?_
        rcases mem_union.1 hq with h | h
        · exact hG'1 q (hS'p q h).two_le
        · exact hG'1 q (hpf2 q h)
    _ = ∏ q ∈ n.primeFactors, G' q := by
        symm
        refine prod_subset subset_union_right fun q hq hnot => ?_
        simp only [hG']
        rw [if_neg]
        intro hd
        rcases mem_union.1 hq with h | h
        · exact hnot (Nat.mem_primeFactors.2 ⟨hS'p q h, hd, hn⟩)
        · exact hnot h
    _ = ∏ q ∈ n.primeFactors, G2 q := by
        refine prod_congr rfl fun q hq => ?_
        simp only [hG']
        rw [if_pos (Nat.dvd_of_mem_primeFactors hq)]
    _ = (∏ q ∈ n.primeFactors with 2 < q, G2 q) * ∏ q ∈ n.primeFactors with ¬ 2 < q, G2 q :=
        (prod_filter_mul_prod_filter_not _ _ _).symm
    _ ≤ H n * 2 := by
        have hH : ∏ q ∈ n.primeFactors with 2 < q, G2 q = H n := by
          unfold H
          refine prod_congr rfl fun q hq => ?_
          unfold G2
          rw [if_neg (by have := (mem_filter.1 hq).2; omega)]
        rw [hH]
        refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (one_le_H n))
        calc ∏ q ∈ n.primeFactors with ¬ 2 < q, G2 q ≤ ∏ q ∈ ({2} : Finset ℕ), G2 q := by
              refine prod_le_prod_of_subset_of_one_le₀ (fun q hq => ?_)
                (fun q hq => le_trans zero_le_one (one_le_G2 (hpf2 q (mem_filter.1 hq).1)))
                fun q hq _ => by rw [mem_singleton] at hq; rw [hq]; exact one_le_G2 le_rfl
              rw [mem_filter] at hq
              have := hpf2 q hq.1
              rw [mem_singleton]; omega
          _ = 2 := by simp [G2]
    _ = 2 * H n := by ring

/-- `𝔖(n) ≤ 2 H(n)` for `n ≥ 1`. -/
theorem sing_le_two_H {n : ℕ} (hn : n ≠ 0) : Sing n ≤ 2 * H n := by
  have hS : Sing n = ∏' p, singF n p := rfl
  rw [hS]
  by_cases hm : Multipliable (singF n)
  · exact le_of_tendsto hm.hasProd (Eventually.of_forall fun S => partial_le_two_H hn S)
  · rw [tprod_eq_one_of_not_multipliable hm]
    have := one_le_H n
    linarith

end

end LeanLab.LPZ2007
