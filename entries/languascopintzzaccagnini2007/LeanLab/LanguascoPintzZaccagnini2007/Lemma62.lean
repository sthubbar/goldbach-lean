module

public import LeanLab.LanguascoPintzZaccagnini2007.Lemma62Aux

/-!
# P0045 Lemma 6.2, in the lab's repaired form with `r ≥ r₀`

Lab proof, unit U-5606, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics;
the argument of the paper, page 9 displays (27) to (30). Binary Goldbach is OPEN.

For `ν` in the admissible set `V` write `n_ν = m - 2^ν`. With `𝔖(n) ≤ 2H(n)`,
`H(n) = Σ_{s ⊆ odd prime factors of n} W(s)`, `W(s) = ∏_{p ∈ s} 1/(p - 2)`; swapping the sums, the set
`s`, with `d = ∏ s`, is counted at most `L/ξ([d, r]) + 1` times. Then
* `d ≤ D`: `ξ([d, r]) ≥ ξ(r) > log₂ r`, and `Σ_{d ≤ D} W ≤ e^27 log D`;
* `d > D`: `ξ([d, r]) ≥ ξ(d)`, the tail of the series (26) of Lemma 6.1;
* the `+1` terms: at most `H` of `P = ∏ n_ν`, which has at most `L²` prime factors, so `≪ log L`.

* `sum_H_le`: the three-part bound.
* `lemma62_proved : Lemma62`, the cited `lpz_lemma62` with no cited input, PROVED.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The odd prime factors. -/
def opf (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => 2 < p)

/-- `W(s) = ∏_{p ∈ s} 1/(p - 2)`. -/
def W (s : Finset ℕ) : ℝ := ∏ p ∈ s, 1 / ((p : ℝ) - 2)

lemma H_eq_sum (n : ℕ) : H n = ∑ s ∈ (opf n).powerset, W s := by
  unfold H W opf; exact prod_one_add _

lemma W_nonneg {s : Finset ℕ} (hs : ∀ p ∈ s, 2 < p) : 0 ≤ W s := by
  unfold W
  refine prod_nonneg fun p hp => ?_
  have : (3 : ℝ) ≤ p := by exact_mod_cast (hs p hp)
  have : 0 < (p : ℝ) - 2 := by linarith
  positivity

lemma opf_spec {n p : ℕ} (h : p ∈ opf n) : p.Prime ∧ 2 < p ∧ p ∣ n := by
  unfold opf at h
  rw [mem_filter, Nat.mem_primeFactors] at h
  exact ⟨h.1.1, h.2, h.1.2.1⟩

/-- The facts about `d = ∏ s` for a set `s` of odd primes. -/
lemma set_facts {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    OddSqf (∏ p ∈ s, p) ∧ (∏ p ∈ s, p).primeFactors = s ∧ fd (∏ p ∈ s, p) = W s := by
  have hpr : ∀ p ∈ s, p.Prime := fun p hp => (hs p hp).1
  have hpos : 0 < ∏ p ∈ s, p := prod_pos fun p hp => (hpr p hp).pos
  have hodd : Odd (∏ p ∈ s, p) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨p, hp, hdvd⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).1 h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hpr p hp)).1 hdvd
    have := (hs p hp).2
    omega
  have hsq : Squarefree (∏ p ∈ s, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hne => ?_)
      fun p hp => (hpr p hp).prime.irreducible.squarefree
    exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hpr p hp) (hpr q hq)).2 hne)
  have hpf : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod hpr
  have hos : OddSqf (∏ p ∈ s, p) := ⟨hpos, hodd, hsq⟩
  refine ⟨hos, hpf, ?_⟩
  rw [fd_eq hos, hpf]; rfl

lemma prod_dvd_of_subset {s : Finset ℕ} {n : ℕ} (hn : n ≠ 0) (h : s ⊆ opf n) :
    ∏ p ∈ s, p ∣ n :=
  prod_primes_dvd n (fun p hp => (opf_spec (h hp)).1.prime) fun p hp => (opf_spec (h hp)).2.2

lemma opf_mono {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) : opf a ⊆ opf b := by
  unfold opf
  exact filter_subset_filter _ (Nat.primeFactors_mono hab hb)

/-- The odd primes up to `D` carry `Σ W ≤ e^27 log D`. -/
lemma sum_W_small (D : ℕ) (hD : 4 ≤ D) :
    ∑ s ∈ ((Icc 3 D).filter Nat.Prime).powerset, W s ≤ exp 27 * log D := by
  set Q := (Icc 3 D).filter Nat.Prime with hQ
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (mem_filter.1 hp).2
  have hpf : (∏ p ∈ Q, p).primeFactors = Q := Nat.primeFactors_prod hQp
  have h := prodH_le (∏ p ∈ Q, p) D hD (fun p hp => by
      rw [hpf] at hp; exact (mem_Icc.1 (mem_filter.1 hp).1).1)
    (by rw [hpf]; refine le_trans (card_filter_le _ _) ?_; simp)
  rw [hpf] at h
  unfold W
  rw [← prod_one_add]
  exact h

/-- A finite set of `d > D` carries at most the tail of (26). -/
lemma tail_le (D : ℕ) (T : Finset ℕ) (hT : ∀ d ∈ T, D < d) :
    ∑ d ∈ T, seriesTerm d ≤ ∑' k, seriesTerm (k + (D + 1)) := by
  have hsum : Summable (fun k => seriesTerm (k + (D + 1))) :=
    (summable_nat_add_iff (D + 1)).2 lemma61_proved
  have e : ∑ d ∈ T, seriesTerm d = ∑ k ∈ T.image (fun d => d - (D + 1)), seriesTerm (k + (D + 1)) := by
    rw [sum_image]
    · refine sum_congr rfl fun d hd => ?_
      have := hT d hd
      congr 1; omega
    · intro a ha b hb hab
      have := hT a ha; have := hT b hb
      simp only at hab; omega
  rw [e]
  exact hsum.sum_le_tsum _ fun k _ => seriesTerm_nonneg _

/-- **The three-part bound** for `Σ_{ν ∈ V} H(m - 2^ν)`. -/
theorem sum_H_le (V : Finset ℕ) (K' m r D : ℕ) (L : ℝ)
    (hV : ∀ ν ∈ V, ν ∈ Icc 1 K' ∧ 2 ^ ν < m ∧ r ∣ m - 2 ^ ν) (hr : Odd r) (hr0 : 0 < r)
    (hK : (K' : ℝ) ≤ L) (hD : 4 ≤ D) :
    ∑ ν ∈ V, H (m - 2 ^ ν) ≤ L * (exp 27 * log D) / xi r +
      L * ∑' k, seriesTerm (k + (D + 1)) +
      ∑ s ∈ (opf (∏ ν ∈ V, (m - 2 ^ ν))).powerset, W s := by
  have hn0 : ∀ ν ∈ V, m - 2 ^ ν ≠ 0 := fun ν hν => by have := (hV ν hν).2.1; omega
  set P := ∏ ν ∈ V, (m - 2 ^ ν) with hP
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn0
  set Pν : ℕ → Finset (Finset ℕ) := fun ν => (opf (m - 2 ^ ν)).powerset with hPν
  set U := V.biUnion Pν with hU
  have hPU : ∀ ν ∈ V, Pν ν ⊆ U := fun ν hν => subset_biUnion_of_mem Pν hν
  have hUs : ∀ s ∈ U, ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro s hs p hp
    rw [hU, mem_biUnion] at hs
    obtain ⟨ν, _, hsν⟩ := hs
    have := opf_spec (mem_powerset.1 hsν hp)
    exact ⟨this.1, this.2.1⟩
  have hL0 : 0 ≤ L := le_trans (Nat.cast_nonneg _) hK
  -- step 1: expand and swap
  have step1 : ∑ ν ∈ V, H (m - 2 ^ ν) = ∑ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) * W s := by
    calc ∑ ν ∈ V, H (m - 2 ^ ν) = ∑ ν ∈ V, ∑ s ∈ U, if s ∈ Pν ν then W s else 0 := by
          refine sum_congr rfl fun ν hν => ?_
          rw [H_eq_sum, sum_ite_mem, inter_eq_right.2 (hPU ν hν)]
      _ = ∑ s ∈ U, ∑ ν ∈ V, if s ∈ Pν ν then W s else 0 := sum_comm
      _ = _ := by
          refine sum_congr rfl fun s _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
  -- step 2: the count
  have hcount : ∀ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) ≤
      L / xi (Nat.lcm (∏ p ∈ s, p) r) + 1 := by
    intro s hs
    obtain ⟨hos, -, -⟩ := set_facts (hUs s hs)
    set d := ∏ p ∈ s, p
    have hlodd : Odd (Nat.lcm d r) := (hos.2.1.mul hr).of_dvd_nat (Nat.lcm_dvd_mul d r)
    have hlpos : 0 < Nat.lcm d r := Nat.lcm_pos hos.1 hr0
    have hsub : V.filter (fun ν => s ∈ Pν ν) ⊆
        (Icc 1 K').filter (fun ν => 2 ^ ν < m ∧ Nat.lcm d r ∣ m - 2 ^ ν) := by
      intro ν hν
      rw [mem_filter] at hν
      obtain ⟨h1, h2, h3⟩ := hV ν hν.1
      rw [mem_filter]
      refine ⟨h1, h2, Nat.lcm_dvd ?_ h3⟩
      exact prod_dvd_of_subset (hn0 ν hν.1) (mem_powerset.1 hν.2)
    have h1 := le_trans (card_le_card hsub) (card_nu_le hlodd hlpos K' m)
    have hxi : (0 : ℝ) < xi (Nat.lcm d r) := by exact_mod_cast (xi_odd hlodd hlpos).1
    calc (#{ν ∈ V | s ∈ Pν ν} : ℝ) ≤ ((K' / xi (Nat.lcm d r) + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ (K' : ℝ) / xi (Nat.lcm d r) + 1 := by push_cast; linarith [Nat.cast_div_le (m := K') (n := xi (Nat.lcm d r)) (α := ℝ)]
      _ ≤ L / xi (Nat.lcm d r) + 1 := by gcongr
  have hW0 : ∀ s ∈ U, 0 ≤ W s := fun s hs => W_nonneg fun p hp => (hUs s hs p hp).2
  have step2 : ∑ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) * W s ≤
      ∑ s ∈ U, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s + ∑ s ∈ U, W s := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun s hs => ?_
    have := mul_le_mul_of_nonneg_right (hcount s hs) (hW0 s hs)
    linarith
  -- the `+1` part
  have part3 : ∑ s ∈ U, W s ≤ ∑ s ∈ (opf P).powerset, W s := by
    refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s hs _ => ?_
    · rw [hU, mem_biUnion] at hs
      obtain ⟨ν, hν, hsν⟩ := hs
      rw [mem_powerset]
      exact (mem_powerset.1 hsν).trans (opf_mono (dvd_prod_of_mem _ hν) hP0)
    · exact W_nonneg fun p hp => (opf_spec (mem_powerset.1 hs hp)).2.1
  -- the main part, split at `D`
  have hsplit := sum_filter_add_sum_filter_not U (fun s => ∏ p ∈ s, p ≤ D)
    (fun s => L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s)
  have hxr : (0 : ℝ) < xi r := by exact_mod_cast (xi_odd hr hr0).1
  have part1 : ∑ s ∈ U with ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s ≤
      L * (exp 27 * log D) / xi r := by
    calc ∑ s ∈ U with ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s
        ≤ ∑ s ∈ U with ∏ p ∈ s, p ≤ D, L / xi r * W s := by
          refine sum_le_sum fun s hs => ?_
          rw [mem_filter] at hs
          refine mul_le_mul_of_nonneg_right ?_ (hW0 s hs.1)
          obtain ⟨hos, -, -⟩ := set_facts (hUs s hs.1)
          have hlodd : Odd (Nat.lcm (∏ p ∈ s, p) r) :=
            (hos.2.1.mul hr).of_dvd_nat (Nat.lcm_dvd_mul _ r)
          have hlpos : 0 < Nat.lcm (∏ p ∈ s, p) r := Nat.lcm_pos hos.1 hr0
          have hm : xi r ≤ xi (Nat.lcm (∏ p ∈ s, p) r) :=
            xi_mono hlodd hlpos (Nat.dvd_lcm_right _ r)
          have hm' : (xi r : ℝ) ≤ xi (Nat.lcm (∏ p ∈ s, p) r) := by exact_mod_cast hm
          exact div_le_div_of_nonneg_left hL0 hxr hm'
      _ = L / xi r * ∑ s ∈ U with ∏ p ∈ s, p ≤ D, W s := by rw [mul_sum]
      _ ≤ L / xi r * ∑ s ∈ ((Icc 3 D).filter Nat.Prime).powerset, W s := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hL0 hxr.le)
          refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s hs _ => ?_
          · rw [mem_filter] at hs
            rw [mem_powerset]
            intro p hp
            have hps := hUs s hs.1 p hp
            have hle : p ≤ ∏ q ∈ s, q :=
              Nat.le_of_dvd (prod_pos fun q hq => (hUs s hs.1 q hq).1.pos) (dvd_prod_of_mem _ hp)
            rw [mem_filter, mem_Icc]
            exact ⟨⟨by omega, le_trans hle hs.2⟩, hps.1⟩
          · exact W_nonneg fun p hp => by
              have := (mem_Icc.1 (mem_filter.1 (mem_powerset.1 hs hp)).1).1; omega
      _ ≤ L / xi r * (exp 27 * log D) :=
          mul_le_mul_of_nonneg_left (sum_W_small D hD) (div_nonneg hL0 hxr.le)
      _ = L * (exp 27 * log D) / xi r := by ring
  have part2 : ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s ≤
      L * ∑' k, seriesTerm (k + (D + 1)) := by
    calc ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s
        ≤ ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, L * seriesTerm (∏ p ∈ s, p) := by
          refine sum_le_sum fun s hs => ?_
          rw [mem_filter] at hs
          obtain ⟨hos, -, hfd⟩ := set_facts (hUs s hs.1)
          have hlodd : Odd (Nat.lcm (∏ p ∈ s, p) r) :=
            (hos.2.1.mul hr).of_dvd_nat (Nat.lcm_dvd_mul _ r)
          have hlpos : 0 < Nat.lcm (∏ p ∈ s, p) r := Nat.lcm_pos hos.1 hr0
          have hm : xi (∏ p ∈ s, p) ≤ xi (Nat.lcm (∏ p ∈ s, p) r) :=
            xi_mono hlodd hlpos (Nat.dvd_lcm_left _ r)
          have hxd : (0 : ℝ) < xi (∏ p ∈ s, p) := by
            exact_mod_cast (xi_odd hos.2.1 hos.1).1
          have hm' : (xi (∏ p ∈ s, p) : ℝ) ≤ xi (Nat.lcm (∏ p ∈ s, p) r) := by exact_mod_cast hm
          have hst : seriesTerm (∏ p ∈ s, p) = W s / xi (∏ p ∈ s, p) := by
            unfold seriesTerm; rw [if_pos hos, hfd]
          rw [hst]
          calc L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s ≤ L / xi (∏ p ∈ s, p) * W s :=
                mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hL0 hxd hm') (hW0 s hs.1)
            _ = L * (W s / xi (∏ p ∈ s, p)) := by ring
      _ = L * ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, seriesTerm (∏ p ∈ s, p) := by rw [mul_sum]
      _ = L * ∑ d ∈ (U.filter (fun s => ¬ ∏ p ∈ s, p ≤ D)).image (fun s => ∏ p ∈ s, p),
            seriesTerm d := by
          rw [sum_image]
          intro a ha b hb hab
          have ha' := (set_facts (hUs a (mem_filter.1 (mem_coe.1 ha)).1)).2.1
          have hb' := (set_facts (hUs b (mem_filter.1 (mem_coe.1 hb)).1)).2.1
          simp only at hab
          rw [← ha', ← hb', hab]
      _ ≤ L * ∑' k, seriesTerm (k + (D + 1)) := by
          refine mul_le_mul_of_nonneg_left (tail_le D _ fun d hd => ?_) hL0
          rw [mem_image] at hd
          obtain ⟨s, hs, rfl⟩ := hd
          rw [mem_filter] at hs
          omega
  calc ∑ ν ∈ V, H (m - 2 ^ ν) = ∑ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) * W s := step1
    _ ≤ ∑ s ∈ U, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s + ∑ s ∈ U, W s := step2
    _ ≤ _ := by rw [← hsplit]; linarith

/-- The `+1` part: `Σ_{s ⊆ opf P} W(s) ≤ e^27 log y` once `ω(P) ≤ y`, `y ≥ 4`. -/
lemma sum_W_opf_le (P y : ℕ) (hy : 4 ≤ y) (hω : P.primeFactors.card ≤ y) :
    ∑ s ∈ (opf P).powerset, W s ≤ exp 27 * log y := by
  have hQp : ∀ p ∈ opf P, p.Prime := fun p hp => (opf_spec hp).1
  have hpf : (∏ p ∈ opf P, p).primeFactors = opf P := Nat.primeFactors_prod hQp
  have h := prodH_le (∏ p ∈ opf P, p) y hy (fun p hp => by
      rw [hpf] at hp; have := (opf_spec hp).2.1; omega)
    (by rw [hpf]; exact le_trans (card_filter_le _ _) hω)
  rw [hpf] at h
  unfold W
  rw [← prod_one_add]
  exact h

/-- `log(L² + 5) ≤ 2 + 4√L` for `L ≥ 1`. -/
lemma log_sq_add_le (L : ℝ) (hL : 1 ≤ L) : log (L ^ 2 + 5) ≤ 2 + 4 * Real.sqrt L := by
  have h1 : log (L ^ 2 + 5) ≤ log (6 * L ^ 2) := log_le_log (by positivity) (by nlinarith)
  rw [log_mul (by norm_num) (by positivity), log_pow] at h1
  have h6 : log 6 ≤ 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have h7 : (6 : ℝ) ≤ exp 2 := by
      have := Real.exp_one_gt_d9
      have : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    calc log 6 ≤ log (exp 2) := log_le_log (by norm_num) h7
      _ = 2 := log_exp 2
  have hl := Real.log_le_rpow_div (x := L) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hl
  push_cast at h1
  linarith

lemma aux_third (C δ L ly : ℝ) (hC0 : 0 < C) (hδ0 : 0 < δ) (hL0 : (6 * C / δ) ^ 2 + 1 ≤ L)
    (hly : ly ≤ 2 + 4 * Real.sqrt L) : C * ly ≤ δ * L := by
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * C / δ)]
  have hsqrt : 6 * C / δ ≤ Real.sqrt L := by
    rw [show 6 * C / δ = Real.sqrt ((6 * C / δ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hL1
  have h1 : C * ly ≤ C * (2 + 4 * Real.sqrt L) := mul_le_mul_of_nonneg_left hly hC0.le
  have h2 : C * (2 + 4 * Real.sqrt L) ≤ 6 * C * Real.sqrt L := by
    have := mul_nonneg hC0.le (sub_nonneg.2 hs1)
    linarith
  have h3 : 6 * C ≤ Real.sqrt L * δ := (div_le_iff₀ hδ0).1 hsqrt
  have h4 : 6 * C * Real.sqrt L ≤ δ * L := by
    have := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg L)
    calc 6 * C * Real.sqrt L ≤ Real.sqrt L * δ * Real.sqrt L := this
      _ = δ * (Real.sqrt L * Real.sqrt L) := by ring
      _ = δ * L := by rw [hsL]
  linarith

lemma aux_first (L a δ ξ : ℝ) (hL : 0 ≤ L) (hξ : 0 < ξ) (hδ : 0 < δ) (h : a / δ ≤ ξ) :
    L * a / ξ ≤ δ * L := by
  rw [div_le_iff₀ hξ]
  have h1 : a ≤ ξ * δ := (div_le_iff₀ hδ).1 h
  have := mul_le_mul_of_nonneg_left h1 hL
  linarith

lemma aux_final (S Hs A B T ε L : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) (h1 : S ≤ 2 * Hs)
    (h2 : Hs ≤ A + B + T) (hA : A ≤ ε / 16 * L) (hB : B ≤ ε / 16 * L) (hT : T ≤ ε / 16 * L) :
    S ≤ ε * L := by
  have : 0 ≤ ε * L := mul_nonneg hε.le hL
  linarith

/-- **P0045 Lemma 6.2** in the lab's repaired form: for `ε > 0` there are `r₀, X₀` with
`A(m, r) ≤ ε L` for `X ≥ X₀`, `m ∈ [X/2, X]` and odd `r ≥ r₀`. No cited input. -/
theorem lemma62_proved : Lemma62 := by
  intro ε hε
  set C := exp 27 with hC
  have hC0 : 0 < C := exp_pos 27
  set δ := ε / 16 with hδ
  have hδ0 : 0 < δ := by positivity
  -- the tail
  obtain ⟨D₁, hD₁⟩ := (tendsto_order.1 (tendsto_sum_nat_add seriesTerm)).2 δ hδ0 |>.exists_forall_of_atTop
  set D := max D₁ 4 with hDdef
  have hD4 : 4 ≤ D := le_max_right _ _
  have htail : ∑' k, seriesTerm (k + (D + 1)) < δ := hD₁ (D + 1) (by omega)
  have hlogD : 0 < log (D : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < D))
  -- `r₀`
  set N₁ := ⌈C * log D / δ⌉₊ with hN₁
  refine ⟨2 ^ N₁, 2 ^ ⌈(6 * C / δ) ^ 2 + 1⌉₊, fun X hX m r hm1 hm2 hr0 hr hrr => ?_⟩
  set L := Lg X with hLdef
  have hX1 : 1 ≤ X := le_trans Nat.one_le_two_pow hX
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hLge : ((⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) ≤ L := by
    rw [hLdef, Lg]
    have : ((2 ^ ⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
    calc ((⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) = Real.logb 2 ((2 ^ ⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) := by
          push_cast; rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
      _ ≤ Real.logb 2 X := Real.logb_le_logb_of_le (by norm_num) (by positivity) this
  have hL0 : (6 * C / δ) ^ 2 + 1 ≤ L := le_trans (Nat.le_ceil _) hLge
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * C / δ)]
  -- the admissible set
  set K' := ⌊L - Real.sqrt L⌋₊ with hK'
  have hK'L : (K' : ℝ) ≤ L := by
    rcases le_or_gt 0 (L - Real.sqrt L) with h | h
    · exact le_trans (Nat.floor_le h) (by linarith [Real.sqrt_nonneg L])
    · rw [hK', Nat.floor_eq_zero.2 (by linarith)]; push_cast; linarith
  unfold Amr
  rw [← hLdef]
  set V := (Icc 1 K').filter (fun ν => 2 ^ ν < m ∧ r ∣ m - 2 ^ ν) with hV
  have hVp : ∀ ν ∈ V, ν ∈ Icc 1 K' ∧ 2 ^ ν < m ∧ r ∣ m - 2 ^ ν := fun ν hν => by
    rw [hV, mem_filter] at hν; exact ⟨hν.1, hν.2.1, hν.2.2⟩
  have hmain := sum_H_le V K' m r D L hVp hr hr0 hK'L hD4
  -- the `+1` part: `ω(P) ≤ L²`
  set P := ∏ ν ∈ V, (m - 2 ^ ν) with hP
  have hn0 : ∀ ν ∈ V, m - 2 ^ ν ≠ 0 := fun ν hν => by have := (hVp ν hν).2.1; omega
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn0
  have hcardV : (V.card : ℝ) ≤ L := by
    have : V.card ≤ K' := by
      calc V.card ≤ (Icc 1 K').card := card_le_card (filter_subset _ _)
        _ = K' := by simp
    exact le_trans (by exact_mod_cast this) hK'L
  have hω : (P.primeFactors.card : ℝ) ≤ L ^ 2 := by
    have h1 : 2 ^ P.primeFactors.card ≤ P := Romanov.two_pow_card_le P hP0
    have h2 : P ≤ X ^ V.card := by
      have hmX : m ≤ X := by exact_mod_cast hm2
      calc P ≤ ∏ _ν ∈ V, X := prod_le_prod' fun ν _ => le_trans (Nat.sub_le m _) hmX
        _ = X ^ V.card := by rw [prod_const]
    have h3 : ((2 : ℝ) ^ P.primeFactors.card) ≤ (X : ℝ) ^ V.card := by
      exact_mod_cast le_trans h1 h2
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow, Real.log_pow] at h4
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hLX : Real.log X = L * Real.log 2 := by
      rw [hLdef, Lg, Real.logb, div_mul_cancel₀ _ hl2.ne']
    rw [hLX] at h4
    have : (P.primeFactors.card : ℝ) ≤ V.card * L := by
      have := h4
      nlinarith
    nlinarith
  set y := ⌈L ^ 2⌉₊ + 4 with hy
  have hy4 : 4 ≤ y := by omega
  have hωy : P.primeFactors.card ≤ y := by
    have : P.primeFactors.card ≤ ⌈L ^ 2⌉₊ := by
      have h := le_trans hω (Nat.le_ceil (L ^ 2))
      exact_mod_cast h
    omega
  have hpart3 := sum_W_opf_le P y hy4 hωy
  have hlogy : log (y : ℝ) ≤ log (L ^ 2 + 5) := by
    apply log_le_log (by positivity)
    rw [hy]; push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ L ^ 2)]
  have hsq := log_sq_add_le L hL1
  -- `ξ(r)` is large
  have hxi : C * log D / δ ≤ xi r := by
    have h1 : N₁ ≤ Nat.log 2 r := Nat.le_log_of_pow_le (by norm_num) hrr
    have h2 := log_lt_xi hr hr0
    have : (N₁ : ℝ) ≤ xi r := by exact_mod_cast (by omega : N₁ ≤ xi r)
    exact le_trans (Nat.le_ceil _) this
  have hxr : (0 : ℝ) < xi r := by exact_mod_cast (xi_odd hr hr0).1
  have hpart1 : L * (C * log D) / xi r ≤ δ * L := aux_first L _ δ _ (by linarith) hxr hδ0 hxi
  have hpart3' : C * log y ≤ δ * L := aux_third C δ L _ hC0 hδ0 hL0 (le_trans hlogy hsq)
  have hsing : ∑ ν ∈ V, Sing (m - 2 ^ ν) ≤ 2 * ∑ ν ∈ V, H (m - 2 ^ ν) := by
    rw [mul_sum]; exact sum_le_sum fun ν hν => sing_le_two_H (hn0 ν hν)
  have htail' : L * ∑' k, seriesTerm (k + (D + 1)) ≤ δ * L := by
    have := mul_le_mul_of_nonneg_left htail.le (by linarith : (0 : ℝ) ≤ L); linarith
  have hmain' : ∑ ν ∈ V, H (m - 2 ^ ν) ≤ L * (C * log D) / xi r +
      L * ∑' k, seriesTerm (k + (D + 1)) + C * log y := by
    have := hmain
    rw [← hC] at this
    linarith
  exact aux_final _ _ _ _ _ ε L (by linarith) hε hsing hmain' hpart1 htail' hpart3'

end

end LeanLab.LPZ2007
