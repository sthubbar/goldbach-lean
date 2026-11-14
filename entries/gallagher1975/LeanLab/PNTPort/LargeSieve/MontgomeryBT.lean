module

public import LeanLab.PNTPort.LargeSieve.Montgomery
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Brun-Titchmarsh from Montgomery's sieve, explicit

Lab proof, unit U-5551, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Montgomery 1968; the sharp form `2y/log y` is Montgomery-Vaughan 1973, here with the lab's weak
large sieve constant `N + 2Q²`. No cited input.

* `sum_inv_pf_eq_le`: `∑_{n ≤ Q, primeFactors n = P} 1/n ≤ ∏_{p ∈ P} 1/(p - 1)`.
* `log_le_sum_sqf`: `log(Q + 1) ≤ ∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p - 1) = ∑_{q ≤ Q} μ²(q)/φ(q)`.
* `brun_titchmarsh_montgomery`: for every `x, y` and `Q ≥ 1`,
  `π(x + y) - π(x) ≤ Q + (y + 2Q²)/log(Q + 1)`. With `Q` near `√y / log y` this is
  `π(x + y) - π(x) ≤ (2 + o(1)) y / log y`, with an error of order `y log log y / log² y`,
  no `y (log y)³` term.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Finset Real

/-- `∑_{y ∈ f(s)} g y ≤ ∑_{x ∈ s} g (f x)` for `g ≥ 0`. -/
lemma sum_image_le_of_nonneg' {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (g : β → ℝ) (hg : ∀ y, 0 ≤ g y) : ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
  rw [Finset.sum_comp g f]
  refine sum_le_sum fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  have h1 : 1 ≤ (s.filter (fun a => f a = f x)).card :=
    card_pos.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
  rw [nsmul_eq_mul]
  have : (1 : ℝ) ≤ (s.filter (fun a => f a = f x)).card := by exact_mod_cast h1
  nlinarith [hg (f x)]

lemma geom_inv_le {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    ∑ k ∈ Icc 1 Q, (1 / (p : ℝ)) ^ k ≤ 1 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have h1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have := geom_sum_Ico_le_of_lt_one (m := 1) (n := Q + 1) h0 h1
  rw [show Icc 1 Q = Ico 1 (Q + 1) by ext; simp]
  refine this.trans (le_of_eq ?_)
  field_simp

/-- The fibre of `n ↦ primeFactors n` over a finite set of primes. -/
theorem sum_inv_pf_eq_le (Q : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = P), (1 / (n : ℝ)) ≤
      ∏ p ∈ P, 1 / ((p : ℝ) - 1) := by
  induction P using Finset.induction_on with
  | empty =>
    rw [prod_empty]
    have : (Icc 1 Q).filter (fun n => n.primeFactors = ∅) ⊆ {1} := by
      intro n hn
      rw [mem_filter, Nat.primeFactors_eq_empty, mem_Icc] at hn
      rw [mem_singleton]; omega
    refine (sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => by positivity)).trans ?_
    simp
  | insert p P' hpP' ih =>
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ r ∈ P', r.Prime := fun r hr => hP r (mem_insert_of_mem hr)
    set T' := (Icc 1 Q).filter (fun n => n.primeFactors = P')
    have hsub : (Icc 1 Q).filter (fun n => n.primeFactors = insert p P') ⊆
        (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2) := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn
      obtain ⟨⟨hn1, hnQ⟩, hpf⟩ := hn
      have hn0 : n ≠ 0 := by omega
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors (by rw [hpf]; exact mem_insert_self _ _)
      set k := n.factorization p
      have hk1 : 1 ≤ k := hp.factorization_pos_of_dvd hn0 hpn
      have hpk : p ^ k ∣ n := Nat.ordProj_dvd n p
      have hkQ : k ≤ Q := by
        have := Nat.lt_pow_self hp.one_lt (n := k)
        have := Nat.le_of_dvd (by omega) hpk
        omega
      set m := n / p ^ k
      have hm0 : 0 < m := Nat.ordCompl_pos p hn0
      have hmQ : m ≤ Q := (Nat.div_le_self n _).trans hnQ
      have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
      have hmn : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hpfm : m.primeFactors = P' := by
        ext r
        constructor
        · intro hr
          have hrn : r ∈ n.primeFactors :=
            Nat.primeFactors_mono (Nat.ordCompl_dvd n p) hn0 hr
          rw [hpf, mem_insert] at hrn
          rcases hrn with rfl | h
          · exact absurd (Nat.dvd_of_mem_primeFactors hr)
              ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)
          · exact h
        · intro hr
          have hrn : r ∈ n.primeFactors := by rw [hpf]; exact mem_insert_of_mem hr
          have hrp : r ≠ p := fun h => hpP' (h ▸ hr)
          have hrprime := hP' r hr
          have hcr : Nat.Coprime r (p ^ k) :=
            Nat.Coprime.pow_right k ((Nat.coprime_primes hrprime hp).2 hrp)
          have hrd : r ∣ p ^ k * m := hmn ▸ Nat.dvd_of_mem_primeFactors hrn
          exact Nat.mem_primeFactors.2 ⟨hrprime, hcr.dvd_of_dvd_mul_left hrd, hm0.ne'⟩
      refine mem_image.2 ⟨(k, m), ?_, hmn.symm⟩
      rw [mem_product, mem_Icc]
      exact ⟨⟨hk1, hkQ⟩, mem_filter.2 ⟨mem_Icc.2 ⟨hm0, hmQ⟩, hpfm⟩⟩
    calc ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = insert p P'), (1 / (n : ℝ))
        ≤ ∑ n ∈ (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2), (1 / (n : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ km ∈ Icc 1 Q ×ˢ T', (1 / ((p ^ km.1 * km.2 : ℕ) : ℝ)) :=
          sum_image_le_of_nonneg' _ _ (fun n : ℕ => 1 / (n : ℝ)) (fun _ => by positivity)
      _ = (∑ k ∈ Icc 1 Q, (1 / (p : ℝ)) ^ k) * ∑ m ∈ T', (1 / (m : ℝ)) := by
          rw [sum_mul_sum, sum_product]
          refine sum_congr rfl fun k _ => sum_congr rfl fun m _ => ?_
          push_cast
          rw [one_div_pow, one_div_mul_one_div]
      _ ≤ 1 / ((p : ℝ) - 1) * ∏ r ∈ P', 1 / ((r : ℝ) - 1) := by
          apply mul_le_mul (geom_inv_le hp Q) (ih hP') (sum_nonneg fun _ _ => by positivity)
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          exact div_nonneg zero_le_one (by linarith)
      _ = ∏ r ∈ insert p P', 1 / ((r : ℝ) - 1) := by rw [prod_insert hpP']

/-- The radical `∏_{p ∣ n} p`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma rad_pf (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors hp)

lemma rad_sqf (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (Nat.prime_of_mem_primeFactors hp).prime.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq

lemma rad_pos (n : ℕ) : 0 < rad n :=
  prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- `log(Q + 1) ≤ ∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p - 1)`. -/
theorem log_le_sum_sqf (Q : ℕ) :
    Real.log ((Q : ℝ) + 1) ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) := by
  have hH := log_add_one_le_harmonic Q
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  refine hH.trans ?_
  rw [← sum_fiberwise_of_maps_to (s := Icc 1 Q) (t := (Icc 1 Q).filter Squarefree) (g := rad)
    (fun n hn => by
      rw [mem_Icc] at hn
      refine mem_filter.2 ⟨mem_Icc.2 ⟨rad_pos n, ?_⟩, rad_sqf n⟩
      exact (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)).trans hn.2)]
  refine sum_le_sum fun q hq => ?_
  rw [mem_filter] at hq
  have hsub : (Icc 1 Q).filter (fun n => rad n = q) ⊆
      (Icc 1 Q).filter (fun n => n.primeFactors = q.primeFactors) := by
    intro n hn
    rw [mem_filter] at hn ⊢
    exact ⟨hn.1, by rw [← rad_pf n, hn.2]⟩
  calc ∑ n ∈ (Icc 1 Q).filter (fun n => rad n = q), ((n : ℝ))⁻¹
      ≤ ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = q.primeFactors), (1 / (n : ℝ)) := by
        simp_rw [one_div]
        exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := sum_inv_pf_eq_le Q _ (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- **Brun-Titchmarsh, explicit, from Montgomery's sieve.** For `Q ≥ 1`,
`π(x + y) - π(x) ≤ Q + (y + 2Q²)/log(Q + 1)`. -/
theorem brun_titchmarsh_montgomery (x y Q : ℕ) (hQ : 1 ≤ Q) :
    ((((Ioc x (x + y)).filter Nat.Prime).card : ℕ) : ℝ) ≤
      Q + (y + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
  set P := (Ioc x (x + y)).filter Nat.Prime
  set Psmall := P.filter (· ≤ Q)
  set Pbig := P.filter (fun r => ¬ r ≤ Q)
  have hsplit : P.card = Psmall.card + Pbig.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ Q := by
    have : Psmall ⊆ Icc 1 Q := by
      intro r hr
      simp only [Psmall, P, mem_filter, mem_Ioc] at hr
      exact mem_Icc.2 ⟨hr.1.2.one_lt.le, hr.2⟩
    have := card_le_card this
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Psmall.card ≤ Q)
  -- the big primes as integers
  set A : Finset ℤ := Pbig.image (fun r : ℕ => (r : ℤ))
  have hAcard : A.card = Pbig.card := card_image_of_injective _ Nat.cast_injective
  have hA : A ⊆ Ioc (x : ℤ) ((x : ℤ) + (y : ℕ)) := by
    intro n hn
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Ioc] at hr
    rw [mem_Ioc]
    constructor <;> push_cast <;> omega
  set B : ℕ → Finset ℕ := fun _ => {0}
  have hB : ∀ p, p.Prime → B p ⊆ range p ∧ (B p).card < p := by
    intro p hp
    refine ⟨?_, ?_⟩
    · intro b hb
      rw [mem_singleton] at hb
      rw [hb, mem_range]; exact hp.pos
    · rw [card_singleton]; exact hp.one_lt
  have hAB : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ A, (n % (p : ℤ)).toNat ∉ B p := by
    intro p hp hpQ n hn
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Ioc] at hr
    simp only [B, mem_singleton]
    rw [← Int.natCast_mod, Int.toNat_natCast]
    intro h0
    have hdvd : p ∣ r := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq hp hr.1.2).1 hdvd
    omega
  have hmont := montgomery_sieve hQ (x : ℤ) y A hA B hB hAB
  have hW_eq : ∀ q, hW B q = ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) := by
    intro q
    unfold hW
    refine prod_congr rfl fun _ _ => ?_
    simp [B]
  simp_rw [hW_eq] at hmont
  have hlog := log_le_sum_sqf Q
  have hlogpos : 0 < Real.log ((Q : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hbig : (Pbig.card : ℝ) ≤ (y + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
    rw [le_div_iff₀ hlogpos, ← hAcard]
    calc (A.card : ℝ) * Real.log ((Q : ℝ) + 1)
        ≤ (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree,
            ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ ≤ _ := hmont
  rw [hsplit, Nat.cast_add]
  linarith

end LeanLab.PNTPort.LargeSieve

