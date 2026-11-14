module

public import Mathlib

/-!
# A coprime harmonic sum

Lab proof, unit U-5304, CLOUD 20261019T0814Z-cloud20, moved here from TauGoldbachMain.lean in U-5305
so the sieve files can use it without importing the analytic chain. AI wrote the Lean code. Known
mathematics. `coprime_harm_ge`: `Σ_{d ≤ Q, (d,N)=1} 1/d ≥ (φ(N)/N) log(Q + 1)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset Real

/-- `Σ_{d ≤ Q, p ∤ d for every p ∈ S} 1/d`. -/
noncomputable def harmS (S : Finset ℕ) (Q : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 Q).filter (fun d => ∀ p ∈ S, ¬ p ∣ d), (1 : ℝ) / d

lemma geom_le (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∑ k ∈ range n, ((1 : ℝ) / p) ^ k ≤ (p : ℝ) / (p - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hx1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  rw [geom_sum_eq hx1.ne]
  have hpow : 0 ≤ ((1 : ℝ) / p) ^ n := pow_nonneg hx0 n
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hne2 : (1 : ℝ) / p - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have e : (((1 : ℝ) / p) ^ n - 1) / (1 / p - 1) = (1 - ((1 : ℝ) / p) ^ n) * ((p : ℝ) / (p - 1)) := by
    rw [div_eq_iff hne2]; field_simp; ring
  rw [e]
  have hq : 0 ≤ (p : ℝ) / (p - 1) := div_nonneg (by linarith) (by linarith)
  nlinarith

/-- One prime step: `harmS S Q ≤ p/(p - 1) · harmS (insert p S) Q`. -/
lemma harmS_step (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (Q : ℕ) :
    harmS S Q ≤ (p : ℝ) / (p - 1) * harmS (insert p S) Q := by
  unfold harmS
  set T := (Icc 1 Q).filter (fun d => ∀ q ∈ S, ¬ q ∣ d) with hT
  set T' := (Icc 1 Q).filter (fun d => ∀ q ∈ insert p S, ¬ q ∣ d) with hT'
  set φ : ℕ → ℕ × ℕ := fun d => (d.factorization p, d / p ^ d.factorization p) with hφ
  have hinj : ∀ x ∈ T, ∀ y ∈ T, φ x = φ y → x = y := by
    intro x _ y _ hxy
    simp only [hφ, Prod.mk.injEq] at hxy
    calc x = p ^ x.factorization p * (x / p ^ x.factorization p) :=
          (Nat.ordProj_mul_ordCompl_eq_self x p).symm
      _ = p ^ y.factorization p * (y / p ^ y.factorization p) := by rw [hxy.2, hxy.1]
      _ = y := Nat.ordProj_mul_ordCompl_eq_self y p
  have hsub : T.image φ ⊆ range (Q + 1) ×ˢ T' := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hz
    simp only [hT, mem_filter, mem_Icc] at hd
    have hd0 : d ≠ 0 := by omega
    simp only [mem_product, mem_range, hT', mem_filter, mem_Icc, mem_insert, hφ]
    have hpk : p ^ d.factorization p ≤ d := Nat.ordProj_le p hd0
    have hk : d.factorization p < p ^ d.factorization p :=
      Nat.lt_pow_self hp.one_lt
    have hm0 : d / p ^ d.factorization p ≠ 0 := by
      have := Nat.ordProj_mul_ordCompl_eq_self d p
      intro h; rw [h, mul_zero] at this; exact hd0 this.symm
    refine ⟨Nat.lt_succ_of_le (hk.le.trans (hpk.trans hd.1.2)),
      ⟨⟨Nat.pos_of_ne_zero hm0, (Nat.ordCompl_le d p).trans hd.1.2⟩, ?_⟩⟩
    intro q hq
    rcases hq with rfl | hq
    · exact fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_ordCompl hp hd0) h
    · exact fun h => hd.2 q hq (h.trans (Nat.ordCompl_dvd d p))
  have hval : ∀ d ∈ T, (1 : ℝ) / d =
      (fun z : ℕ × ℕ => ((1 : ℝ) / p) ^ z.1 * ((1 : ℝ) / z.2)) (φ d) := by
    intro d hd
    simp only [hφ]
    have e := Nat.ordProj_mul_ordCompl_eq_self d p
    conv_lhs => rw [← e]
    push_cast
    rw [div_pow, one_pow, one_div_mul_one_div]
  calc ∑ d ∈ T, (1 : ℝ) / d
      = ∑ z ∈ T.image φ, ((1 : ℝ) / p) ^ z.1 * ((1 : ℝ) / z.2) := by
        rw [sum_image hinj]; exact sum_congr rfl hval
    _ ≤ ∑ z ∈ range (Q + 1) ×ˢ T', ((1 : ℝ) / p) ^ z.1 * ((1 : ℝ) / z.2) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ k ∈ range (Q + 1), ((1 : ℝ) / p) ^ k) * ∑ m ∈ T', (1 : ℝ) / m := by
        rw [sum_product, sum_mul_sum]
    _ ≤ (p : ℝ) / (p - 1) * ∑ m ∈ T', (1 : ℝ) / m :=
        mul_le_mul_of_nonneg_right (geom_le p hp _) (sum_nonneg (fun _ _ => by positivity))

/-- `Σ_{d ≤ Q} 1/d ≤ Π_{p ∈ S} p/(p - 1) · harmS S Q` for a finset `S` of primes. -/
lemma harm_le_prod_mul (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (Q : ℕ) :
    harmS ∅ Q ≤ (∏ p ∈ S, (p : ℝ) / (p - 1)) * harmS S Q := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
      have hp : p.Prime := hS p (mem_insert_self p S)
      have ih' := ih (fun q hq => hS q (mem_insert_of_mem hq))
      have hstep := harmS_step p hp S Q
      have hprod0 : 0 ≤ ∏ q ∈ S, (q : ℝ) / (q - 1) := by
        apply prod_nonneg; intro q hq
        have : (1 : ℝ) ≤ q := by
          exact_mod_cast (hS q (mem_insert_of_mem hq)).one_le
        exact div_nonneg (by linarith) (by linarith)
      rw [prod_insert hpS]
      calc harmS ∅ Q ≤ (∏ q ∈ S, (q : ℝ) / (q - 1)) * harmS S Q := ih'
        _ ≤ (∏ q ∈ S, (q : ℝ) / (q - 1)) * ((p : ℝ) / (p - 1) * harmS (insert p S) Q) :=
            mul_le_mul_of_nonneg_left hstep hprod0
        _ = _ := by ring

/-- `Π_{p ∣ N} p/(p - 1) = N/φ(N)`. -/
lemma prod_primeFactors_eq (N : ℕ) (hN : 1 ≤ N) :
    ∏ p ∈ N.primeFactors, (p : ℝ) / (p - 1) = (N : ℝ) / N.totient := by
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have key := Nat.totient_mul_prod_primeFactors N
  have keyR : (N.totient : ℝ) * ∏ p ∈ N.primeFactors, (p : ℝ) =
      (N : ℝ) * ∏ p ∈ N.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) key
    push_cast at this
    rw [this]
    congr 1
    apply prod_congr rfl
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [this]; ring
  have hpos : (0 : ℝ) < ∏ p ∈ N.primeFactors, ((p : ℝ) - 1) := by
    apply prod_pos; intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [prod_div_distrib, div_eq_div_iff hpos.ne' hφ.ne']
  linarith [keyR]

/-- `Σ_{d ≤ Q, (d,N)=1} 1/d ≥ (φ(N)/N) log(Q + 1)`. -/
theorem coprime_harm_ge (N Q : ℕ) (hN : 1 ≤ N) :
    (N.totient : ℝ) / N * Real.log (Q + 1) ≤
      ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N), (1 : ℝ) / d := by
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := harm_le_prod_mul N.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) Q
  rw [prod_primeFactors_eq N hN] at h1
  have hH : Real.log (Q + 1) ≤ harmS ∅ Q := by
    have := log_add_one_le_harmonic Q
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [harmS, one_div] using this
  have hsub : harmS N.primeFactors Q ≤
      ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N), (1 : ℝ) / d := by
    unfold harmS
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
    intro d hd
    simp only [mem_filter] at hd ⊢
    refine ⟨hd.1, Nat.coprime_of_dvd (fun k hk hkd hkN => ?_)⟩
    exact hd.2 k (Nat.mem_primeFactors.mpr ⟨hk, hkN, by omega⟩) hkd
  have h2 : Real.log (Q + 1) ≤ (N : ℝ) / N.totient *
      ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N), (1 : ℝ) / d :=
    hH.trans (h1.trans (mul_le_mul_of_nonneg_left hsub (by positivity)))
  rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
  calc (N.totient : ℝ) * Real.log (Q + 1) ≤ (N.totient : ℝ) * ((N : ℝ) / N.totient *
        ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N), (1 : ℝ) / d) :=
        mul_le_mul_of_nonneg_left h2 hφ.le
    _ = _ := by field_simp

end LeanLab.PNTPort.BVMax

