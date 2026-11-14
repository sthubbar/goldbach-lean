module

public import LeanLab.PNTPort.LargeSieve.PrimeSieve
public import Mathlib.Data.Nat.Squarefree
import Mathlib

/-!
# Montgomery's sieve over squarefree moduli

Lab proof, unit U-5551, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Montgomery 1968, in the form of Montgomery-Vaughan 1973 with the lab's weak constant `N + 2Q²`.
No cited input.

* `S I a x = ∑_{n ∈ I} a n e(nx)` and `Pr I a q = ∑_{c < q, (c, q) = 1} ‖S I a (c/q)‖²`.
* `Pr_prime_ge`: if `a` vanishes on the residue classes `Bad p` modulo a prime `p`, with
  `ω = |Bad p| < p`, then `Pr I a p ≥ ω/(p - ω) ‖S I a 0‖²`.
* `Pr_mul`: for coprime `q₁, q₂`, `Pr I a (q₁q₂) = ∑_{c ∈ U q₁} Pr I (a · e(·c/q₁)) q₂`, by the
  Chinese remainder theorem.
* `Pr_sqf_ge`: for squarefree `q` whose primes all carry the hypothesis,
  `Pr I a q ≥ h(q) ‖S I a 0‖²`, `h(q) = ∏_{p ∣ q} ω(p)/(p - ω(p))`.
* `montgomery_sieve`: if `A ⊆ (M, M + N]` avoids `Bad p` modulo every prime `p ≤ Q`, then
  `|A| ∑_{q ≤ Q squarefree} h(q) ≤ N + 2Q²`.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

/-- The exponential sum `S(x) = ∑_{n ∈ I} a n e(nx)`. -/
noncomputable def S (I : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ I, a n * e (n * x)

/-- The reduced residues modulo `q`, in the order `Nat.totient` uses. -/
def U (q : ℕ) : Finset ℕ := (range q).filter (Nat.Coprime q)

lemma card_U (q : ℕ) : (U q).card = q.totient := rfl

/-- The sum over primitive fractions `c/q`. -/
noncomputable def Pr (I : Finset ℤ) (a : ℤ → ℂ) (q : ℕ) : ℝ :=
  ∑ c ∈ U q, ‖S I a ((c : ℝ) / q)‖ ^ 2

lemma S_add_int (I : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) (k : ℤ) : S I a (x + k) = S I a x := by
  unfold S
  refine sum_congr rfl fun n _ => ?_
  rw [mul_add, e_add, show ((n : ℝ) * (k : ℝ)) = ((n * k : ℤ) : ℝ) by push_cast; ring, e_int,
    mul_one]

lemma S_twist (I : Finset ℤ) (a : ℤ → ℂ) (x y : ℝ) :
    S I (fun n => a n * e (n * x)) y = S I a (x + y) := by
  unfold S
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← e_add, mul_add]

lemma resSum_fiber (I : Finset ℤ) (a : ℤ → ℂ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    resSum I a p b = ∑ n ∈ I.filter (fun n : ℤ => (n % (p : ℤ)).toNat = b), a n := by
  unfold resSum
  congr 1
  ext n
  simp only [mem_filter]
  have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; simp⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

lemma S_zero_eq_sum_res (I : Finset ℤ) (a : ℤ → ℂ) {p : ℕ} (hp : 0 < p) :
    S I a 0 = ∑ b ∈ range p, resSum I a p b := by
  simp_rw [resSum_fiber I a hp]
  unfold S
  simp only [mul_zero, e_zero, mul_one]
  refine (sum_fiberwise_of_maps_to (g := fun n : ℤ => (n % (p : ℤ)).toNat) ?_ _).symm
  intro n _
  rw [mem_range]
  have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have h1 : n % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  omega

/-- `a` vanishes on the classes `B` modulo `p`. -/
def Avoids (I : Finset ℤ) (a : ℤ → ℂ) (p : ℕ) (B : Finset ℕ) : Prop :=
  ∀ n ∈ I, (n % (p : ℤ)).toNat ∈ B → a n = 0

lemma avoids_twist {I : Finset ℤ} {a : ℤ → ℂ} {p : ℕ} {B : Finset ℕ} (h : Avoids I a p B)
    (x : ℝ) : Avoids I (fun n => a n * e (n * x)) p B := by
  intro n hn hb
  show a n * _ = 0
  rw [h n hn hb, zero_mul]

lemma U_prime {p : ℕ} (hp : p.Prime) : U p = (range p).erase 0 := by
  ext c
  simp only [U, mem_filter, mem_range, mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rintro rfl
    rw [Nat.coprime_zero_right] at h2
    exact hp.one_lt.ne' h2
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact h1 (Nat.eq_zero_of_dvd_of_lt hd h2)

/-- The prime case of Montgomery's inequality. -/
theorem Pr_prime_ge (I : Finset ℤ) (a : ℤ → ℂ) {p : ℕ} (hp : p.Prime) {B : Finset ℕ}
    (hB : B ⊆ range p) (hBp : B.card < p) (ha : Avoids I a p B) :
    (B.card : ℝ) / (p - B.card) * ‖S I a 0‖ ^ 2 ≤ Pr I a p := by
  have hp0 := hp.pos
  set z : ℕ → ℂ := fun b => resSum I a p b with hz
  have hzero : ∀ b ∈ B, z b = 0 := by
    intro b hb
    simp only [hz]
    rw [resSum_fiber I a hp0]
    refine sum_eq_zero fun n hn => ?_
    rw [mem_filter] at hn
    exact ha n hn.1 (by rw [hn.2]; exact hb)
  -- the full sum by Parseval
  have hpars := parseval_mod I a hp0
  have hfull : ∑ c ∈ range p, ‖S I a ((c : ℝ) / p)‖ ^ 2 = p * ∑ b ∈ range p, ‖z b‖ ^ 2 := by
    rw [← hpars]
    refine sum_congr rfl fun c _ => ?_
    unfold S
    congr 2
    refine sum_congr rfl fun n _ => ?_
    rw [mul_div_assoc]
  have hsplit : ∑ c ∈ range p, ‖S I a ((c : ℝ) / p)‖ ^ 2 = Pr I a p + ‖S I a 0‖ ^ 2 := by
    unfold Pr
    rw [U_prime hp, ← add_sum_erase _ _ (mem_range.2 hp0)]
    simp only [Nat.cast_zero, zero_div]
    ring
  -- Cauchy-Schwarz over the classes outside `B`
  set R := range p \ B with hR
  have hS0 : S I a 0 = ∑ b ∈ R, z b := by
    rw [S_zero_eq_sum_res I a hp0, hR, sum_sdiff_eq_sub hB]
    rw [sum_eq_zero hzero, sub_zero]
  have hRcard : (R.card : ℝ) = p - B.card := by
    rw [hR, card_sdiff_of_subset hB, card_range, Nat.cast_sub hBp.le]
  have hcs : ‖S I a 0‖ ^ 2 ≤ (p - B.card) * ∑ b ∈ range p, ‖z b‖ ^ 2 := by
    rw [hS0]
    have h1 : ‖∑ b ∈ R, z b‖ ≤ ∑ b ∈ R, ‖z b‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := R) (f := fun b => ‖z b‖)
    have h3 : ∑ b ∈ R, ‖z b‖ ^ 2 ≤ ∑ b ∈ range p, ‖z b‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)
    rw [← hRcard]
    calc ‖∑ b ∈ R, z b‖ ^ 2 ≤ (∑ b ∈ R, ‖z b‖) ^ 2 := by gcongr
      _ ≤ R.card * ∑ b ∈ R, ‖z b‖ ^ 2 := h2
      _ ≤ R.card * ∑ b ∈ range p, ‖z b‖ ^ 2 := by gcongr
  have hpω : (0 : ℝ) < p - B.card := by
    have : (B.card : ℝ) < p := by exact_mod_cast hBp
    linarith
  -- assemble
  have hT : ‖S I a 0‖ ^ 2 / (p - B.card) ≤ ∑ b ∈ range p, ‖z b‖ ^ 2 := by
    rw [div_le_iff₀ hpω]; linarith
  have hP : Pr I a p = p * ∑ b ∈ range p, ‖z b‖ ^ 2 - ‖S I a 0‖ ^ 2 := by linarith
  rw [hP]
  have : (B.card : ℝ) / (p - B.card) * ‖S I a 0‖ ^ 2 =
      p * (‖S I a 0‖ ^ 2 / (p - B.card)) - ‖S I a 0‖ ^ 2 := by
    field_simp; ring
  rw [this]
  have hp' : (0 : ℝ) ≤ p := by positivity
  nlinarith

/-- The Chinese remainder map on reduced residues. -/
def crt (q₁ q₂ : ℕ) (c : ℕ × ℕ) : ℕ := (c.1 * q₂ + c.2 * q₁) % (q₁ * q₂)

lemma coprime_of_mod {m x y : ℕ} (h : x % m = y % m) (hy : Nat.Coprime m y) : Nat.Coprime m x := by
  unfold Nat.Coprime at *
  rw [Nat.gcd_rec m x, h, ← Nat.gcd_rec, hy]

lemma crt_mem {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) {c : ℕ × ℕ}
    (hc : c ∈ U q₁ ×ˢ U q₂) : crt q₁ q₂ c ∈ U (q₁ * q₂) := by
  simp only [U, mem_product, mem_filter, mem_range] at hc
  simp only [U, mem_filter, mem_range, crt]
  refine ⟨Nat.mod_lt _ (Nat.mul_pos hq₁ hq₂), Nat.coprime_mul_iff_left.2 ⟨?_, ?_⟩⟩
  · apply coprime_of_mod (y := c.1 * q₂)
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right q₁ q₂), Nat.add_mul_mod_self_right]
    · exact Nat.coprime_mul_iff_right.2 ⟨hc.1.2, h⟩
  · apply coprime_of_mod (y := c.2 * q₁)
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left q₂ q₁), add_comm, Nat.add_mul_mod_self_right]
    · exact Nat.coprime_mul_iff_right.2 ⟨hc.2.2, h.symm⟩

lemma crt_inj {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) {c d : ℕ × ℕ}
    (hc : c ∈ U q₁ ×ˢ U q₂) (hd : d ∈ U q₁ ×ˢ U q₂) (he : crt q₁ q₂ c = crt q₁ q₂ d) :
    c = d := by
  simp only [U, mem_product, mem_filter, mem_range] at hc hd
  have hmod : c.1 * q₂ + c.2 * q₁ ≡ d.1 * q₂ + d.2 * q₁ [MOD q₁ * q₂] := he
  have h1 : c.1 * q₂ ≡ d.1 * q₂ [MOD q₁] := by
    have := Nat.ModEq.of_mul_right q₂ hmod
    unfold Nat.ModEq at this ⊢
    rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at this
  have h2 : c.2 * q₁ ≡ d.2 * q₁ [MOD q₂] := by
    have := Nat.ModEq.of_mul_left q₁ hmod
    unfold Nat.ModEq at this ⊢
    rwa [add_comm, Nat.add_mul_mod_self_right, add_comm, Nat.add_mul_mod_self_right] at this
  have e1 := Nat.ModEq.cancel_right_of_coprime h h1
  have e2 := Nat.ModEq.cancel_right_of_coprime h.symm h2
  unfold Nat.ModEq at e1 e2
  rw [Nat.mod_eq_of_lt hc.1.1, Nat.mod_eq_of_lt hd.1.1] at e1
  rw [Nat.mod_eq_of_lt hc.2.1, Nat.mod_eq_of_lt hd.2.1] at e2
  exact Prod.ext e1 e2

lemma crt_image {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (U q₁ ×ˢ U q₂).image (crt q₁ q₂) = U (q₁ * q₂) := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    exact crt_mem h hq₁ hq₂ hc
  · rw [card_image_of_injOn (fun c hc d hd he => crt_inj h hc hd he), card_product, card_U,
      card_U, card_U, Nat.totient_mul h]

lemma S_crt (I : Finset ℤ) (a : ℤ → ℂ) {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (c : ℕ × ℕ) :
    S I a ((crt q₁ q₂ c : ℕ) / ((q₁ * q₂ : ℕ) : ℝ)) =
      S I a ((c.1 : ℝ) / q₁ + (c.2 : ℝ) / q₂) := by
  set x := c.1 * q₂ + c.2 * q₁
  set m := q₁ * q₂
  have hm : (0 : ℝ) < m := by positivity
  have hdiv : x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
  have hx : (x : ℝ) = m * ((x / m : ℕ) : ℝ) + ((x % m : ℕ) : ℝ) := by exact_mod_cast hdiv
  have hq1 : (q₁ : ℝ) ≠ 0 := by positivity
  have hq2 : (q₂ : ℝ) ≠ 0 := by positivity
  have hxdef : (x : ℝ) = c.1 * q₂ + c.2 * q₁ := by simp [x]
  have hmdef : (m : ℝ) = q₁ * q₂ := by simp [m]
  have k1 : (c.1 : ℝ) / q₁ + (c.2 : ℝ) / q₂ = (x : ℝ) / m := by
    rw [hxdef, hmdef]; field_simp
  have k2 : (x : ℝ) / m = ((x % m : ℕ) : ℝ) / (m : ℝ) + (((x / m : ℕ) : ℤ) : ℝ) := by
    rw [hx, Int.cast_natCast]; field_simp; ring
  rw [k1, k2, S_add_int]
  rfl

/-- Multiplicativity of the primitive sums, by the Chinese remainder theorem. -/
theorem Pr_mul (I : Finset ℤ) (a : ℤ → ℂ) {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂) :
    Pr I a (q₁ * q₂) = ∑ c ∈ U q₁, Pr I (fun n => a n * e (n * ((c : ℝ) / q₁))) q₂ := by
  unfold Pr
  simp_rw [S_twist]
  rw [← sum_product (f := fun c : ℕ × ℕ => ‖S I a ((c.1 : ℝ) / q₁ + (c.2 : ℝ) / q₂)‖ ^ 2),
    ← crt_image h hq₁ hq₂, sum_image (fun c hc d hd he => crt_inj h hc hd he)]
  refine sum_congr rfl fun c _ => ?_
  rw [← S_crt I a hq₁ hq₂ c]

/-- The weight `h(q) = ∏_{p ∣ q} ω(p)/(p - ω(p))`. -/
noncomputable def hW (B : ℕ → Finset ℕ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((B p).card : ℝ) / (p - (B p).card)

lemma Pr_one (I : Finset ℤ) (a : ℤ → ℂ) : Pr I a 1 = ‖S I a 0‖ ^ 2 := by
  unfold Pr U
  rw [show (range 1).filter (Nat.Coprime 1) = {0} by decide, sum_singleton]
  simp

/-- Montgomery's inequality for a squarefree modulus. -/
theorem Pr_sqf_ge (I : Finset ℤ) (a : ℤ → ℂ) (B : ℕ → Finset ℕ)
    (hB : ∀ p, p.Prime → B p ⊆ range p ∧ (B p).card < p) :
    ∀ q, Squarefree q → (∀ p ∈ q.primeFactors, Avoids I a p (B p)) →
      hW B q * ‖S I a 0‖ ^ 2 ≤ Pr I a q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq hav
  rcases Nat.lt_or_ge q 2 with hlt | hge
  · interval_cases q
    · exact absurd hq not_squarefree_zero
    · simp [hW, Pr_one]
  · obtain ⟨p, hpdef⟩ : ∃ p, p = q.minFac := ⟨_, rfl⟩
    have hp : p.Prime := hpdef ▸ Nat.minFac_prime (by omega)
    have hpq : p ∣ q := hpdef ▸ Nat.minFac_dvd q
    obtain ⟨q₁, hq₁def⟩ : ∃ q₁, q₁ = q / p := ⟨_, rfl⟩
    have hq_eq : q = q₁ * p := by rw [hq₁def]; exact (Nat.div_mul_cancel hpq).symm
    have hq₁pos : 0 < q₁ := hq₁def ▸ Nat.div_pos (Nat.le_of_dvd (by omega) hpq) hp.pos
    have hcop : Nat.Coprime q₁ p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have : p * p ∣ q := by rw [hq_eq]; exact Nat.mul_dvd_mul_right hd p
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hq p this))
    have hq₁lt : q₁ < q := hq₁def ▸ Nat.div_lt_self (by omega) hp.one_lt
    have hq₁sqf : Squarefree q₁ := hq.squarefree_of_dvd (hq₁def ▸ Nat.div_dvd_of_dvd hpq)
    have hpf : q.primeFactors = insert p q₁.primeFactors := by
      rw [hq_eq, Nat.primeFactors_mul hq₁pos.ne' hp.ne_zero, hp.primeFactors, union_comm]; rfl
    have hpnot : p ∉ q₁.primeFactors := by
      intro hm
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm (Nat.dvd_of_mem_primeFactors hm)
    have hav₁ : ∀ r ∈ q₁.primeFactors, Avoids I a r (B r) := fun r hr =>
      hav r (by rw [hpf]; exact mem_insert_of_mem hr)
    have havp : Avoids I a p (B p) := hav p (by rw [hpf]; exact mem_insert_self _ _)
    have hW_eq : hW B q = ((B p).card : ℝ) / (p - (B p).card) * hW B q₁ := by
      unfold hW; rw [hpf, prod_insert hpnot]
    have hBp := hB p hp
    have hhp : (0 : ℝ) ≤ ((B p).card : ℝ) / (p - (B p).card) := by
      have : ((B p).card : ℝ) < p := by exact_mod_cast hBp.2
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    rw [hW_eq]
    clear hq₁def hpdef hpf
    subst hq_eq
    rw [Pr_mul I a hcop hq₁pos hp.pos]
    have step : ∀ c ∈ U q₁, ((B p).card : ℝ) / (p - (B p).card) * ‖S I a ((c : ℝ) / q₁)‖ ^ 2 ≤
        Pr I (fun n => a n * e (n * ((c : ℝ) / q₁))) p := by
      intro c _
      have := Pr_prime_ge I (fun n => a n * e (n * ((c : ℝ) / q₁))) hp hBp.1 hBp.2
        (avoids_twist havp _)
      rwa [S_twist, add_zero] at this
    calc ((B p).card : ℝ) / (p - (B p).card) * hW B q₁ * ‖S I a 0‖ ^ 2
        = ((B p).card : ℝ) / (p - (B p).card) * (hW B q₁ * ‖S I a 0‖ ^ 2) := by ring
      _ ≤ ((B p).card : ℝ) / (p - (B p).card) * Pr I a q₁ := by
          exact mul_le_mul_of_nonneg_left (ih q₁ hq₁lt hq₁sqf hav₁) hhp
      _ = ∑ c ∈ U q₁, ((B p).card : ℝ) / (p - (B p).card) * ‖S I a ((c : ℝ) / q₁)‖ ^ 2 := by
          unfold Pr; rw [mul_sum]
      _ ≤ _ := sum_le_sum step

/-- The Farey sum regrouped by denominator. -/
lemma farey_sum_eq (Q : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ x ∈ farey Q, F x = ∑ q ∈ Icc 1 Q, ∑ c ∈ U q, F (q, c) := by
  unfold farey
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun q hq => ?_
  rw [mem_Icc] at hq
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [mem_filter, mem_range, U]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, Nat.coprime_comm.1 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, Nat.coprime_comm.1 h2⟩

/-- **Montgomery's sieve.** If `A ⊆ (M, M + N]` avoids the classes `B p` modulo every prime
`p ≤ Q`, with `|B p| < p`, then `|A| ∑_{q ≤ Q squarefree} h(q) ≤ N + 2Q²`. -/
theorem montgomery_sieve {Q : ℕ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Ioc M (M + N)) (B : ℕ → Finset ℕ)
    (hB : ∀ p, p.Prime → B p ⊆ range p ∧ (B p).card < p)
    (hAB : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ A, (n % (p : ℤ)).toNat ∉ B p) :
    (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q ≤ N + 2 * (Q : ℝ) ^ 2 := by
  set I := Ioc M (M + N)
  set a : ℤ → ℂ := fun n => if n ∈ A then 1 else 0 with ha
  have hS0 : S I a 0 = A.card := by
    unfold S
    simp only [ha, mul_zero, e_zero, mul_one]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  have hsq : ∑ n ∈ I, ‖a n‖ ^ 2 = A.card := by
    have : ∀ n, ‖a n‖ ^ 2 = if n ∈ A then 1 else 0 := by
      intro n; simp only [ha]; split_ifs <;> simp
    simp_rw [this]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  have hls := farey_large_sieve hQ a M N
  rw [hsq] at hls
  have hfs : ∑ p ∈ farey Q, ‖∑ n ∈ I, a n * e (n * fareyPt p)‖ ^ 2 =
      ∑ q ∈ Icc 1 Q, Pr I a q := by
    rw [farey_sum_eq Q (fun p => ‖∑ n ∈ I, a n * e (n * fareyPt p)‖ ^ 2)]
    rfl
  rw [hfs] at hls
  have hlow : ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q * (A.card : ℝ) ^ 2 ≤
      ∑ q ∈ Icc 1 Q, Pr I a q := by
    calc ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q * (A.card : ℝ) ^ 2
        ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, Pr I a q := by
          refine sum_le_sum fun q hq => ?_
          rw [mem_filter, mem_Icc] at hq
          have := Pr_sqf_ge I a B hB q hq.2 (fun p hp => by
            intro n hn hb
            have hpQ : p ≤ Q := (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans
              hq.1.2
            simp only [ha, ite_eq_right_iff, one_ne_zero, imp_false]
            intro hnA
            exact hAB p (Nat.prime_of_mem_primeFactors hp) hpQ n hnA hb)
          rwa [hS0, Complex.norm_natCast] at this
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun q _ _ => by unfold Pr; positivity)
  rw [← sum_mul] at hlow
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0]; simp; positivity
  · have hpos' : (0 : ℝ) < A.card := by exact_mod_cast hpos
    have := hlow.trans hls
    rw [show (A.card : ℝ) ^ 2 = A.card * A.card by ring, ← mul_assoc] at this
    have := le_of_mul_le_mul_right this hpos'
    linarith

end LeanLab.PNTPort.LargeSieve

