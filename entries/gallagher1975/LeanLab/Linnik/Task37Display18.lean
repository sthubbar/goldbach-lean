module

public import LeanLab.Linnik.U1474R0

/-!
Li and Liu, https://arxiv.org/html/2610.15784, Section 3, Lemma 3.1 display 18.
The finite divisor part is bounded using the count modulo q alone.
The remaining divisor part is bounded by display 17.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Task37Display18

open Set Real Filter Finset Topology
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7205Display34
open LeanLab.Linnik.U1447Display30
open LeanLab.Linnik.U7203Display33
open LeanLab.Linnik.U1458Lemma42
open LeanLab.Linnik.U1464Display20
open LeanLab.Linnik.U1466Display17
open LeanLab.Linnik.U1474R0
open LeanLab.Linnik.U1434Lemma21 (sv)

/-- The integer form of the order lower bound in the proof of display 18. -/
lemma modulus_le_pow {q : ℕ} (hq : Odd q) : q + 1 ≤ 2 ^ eps q := by
  have hp := eps_pos hq
  have hpow : 0 < 2 ^ eps q - 1 := by
    have : 2 ≤ 2 ^ eps q := by
      calc 2 = 2 ^ 1 := by norm_num
           _ ≤ 2 ^ eps q := Nat.pow_le_pow_right (by norm_num) hp
    omega
  have := Nat.le_of_dvd hpow (dvd_two_pow_eps hq)
  omega

/-- The paper's logarithmic order bound. -/
lemma eps_log_lower {q : ℕ} (hq : Odd q) :
    Real.log ((q : ℝ) + 1) / Real.log 2 ≤ eps q := by
  have hb : (q : ℝ) + 1 ≤ (2 : ℝ) ^ eps q := by exact_mod_cast modulus_le_pow hq
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (q : ℝ) + 1) hb
  rw [Real.log_pow] at hl
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

lemma eps_tendsto (q : ℕ → ℕ) (ho : ∀ N, Odd (q N))
    (hq : Tendsto q atTop atTop) : Tendsto (fun N => eps (q N)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [hq.eventually_ge_atTop (2 ^ b + 1)] with N hN
  have hle := modulus_le_pow (ho N)
  by_contra hb
  have he : eps (q N) ≤ b := by omega
  have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) he
  omega

lemma cnt_le (I J L q : ℕ) (hq : Odd q) :
    cnt (I + 1) J L q ≤ (L : ℝ) ^ (I + J) * ((L : ℝ) / eps q + 1) := by
  rw [cnt, U1466Display17.sum_cons]
  have key (ν : Fin I → Fin L) (μ : Fin J → Fin L) :
      (∑ x : Fin L, if sv (Fin.cons x ν) = sv μ then (0 : ℝ) else
        if (q : ℤ) ∣ ((sv (Fin.cons x ν) : ℤ) - sv μ) then 1 else 0) ≤
        (L : ℝ) / eps q + 1 := by
    have e (x : Fin L) : ((sv (Fin.cons x ν) : ℤ) - sv μ) =
        hval ((sv μ : ℤ) - sv ν) x := by
      rw [U1466Display17.sv_cons]; unfold hval; push_cast; ring
    have hc : (∑ x : Fin L, if sv (Fin.cons x ν) = sv μ then (0 : ℝ) else
        if (q : ℤ) ∣ ((sv (Fin.cons x ν) : ℤ) - sv μ) then 1 else 0) =
        (cntX L q ((sv μ : ℤ) - sv ν) : ℝ) := by
      unfold cntX
      rw [← Finset.sum_boole]
      refine sum_congr rfl fun x _ => ?_
      have hz : sv (Fin.cons x ν) = sv μ ↔ hval ((sv μ : ℤ) - sv ν) x = 0 := by
        rw [← e x, sub_eq_zero, Nat.cast_inj]
      by_cases hs : sv (Fin.cons x ν) = sv μ
      · simp [hs, hz.mp hs]
      · have hn : hval ((sv μ : ℤ) - sv ν) x ≠ 0 := fun hx => hs (hz.mpr hx)
        simp [hs, hn, e x]
    rw [hc]
    have hb := cntX_le (L := L) hq ((sv μ : ℤ) - sv ν)
    split_ifs at hb <;> linarith
  calc _ = ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L,
        ∑ x : Fin L, if sv (Fin.cons x ν) = sv μ then (0 : ℝ) else
          if (q : ℤ) ∣ ((sv (Fin.cons x ν) : ℤ) - sv μ) then 1 else 0 := by
            exact sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ _ν : Fin I → Fin L, ∑ _μ : Fin J → Fin L,
        ((L : ℝ) / eps q + 1) := sum_le_sum fun ν _ => sum_le_sum fun μ _ => key ν μ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      rw [pow_add]; ring

lemma soffQ_le (I J L q D : ℕ) :
    SOffQ q L I J ≤ 2 * C0 *
      ((∑ d ∈ range (D + 1), wt d) * cnt I J L q + T17 I J L D) := by
  have hp (ν : Fin I → Fin L) (μ : Fin J → Fin L) :
      (if sv ν = sv μ then (0 : ℝ) else
        if (q : ℤ) ∣ ((sv ν : ℤ) - sv μ) then
          singS ((sv ν : ℤ) - sv μ) else 0) ≤
      2 * C0 *
        ((∑ d ∈ range (D + 1), wt d) *
          (if sv ν = sv μ then 0 else if (q : ℤ) ∣ ((sv ν : ℤ) - sv μ) then 1 else 0) +
          (if sv ν = sv μ then 0 else
            ∑ d ∈ ((sv ν : ℤ) - sv μ).natAbs.divisors.filter (fun d => D < d), wt d)) := by
    by_cases hs : sv ν = sv μ
    · simp [hs]
    simp only [ite_eq_right hs]
    have ht : 0 ≤ ∑ d ∈ ((sv ν : ℤ) - sv μ).natAbs.divisors.filter (fun d => D < d), wt d :=
      sum_nonneg fun d _ => wt_nonneg d
    by_cases hq : (q : ℤ) ∣ ((sv ν : ℤ) - sv μ)
    · simp only [ite_eq_left hq, mul_one]
      rw [singS_expand _ (sub_ne_zero.mpr (by exact_mod_cast hs)) (even_h ν μ),
        split_tuple D _ (sub_ne_zero.mpr (by exact_mod_cast hs))]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) C0_nonneg)
      exact add_le_add (sum_le_sum fun d _ => by split_ifs <;> simp [wt_nonneg]) le_rfl
    · simp only [ite_eq_right hq, mul_zero, zero_add]
      exact mul_nonneg (mul_nonneg (by norm_num) C0_nonneg) ht
  unfold SOffQ
  calc _ ≤ ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L,
      2 * C0 *
        ((∑ d ∈ range (D + 1), wt d) *
          (if sv ν = sv μ then 0 else if (q : ℤ) ∣ ((sv ν : ℤ) - sv μ) then 1 else 0) +
          (if sv ν = sv μ then 0 else
            ∑ d ∈ ((sv ν : ℤ) - sv μ).natAbs.divisors.filter (fun d => D < d), wt d)) :=
      sum_le_sum fun ν _ => sum_le_sum fun μ _ => hp ν μ
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]; rfl

lemma normalized_le (i j : Fin 3) (L q D : ℕ) (hq : Odd q) (hL : 0 < L) :
    SOffQ q L ((i : ℕ) + 1) ((j : ℕ) + 1) / (L : ℝ) ^ ((i : ℕ) + j + 2) ≤
      2 * C0 * ((∑ d ∈ range (D + 1), wt d) * (1 / (eps q : ℝ) + 1 / L) +
        Lhs17 ((i : ℕ) + 1) ((j : ℕ) + 1) L D) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have heR : (eps q : ℝ) ≠ 0 := by exact_mod_cast (eps_pos hq).ne'
  have h1 := soffQ_le ((i : ℕ) + 1) ((j : ℕ) + 1) L q D
  have h2 := cnt_le (i : ℕ) ((j : ℕ) + 1) L q hq
  have hw : 0 ≤ ∑ d ∈ range (D + 1), wt d := sum_nonneg fun d _ => wt_nonneg d
  have h3 := mul_le_mul_of_nonneg_left h2 hw
  have hC : 0 ≤ 2 * C0 := mul_nonneg (by norm_num) C0_nonneg
  have h4 := mul_le_mul_of_nonneg_left (add_le_add h3
    (le_refl (T17 ((i : ℕ) + 1) ((j : ℕ) + 1) L D))) hC
  apply (div_le_iff₀ (by positivity)).mpr
  calc _ ≤ 2 * C0 * ((∑ d ∈ range (D + 1), wt d) *
        ((L : ℝ) ^ ((i : ℕ) + ((j : ℕ) + 1)) * ((L : ℝ) / eps q + 1)) +
        T17 ((i : ℕ) + 1) ((j : ℕ) + 1) L D) := h1.trans h4
    _ = _ := by
      unfold Lhs17
      have he : (i : ℕ) + 1 + ((j : ℕ) + 1) = (i : ℕ) + j + 2 := by omega
      rw [he]
      have hp : (L : ℝ) ^ ((i : ℕ) + j + 2) =
          (L : ℝ) ^ ((i : ℕ) + ((j : ℕ) + 1)) * L := by
        rw [show (i : ℕ) + j + 2 = ((i : ℕ) + ((j : ℕ) + 1)) + 1 by omega, pow_succ]
      rw [hp]
      field_simp

/-- Display 18 with precisely the existing normalization. -/
theorem lemma31_18 : Lemma31_18 := by
  intro i j q ho hq δ hδ
  let K : ℝ := 2 * C0
  have hK : 0 ≤ K := mul_nonneg (by norm_num) C0_nonneg
  let η : ℝ := δ / (2 * (K + 1))
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨D, hD⟩ := display17_lim display17 i j η hη
  let W : ℝ := ∑ d ∈ range (D + 1), wt d
  have hi : Tendsto (fun N => 1 / (eps (q N) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (eps_tendsto q ho hq)
  have hl : Tendsto (fun N => 1 / (Lfun N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp Lfun_tendsto
  have hsmall : Tendsto (fun N => W * (1 / (eps (q N) : ℝ) + 1 / (Lfun N : ℝ)))
      atTop (𝓝 0) := by simpa using (hi.add hl).const_mul W
  filter_upwards [hsmall.eventually (gt_mem_nhds hη), Lfun_tendsto.eventually hD,
    Lfun_tendsto.eventually_ge_atTop 1] with N hs ht hL
  have hb := normalized_le i j (Lfun N) (q N) D (ho N) (by omega)
  have hsum : W * (1 / (eps (q N) : ℝ) + 1 / (Lfun N : ℝ)) +
      Lhs17 ((i : ℕ) + 1) ((j : ℕ) + 1) (Lfun N) D ≤ 2 * η := by linarith
  have hfin : K * (2 * η) ≤ δ := by
    have hp : 0 < 2 * (K + 1) := by positivity
    dsimp [η]
    rw [show K * (2 * (δ / (2 * (K + 1)))) =
      (K * 2 * δ) / (2 * (K + 1)) by ring]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hbound := hb.trans ((mul_le_mul_of_nonneg_left hsum hK).trans hfin)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (Lfun N : ℝ) ^ ((i : ℕ) + j + 2))).mp hbound

/-- The six power conclusion is CONDITIONAL ON Lemma41 for every positive error,
Prop32 Bdef, Display31, MinorSup1924, the arc conditions and the cited constants.
The Lemma31_18 hypothesis of r6_lower10 is discharged. -/
theorem r6_lower11 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814)
    (h32 : Prop32 Bdef (fun i j => (LiLiu.Astar i j : ℝ) + T i j)) :
    ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      (∀ ε > 0, Lemma41 κ P ε) →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) :=
  r6_lower10 T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 lemma31_18 h32

/-- An odd modulus sequence tending to infinity. -/
lemma modulus_instance : (∀ N : ℕ, Odd (2 * N + 1)) ∧
    Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
  refine ⟨fun N => ⟨N, by omega⟩, ?_⟩
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  omega

/-- A concrete instance of the count bound. -/
lemma count_instance : cnt 1 1 4 3 ≤ 4 * (4 / (eps 3 : ℝ) + 1) := by
  simpa using cnt_le 0 1 4 3 (by decide)

/-- A concrete specialization of display 18. -/
lemma display18_instance (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, SOffQ (2 * N + 1) (Lfun N) 1 1 ≤ δ * (Lfun N : ℝ) ^ 2 :=
  lemma31_18 0 0 (fun N => 2 * N + 1) modulus_instance.1 modulus_instance.2 δ hδ

end LeanLab.Linnik.Task37Display18

