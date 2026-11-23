module

public import Mathlib
public import LeanLab.LanguascoPintzZaccagnini2007.Statements

/-!
P0045 Languasco, Pintz, Zaccagnini: elementary steps of the proof, proved without the cited inputs.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.LPZ2007
open Finset Real

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Section 3, page 4, display (7): a mean-square bound over `J(X) = [2X/3, X]` gives
`≪ X^{3/5} L^{10}` exceptions. If `∑ a_N² ≤ K X^{13/5} L^{2k+9}` and every `N ∈ S` has
`|a_N| ≥ N L^{k - 1/2}`, then `|S| ≤ (9/4) K X^{3/5} L^{10}`. -/
theorem count_le_of_sq_sum {S : Finset ℕ} {a : ℕ → ℝ} {X L K : ℝ} {k : ℕ}
    (hX : 0 < X) (hL : 0 < L) (hS : ∀ N ∈ S, 2 * X / 3 ≤ N)
    (ha : ∀ N ∈ S, (N : ℝ) * L ^ ((k : ℝ) - 1 / 2) ≤ |a N|)
    (hsum : ∑ N ∈ S, a N ^ 2 ≤ K * X ^ ((13 : ℝ) / 5) * L ^ (2 * k + 9)) :
    (S.card : ℝ) ≤ 9 / 4 * K * X ^ ((3 : ℝ) / 5) * L ^ 10 := by
  set u : ℝ := L ^ ((k : ℝ) - 1 / 2) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hL _
  have hu2 : u ^ 2 * L ^ 10 = L ^ (2 * k + 9) := by
    have h1 : u ^ 2 = L ^ ((2 * (k : ℝ)) - 1) := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]; congr 1; push_cast; ring
    have h2 : (L : ℝ) ^ 10 = L ^ ((10 : ℕ) : ℝ) := (Real.rpow_natCast L 10).symm
    rw [h1, h2, ← Real.rpow_add hL]
    have : (2 * (k : ℝ) - 1 + ((10 : ℕ) : ℝ)) = ((2 * k + 9 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have hX13 : X ^ ((13 : ℝ) / 5) = X ^ 2 * X ^ ((3 : ℝ) / 5) := by
    have : (13 : ℝ) / 5 = ((2 : ℕ) : ℝ) + 3 / 5 := by push_cast; norm_num
    rw [this, Real.rpow_add hX, Real.rpow_natCast]
  have hterm : ∀ N ∈ S, (2 * X / 3) ^ 2 * u ^ 2 ≤ a N ^ 2 := by
    intro N hN
    have h1 := hS N hN
    have h2 := ha N hN
    have h3 : 2 * X / 3 * u ≤ |a N| :=
      le_trans (mul_le_mul_of_nonneg_right h1 hu0.le) h2
    have h4 : (2 * X / 3 * u) ^ 2 ≤ |a N| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3 2
    rw [sq_abs] at h4
    nlinarith [h4]
  have hcard : (S.card : ℝ) * ((2 * X / 3) ^ 2 * u ^ 2) ≤ ∑ N ∈ S, a N ^ 2 := by
    calc (S.card : ℝ) * ((2 * X / 3) ^ 2 * u ^ 2) = ∑ _N ∈ S, ((2 * X / 3) ^ 2 * u ^ 2) := by
          simp
      _ ≤ _ := Finset.sum_le_sum hterm
  have h1 : (S.card : ℝ) * ((2 * X / 3) ^ 2 * u ^ 2) ≤
      (K * X ^ ((3 : ℝ) / 5) * L ^ 10) * (X ^ 2 * u ^ 2) := by
    have := hcard.trans hsum
    rw [hX13, ← hu2] at this
    nlinarith [this]
  have hc : (0 : ℝ) < X ^ 2 * u ^ 2 := by positivity
  have h2 : ((S.card : ℝ) * (4 / 9)) * (X ^ 2 * u ^ 2) ≤
      (K * X ^ ((3 : ℝ) / 5) * L ^ 10) * (X ^ 2 * u ^ 2) := by
    nlinarith [h1]
  have h3 := le_of_mul_le_mul_right h2 hc
  linarith

/-! ### The bound (19), page 8: `j(d, k, N) ≤ ξ(d)^{k-1}` -/

/-- `j(d, k, N)` of (18), page 8, with `k + 1` exponents: the number of `ν ∈ [1, ξ(d)]^{k+1}` with
`d ∣ N - 2^{ν₁} - … - 2^{ν_{k+1}}`. -/
def jcount (d k N : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin (k + 1) => Icc 1 (xi d))).filter
    (fun ν => (d : ℤ) ∣ (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i)).card

theorem xi_spec {d : ℕ} (hd : Odd d) : 1 ≤ xi d ∧ 2 ^ xi d ≡ 1 [MOD d] := by
  have hne : {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]}.Nonempty := by
    have hcop : Nat.Coprime 2 d := (Nat.coprime_two_left).2 hd
    have hpos : 0 < d := hd.pos
    exact ⟨Nat.totient d, Nat.totient_pos.2 hpos, Nat.ModEq.pow_totient hcop⟩
  exact Nat.sInf_mem hne

theorem xi_le {d μ : ℕ} (h1 : 1 ≤ μ) (h2 : 2 ^ μ ≡ 1 [MOD d]) : xi d ≤ μ :=
  Nat.sInf_le ⟨h1, h2⟩

/-- Distinct powers `2^ν`, `ν ∈ [1, ξ(d)]`, are distinct mod odd `d`. -/
theorem pow_two_inj {d a b : ℕ} (hd : Odd d) (ha : a ∈ Icc 1 (xi d)) (hb : b ∈ Icc 1 (xi d))
    (h : 2 ^ a ≡ 2 ^ b [MOD d]) : a = b := by
  have key : ∀ a b : ℕ, a ∈ Icc 1 (xi d) → b ∈ Icc 1 (xi d) → a < b →
      2 ^ a ≡ 2 ^ b [MOD d] → False := by
    intro a b ha hb hab h
    rw [mem_Icc] at ha hb
    have hcop : Nat.Coprime d (2 ^ a) := Nat.Coprime.pow_right _ ((Nat.coprime_two_right).2 hd)
    have h' : 2 ^ a * 1 ≡ 2 ^ a * 2 ^ (b - a) [MOD d] := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab.le]; exact h
    have h'' := (Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.gcd_comm] using hcop) h').symm
    have := xi_le (d := d) (by omega) h''
    omega
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact (key a b ha hb h1 h).elim
  · exact h1
  · exact (key b a hb ha h1 h.symm).elim

/-- (19), page 8: `j(d, k, N) ≤ ξ(d)^{k-1}` for odd `d`; here with `k + 1` exponents the bound is
`ξ(d)^k`. -/
theorem jcount_le {d : ℕ} (hd : Odd d) (k N : ℕ) : jcount d k N ≤ xi d ^ k := by
  unfold jcount
  have hmaps : ∀ ν ∈ (Fintype.piFinset (fun _ : Fin (k + 1) => Icc 1 (xi d))).filter
      (fun ν => (d : ℤ) ∣ (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i),
      Fin.init ν ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 (xi d)) := by
    intro ν hν
    rw [mem_filter, Fintype.mem_piFinset] at hν
    rw [Fintype.mem_piFinset]
    intro i
    exact hν.1 i.castSucc
  have hinj : Set.InjOn (fun ν : Fin (k + 1) → ℕ => Fin.init ν)
      ((Fintype.piFinset (fun _ : Fin (k + 1) => Icc 1 (xi d))).filter
        (fun ν => (d : ℤ) ∣ (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i) : Finset _) := by
    intro ν hν ν' hν' hi
    simp only [Finset.mem_coe, mem_filter, Fintype.mem_piFinset] at hν hν'
    have hsum : ∑ i : Fin k, (2 : ℤ) ^ ν i.castSucc = ∑ i : Fin k, (2 : ℤ) ^ ν' i.castSucc := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrFun hi i
      simp only [Fin.init] at this
      rw [this]
    have e1 := hν.2
    have e2 := hν'.2
    rw [Fin.sum_univ_castSucc] at e1 e2
    rw [hsum] at e1
    have hdiff : (d : ℤ) ∣ (2 : ℤ) ^ ν (Fin.last k) - (2 : ℤ) ^ ν' (Fin.last k) := by
      have := dvd_sub e2 e1
      convert this using 1; ring
    have hmod : 2 ^ ν (Fin.last k) ≡ 2 ^ ν' (Fin.last k) [MOD d] := by
      rw [Nat.modEq_iff_dvd]
      have := (dvd_neg.2 hdiff)
      convert this using 1; push_cast; ring
    have hl := pow_two_inj hd (hν.1 (Fin.last k)) (hν'.1 (Fin.last k)) hmod
    funext i
    refine Fin.lastCases hl (fun j => ?_) i
    exact congrFun hi j
  calc _ ≤ (Fintype.piFinset (fun _ : Fin k => Icc 1 (xi d))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = xi d ^ k := by simp [Fintype.card_piFinset]

/-! ### Dyadic argument, page 3 -/

/-- The remark after the Theorem, page 3: exceptional sets on the pieces `J(X (2/3)^i)`,
each bounded by `K (X r^i)^{3/5} L^{10}` with `r = 2/3`, add up to `K' X^{3/5} L^{10}`,
`K' = K / (1 - r^{3/5})`, for the bound on `[1, X]`. -/
theorem dyadic_sum {K X L : ℝ} (hK : 0 ≤ K) (hX : 0 ≤ X) (hL : 0 ≤ L) (m : ℕ) :
    ∑ i ∈ range m, K * (X * (2 / 3 : ℝ) ^ i) ^ ((3 : ℝ) / 5) * L ^ 10 ≤
      K / (1 - (2 / 3 : ℝ) ^ ((3 : ℝ) / 5)) * X ^ ((3 : ℝ) / 5) * L ^ 10 := by
  set q : ℝ := (2 / 3 : ℝ) ^ ((3 : ℝ) / 5) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hterm : ∀ i : ℕ, K * (X * (2 / 3 : ℝ) ^ i) ^ ((3 : ℝ) / 5) * L ^ 10 =
      (K * X ^ ((3 : ℝ) / 5) * L ^ 10) * q ^ i := by
    intro i
    have h1 : ((2 / 3 : ℝ) ^ i) ^ ((3 : ℝ) / 5) = q ^ i := by
      rw [hq, Real.rpow_pow_comm (by norm_num)]
    rw [Real.mul_rpow hX (by positivity), h1]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hgeom : ∑ i ∈ range m, q ^ i ≤ 1 / (1 - q) := by
    have h1 := geom_sum_mul_neg q m
    have h2 : 0 < 1 - q := by linarith
    rw [le_div_iff₀ h2, h1]
    have : 0 ≤ q ^ m := by positivity
    linarith
  have hpos : 0 ≤ K * X ^ ((3 : ℝ) / 5) * L ^ 10 := by positivity
  calc _ ≤ (K * X ^ ((3 : ℝ) / 5) * L ^ 10) * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom hpos
    _ = _ := by field_simp

/-! ### The Theorem gives positive weighted counts -/

/-- From the Theorem: with `η = 1/2`, apart from `K X^{3/5} (log X)^10` even `N ≤ X`, `R''_k(N) > 0`.
(`R''_k` is Λ-weighted; this is not yet a count of prime pairs.) -/
theorem main_pos (h : MainTheorem) (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 2 ≤ X →
      (((Icc 1 X).filter (fun N => Even N ∧ ¬ 0 < Rpp k X N)).card : ℝ) ≤
        K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
  obtain ⟨C, hC, K, hKη⟩ := h k hk
  obtain ⟨X₀, hX₀⟩ := hKη (1 / 2) (by norm_num)
  refine ⟨K, X₀, fun X hX hX2 => le_trans ?_ (hX₀ X hX)⟩
  have hL : 0 < Lg X := by
    unfold Lg
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hX2)
  have hsub : ((Icc 1 X).filter (fun N => Even N ∧ ¬ 0 < Rpp k X N)) ⊆ Exc k X C (1 / 2) := by
    intro N hN
    rw [mem_filter, mem_Icc] at hN
    obtain ⟨⟨h1, h2⟩, he, hn⟩ := hN
    rw [Exc, mem_filter, mem_Icc]
    refine ⟨⟨h1, h2⟩, he, ?_⟩
    have hc := hC N he
    have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast h1
    have hLk : 0 < Lg X ^ k := pow_pos hL k
    have hR : Rpp k X N ≤ 0 := not_lt.1 hn
    have : 0 < (C N : ℝ) * N * Lg X ^ k := by
      have : 0 < C N := by linarith [hc.1]
      positivity
    have habs : C N * N * Lg X ^ k - Rpp k X N ≤ |Rpp k X N - C N * N * Lg X ^ k| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have : 1 / 2 * N * Lg X ^ k < C N * N * Lg X ^ k := by
      have : (1 : ℝ) / 2 < C N := by linarith [hc.1]
      have := mul_pos (by linarith : (0 : ℝ) < N) hLk
      nlinarith
    linarith
  exact_mod_cast Finset.card_le_card hsub

end

end LeanLab.LPZ2007
