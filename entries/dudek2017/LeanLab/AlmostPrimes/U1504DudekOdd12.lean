module

public import LeanLab.AlmostPrimes.U1445DudekOdd

/-!
# Dudek 2017, the odd half from `10⁹` with one modulus `12`, U-1504, run 20261023T1343Z-19109

AI wrote the Lean code. KNOWN mathematics, Dudek 2017 Theorem 1, arXiv 1410.7459. Goldbach is OPEN.

U-1445 proved the odd half from `10⁹` CONDITIONAL ON `BMORCor16`, Bennett, Martin, O'Bryant,
Rechnitzer 2018 Corollary 1.6, used at `q = 4` for a lower bound and at `q = 4r²`, `3 ≤ r ≤ 17`,
for upper bounds. This module needs only a LOWER bound at the single modulus `12`:

* `AP12Lower c`: every class `a mod 12` with `gcd(a, 12) = 1` holds more than `c x / log x` primes
  `p ≤ x`, for every integer `x ≥ 10⁹`.
* For odd `N` pick the class `a mod 12` with `a ≡ N + 2 mod 4` and `a ≢ 0, N mod 3`. Then for
  `p ≡ a mod 12`, `p ≤ N`, the number `N - p` is `2 mod 4` and prime to `3`, so the primes `2` and
  `3` never divide it squared. The prime `3` is removed by the choice of class, not by a sieve
  bound, which is what defeats the parity barrier that U-1437 met at `r = 3`.
* Bad `p` with `r² ∣ N - p`: for `5 ≤ r ≤ 17` they lie in one class mod `12r²`, bounded by the
  lab's PROVED large sieve Brun-Titchmarsh `brun_titchmarsh_ap_pow`, `φ(12r²) = 4r(r - 1)`; for
  `r ≥ 19` and the tail, `U1445DudekOdd.bad_sum_ge19`, PROVED.
* Budget: `0.0743 + 0.0230 + 0.11 + 0.0004 < 0.21` times `N / log N`.

`dudek_odd_from_1e9_ap12`: every odd `N > 10⁹` is `p + (N - p)`, `p < N` prime, `N - p`
square-free, CONDITIONAL ON `AP12Lower 0.21` only. `ap12Lower_of_bmor`: `BMORCor16` implies
`AP12Lower 0.21`, so the new input is strictly weaker than the old one.
-/

@[expose] public section


open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.U1504DudekOdd12

open LeanLab.AlmostPrimes.DudekLarge LeanLab.AlmostPrimes.DudekFrom4e18
open LeanLab.AlmostPrimes.DudekGroups LeanLab.AlmostPrimes.DudekFrom1e9
open LeanLab.AlmostPrimes.U1445DudekOdd

/-- **Cited input, weakened.** For every `a` prime to `12` and every integer `x ≥ 10⁹`, the
primes `p ≤ x` with `p ≡ a mod 12` number more than `c x / log x`. At `c = 1/4` this is the lower
half of Bennett, Martin, O'Bryant, Rechnitzer 2018 Corollary 1.6 at `q = 12`; the module uses
`c = 0.21`. -/
def AP12Lower (c : ℝ) : Prop :=
  ∀ a x : ℕ, Nat.Coprime a 12 → 10 ^ 9 ≤ x →
    c * (x : ℝ) / Real.log x < ((primesAP x 12 a).card : ℝ)

/-- `BMORCor16` implies `AP12Lower 0.21`. -/
theorem ap12Lower_of_bmor (hB : BMORCor16) : AP12Lower 0.21 := by
  intro a x ha hx
  have h := (hB 12 a x (by norm_num) (by norm_num) ha (le_trans (by norm_num) hx)).1
  have ht : ((Nat.totient 12 : ℕ) : ℝ) = 4 := by
    have : Nat.totient 12 = 4 := by decide
    rw [this]; norm_num
  rw [ht] at h
  have hxR : (10 ^ 9 : ℝ) ≤ x := by exact_mod_cast hx
  have hL := log_ge_207 hxR
  have hLpos : 0 < Real.log x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have e : 0.21 * (x : ℝ) / Real.log x ≤ (x : ℝ) / (4 * Real.log x) := by
    rw [div_le_div_iff₀ hLpos (by positivity)]
    nlinarith
  linarith

/-- `φ(12r²) = 4r(r - 1)` for a prime `r ≥ 5`. -/
lemma totient_twelve_sq {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    (12 * r ^ 2).totient = 4 * r * (r - 1) := by
  have hnd : ¬ r ∣ 12 := by
    intro h
    have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) h
    interval_cases r <;> first | (norm_num at h; done) | (norm_num at hr; done)
  have hc : Nat.Coprime 12 (r ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hr).mpr hnd).symm
  have h12 : Nat.totient 12 = 4 := by decide
  rw [Nat.totient_mul hc, h12, Nat.totient_prime_pow hr two_pos, show 2 - 1 = 1 from rfl, pow_one]
  ring

/-- **Brun-Titchmarsh for `Icc 1 N`, any modulus.** From the lab's `brun_titchmarsh_ap_pow` at
`x = 0`, `y = N`. -/
theorem ap_card_pow {N k c : ℕ} (hk : 1 ≤ k) (h2 : 2 * k ≤ N)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    {lam : ℝ} (hlam : 0 < lam) (hlt : lam ≤ Real.log ((N : ℝ) / (k : ℝ))) :
    (((Icc 1 N).filter (fun p => p.Prime ∧ p % k = c % k)).card : ℝ) ≤ (N : ℝ) ^ θ +
      1 / θ * (N : ℝ) * (1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam))) /
        (lam * (k.totient : ℝ)) := by
  have hbt := LeanLab.PNTPort.LargeSieve.brun_titchmarsh_ap_pow 0 N k c hk h2 hθ0
  have hI : Ioc 0 (0 + N) = Icc 1 N := by ext p; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI] at hbt
  set t : ℝ := (N : ℝ) / (k : ℝ) with ht
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hk0]; exact_mod_cast h2
  have ht0 : 0 < t := by linarith
  have hlogt : lam ≤ Real.log t := hlt
  have htN : t ≤ N := by
    rw [ht, div_le_iff₀ hk0]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hsplit : t ^ (2 * θ) = t * t ^ (2 * θ - 1) := by
    rw [show 2 * θ = 1 + (2 * θ - 1) by ring, Real.rpow_add ht0, Real.rpow_one]; ring_nf
  have hneg : t ^ (2 * θ - 1) ≤ exp (-((1 - 2 * θ) * lam)) := by
    rw [Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr
    have : 0 < 1 - 2 * θ := by linarith
    nlinarith
  have hinv : 1 / t ≤ exp (-lam) := by
    have : exp lam ≤ t := by
      calc exp lam ≤ exp (Real.log t) := Real.exp_le_exp.mpr hlogt
        _ = t := Real.exp_log ht0
    rw [Real.exp_neg, div_le_iff₀ ht0, inv_mul_eq_div, le_div_iff₀ (exp_pos _)]; linarith
  have hφ : (0 : ℝ) < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 hk
  have hkt : (k : ℝ) * t = (N : ℝ) := by
    rw [ht, mul_div_cancel₀ _ hk0.ne']
  have hmain : (k : ℝ) * (t + 2 + 2 * t ^ (2 * θ)) =
      (N : ℝ) * (1 + 2 * (1 / t) + 2 * t ^ (2 * θ - 1)) := by
    rw [hsplit, ← hkt]; field_simp
  have hfac : 1 + 2 * (1 / t) + 2 * t ^ (2 * θ - 1) ≤
      1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam)) := by linarith
  have hpow1 : t ^ θ ≤ (N : ℝ) ^ θ := Real.rpow_le_rpow ht0.le htN hθ0.le
  have hlogt0 : 0 < Real.log t := lt_of_lt_of_le hlam hlogt
  calc (((Icc 1 N).filter (fun p => p.Prime ∧ p % k = c % k)).card : ℝ)
      ≤ t ^ θ + (k : ℝ) * (t + 2 + 2 * t ^ (2 * θ)) / (θ * ((k.totient : ℝ) * Real.log t)) := by
        exact_mod_cast hbt
    _ = t ^ θ + 1 / θ * (N : ℝ) * (1 + 2 * (1 / t) + 2 * t ^ (2 * θ - 1)) /
          (Real.log t * (k.totient : ℝ)) := by
        rw [hmain]; field_simp
    _ ≤ _ := by gcongr

/-- The bad primes of the class `a mod 12` for one prime `r`: `p ≤ N`, `p ≡ a mod 12`,
`r² ∣ N - p`. -/
def D (N a r : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun p => p.Prime ∧ p % 12 = a % 12 ∧ r ^ 2 ∣ N - p)

/-- `D N a r` lies in one class mod `12r²`, for a prime `r ≥ 5`. -/
lemma D_sub {N a r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (p₀ : ℕ) (hp₀ : p₀ ∈ D N a r) :
    D N a r ⊆ (Icc 1 N).filter (fun p => p.Prime ∧ p % (12 * r ^ 2) = p₀ % (12 * r ^ 2)) := by
  have hnd : ¬ r ∣ 12 := by
    intro h
    have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) h
    interval_cases r <;> first | (norm_num at h; done) | (norm_num at hr; done)
  have hc : Nat.Coprime 12 (r ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hr).mpr hnd).symm
  intro p hp
  rw [D, mem_filter, mem_Icc] at hp hp₀
  obtain ⟨⟨hp1, hpN⟩, hpp, hp12, hpd⟩ := hp
  obtain ⟨⟨-, hp₀N⟩, -, hp₀12, hp₀d⟩ := hp₀
  rw [mem_filter, mem_Icc]
  refine ⟨⟨hp1, hpN⟩, hpp, ?_⟩
  have h1 : p ≡ p₀ [MOD 12] := by unfold Nat.ModEq; omega
  have h2 : p ≡ p₀ [MOD r ^ 2] := by
    have a1 : p ≡ N [MOD r ^ 2] := (Nat.modEq_iff_dvd' hpN).mpr hpd
    have a2 : p₀ ≡ N [MOD r ^ 2] := (Nat.modEq_iff_dvd' hp₀N).mpr hp₀d
    exact a1.trans a2.symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h1, h2⟩

/-- **One bad set, from Brun-Titchmarsh at modulus `12r²`.** -/
theorem D_card_le {N a r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (h2 : 24 * r ^ 2 ≤ N)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    {lam : ℝ} (hlam : 0 < lam) (hlt : lam ≤ Real.log ((N : ℝ) / ((12 * r ^ 2 : ℕ) : ℝ))) :
    ((D N a r).card : ℝ) ≤ (N : ℝ) ^ θ +
      1 / θ * (N : ℝ) * (1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam))) /
        (lam * (4 * (r : ℝ) * ((r : ℝ) - 1))) := by
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast h5
  have hmain0 : 0 ≤ (N : ℝ) ^ θ +
      1 / θ * (N : ℝ) * (1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam))) /
        (lam * (4 * (r : ℝ) * ((r : ℝ) - 1))) := by
    have : 0 < 4 * (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity
  rcases (D N a r).eq_empty_or_nonempty with h | ⟨p₀, hp₀⟩
  · rw [h, card_empty, Nat.cast_zero]; exact hmain0
  · have hsub := D_sub hr h5 p₀ hp₀
    have hk : 1 ≤ 12 * r ^ 2 := by have : 0 < r ^ 2 := by positivity
                                   linarith
    have hbt := ap_card_pow (c := p₀) hk (by linarith) hθ0 hθ1 hlam hlt
    rw [totient_twelve_sq hr h5] at hbt
    have hcast : (((4 * r * (r - 1) : ℕ)) : ℝ) = 4 * (r : ℝ) * ((r : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at hbt
    have hc : ((D N a r).card : ℝ) ≤
        (((Icc 1 N).filter (fun p => p.Prime ∧ p % (12 * r ^ 2) = p₀ % (12 * r ^ 2))).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    linarith

/-- **One group of small primes `r`.** -/
lemma group12_le {N a : ℕ} (hL : 20.7 ≤ Real.log N) (T : Finset ℕ) {b lb θ F k w : ℝ}
    (hT : ∀ r ∈ T, r.Prime ∧ 5 ≤ r ∧ 24 * r ^ 2 ≤ N ∧ ((12 * r ^ 2 : ℕ) : ℝ) ≤ b)
    (hlb : Real.log b ≤ lb) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hlam0 : 0 < 20.7 - lb)
    (hF : ∀ lam : ℝ, 20.7 - lb ≤ lam →
      1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam)) ≤ F)
    (hk : 20.7 ≤ k * (20.7 - lb)) (hk1 : 1 ≤ k)
    (hw : ∑ r ∈ T, (1 : ℝ) / (4 * (r : ℝ) * ((r : ℝ) - 1)) ≤ w) :
    ∑ r ∈ T, ((D N a r).card : ℝ) ≤
      T.card * (N : ℝ) ^ θ + 1 / θ * (N : ℝ) * F * w * k / Real.log N := by
  set L := Real.log N with hLdef
  set lam := L - lb with hlam
  have hlamge : 20.7 - lb ≤ lam := by rw [hlam]; linarith
  have hlampos : 0 < lam := by linarith
  have hFl := hF lam hlamge
  have hF0 : 0 ≤ F := le_trans (by positivity) hFl
  have hLpos : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by
    by_contra h
    push Not at h
    have : (N : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
    rw [hLdef, this, Real.log_zero] at hL; linarith
  have hper : ∀ r ∈ T, ((D N a r).card : ℝ) ≤ (N : ℝ) ^ θ +
      1 / θ * (N : ℝ) * F / lam * ((1 : ℝ) / (4 * (r : ℝ) * ((r : ℝ) - 1))) := by
    intro r hr
    obtain ⟨hp, h5, h2, hrb⟩ := hT r hr
    have hrR : (5 : ℝ) ≤ r := by exact_mod_cast h5
    have hk0 : (0 : ℝ) < ((12 * r ^ 2 : ℕ) : ℝ) := by
      have : 0 < 12 * r ^ 2 := by positivity
      exact_mod_cast this
    have hlog : lam ≤ Real.log ((N : ℝ) / ((12 * r ^ 2 : ℕ) : ℝ)) := by
      rw [Real.log_div hNpos.ne' hk0.ne', hlam]
      have : Real.log ((12 * r ^ 2 : ℕ) : ℝ) ≤ Real.log b := Real.log_le_log hk0 hrb
      linarith
    have hc := D_card_le (a := a) hp h5 h2 hθ0 hθ1 hlampos hlog
    have hrr : (0 : ℝ) < 4 * (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    calc ((D N a r).card : ℝ) ≤ _ := hc
      _ ≤ (N : ℝ) ^ θ + 1 / θ * (N : ℝ) * F / (lam * (4 * (r : ℝ) * ((r : ℝ) - 1))) := by
          gcongr
      _ = _ := by field_simp
  have hw0 : 0 ≤ w := le_trans (sum_nonneg (fun r hr => by
    obtain ⟨-, h5, -, -⟩ := hT r hr
    have hrR : (5 : ℝ) ≤ r := by exact_mod_cast h5
    have : (0 : ℝ) < 4 * (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity)) hw
  calc ∑ r ∈ T, ((D N a r).card : ℝ)
      ≤ ∑ r ∈ T, ((N : ℝ) ^ θ + 1 / θ * (N : ℝ) * F / lam *
          ((1 : ℝ) / (4 * (r : ℝ) * ((r : ℝ) - 1)))) := sum_le_sum hper
    _ = T.card * (N : ℝ) ^ θ + 1 / θ * (N : ℝ) * F / lam *
          ∑ r ∈ T, (1 : ℝ) / (4 * (r : ℝ) * ((r : ℝ) - 1)) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
    _ ≤ T.card * (N : ℝ) ^ θ + 1 / θ * (N : ℝ) * F / lam * w := by
        gcongr
    _ ≤ T.card * (N : ℝ) ^ θ + 1 / θ * (N : ℝ) * F * w * k / L := by
        have hkl : L ≤ k * lam := by rw [hlam]; nlinarith
        have : 1 / lam ≤ k / L := by
          rw [div_le_div_iff₀ hlampos hLpos]; linarith
        have hA : 0 ≤ 1 / θ * (N : ℝ) * F * w := by positivity
        calc T.card * (N : ℝ) ^ θ + 1 / θ * (N : ℝ) * F / lam * w
            = T.card * (N : ℝ) ^ θ + (1 / θ * (N : ℝ) * F * w) * (1 / lam) := by ring
          _ ≤ T.card * (N : ℝ) ^ θ + (1 / θ * (N : ℝ) * F * w) * (k / L) := by gcongr
          _ = _ := by ring

/-- **The class mod 12.** For odd `N` there is `a < 12` prime to `12` such that every `p ≤ N`
with `p ≡ a mod 12` has `N - p ≡ 2 mod 4` and `3 ∤ N - p`. -/
lemma exists_class12 {N : ℕ} (hO : Odd N) :
    ∃ a, Nat.Coprime a 12 ∧
      ∀ p, p ≤ N → p % 12 = a % 12 → (N - p) % 4 = 2 ∧ (N - p) % 3 ≠ 0 := by
  have hN2 : N % 2 = 1 := Nat.odd_iff.mp hO
  have h12 : N % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hcases : N % 12 = 1 ∨ N % 12 = 3 ∨ N % 12 = 5 ∨ N % 12 = 7 ∨ N % 12 = 9 ∨
      N % 12 = 11 := by omega
  rcases hcases with h | h | h | h | h | h
  · exact ⟨11, by decide, fun p hp hpa => ⟨by omega, by omega⟩⟩
  · exact ⟨1, by decide, fun p hp hpa => ⟨by omega, by omega⟩⟩
  · exact ⟨7, by decide, fun p hp hpa => ⟨by omega, by omega⟩⟩
  · exact ⟨5, by decide, fun p hp hpa => ⟨by omega, by omega⟩⟩
  · exact ⟨7, by decide, fun p hp hpa => ⟨by omega, by omega⟩⟩
  · exact ⟨1, by decide, fun p hp hpa => ⟨by omega, by omega⟩⟩

/-- **Counting step.** If no prime `p < N` has `N - p` square-free, then the primes `p ≤ N` with
`p ≡ a mod 12`, for a class as in `exists_class12`, lie in the sets `D N a r` for the primes
`5 ≤ r ≤ 17`, the classes `N mod r²` for the primes `18 ≤ r ≤ Q`, or the tail. -/
theorem card_le_of_no_rep_12 {N a : ℕ} (Q : ℕ)
    (ha : ∀ p, p ≤ N → p % 12 = a % 12 → (N - p) % 4 = 2 ∧ (N - p) % 3 ≠ 0)
    (hno : ¬ ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p)) :
    ((primesAP N 12 a).card : ℝ) ≤
      ∑ r ∈ (Icc 5 17).filter Nat.Prime, ((D N a r).card : ℝ) +
      ∑ r ∈ (Icc 18 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
        ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by
  classical
  set A := primesAP N 12 a with hA
  set B0 := ((Icc 5 17).filter Nat.Prime).biUnion (fun r => D N a r) with hB0
  set B1 := ((Icc 18 Q).filter Nat.Prime).biUnion (fun r => cls N r) with hB1
  set B2 := (Ioc Q N).biUnion (fun n => (range N).filter (fun p => n ^ 2 ∣ N - p)) with hB2
  have hsub : A ⊆ B0 ∪ B1 ∪ B2 := by
    intro p hp
    rw [hA, primesAP, mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hp, h12⟩ := hp
    obtain ⟨h4, h3⟩ := ha p hpN h12
    have hpN' : p < N := by omega
    have hm : ¬ Squarefree (N - p) := fun hsq => hno ⟨p, hp, hpN', hsq⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hm
    push Not at hm
    obtain ⟨r, hr, hrr⟩ := hm
    have hr2 : r ≠ 2 := by
      rintro rfl
      obtain ⟨m, hm⟩ := hrr
      omega
    have hr3 : r ≠ 3 := by
      rintro rfl
      obtain ⟨m, hm⟩ := hrr
      omega
    have hr5 : 5 ≤ r := by
      have := hr.two_le
      by_contra hc
      have : r = 4 := by omega
      subst this; norm_num at hr
    have hrr' : r ^ 2 ∣ N - p := by rw [sq]; exact hrr
    rw [mem_union, mem_union]
    by_cases h17 : r ≤ 17
    · left; left
      rw [hB0, mem_biUnion]
      refine ⟨r, by rw [mem_filter, mem_Icc]; exact ⟨⟨hr5, h17⟩, hr⟩, ?_⟩
      rw [D, mem_filter, mem_Icc]
      exact ⟨⟨hp1, hpN⟩, hp, h12, hrr'⟩
    · by_cases hQr : r ≤ Q
      · left; right
        rw [hB1, mem_biUnion]
        refine ⟨r, by rw [mem_filter, mem_Icc]; exact ⟨⟨by omega, hQr⟩, hr⟩, ?_⟩
        rw [cls, mem_filter, mem_Icc]
        refine ⟨⟨hp1, by omega⟩, hp, ?_⟩
        exact ((Nat.modEq_iff_dvd' hpN).mpr hrr')
      · right
        rw [hB2, mem_biUnion]
        have hpos : 0 < N - p := by omega
        have hrle : r ≤ N - p := by
          have := Nat.le_of_dvd hpos hrr
          nlinarith
        refine ⟨r, by rw [mem_Ioc]; omega, ?_⟩
        rw [mem_filter, mem_range]
        exact ⟨hpN', hrr'⟩
  have hcard : A.card ≤
      ∑ r ∈ (Icc 5 17).filter Nat.Prime, (D N a r).card +
      ∑ r ∈ (Icc 18 Q).filter Nat.Prime, (cls N r).card + ∑ n ∈ Ioc Q N, N / n ^ 2 := by
    calc A.card ≤ (B0 ∪ B1 ∪ B2).card := card_le_card hsub
      _ ≤ (B0 ∪ B1).card + B2.card := card_union_le _ _
      _ ≤ B0.card + B1.card + B2.card := by
          have := card_union_le B0 B1; omega
      _ ≤ _ := by
        apply add_le_add (add_le_add card_biUnion_le card_biUnion_le)
        exact card_biUnion_le.trans (sum_le_sum fun n _ => card_dvd_sub_le N n)
  exact_mod_cast hcard

set_option maxHeartbeats 4000000 in
/-- **The small primes `5 ≤ r ≤ 17`, from `10⁹`.** -/
theorem small12_le (N a : ℕ) (hN : (10 ^ 9 : ℝ) ≤ N) :
    ∑ r ∈ (Icc 5 17).filter Nat.Prime, ((D N a r).card : ℝ) ≤ 0.0977 * N / Real.log N := by
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 20.7 ≤ L := log_ge_207 hN
  have hLpos : 0 < L := by linarith
  have hN9' : ((1000000000 : ℕ) : ℝ) ≤ N := by push_cast; linarith
  have hN9 : 1000000000 ≤ N := by exact_mod_cast hN9'
  have hsmall : (Icc 5 17).filter Nat.Prime = {5, 7} ∪ {11, 13, 17} := by decide
  rw [hsmall, sum_union (by decide)]
  -- group {5, 7}
  have lb1 : Real.log 588 ≤ 6.3770 := by
    have := log_le_pow2 588 (by norm_num) 5 46 (by norm_num) (by norm_num)
    linarith [show (46 : ℝ) / 5 * 0.6931471808 ≤ 6.3770 by norm_num]
  have G1 := group12_le (N := N) (a := a) hL ({5, 7} : Finset ℕ) (b := 588) (lb := 6.3770)
    (θ := 39/100) (F := 1.0858) (k := 1.4453) (w := 0.018453)
    (by intro r hr; simp only [mem_insert, mem_singleton] at hr
        rcases hr with h | h <;> subst h <;> exact ⟨by norm_num, by norm_num, by norm_num; omega, by norm_num⟩)
    lb1 (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 14 (x := lam) (y₀ := (20.7 - 6.3770)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (39/100 : ℝ)) * lam)
        (y₀ := (1 - 2 * (39/100 : ℝ)) * (20.7 - 6.3770)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 14 * (1 + ((20.7 - 6.3770) - (14 : ℕ)) +
          ((20.7 - 6.3770) - (14 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (39/100 : ℝ)) * (20.7 - 6.3770) - (3 : ℕ)) +
          ((1 - 2 * (39/100 : ℝ)) * (20.7 - 6.3770) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0858 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_insert, Finset.sum_singleton])
  have C1 := count_term hNpos hLdef hL ({5, 7} : Finset ℕ) 2 (by decide)
    (cnt_le' 2 (a := 1 - 39/100) (c := 0.0029) (E₀ := 296000) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 39/100) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group {11, 13, 17}
  have lb2 : Real.log 3468 ≤ 8.1792 := by
    have := log_le_pow2 3468 (by norm_num) 5 59 (by norm_num) (by norm_num)
    linarith [show (59 : ℝ) / 5 * 0.6931471808 ≤ 8.1792 by norm_num]
  have G2 := group12_le (N := N) (a := a) hL ({11, 13, 17} : Finset ℕ) (b := 3468) (lb := 8.1792)
    (θ := 38/100) (F := 1.0992) (k := 1.6533) (w := 0.0047945)
    (by intro r hr; simp only [mem_insert, mem_singleton] at hr
        rcases hr with h | h | h <;> subst h <;>
          exact ⟨by norm_num, by norm_num, by norm_num; omega, by norm_num⟩)
    lb2 (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 12 (x := lam) (y₀ := (20.7 - 8.1792)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (38/100 : ℝ)) * lam)
        (y₀ := (1 - 2 * (38/100 : ℝ)) * (20.7 - 8.1792)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 12 * (1 + ((20.7 - 8.1792) - (12 : ℕ)) +
          ((20.7 - 8.1792) - (12 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (38/100 : ℝ)) * (20.7 - 8.1792) - (3 : ℕ)) +
          ((1 - 2 * (38/100 : ℝ)) * (20.7 - 8.1792) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0992 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_insert, Finset.sum_singleton])
  have C2 := count_term hNpos hLdef hL ({11, 13, 17} : Finset ℕ) 3 (by decide)
    (cnt_le' 3 (a := 1 - 38/100) (c := 0.0037) (E₀ := 355000) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 38/100) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have G1' := mul_le_mul_of_nonneg_right G1 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G1'
  have G2' := mul_le_mul_of_nonneg_right G2 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G2'
  rw [le_div_iff₀ hLpos, add_mul]
  linarith

/-- **Dudek 2017 for odd `N > 10⁹`, CONDITIONAL ON `AP12Lower 0.21`.** Every odd `N > 10⁹` is
`p + (N - p)` with `p < N` prime and `N - p` square-free. -/
theorem dudek_odd_from_1e9_ap12 (hA : AP12Lower 0.21) (N : ℕ) (hO : Odd N) (hN : 10 ^ 9 < N) :
    ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) := by
  by_contra hno
  have hNR : (10 ^ 9 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 20.7 ≤ L := log_ge_207 hNR
  have hLpos : 0 < L := by linarith
  obtain ⟨a, ha12, ha⟩ := exists_class12 hO
  have hlow := hA a N ha12 hN.le
  rw [← hLdef] at hlow
  have hcount := card_le_of_no_rep_12 (80 * ⌈L⌉₊) ha hno
  have hbad := bad_sum_ge19 N hNR
  rw [← hLdef] at hbad
  have hsm := small12_le N a hNR
  rw [← hLdef] at hsm
  have hX : 0 < (N : ℝ) / L := div_pos hNpos hLpos
  have r1 : 0.11 * (N : ℝ) / L = 0.11 * ((N : ℝ) / L) := by ring
  have r2 : 0.0977 * (N : ℝ) / L = 0.0977 * ((N : ℝ) / L) := by ring
  have r3 : 0.21 * (N : ℝ) / L = 0.21 * ((N : ℝ) / L) := by ring
  rw [r1] at hbad
  rw [r2] at hsm
  rw [r3] at hlow
  linarith

/-- **`DudekOddFrom (10^9)` in the form of `U1445DudekAllOdd`, CONDITIONAL ON `BMORCor16`, through
the weaker `AP12Lower 0.21`.** A consistency check that the new route reproduces the old result. -/
theorem dudek_odd_from_1e9_bmor' (hB : BMORCor16) (N : ℕ) (hO : Odd N) (hN : 10 ^ 9 < N) :
    ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) :=
  dudek_odd_from_1e9_ap12 (ap12Lower_of_bmor hB) N hO hN

end LeanLab.AlmostPrimes.U1504DudekOdd12
