module

public import LeanLab.ChenExplicit.MertensProduct260
public import LeanLab.ChenExplicit.Decomp1552a
public import LeanLab.ChenExplicit.Reductions
public import LeanLab.RieselVaughan1983.OddSums
public import LeanLab.RieselVaughan1983.Lemma10Sum

/-!
AI-written Lean code, Claude, 2026-10-26, run 20261026T1219Z-15327, unit U-1552, track T1, DECOMPOSE.
T. Yamada 2015, Explicit Chen's theorem, arXiv 1511.03409v2, Section 7, proof of Theorem 7.1.

Codex task161 proof additions, 2026-10-28. AI wrote the Lean code.
Six original leaves have unconditional proofs. Eq123 is CONDITIONAL ON h72.
Task260 derives eq43_V1 CONDITIONAL ON Mertens260.dusart_mertens_upper.
The remaining OPEN leaf in this file is lemma72.

Codex task260 product proof additions, 2026-11-04. AI wrote the Lean code.
The original eq43_V1 statement is unchanged. Its cited Dusart input remains unproved.

Codex task173 proof additions, 2026-10-29. AI wrote the Lean code.
Eq125_phi has an unconditional elementary proof through a finite Euler coefficient bound.

Part b: the sieve side of Theorem 7.1, (107) and (117) to (126), with the explicit
Bombieri-Vinogradov type Lemma 7.2, (99). Every placeholder proof of the lab file is an OPEN LEAF, except
`thm31_upper_applied`, which is Yamada's Theorem 3.1 from his unpublished reference [22] and is
entered as Cited. Proved here, no placeholder proof: `sum_sifted_le`, `abs_r_le`, `eq118`,
`adm_zero`, `lemma72_zero`, the last two vacuity instances.

Corrections built in, see ChenExplicit/STATEMENTS.md, U-1552 block:
* (117) has the coefficient `U_N^(1)` in front of `F(s)/log D`; the printed (40) has `2`,
  the lab's earlier QUESTION; (117) is stated as the proof applies it.
* (123): Lemma 7.2 with `X = N/w_j`, `Y = min{y, (1+ε)w_j}` gives `e^{-144}(1+ε)N / log⁴ Y`;
  (123) prints `log⁴ y`, but `Y ≤ y`. The leaves keep `log⁴ Y_j`, and (124) becomes
  `≤ 1.2 e^{-139} N/(ε log³ N)`, numerically about `1.11 e^{-139}`; Theorem 7.1's `e^{-138}`
  still follows since `2.2 < e`.
* Lemma 7.2 is stated with `Z ≥ z`; the printed `Z > z` fails at `j = 0`, where `Z = z`.
Chen's theorem is known; binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.D1552

open LeanLab.ChenExplicit

/-- `ε₀(N) = 1 / max{57, log log N}`, (47); the same as `Yamada.eps0`. -/
def eps0' (N : ℕ) : ℝ := 1 / max 57 (log (log N))

/-- (46): `q₁` is the largest prime factor of the exceptional modulus `k₁`, and
`q₁ ≥ max{59, 2 + log log N}`; `q₁ = 0` codes `k₁ = 0`, no exceptional modulus. -/
def Adm (N q₁ : ℕ) : Prop := q₁ = 0 ∨ (q₁.Prime ∧ max 59 (2 + log (log N)) ≤ (q₁ : ℝ))

/-- Vacuity instance for `Adm`: `q₁ = 0` is admissible. -/
theorem adm_zero (N : ℕ) : Adm N 0 := Or.inl rfl

/-- `U_N^(1)`, (44) and (131) at `j = 1`: `U_N` times `(q₁-1)/(q₁-2)` when `q₁` is an odd prime
not dividing `N`. -/
def U1 (N q₁ : ℕ) : ℝ :=
  U N * (if q₁.Prime ∧ 2 < q₁ ∧ ¬ q₁ ∣ N then ((q₁ : ℝ) - 1) / ((q₁ : ℝ) - 2) else 1)

/-- `V^(1)(x) = ∏_{p < x, p ∤ N, p ≠ q₁} (1 - ρ(p)/p)` with `ρ(p)/p = 1/(p-1)`, `ρ(2) = 0`. -/
def V1 (N q₁ : ℕ) (x : ℝ) : ℝ :=
  ∏ p ∈ (range ⌈x⌉₊).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N ∧ p ≠ q₁),
    (1 - 1 / ((p : ℝ) - 1))

/-- `N - m` is coprime to `P^(1)(x) = ∏_{p < x, p ∤ N, p ≠ q₁} p`, Section 4. -/
def SiftedZ (N q₁ : ℕ) (x : ℝ) (m : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → (r : ℝ) < x → ¬ r ∣ N → r ≠ q₁ → ¬ (r : ℤ) ∣ (N : ℤ) - m

/-- `S(B^(j), P^(1)(y))`. -/
def SBj (N q₁ : ℕ) (ε : ℝ) (j : ℕ) : ℕ := ((Bj N ε j).filter (SiftedZ N q₁ (y3 N))).card

/-- `B^# = ⋃_j B^(j)`, (107), as products `m`. -/
def BSharp (N : ℕ) (ε : ℝ) : Finset ℕ := (range (Jblk N ε)).biUnion (Bj N ε)

/-- `D = N^{1/2} / log^{10} N`, Section 7. -/
def Dsv (N : ℕ) : ℝ := √(N : ℝ) / log N ^ 10

/-- `d ∣ P^(1)(y)`: `d` squarefree, every prime factor `< y`, not dividing `N`, not `q₁`. -/
def DivP1 (N q₁ : ℕ) (x : ℝ) (d : ℕ) : Prop :=
  Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < x ∧ ¬ p ∣ N ∧ p ≠ q₁

/-- The moduli `d < D`, `d ∣ P^(1)(y)`, of (117) and (123). -/
def Dset (N q₁ : ℕ) : Finset ℕ := (range ⌈Dsv N⌉₊).filter (DivP1 N q₁ (y3 N))

/-- `#{m ∈ B^(j) : d ∣ N - m}`. -/
def cntDiv (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ :=
  (((Bj N ε j).filter fun m => (d : ℤ) ∣ (N : ℤ) - m).card : ℝ)

/-- `#{m ∈ B^(j) : (m, d) = 1}`. -/
def cntCop (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ :=
  (((Bj N ε j).filter fun m => Nat.Coprime m d).card : ℝ)

/-- `r_d^(j) = |B^(j)_d| - |B^(j)|/φ(d)`, (120). -/
def rj (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ := cntDiv N ε j d - ((Bj N ε j).card : ℝ) / d.totient

/-- `r_d^(j,1)`, (121). -/
def r1 (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ := cntDiv N ε j d - cntCop N ε j d / d.totient

/-- `r_d^(j,2)`, (122), up to sign: `#{m ∈ B^(j) : (m, d) > 1} / φ(d)`. -/
def r2 (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ := (((Bj N ε j).card : ℝ) - cntCop N ε j d) / d.totient

/-- `Y_j = min{y, (1+ε)w_j}`, proof of (123). -/
def Yj (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ := min (y3 N) ((1 + ε) * wj N ε j)

/-- Yamada's `F(s) = 2e^γ - s` for `0 ≤ s ≤ 3`, (41); only used at `s = log D / log y < 3`. -/
def F1lin (s : ℝ) : ℝ := 2 * exp eulerMascheroniConstant - s

/-- `r_d^(j) = r_d^(j,1) - r_d^(j,2)`, so `|r_d^(j)| ≤ |r_d^(j,1)| + |r_d^(j,2)|`, (120). PROVED. -/
theorem abs_r_le (N : ℕ) (ε : ℝ) (j d : ℕ) :
    |rj N ε j d| ≤ |r1 N ε j d| + |r2 N ε j d| := by
  have h : rj N ε j d = r1 N ε j d - r2 N ε j d := by
    unfold rj r1 r2; ring
  rw [h]; exact abs_sub _ _

/-- LEAF. Unit U-1552. Yamada 2015, (107), first two inequalities, Section 7: for
`0 < ε < 1/100` and any `q₁`, `S(B, P(y)) ≤ S(B^#, P^(1)(y))`: `B ⊆ B^#` through `b = N - m`,
since `p₁p₂p₃ < N` and `w_j ≤ p₁` give `w_j p₂p₃ < N`, the `J` blocks cover `[z, y)`,
and sifting by fewer primes keeps more elements. -/
theorem eq107_sub (N q₁ : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    SB N (z8 N) (y3 N) ≤ ((BSharp N ε).filter (SiftedZ N q₁ (y3 N))).card := by
  unfold SB
  apply Finset.card_le_card_of_injOn (fun b => N - b)
  · intro b hb
    obtain ⟨hbB, hbS⟩ := mem_filter.mp hb
    obtain ⟨hbN, hbB⟩ := mem_filter.mp hbB
    have hbN : b < N := mem_range.mp hbN
    obtain ⟨p₁, p₂, p₃, hp₁, hp₂, hp₃, hz, hy, hyp₂, hp₂₃, hprod, hcop, hbeq⟩ := hbB
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
    have hrpos : 0 < 1 + ε := by linarith
    obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near
      ((one_le_div hzpos).mpr hz) (show 1 < 1 + ε by linarith)
    have hwlo : wj N ε j ≤ p₁ := by
      unfold wj
      simpa only [mul_comm] using (le_div_iff₀ hzpos).mp hjlo
    have hwhi : (p₁ : ℝ) < (1 + ε) * wj N ε j := by
      have h := (div_lt_iff₀ hzpos).mp hjhi
      simpa only [wj, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
    have hj : j < Jblk N ε := by
      apply Nat.lt_ceil.mpr
      apply (lt_div_iff₀ (log_pos (show 1 < 1 + ε by linarith))).2
      have hp : (1 + ε) ^ j < y3 N / z8 N := hjlo.trans_lt ((div_lt_div_iff_of_pos_right hzpos).mpr hy)
      have hl := log_lt_log (pow_pos hrpos _) hp
      rwa [log_pow] at hl
    have hNb : N - b = p₁ * p₂ * p₃ := by omega
    apply mem_filter.mpr
    constructor
    · apply mem_biUnion.mpr
      refine ⟨j, mem_range.mpr hj, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩⟩
      · change N - b < 2 * N
        omega
      · refine ⟨p₁, p₂, p₃, hp₁, hp₂, hp₃, hz, hy, hyp₂, hp₂₃, ?_, ?_, hwlo, hwhi, hNb⟩
        · have hprodR : (p₁ : ℝ) * p₂ * p₃ < N := by exact_mod_cast hprod
          exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwlo (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans_lt hprodR
        · exact Nat.Coprime.of_dvd_left (dvd_mul_left (p₂ * p₃) p₁) (by simpa only [mul_assoc] using hcop)
    · intro r hr hry hrN hrq hrd
      apply hbS r hr hry hrN
      have heq : (N : ℤ) - (N - b : ℕ) = b := by rw [Int.natCast_sub (by omega)]; ring
      rw [heq] at hrd
      exact_mod_cast hrd
  · intro a ha b hb hab
    have haN := mem_range.mp (mem_filter.mp (mem_filter.mp ha).1).1
    have hbN := mem_range.mp (mem_filter.mp (mem_filter.mp hb).1).1
    change N - a = N - b at hab
    omega

/-- (107), last inequality: `S(B^#, P^(1)(y)) ≤ Σ_j S(B^(j), P^(1)(y))`. PROVED. -/
theorem sum_sifted_le (N q₁ : ℕ) (ε : ℝ) :
    ((BSharp N ε).filter (SiftedZ N q₁ (y3 N))).card ≤
      ∑ j ∈ range (Jblk N ε), SBj N q₁ ε j := by
  unfold BSharp SBj
  rw [Finset.filter_biUnion]
  exact Finset.card_biUnion_le


/-- Finite removal of the primes dividing N and the exceptional prime.
This is the elementary factor comparison in Yamada page 11 eqs 43 and 44. -/
theorem V1_remove_factors (N q₁ : ℕ) (hN0 : N ≠ 0) (x : ℝ) :
    V1 N q₁ x ≤
      (∏ p ∈ (range ⌈x⌉₊).filter (fun p => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) *
      (∏ p ∈ N.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
      (if q₁.Prime ∧ 2 < q₁ ∧ ¬ q₁ ∣ N then ((q₁ : ℝ) - 1) / ((q₁ : ℝ) - 2) else 1) := by
  let S := (range ⌈x⌉₊).filter (fun p => p.Prime ∧ 2 < p)
  let T := N.primeFactors.filter (2 < ·)
  let Q : Finset ℕ := if q₁.Prime ∧ 2 < q₁ ∧ ¬ q₁ ∣ N then {q₁} else ∅
  have hS (p : ℕ) (hp : p ∈ S) : 2 < p := (mem_filter.mp hp).2.2
  have hT (p : ℕ) (hp : p ∈ T) : 2 < p := (mem_filter.mp hp).2
  have hQ (p : ℕ) (hp : p ∈ Q) : 2 < p := by
    dsimp [Q] at hp
    split_ifs at hp with h
    · have he : p = q₁ := mem_singleton.mp hp
      simpa only [he] using h.2.1
    · simp at hp
  have hmemT (p : ℕ) (hp : p ∈ S) : p ∈ T ↔ p ∣ N := by
    have hpr := (mem_filter.mp hp).2.1
    simp only [T, mem_filter, Nat.mem_primeFactors]
    exact ⟨fun h => h.1.2.1, fun hd => ⟨⟨hpr, hd, hN0⟩, hS p hp⟩⟩
  have heq : (range ⌈x⌉₊).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N ∧ p ≠ q₁) =
      (S.filter (fun p => p ∉ T)).filter (fun p => p ∉ Q) := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨hp, hpr, h2, hd, hq⟩
      have hpS : p ∈ S := mem_filter.mpr ⟨hp, hpr, h2⟩
      refine ⟨⟨hpS, fun h => hd ((hmemT p hpS).mp h)⟩, ?_⟩
      dsimp [Q]
      split_ifs <;> simp [hq]
    · rintro ⟨⟨hpS, hpT⟩, hpQ⟩
      obtain ⟨hp, hpr, h2⟩ := mem_filter.mp hpS
      have hd : ¬ p ∣ N := fun hd => hpT ((hmemT p hpS).mpr hd)
      refine ⟨hp, hpr, h2, hd, ?_⟩
      intro he
      subst p
      have helig : q₁.Prime ∧ 2 < q₁ ∧ ¬ q₁ ∣ N := ⟨hpr, h2, hd⟩
      exact hpQ (by simp [Q, helig])
  have hfirst := Mertens260.remove_odd_factors_le S T hS hT
  have hsecond := Mertens260.remove_odd_factors_le
    (S.filter (fun p => p ∉ T)) Q (fun p hp => hS p (mem_filter.mp hp).1) hQ
  have hprodQ : (∏ p ∈ Q, ((p : ℝ) - 1) / ((p : ℝ) - 2)) =
      if q₁.Prime ∧ 2 < q₁ ∧ ¬ q₁ ∣ N then ((q₁ : ℝ) - 1) / ((q₁ : ℝ) - 2) else 1 := by
    dsimp [Q]
    split_ifs <;> simp
  unfold V1
  rw [heq]
  calc
    _ ≤ (∏ p ∈ S.filter (fun p => p ∉ T), (1 - 1 / ((p : ℝ) - 1))) *
        ∏ p ∈ Q, ((p : ℝ) - 1) / ((p : ℝ) - 2) := hsecond
    _ ≤ ((∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))) *
        ∏ p ∈ T, ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        ∏ p ∈ Q, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
      apply mul_le_mul_of_nonneg_right hfirst
      apply prod_nonneg
      intro p hp
      have hpR : (2 : ℝ) < p := by exact_mod_cast hQ p hp
      apply div_nonneg <;> linarith
    _ = _ := by rw [hprodQ]

/-- LEAF. Unit U-1552. Numerical step behind (118), Section 7: for `N > exp exp 36`,
`(1 + 1/(5 log² y)) (1 + 8 log y / y) ≤ 1 + 1/(5 log y)`. -/
theorem eq118_num (N : ℕ) (hN : exp (exp 36) < N) :
    (1 + 1 / (5 * log (y3 N) ^ 2)) * (1 + 8 * log (y3 N) / y3 N) ≤ 1 + 1 / (5 * log (y3 N)) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by
    simpa using log_lt_log (exp_pos _) hN
  have h36 : (3600 : ℝ) < exp 36 := by
    have h := pow_div_factorial_le_exp 36 (by norm_num : (0 : ℝ) ≤ 36) 4
    norm_num at h
    linarith
  set t := log (y3 N)
  have htlog : t = (1 / 3 : ℝ) * log N := log_rpow hNp _
  have ht : 1200 < t := by linarith
  have htp : 0 < t := by linarith
  have hty : exp t = y3 N := exp_log (rpow_pos_of_pos hNp _)
  have hy : 100 * t ^ 2 ≤ exp t := by
    have he := pow_div_factorial_le_exp t htp.le 3
    norm_num at he
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ t - 600 by linarith)]
  rw [← hty]
  apply (mul_le_mul_iff_left₀ (show 0 < 5 * t ^ 2 * exp t by positivity)).mp
  field_simp
  nlinarith [mul_nonneg (show 0 ≤ t - 1 by linarith) (show 0 ≤ exp t - 100 * t ^ 2 by linarith),
    mul_nonneg (sq_nonneg t) (show 0 ≤ t - 2 by linarith)]

/-- LEAF. Unit U-1552. Positivity facts used in (118): for `N > exp exp 36`,
`0 < log y` and `0 < log D` with `D = N^{1/2}/log^{10} N`, and `0 ≤ U_N^(1)`. -/
theorem logs_pos (N q₁ : ℕ) (hN : exp (exp 36) < N) :
    0 < log (y3 N) ∧ 0 < log (Dsv N) ∧ 0 ≤ U1 N q₁ := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have h36 : (3600 : ℝ) < exp 36 := by
    have h := pow_div_factorial_le_exp 36 (by norm_num : (0 : ℝ) ≤ 36) 4
    norm_num at h
    linarith
  have hLp : 0 < log N := by linarith
  have hr := log_div_self_antitoneOn
    (show exp 36 ∈ Set.Ici (exp 1) by simp only [Set.mem_Ici]; exact exp_le_exp.mpr (by norm_num))
    (show log (N : ℝ) ∈ Set.Ici (exp 1) by
      simp only [Set.mem_Ici]; exact (exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 36)).trans hL.le)
    hL.le
  simp only [log_exp] at hr
  have hratio : 36 / exp 36 < (1 / 20 : ℝ) := by
    apply (div_lt_iff₀ (exp_pos _)).2
    linarith
  have hlog : log (log N) < log N / 20 := by
    have h := hr.trans_lt hratio
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (div_lt_iff₀ hLp).mp h
  refine ⟨?_, ?_, ?_⟩
  · change 0 < log ((N : ℝ) ^ ((1 : ℝ) / 3))
    rw [log_rpow hNp]
    positivity
  · unfold Dsv
    rw [log_div (sqrt_pos_of_pos hNp).ne' (pow_pos hLp _).ne', log_sqrt hNp.le, log_pow]
    linarith
  · unfold U1
    apply mul_nonneg (U_pos N).le
    split_ifs with hq
    · have hqR : (2 : ℝ) < q₁ := by exact_mod_cast hq.2.1
      apply div_nonneg <;> linarith
    · norm_num

/-- Lemma 7.2, (99), its conclusion at one choice of residues: for `c : ℕ → ℝ` and residues
`res d` coprime to `d`, `Σ_{d < D*, q₁ ∤ d} |Σ_{n<X} Σ_{Z≤p<Y, np ≡ res d (d)} c(n)
- (1/φ(d)) Σ_{n<X} Σ_{Z≤p<Y, (np,d)=1} c(n)| ≤ e^{-144} XY / log⁴ Y`, `D* = (XY)^{1/2}/log^{10} Y`.
Over all `res` this is the printed `max_{(a,d)=1}` form. -/
def Lemma72At (q₁ : ℕ) (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ) : Prop :=
  ∑ d ∈ (range ⌈√(X * Y) / log Y ^ 10⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d),
      |∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
          (if (n * p : ℕ) ≡ res d [MOD d] then c n else 0) -
        (1 / (d.totient : ℝ)) * ∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
          (if Nat.Coprime (n * p) d then c n else 0)| ≤
    exp (-144) * X * Y / log Y ^ 4

/-- Vacuity instance for `Lemma72At`: it holds for `c = 0`. -/
theorem lemma72_zero (q₁ : ℕ) (res : ℕ → ℕ) (X Y Z : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Lemma72At q₁ (fun _ => 0) res X Y Z := by
  unfold Lemma72At
  simp only [ite_self, sum_const_zero, mul_zero, sub_zero, abs_zero]
  positivity


/-- Weighted product reindexing for Yamada eqs 105 and 120. -/
theorem sum_Bj_bilinear (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100)
    (j : ℕ) (hj : j < Jblk N ε) :
    ∀ g : ℕ → ℝ, ∑ m ∈ Bj N ε j, g m =
      ∑ n ∈ Ico 1 ⌈(N : ℝ) / wj N ε j⌉₊, ∑ p ∈ primesIco (wj N ε j) (Yj N ε j),
        if (∃ r s : ℕ, r.Prime ∧ s.Prime ∧ y3 N ≤ r ∧ r ≤ s ∧ n = r * s ∧ Nat.Coprime n N)
          then g (n * p) else 0 := by
  let C := fun n : ℕ => ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ y3 N ≤ r ∧ r ≤ s ∧ n = r * s ∧ Nat.Coprime n N
  let X := (N : ℝ) / wj N ε j
  let P := primesIco (wj N ε j) (Yj N ε j)
  let T := ((Ico 1 ⌈X⌉₊).product P).filter (fun a => C a.1)
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 0 < log N := by linarith [exp_pos (36 : ℝ)]
  have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
  have hypos : 0 < y3 N := rpow_pos_of_pos hNp _
  have hb : 1 < 1 + ε := by linarith
  have hwpos : 0 < wj N ε j := mul_pos hzpos (pow_pos (by linarith) _)
  have hzw : z8 N ≤ wj N ε j := by
    unfold wj
    exact le_mul_of_one_le_right hzpos.le (one_le_pow₀ hb.le)
  have hwy : wj N ε j < y3 N := by
    apply (log_lt_log_iff hwpos hypos).mp
    have h := (lt_div_iff₀ (log_pos hb)).mp (Nat.lt_ceil.mp hj)
    rw [log_div hypos.ne' hzpos.ne', log_rpow hNp, log_rpow hNp] at h
    rw [wj, log_mul hzpos.ne' (pow_pos (by linarith : 0 < 1 + ε) _).ne', log_pow, log_rpow hNp, log_rpow hNp]
    linarith
  have hT (n p : ℕ) : (n,p) ∈ T ↔ 1 ≤ n ∧ (n : ℝ) < X ∧ p.Prime ∧ wj N ε j ≤ p ∧
      (p : ℝ) < Yj N ε j ∧ C n := by
    simp only [T, P, primesIco, Finset.product_eq_sprod, mem_filter, Finset.mem_product, mem_Ico, mem_range, Nat.lt_ceil]
    constructor
    · rintro ⟨⟨⟨hn1, hnX⟩, hpY, hp, hwp⟩, hc⟩
      exact ⟨hn1, hnX, hp, hwp, hpY, hc⟩
    · rintro ⟨hn1, hnX, hp, hwp, hpY, hc⟩
      exact ⟨⟨⟨hn1, hnX⟩, hpY, hp, hwp⟩, hc⟩
  have hmap : Bj N ε j = T.image (fun a => a.1 * a.2) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hmrange, p, r, s, hp, hr, hs, hz, hpy, hyr, hrs, hprod, hcop, hjlo, hjhi, hmeq⟩ := mem_filter.mp hm
      apply mem_image.mpr
      refine ⟨(r*s,p), (hT _ _).mpr ⟨?_, ?_, hp, hjlo, ?_, ?_⟩, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr.ne_zero hs.ne_zero)
      · apply (lt_div_iff₀ hwpos).mpr
        push_cast
        nlinarith
      · exact lt_min hpy hjhi
      · exact ⟨r,s,hr,hs,hyr,hrs,rfl,hcop⟩
      · simpa only [mul_comm, mul_left_comm, mul_assoc] using hmeq.symm
    · intro hm
      obtain ⟨⟨n,p⟩, ht, hmeq⟩ := mem_image.mp hm
      obtain ⟨hn1, hnX, hp, hwp, hpY, r,s,hr,hs,hyr,hrs,hne,hcop⟩ := (hT _ _).mp ht
      have hpy : (p : ℝ) < y3 N := hpY.trans_le (min_le_left _ _)
      have hpw : (p : ℝ) < (1 + ε) * wj N ε j := hpY.trans_le (min_le_right _ _)
      have hnprod : wj N ε j * n < N := by
        have h := (lt_div_iff₀ hwpos).mp hnX
        nlinarith
      have hmN : (m : ℝ) < 2 * N := by
        have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
        have hmnp : (m : ℝ) = n * p := by exact_mod_cast hmeq.symm
        rw [hmnp]
        have h := mul_lt_mul_of_pos_left hpw hnr
        have h' := mul_lt_mul_of_pos_left hnprod (by linarith : 0 < 1 + ε)
        nlinarith
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by exact_mod_cast hmN), p,r,s,hp,hr,hs,hzw.trans hwp,hpy,hyr,hrs,?_,(by simpa only [hne] using hcop),hwp,hpw,?_⟩
      · rw [hne] at hnprod
        push_cast at hnprod
        nlinarith
      · rw [← hmeq, hne]; ring
  have hinj : Set.InjOn (fun a : ℕ × ℕ => a.1 * a.2) (↑T : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    rcases a with ⟨n,p⟩
    rcases b with ⟨m,q⟩
    obtain ⟨hn1, hnX, hp, hwp, hpY, r,s,hr,hs,hyr,hrs,hne,hcop⟩ := (hT _ _).mp ha
    obtain ⟨hm1, hmX, hq, hwq, hqY, u,v,hu,hv,hyu,huv,hme,hcopq⟩ := (hT _ _).mp hb
    change n * p = m * q at hab
    have hpq : p = q := by
      have hd : p ∣ m * q := by rw [← hab]; exact dvd_mul_left p n
      rcases hp.dvd_mul.mp hd with hpm | hpq
      · rw [hme] at hpm
        rcases hp.dvd_mul.mp hpm with hpu | hpv
        · have he := (Nat.prime_dvd_prime_iff_eq hp hu).mp hpu
          have hlt : (p : ℝ) < u := (hpY.trans_le (min_le_left _ _)).trans_le hyu
          exact False.elim ((ne_of_lt hlt) (by exact_mod_cast he))
        · have he := (Nat.prime_dvd_prime_iff_eq hp hv).mp hpv
          have hlt : (p : ℝ) < v := (hpY.trans_le (min_le_left _ _)).trans_le (hyu.trans (by exact_mod_cast huv))
          exact False.elim ((ne_of_lt hlt) (by exact_mod_cast he))
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    subst q
    have hnm : n = m := Nat.eq_of_mul_eq_mul_right hp.pos hab
    exact Prod.ext hnm rfl
  intro g
  rw [hmap, sum_image hinj]
  simp only [T, sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  rfl

/-- LEAF. Unit U-1552. Yamada 2015, (123), Section 7, from Lemma 7.2 with `X = N/w_j`,
`Y = Y_j = min{y, (1+ε)w_j}`, `Z = max{w_j, z}`, residue `N`, and `c(n) = 1` for
`n = p₂p₃`, `y ≤ p₂ ≤ p₃`, `(p₂p₃, N) = 1`: for even `N > exp exp 36`, `0 < ε < 1/100`,
if `q₁` satisfies the conclusion of `lemma72` then for `j < J`,
`Σ_{d<D, d ∣ P^(1)(y)} |r_d^(j,1)| ≤ e^{-144}(1+ε)N / log⁴ Y_j`. The printed (123) has
`log⁴ y` in place of `log⁴ Y_j`; see the header. -/
theorem eq123 (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁)
    (h72 : ∀ (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
      (∀ d, 0 < d → Nat.Coprime (res d) d) → log Y ^ 10 < X → X ≤ N / z8 N →
      X * Y < 2 * N → z8 N < Y → z8 N ≤ Z → Lemma72At q₁ c res X Y Z)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) (j : ℕ) (hj : j < Jblk N ε) :
    ∑ d ∈ Dset N q₁, |r1 N ε j d| ≤ exp (-144) * (1 + ε) * N / log (Yj N ε j) ^ 4 := by
  let C := fun n : ℕ => ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ y3 N ≤ r ∧ r ≤ s ∧ n = r * s ∧ Nat.Coprime n N
  let c : ℕ → ℝ := fun n => if C n then 1 else 0
  let res := fun d => if Nat.Coprime N d then N else 1
  let X := (N : ℝ) / wj N ε j
  let Y := Yj N ε j
  let Z := wj N ε j
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have h36 : (100000 : ℝ) < exp 36 := by
    have h := pow_div_factorial_le_exp 36 (by norm_num : (0 : ℝ) ≤ 36) 5
    norm_num at h
    linarith
  have hLp : 0 < log N := by linarith
  have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
  have hypos : 0 < y3 N := rpow_pos_of_pos hNp _
  have hb : 1 < 1 + ε := by linarith
  have hwpos : 0 < Z := mul_pos hzpos (pow_pos (by linarith) _)
  have hzw : z8 N ≤ Z := by
    unfold Z wj
    exact le_mul_of_one_le_right hzpos.le (one_le_pow₀ hb.le)
  have hwlog : log Z = log N / 8 + j * log (1 + ε) := by
    change log (wj N ε j) = _
    rw [wj, log_mul hzpos.ne' (pow_pos (by linarith : 0 < 1 + ε) _).ne', log_pow, log_rpow hNp]
    ring
  have hwy : Z < y3 N := by
    apply (log_lt_log_iff hwpos hypos).mp
    have h := (lt_div_iff₀ (log_pos hb)).mp (Nat.lt_ceil.mp hj)
    rw [log_div hypos.ne' hzpos.ne', log_rpow hNp, log_rpow hNp] at h
    rw [hwlog, log_rpow hNp]
    linarith
  have hwY : Z ≤ Y := le_min hwy.le (by dsimp [Z]; nlinarith)
  have hYy : Y ≤ y3 N := min_le_left _ _
  have hYw : Y ≤ (1 + ε) * Z := min_le_right _ _
  have hYpos : 0 < Y := hwpos.trans_le hwY
  have hYlog : 0 < log Y := by
    have hlogz : 0 < log (z8 N) := by rw [log_rpow hNp]; positivity
    exact hlogz.trans_le (log_le_log hzpos (hzw.trans hwY))
  have hYlogL : log Y ≤ log N := by
    have h := log_le_log hYpos hYy
    rw [log_rpow hNp] at h
    linarith
  have hr := log_div_self_antitoneOn
    (show exp 36 ∈ Set.Ici (exp 1) by simp only [Set.mem_Ici]; exact exp_le_exp.mpr (by norm_num))
    (show log (N : ℝ) ∈ Set.Ici (exp 1) by
      simp only [Set.mem_Ici]; exact (exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 36)).trans hL.le)
    hL.le
  simp only [log_exp] at hr
  have hratio : 36 / exp 36 < (1 / 1000 : ℝ) := by apply (div_lt_iff₀ (exp_pos _)).2; linarith
  have hloglog : log (log N) < log N / 1000 := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (div_lt_iff₀ hLp).mp (hr.trans_lt hratio)
  have hXpos : 0 < X := div_pos hNp hwpos
  have hXlarge : log Y ^ 10 < X := by
    apply (log_lt_log_iff (pow_pos hYlog _) hXpos).mp
    rw [log_pow]
    have hll := (log_le_log hYlog hYlogL).trans_lt hloglog
    have hwly := log_lt_log hwpos hwy
    rw [log_rpow hNp] at hwly
    change 10 * log (log Y) < log ((N : ℝ) / Z)
    rw [log_div hNp.ne' hwpos.ne']
    linarith
  have hXupper : X ≤ N / z8 N := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hzpos hzw
  have hXYlo : (N : ℝ) ≤ X * Y := by
    have hxZ : X * Z = N := by dsimp [X,Z]; field_simp [show wj N ε j ≠ 0 from hwpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left hwY hXpos.le]
  have hXYhi : X * Y < 2 * N := by
    have hxZ : X * Z = N := by dsimp [X,Z]; field_simp [show wj N ε j ≠ 0 from hwpos.ne']
    have h := mul_le_mul_of_nonneg_left hYw hXpos.le
    nlinarith
  have hYz : z8 N < Y := lt_min (hzw.trans_lt hwy) (by nlinarith)
  have hbound := h72 c res X Y Z (by intro n; dsimp [c]; split_ifs <;> norm_num)
    (by intro d hd; dsimp [res]; split_ifs with h; exact h; exact Nat.coprime_one_left d)
    hXlarge hXupper hXYhi hYz hzw
  have hdprops (d : ℕ) (hd : d ∈ Dset N q₁) :
      0 < d ∧ ¬ q₁ ∣ d ∧ Nat.Coprime N d ∧ res d = N := by
    obtain ⟨hdD, hdP⟩ := mem_filter.mp hd
    have hdp : 0 < d := Nat.pos_of_ne_zero hdP.1.ne_zero
    have hnd : Nat.Coprime N d := by
      apply Nat.coprime_of_dvd'
      intro p hp hpN hpd
      exact False.elim ((hdP.2 p hp hpd).2.1 hpN)
    refine ⟨hdp, ?_, hnd, by change (if Nat.Coprime N d then N else 1) = N; exact ite_eq_left hnd⟩
    intro hqd
    rcases hq with hq0 | ⟨hqp, hqbound⟩
    · subst q₁; simp only [zero_dvd_iff] at hqd; omega
    · exact (hdP.2 q₁ hqp hqd).2.2 rfl
  have hDupper : Dsv N ≤ sqrt (X * Y) / log Y ^ 10 := by
    unfold Dsv
    gcongr
  have hdsub : Dset N q₁ ⊆ (range ⌈sqrt (X * Y) / log Y ^ 10⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d) := by
    intro d hd
    have hp := hdprops d hd
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr ?_), hp.1, hp.2.1⟩
    exact (Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hd).1)).trans_le hDupper
  have hcnt (g : ℕ → ℝ) := sum_Bj_bilinear N hN ε hε hε1 j hj g
  have hdiv (d : ℕ) : cntDiv N ε j d = ∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
      if n * p ≡ N [MOD d] then c n else 0 := by
    letI : DecidableEq ℤ := Classical.decEq ℤ
    calc
      _ = ∑ m ∈ Bj N ε j, if (d : ℤ) ∣ (N : ℤ) - (m : ℤ) then (1 : ℝ) else 0 := by
        unfold cntDiv
        simp only [Finset.bind_def, Finset.pure_def, Finset.sup_eq_biUnion,
          Finset.biUnion_singleton, Finset.filter_image,
          sum_boole]
        exact congrArg (Nat.cast : ℕ → ℝ) (Finset.card_image_of_injective _ (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℤ)))
      _ = _ := (hcnt (fun m => if (d : ℤ) ∣ (N : ℤ) - (m : ℤ) then 1 else 0)).trans (by
        apply sum_congr rfl
        intro n hn
        apply sum_congr rfl
        intro p hp
        change (if C n then (if (d : ℤ) ∣ (N : ℤ) - (n*p : ℕ) then 1 else 0) else 0) = _
        dsimp only [c]
        simp only [← Nat.modEq_iff_dvd]
        split_ifs <;> rfl)
  have hcop (d : ℕ) : cntCop N ε j d = ∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
      if Nat.Coprime (n * p) d then c n else 0 := by
    calc
      _ = ∑ m ∈ Bj N ε j, if Nat.Coprime m d then (1 : ℝ) else 0 := by simp only [sum_boole]; rfl
      _ = _ := (hcnt (fun m => if Nat.Coprime m d then 1 else 0)).trans (by
        apply sum_congr rfl
        intro n hn
        apply sum_congr rfl
        intro p hp
        change (if C n then (if Nat.Coprime (n*p) d then 1 else 0) else 0) = _
        dsimp only [c]
        split_ifs <;> rfl)
  unfold Lemma72At at hbound
  calc
    _ ≤ ∑ d ∈ (range ⌈sqrt (X * Y) / log Y ^ 10⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d),
        |∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y, (if n*p ≡ res d [MOD d] then c n else 0) -
          (1 / (d.totient : ℝ)) * ∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
            (if Nat.Coprime (n*p) d then c n else 0)| := by
      apply (sum_le_sum fun d hd => le_of_eq ?_).trans
        (sum_le_sum_of_subset_of_nonneg hdsub (by intros; positivity))
      rw [(hdprops d hd).2.2.2, r1, hdiv, hcop]
      congr 1
      ring
    _ ≤ exp (-144) * X * Y / log Y ^ 4 := hbound
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hxZ : X * Z = N := by dsimp [X,Z]; field_simp [show wj N ε j ≠ 0 from hwpos.ne']
      have hxy : X * Y ≤ (1 + ε) * N := by
        calc
          _ ≤ X * ((1 + ε) * Z) := mul_le_mul_of_nonneg_left hYw hXpos.le
          _ = (1 + ε) * (X * Z) := by ring
          _ = _ := by rw [hxZ]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hxy (exp_pos (-144)).le

/-- Reciprocal fourth power bound for the corrected block sum in Yamada eq 124. -/
theorem sum_inv_affine_four_le (a h : ℝ) (ha : 0 < a) (hh : 0 < h) (n : ℕ) :
    ∑ j ∈ range n, 1 / (a + j * h) ^ 4 ≤ 1 / a ^ 4 + 1 / (3 * h * a ^ 3) := by
  have step (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
      1 / (a + h) ^ 4 ≤ (1 / a ^ 3 - 1 / (a + h) ^ 3) / (3 * h) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 3 * h * a ^ 3 * (a + h) ^ 4 by positivity)).mp
    field_simp
    nlinarith [show 0 ≤ 6 * a ^ 2 * h ^ 2 + 4 * a * h ^ 3 + h ^ 4 by positivity]
  have shifted (a h : ℝ) (ha : 0 < a) (hh : 0 < h) (n : ℕ) :
      ∑ j ∈ range n, 1 / (a + (j + 1) * h) ^ 4 ≤
        (1 / a ^ 3 - 1 / (a + n * h) ^ 3) / (3 * h) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have hn : 0 < a + n * h := by positivity
      have hs := step (a + n * h) h hn hh
      calc
        _ ≤ (1 / a ^ 3 - 1 / (a + n * h) ^ 3) / (3 * h) +
            (1 / (a + n * h) ^ 3 - 1 / (a + n * h + h) ^ 3) / (3 * h) := by
          convert add_le_add ih hs using 1; ring
        _ = _ := by push_cast; ring
  cases n with
  | zero => simp; positivity
  | succ n =>
    rw [sum_range_succ']
    have hs := shifted a h ha hh n
    have hn : 0 ≤ 1 / (a + n * h) ^ 3 := by positivity
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
    calc
      _ ≤ (1 / a ^ 3 - 1 / (a + n * h) ^ 3) / (3 * h) + 1 / a ^ 4 := add_le_add hs (le_refl _)
      _ ≤ 1 / a ^ 3 / (3 * h) + 1 / a ^ 4 := by gcongr; linarith
      _ = _ := by ring

/-- LEAF. Unit U-1552. Yamada 2015, (124), CORRECTED to `log⁴ Y_j`, Section 7: for
`N > exp exp 36`, `0 < ε < 1/100`, `Σ_{j<J} e^{-144}(1+ε)N/log⁴ Y_j ≤ 1.2 e^{-139} N/(ε log³ N)`;
by `log Y_j ≥ log z + j log(1+ε)` and reciprocal-cube telescoping the sum is at most about `(8³/3) e^{-144}/(ε log³ N)`,
numerically `1.11 e^{-139}/(ε log³ N)`. -/
theorem eq124 (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    ∑ j ∈ range (Jblk N ε), exp (-144) * (1 + ε) * N / log (Yj N ε j) ^ 4 ≤
      6 / 5 * exp (-139) * N / (ε * log N ^ 3) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have h36 : (100000 : ℝ) < exp 36 := by
    have h := pow_div_factorial_le_exp 36 (by norm_num : (0 : ℝ) ≤ 36) 5
    norm_num at h
    linarith
  have hLp : 0 < log N := by linarith
  have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
  have hypos : 0 < y3 N := rpow_pos_of_pos hNp _
  have hb : 0 < 1 + ε := by linarith
  have hh : 0 < log (1 + ε) := log_pos (by linarith)
  have hY (j : ℕ) (hj : j ∈ range (Jblk N ε)) :
      log N / 8 + j * log (1 + ε) ≤ log (Yj N ε j) := by
    have hwpos : 0 < wj N ε j := mul_pos hzpos (pow_pos hb _)
    have hwlog : log (wj N ε j) = log N / 8 + j * log (1 + ε) := by
      rw [wj, log_mul hzpos.ne' (pow_pos hb _).ne', log_pow, log_rpow hNp]
      ring
    have hjr := Nat.lt_ceil.mp (mem_range.mp hj)
    have hjl := (lt_div_iff₀ hh).mp hjr
    rw [log_div hypos.ne' hzpos.ne', log_rpow hNp, log_rpow hNp] at hjl
    have hwy : wj N ε j ≤ y3 N := by
      apply (log_le_log_iff hwpos hypos).mp
      rw [hwlog, log_rpow hNp]
      linarith
    have hwY : wj N ε j ≤ Yj N ε j := by
      apply le_min hwy
      nlinarith
    rw [← hwlog]
    exact log_le_log hwpos hwY
  have hsum : ∑ j ∈ range (Jblk N ε), 1 / log (Yj N ε j) ^ 4 ≤
      1 / (log N / 8) ^ 4 + 1 / (3 * log (1 + ε) * (log N / 8) ^ 3) := by
    calc
      _ ≤ ∑ j ∈ range (Jblk N ε), 1 / (log N / 8 + j * log (1 + ε)) ^ 4 := by
        apply sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le (by positivity)
        gcongr
        exact hY j hj
      _ ≤ _  := sum_inv_affine_four_le _ _ (by positivity) hh _
  have hloglower : ε / (1 + ε) ≤ log (1 + ε) := by
    have h := log_le_sub_one_of_pos (inv_pos.mpr hb)
    rw [log_inv] at h
    have he : 1 - (1 + ε)⁻¹ = ε / (1 + ε) := by field_simp <;> ring
    linarith
  have hexp : (148 : ℝ) < exp 5 := by
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 13
    norm_num [sum_range_succ] at h
    linarith
  have hcoeff : (1 + ε) * (4096 / log N + 512 / (3 * log (1 + ε))) ≤ (6 / 5) * exp 5 / ε := by
    have hinv : 1 / log (1 + ε) ≤ (1 + ε) / ε := by
      simpa only [one_div_div] using one_div_le_one_div_of_le (div_pos hε hb) hloglower
    have hsmall : 4096 / log N < (1 : ℝ) := by apply (div_lt_iff₀ hLp).2; linarith
    have hsq : (1 + ε) ^ 2 ≤ (101 / 100 : ℝ) ^ 2 := by gcongr <;> linarith

    calc
      _ ≤ (1 + ε) * (1 + (512 / 3) * ((1 + ε) / ε)) := by
        apply mul_le_mul_of_nonneg_left _ hb.le
        have hi := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 512 / 3)
        have heq : 512 / (3 * log (1 + ε)) = (512 / 3) * (1 / log (1 + ε)) := by ring
        rw [heq]
        linarith
      _ = (ε * (1 + ε) + (512 / 3) * (1 + ε) ^ 2) / ε := by field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hε.le
        have hprod : ε * (1 + ε) ≤ (1 / 100 : ℝ) * (101 / 100) :=
          mul_le_mul hε1.le (by linarith) hb.le (by norm_num)
        nlinarith

  calc
    _ = (exp (-144) * (1 + ε) * N) * ∑ j ∈ range (Jblk N ε), 1 / log (Yj N ε j) ^ 4 := by rw [mul_sum]; congr 1; ext j; ring
    _ ≤ (exp (-144) * (1 + ε) * N) *
        (1 / (log N / 8) ^ 4 + 1 / (3 * log (1 + ε) * (log N / 8) ^ 3)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = exp (-144) * N / log N ^ 3 * ((1 + ε) * (4096 / log N + 512 / (3 * log (1 + ε)))) := by field_simp <;> ring
    _ ≤ exp (-144) * N / log N ^ 3 * ((6 / 5) * exp 5 / ε) := mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = _ := by
      have he : exp (-144) * exp 5 = exp (-139) := by rw [← exp_add]; norm_num
      field_simp
      nlinarith [he]

/-- The corrected geometric blocks are disjoint, Yamada eqs 105 and 106. -/
theorem Bj_pairwise_disjoint (N : ℕ) (ε : ℝ) (hε : 0 < ε) (j k : ℕ) (hjk : j ≠ k) :
    Disjoint (Bj N ε j) (Bj N ε k) := by
  apply disjoint_left.mpr
  intro m hmj hmk
  obtain ⟨_, p, r, s, hp, hr, hs, hz, hpy, hyr, hrs, hprod, hcop, hjlo, hjhi, hm⟩ := mem_filter.mp hmj
  obtain ⟨_, q, u, v, hq, hu, hv, hzq, hqy, hyu, huv, hprodq, hcopq, hklo, hkhi, hmq⟩ := mem_filter.mp hmk
  have hpq : p = q := by
    have hd : p ∣ q * u * v := by rw [← hmq, hm]; exact dvd_mul_of_dvd_left (dvd_mul_right p r) s
    rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
      · have he := (Nat.prime_dvd_prime_iff_eq hp hu).mp hd
        have : (p : ℝ) < u := hpy.trans_le hyu
        exact False.elim ((ne_of_lt this) (by exact_mod_cast he))
    · have he := (Nat.prime_dvd_prime_iff_eq hp hv).mp hd
      have : (p : ℝ) < v := hpy.trans_le (hyu.trans (by exact_mod_cast huv))
      exact False.elim ((ne_of_lt this) (by exact_mod_cast he))
  subst q
  have hb : 1 < 1 + ε := by linarith
  have hw (a b : ℕ) (hab : a < b) : (1 + ε) * wj N ε a ≤ wj N ε b := by
    unfold wj
    have hzpos : 0 ≤ z8 N := rpow_nonneg (Nat.cast_nonneg _) _
    have hpw := pow_le_pow_right₀ hb.le (show a + 1 ≤ b by omega)
    have h := mul_le_mul_of_nonneg_left hpw hzpos
    simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
  rcases lt_or_gt_of_ne hjk with h | h
  · have hbound := hw j k h
    linarith
  · have hbound := hw k j h
    linarith

/-- LEAF. Unit U-1552. Yamada 2015, (126), Section 7: for even `N > exp exp 36`,
`0 < ε < 1/100`, admissible `q₁` and `d < D`, `d ∣ P^(1)(y)`:
`Σ_{j<J} r_d^(j,2) ≤ 8 N^{7/8} / φ(d)`; `(m, d) > 1` forces `p₁ ∣ d`, `d < N^{1/2}` has at most
four prime factors `≥ z`, and each gives at most `(1+ε)N/z` products. -/
theorem eq126 (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) (d : ℕ) (hd : d ∈ Dset N q₁) :
    ∑ j ∈ range (Jblk N ε), |r2 N ε j d| ≤ 8 * (N : ℝ) ^ ((7 : ℝ) / 8) / d.totient := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 1 < log N := by linarith [add_one_le_exp (36 : ℝ)]
  have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
  have hz1 : 1 ≤ z8 N := by
    apply one_le_rpow (by linarith [log_le_sub_one_of_pos hNp]) (by norm_num)
  obtain ⟨hdD, hdP⟩ := mem_filter.mp hd
  have hd0 : d ≠ 0 := hdP.1.ne_zero
  have hdp : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hdlt : (d : ℝ) < z8 N ^ 4 := by
    have hds : (d : ℝ) < Dsv N := Nat.lt_ceil.mp (mem_range.mp hdD)
    have hD : Dsv N ≤ sqrt (N : ℝ) := by
      unfold Dsv
      apply div_le_self (sqrt_nonneg _) (one_le_pow₀ hLp.le)
    have hz4 : z8 N ^ 4 = sqrt (N : ℝ) := by
      rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hNp.le]
      norm_num
    rw [hz4]
    exact hds.trans_le hD
  let big := d.primeFactors.filter (fun p : ℕ => z8 N ≤ p)
  have hbigcard : big.card ≤ 4 := by
    by_contra hc
    have hc4 : 4 ≤ big.card := by omega
    have hdvd : (∏ p ∈ big, p) ∣ d :=
      dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)) (Nat.prod_primeFactors_dvd d)
    have hle : ((∏ p ∈ big, p : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdvd
    have hge : z8 N ^ big.card ≤ ((∏ p ∈ big, p : ℕ) : ℝ) := by
      push_cast
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod₀ (fun _ _ => hzpos.le)
      intro p hp
      exact (mem_filter.mp hp).2
    have hpow := pow_le_pow_right₀ hz1 hc4
    linarith
  let bad := fun j => (Bj N ε j).filter (fun m => ¬ Nat.Coprime m d)
  have hbadDis : (↑(range (Jblk N ε)) : Set ℕ).PairwiseDisjoint bad := by
    intro j hj k hk hne
    exact (Bj_pairwise_disjoint N ε hε j k hne).mono (filter_subset _ _) (filter_subset _ _)
  have hbadsub : (range (Jblk N ε)).biUnion bad ⊆
      big.biUnion (fun p => (range (2 * N + 1)).filter (fun m => m ≠ 0 ∧ p ∣ m)) := by
    intro m hm
    obtain ⟨j, hj, hmb⟩ := mem_biUnion.mp hm
    obtain ⟨hmj, hbad⟩ := mem_filter.mp hmb
    obtain ⟨hmrange, p, r, s, hp, hr, hs, hz, hpy, hyr, hrs, hprod, hcop, hjlo, hjhi, hmeq⟩ := mem_filter.mp hmj
    have hrd : Nat.Coprime r d := by
      apply hr.coprime_iff_not_dvd.mpr
      intro hrd
      have h := (hdP.2 r hr hrd).1
      linarith
    have hsd : Nat.Coprime s d := by
      apply hs.coprime_iff_not_dvd.mpr
      intro hsd
      have h := (hdP.2 s hs hsd).1
      have hsr : (r : ℝ) ≤ s := by exact_mod_cast hrs
      linarith
    have hpd : p ∣ d := by
      apply hp.dvd_iff_not_coprime.mpr
      intro hpc
      apply hbad
      rw [hmeq]
      exact (hpc.mul_left hrd).mul_left hsd
    apply mem_biUnion.mpr
    refine ⟨p, mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩, hz⟩, mem_filter.mpr ⟨?_, ?_, ?_⟩⟩
    · exact mem_range.mpr (by have h := mem_range.mp hmrange; omega)
    · rw [hmeq]; exact Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hr.ne_zero) hs.ne_zero
    · rw [hmeq]; exact dvd_mul_of_dvd_left (dvd_mul_right p r) s
  have hcount : ((range (Jblk N ε)).biUnion bad).card ≤
      ∑ p ∈ big, (2 * N) / p := by
    calc
      _ ≤ (big.biUnion fun p => (range (2 * N + 1)).filter (fun m => m ≠ 0 ∧ p ∣ m)).card := card_le_card hbadsub
      _ ≤ ∑ p ∈ big, ((range (2 * N + 1)).filter (fun m => m ≠ 0 ∧ p ∣ m)).card := card_biUnion_le
      _ = _ := by congr 1; ext p; exact Nat.card_multiples' (2 * N) p
  have hcountR : (∑ j ∈ range (Jblk N ε), ((bad j).card : ℝ)) ≤ 8 * (N : ℝ) ^ ((7 : ℝ) / 8) := by
    rw [← Nat.cast_sum, ← card_biUnion hbadDis]
    calc
      _ ≤ ((∑ p ∈ big, (2 * N) / p : ℕ) : ℝ) := by exact_mod_cast hcount
      _ ≤ ∑ p ∈ big, (2 * (N : ℝ)) / p := by
        push_cast
        apply sum_le_sum
        intro p hp
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_div_le (m := 2 * N) (n := p) : ((2 * N) / p : ℕ) ≤ ((2 * N : ℕ) : ℝ) / p)
      _ ≤ ∑ p ∈ big, 2 * (N : ℝ) / z8 N := by
        apply sum_le_sum
        intro p hp
        apply div_le_div_of_nonneg_left (by positivity) hzpos (mem_filter.mp hp).2
      _ = big.card * (2 * (N : ℝ) / z8 N) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 4 * (2 * (N : ℝ) / z8 N) := by gcongr; exact_mod_cast hbigcard
      _ = _ := by
        rw [show (7 : ℝ) / 8 = 1 - 1 / 8 by norm_num, rpow_sub hNp, rpow_one]
        ring
  have hr2 (j : ℕ) : |r2 N ε j d| = ((bad j).card : ℝ) / d.totient := by
    have hc := card_filter_add_card_filter_not (s := Bj N ε j) (fun m => Nat.Coprime m d)
    have hcR : (Bj N ε j).card = ((Bj N ε j).filter fun m => Nat.Coprime m d).card + (bad j).card := by simpa only [bad] using hc.symm
    unfold r2 cntCop
    rw [hcR]
    push_cast
    rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
  simp_rw [hr2]
  rw [← sum_div]
  exact div_le_div_of_nonneg_right hcountR (Nat.cast_nonneg _)

open LeanLab.RieselVaughan1983.OddSums

/-- A finite prime product bound used for Yamada 2015 page 28 eq 125.
The primes through 31 are checked exactly. The remaining factors have a telescoping bound. -/
theorem prod_prime_inv_mul_pred_le_two (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 + h10 p) ≤ 2 := by
  let small : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
  let tail := s.filter (fun p => 31 < p)
  have hhead : ∏ p ∈ s.filter (fun p => p ≤ 31), (1 + h10 p) ≤
      ∏ p ∈ small, (1 + h10 p) := by
    apply prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      have hp' := (mem_filter.mp hp)
      have hpr := hs p hp'.1
      have hple := hp'.2
      norm_num [small, Finset.mem_insert, Finset.mem_singleton] at ⊢
      interval_cases p <;> norm_num [small] at *
    · intro p hp; linarith [h10_nonneg p]
    · intro p hp hnot; linarith [h10_nonneg p]
  have hsum : ∑ p ∈ tail, h10 p ≤ 1 / 31 := by
    let B := max 31 (s.sup id)
    have hsub : tail ⊆ Icc 32 B := by
      intro p hp
      obtain ⟨hp, h31⟩ := mem_filter.mp hp
      have hpb : p ≤ s.sup id := Finset.le_sup (f := id) hp
      simp only [mem_Icc]
      exact ⟨by omega, hpb.trans (le_max_right _ _)⟩
    have hle : ∑ p ∈ tail, h10 p ≤ ∑ p ∈ Icc 32 B, h10 p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => h10_nonneg p)
    have heq : Icc 2 B = Icc 2 31 ∪ Icc 32 B := by
      ext p
      simp only [mem_Icc, mem_union]
      have : 31 ≤ B := le_max_left _ _
      omega
    have hdis : Disjoint (Icc 2 31) (Icc 32 B) := by
      apply disjoint_left.mpr
      intro p hp hq
      simp only [mem_Icc] at hp hq
      omega
    have htotal := sum_inv_mul_pred_le B
    change (∑ p ∈ Icc 2 B, h10 p) ≤ _ at htotal
    rw [heq, sum_union hdis] at htotal
    have hheadval : ∑ p ∈ Icc 2 31, h10 p = 30 / 31 := by
      norm_num [Finset.sum_Icc_succ_top, h10]
    rw [hheadval] at htotal
    have hnon : (0 : ℝ) ≤ 1 / (max B 1 : ℕ) := by positivity
    linarith
  have htail : ∏ p ∈ tail, (1 + h10 p) ≤ 31 / 30 := by
    calc
      _ ≤ exp (∑ p ∈ tail, h10 p) := prod_le_exp h10 h10_nonneg tail
      _ ≤ exp (1 / 31) := exp_le_exp.mpr hsum
      _ ≤ 31 / 30 := by
        have h := exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 31) (by norm_num : (1 : ℝ) / 31 < 1)
        norm_num at h ⊢
        exact h
  have hprod : (∏ p ∈ s, (1 + h10 p)) =
      (∏ p ∈ s.filter (fun p => p ≤ 31), (1 + h10 p)) * ∏ p ∈ tail, (1 + h10 p) := by
    simpa only [tail, Nat.not_le] using (prod_filter_mul_prod_filter_not s (fun p => p ≤ 31) (fun p => 1 + h10 p)).symm
  rw [hprod]
  calc
    _ ≤ (∏ p ∈ small, (1 + h10 p)) * (31 / 30) :=
      mul_le_mul hhead htail (prod_nonneg (fun p _ => by linarith [h10_nonneg p]))
        (prod_nonneg (fun p _ => by linarith [h10_nonneg p]))
    _ ≤ 2 := by norm_num [small, h10]


open scoped ArithmeticFunction.Moebius

/-- Elementary coefficient bound for Yamada page 28 eq 125. -/
theorem sum_mu_sq_inv_mul_totient_le_two (B : ℕ) :
    ∑ r ∈ Icc 1 B, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ)) ≤ 2 := by
  let S := (Icc 2 B).filter Nat.Prime
  let R := (Icc 1 B).filter Squarefree
  have hsplit : (∑ r ∈ Icc 1 B, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ))) =
      ∑ r ∈ R, ∏ p ∈ r.primeFactors, h10 p := by
    rw [show (∑ r ∈ R, ∏ p ∈ r.primeFactors, h10 p) =
        ∑ r ∈ Icc 1 B, if Squarefree r then ∏ p ∈ r.primeFactors, h10 p else 0 from sum_filter _ _]
    apply sum_congr rfl
    intro r hr
    split_ifs with hs
    · have hm : ((μ r : ℝ)) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
      rw [hm, inv_mul_totient_eq hs]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; simp
  have hinj : Set.InjOn (fun r : ℕ => r.primeFactors) (R : Set ℕ) := by
    intro a ha b hb hab
    have ea := Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2
    have eb := Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2
    change a.primeFactors = b.primeFactors at hab
    rw [← ea, ← eb, hab]
  have hsub : R.image Nat.primeFactors ⊆ S.powerset := by
    intro T hT
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hT
    apply mem_powerset.mpr
    intro p hp
    have hrB := mem_Icc.mp (mem_filter.mp hr).1
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.two_le,
      (Nat.le_of_dvd hrB.1 hpd).trans hrB.2⟩, hpp⟩
  calc
    _ = ∑ r ∈ R, ∏ p ∈ r.primeFactors, h10 p := hsplit
    _ = ∑ T ∈ R.image Nat.primeFactors, ∏ p ∈ T, h10 p := (sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, h10 p) hinj).symm
    _ ≤ ∑ T ∈ S.powerset, ∏ p ∈ T, h10 p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => prod_nonneg (fun p _ => h10_nonneg p))
    _ = ∏ p ∈ S, (1 + h10 p) := (prod_one_add _).symm
    _ ≤ 2 := prod_prime_inv_mul_pred_le_two S (fun p hp => (mem_filter.mp hp).2)


/-- A logarithmic reciprocal totient bound derived for Yamada page 28 eq 125. -/
theorem sum_inv_totient_le_two_log (M : ℕ) (hM : 1 ≤ M) :
    ∑ d ∈ Icc 1 M, 1 / (d.totient : ℝ) ≤ 2 * (1 + Real.log M) := by
  let G : ℕ → ℝ := fun r => ((μ r : ℝ)) ^ 2 / (r.totient : ℝ)
  have hG : ∀ r, 0 ≤ G r := fun r => by dsimp [G]; positivity
  have hlog : 0 ≤ 1 + log (M : ℝ) := by
    have h : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith [log_nonneg h]
  have hid : ∑ d ∈ Icc 1 M, 1 / (d.totient : ℝ) =
      ∑ d ∈ Icc 1 M, ∑ r ∈ d.divisors, G r * (1 / (d : ℝ)) := by
    apply sum_congr rfl
    intro d hd
    rw [LeanLab.RieselVaughan1983.L10.inv_totient_eq d (mem_Icc.mp hd).1, mul_sum]
    apply sum_congr rfl
    intro r hr
    dsimp [G]
    ring
  have hswap : (∑ d ∈ Icc 1 M, ∑ r ∈ d.divisors, G r * (1 / (d : ℝ))) =
      ∑ r ∈ Icc 1 M, ∑ d ∈ (Icc 1 M).filter (fun d => r ∣ d), G r * (1 / (d : ℝ)) := by
    apply sum_comm'
    intro d r
    simp only [mem_Icc, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, hdM⟩, hrd, hd0⟩
      exact ⟨⟨⟨hd1, hdM⟩, hrd⟩,
        ⟨Nat.pos_of_dvd_of_pos hrd hd1, (Nat.le_of_dvd hd1 hrd).trans hdM⟩⟩
    · rintro ⟨⟨⟨hd1, hdM⟩, hrd⟩, hr⟩
      exact ⟨⟨hd1, hdM⟩, hrd, by omega⟩
  have hinner (r : ℕ) (hr : r ∈ Icc 1 M) :
      ∑ d ∈ (Icc 1 M).filter (fun d => r ∣ d), G r * (1 / (d : ℝ)) ≤
        G r / r * (1 + Real.log M) := by
    have hr1 := (mem_Icc.mp hr).1
    have hrp : (0 : ℝ) < r := by exact_mod_cast hr1
    have hsub : (Icc 1 M).filter (fun d => r ∣ d) ⊆ (Icc 1 M).image (fun n => r * n) := by
      intro d hd
      obtain ⟨hd, ⟨n, rfl⟩⟩ := mem_filter.mp hd
      have hdm := mem_Icc.mp hd
      apply mem_image.mpr
      refine ⟨n, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · nlinarith
      · have := Nat.le_mul_of_pos_left n hr1
        omega
    have hinj : Set.InjOn (fun n : ℕ => r * n) (Icc 1 M : Set ℕ) := by
      intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hr1 hab
    calc
      _ ≤ ∑ d ∈ (Icc 1 M).image (fun n => r * n), G r * (1 / (d : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => mul_nonneg (hG r) (by positivity))
      _ = ∑ n ∈ Icc 1 M, G r * (1 / ((r * n : ℕ) : ℝ)) := sum_image hinj
      _ = G r / r * ∑ n ∈ Icc 1 M, 1 / (n : ℝ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        push_cast
        ring
      _ ≤ G r / r * (1 + Real.log M) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (hG r) hrp.le)
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          one_div] using harmonic_le_one_add_log M
  calc
    _ = ∑ r ∈ Icc 1 M, ∑ d ∈ (Icc 1 M).filter (fun d => r ∣ d), G r * (1 / (d : ℝ)) := hid.trans hswap
    _ ≤ ∑ r ∈ Icc 1 M, G r / r * (1 + Real.log M) := sum_le_sum hinner
    _ = (∑ r ∈ Icc 1 M, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ))) * (1 + Real.log M) := by
      rw [← sum_mul]
      congr 1
      apply sum_congr rfl
      intro r hr
      dsimp [G]
      ring
    _ ≤ 2 * (1 + Real.log M) := mul_le_mul_of_nonneg_right (sum_mu_sq_inv_mul_totient_le_two M) hlog

/-- LEAF. Unit U-1552. Yamada 2015, (125), middle step, Section 7: for `N > exp exp 36`,
`Σ_{d<D, d ∣ P^(1)(y)} 1/φ(d) < log N`, from `Σ_{d ≤ x} μ²(d)/φ(d) ≤ log x + 1.4` and
`D < N^{1/2}`. -/
theorem eq125_phi (N q₁ : ℕ) (hN : exp (exp 36) < N) :
    ∑ d ∈ Dset N q₁, 1 / (d.totient : ℝ) < log N := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 0 < log N := (exp_pos _).trans hL
  have hLL : 36 < log (log N) := by simpa using log_lt_log (exp_pos _) hL
  have hDp : 0 < Dsv N := div_pos (sqrt_pos_of_pos hNp) (pow_pos hLp _)
  have hDlog : 0 < log (Dsv N) := (logs_pos N 0 hN).2.1
  have hD1 : 1 < Dsv N := by
    have h := exp_lt_exp.mpr hDlog
    simpa only [exp_zero, exp_log hDp] using h
  let M := ⌈Dsv N⌉₊
  have hceil : Dsv N ≤ (M : ℝ) := Nat.le_ceil _
  have hM1 : 1 ≤ M := by
    have h : (1 : ℝ) < M := hD1.trans_le hceil
    exact_mod_cast h.le
  have hMle : (M : ℝ) ≤ 2 * Dsv N := by
    have h := Nat.ceil_lt_add_one hDp.le
    change (M : ℝ) < Dsv N + 1 at h
    linarith
  have hsub : Dset N q₁ ⊆ Icc 1 M := by
    intro d hd
    obtain ⟨hdr, hdP⟩ := mem_filter.mp hd
    have hd0 := hdP.1.ne_zero
    have hdM : d < M := mem_range.mp hdr
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0, hdM.le⟩
  have hsum : ∑ d ∈ Dset N q₁, 1 / (d.totient : ℝ) ≤ 2 * (1 + log M) := by
    calc
      _ ≤ ∑ d ∈ Icc 1 M, 1 / (d.totient : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
      _ ≤ _ := sum_inv_totient_le_two_log M hM1
  have hlogM : log (M : ℝ) ≤ log 2 + log (Dsv N) := by
    calc
      _ ≤ log (2 * Dsv N) := log_le_log (by exact_mod_cast hM1) hMle
      _ = _ := log_mul (by norm_num) hDp.ne'
  have hlogD : log (Dsv N) = log N / 2 - 10 * log (log N) := by
    unfold Dsv
    rw [log_div (sqrt_pos_of_pos hNp).ne' (pow_pos hLp _).ne', log_sqrt hNp.le, log_pow]
    norm_num
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  linarith


/-- LEAF. Unit U-1552. Yamada 2015, (125), last step, Section 7: for `N > exp exp 36`,
`8 N^{7/8} log N < e^{-139} N / log³ N`. -/
theorem eq125_num (N : ℕ) (hN : exp (exp 36) < N) :
    8 * (N : ℝ) ^ ((7 : ℝ) / 8) * log N < exp (-139) * N / log N ^ 3 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have h36 : (100000 : ℝ) < exp 36 := by
    have h := pow_div_factorial_le_exp 36 (by norm_num : (0 : ℝ) ≤ 36) 5
    norm_num at h
    linarith
  have hLp : 0 < log N := by linarith
  have hr := log_div_self_antitoneOn
    (show exp 36 ∈ Set.Ici (exp 1) by simp only [Set.mem_Ici]; exact exp_le_exp.mpr (by norm_num))
    (show log (N : ℝ) ∈ Set.Ici (exp 1) by
      simp only [Set.mem_Ici]; exact (exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 36)).trans hL.le)
    hL.le
  simp only [log_exp] at hr
  have hratio : 36 / exp 36 < (1 / 1000 : ℝ) := by
    apply (div_lt_iff₀ (exp_pos _)).2
    linarith
  have hlog : log (log N) < log N / 1000 := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (div_lt_iff₀ hLp).mp (hr.trans_lt hratio)
  have h8 : log (8 : ℝ) ≤ 7 := by simpa only [show (8 : ℝ) - 1 = 7 by norm_num] using log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  have hs : log 8 + log N * (7 / 8) + 4 * log (log N) < -139 + log N := by linarith
  apply (lt_div_iff₀ (pow_pos hLp 3)).2
  calc
    8 * (N : ℝ) ^ ((7 : ℝ) / 8) * log N * log N ^ 3 =
        exp (log 8 + log N * (7 / 8) + 4 * log (log N)) := by
      rw [exp_add, exp_add, exp_log (by norm_num : (0 : ℝ) < 8),
        ← rpow_def_of_pos hNp, show exp (4 * log (log N)) = log N ^ 4 from by simpa using (exp_nat_mul (log (log N)) 4).trans (by rw [exp_log hLp])]
      ring
    _ < exp (-139 + log N) := exp_lt_exp.mpr hs
    _ = exp (-139) * N := by rw [exp_add, exp_log hNp]

end LeanLab.ChenExplicit.D1552
