module

public import LeanLab.Tolev2009.Decomp341b
public import LeanLab.Tolev2009.Decomp336b

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 page 85 displays 60 to 62.
The scalar rational approximation estimate uses the proved PNTPort reciprocal sum.
-/

@[expose] public section

set_option exponentiation.threshold 2048

open Finset Real
namespace LeanLab.Tolev2009.OffDiagonal341
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a LeanLab.Tolev2009.Decomp310b
open LeanLab.Tolev2009.Decomp336a LeanLab.Tolev2009.Decomp341a
open LeanLab.Tolev2009.Decomp341b LeanLab.HeathBrown1985

/-- The coefficient free divisor phase sum after the product regrouping on page 85.
The fifth power counts the modulus pair lcm fiber and its divisor index. -/
noncomputable def divisorPhase (α X : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, (n.divisors.card : ℝ)^5 * phaseCap α X n

/-- The scalar phase moment is nonnegative at a nonnegative upper shell. -/
theorem divisorPhase_nonneg (α X : ℝ) (T : ℕ) (hX : 0 ≤ X) :
    0 ≤ divisorPhase α X T :=
  sum_nonneg (fun n hn => mul_nonneg (by positivity) (phaseCap_nonneg α X n hX))

/-- The reciprocal divisor moment Cauchy bound in the adaptation of display 61. -/
theorem divisorPhase_sq (α X : ℝ) (T : ℕ) (hX : 0 ≤ X) :
    divisorPhase α X T ^ 2 ≤ Hn T ^ (1024:ℕ) *
      ((2*X+T)*∑ n ∈ Icc 1 T, phaseCap α X n) := by
  have hm : (∑ n ∈ Icc 1 T, ((n.divisors.card : ℝ)^5)^2 / n) ≤ Hn T^(1024:ℕ) := by
    simpa only [← pow_mul, show (5:ℕ)*2=10 by norm_num, show (2:ℕ)^10=1024 by norm_num] using
      divisor_power_reciprocal 10 T
  exact (weighted_phase_cauchy (fun n => (n.divisors.card:ℝ)^5) T α X hX).trans
    (mul_le_mul_of_nonneg_right hm
      (mul_nonneg (by positivity) (sum_nonneg (fun n hn => phaseCap_nonneg α X n hX))))

/-- The unweighted reciprocal phase sum for an upper shell at most four N.
This is the rational approximation input in Tolev 1999 display 62. -/
theorem phase_mass_four (A : ℝ) (N T q : ℕ) (a : ℤ) (α X : ℝ)
    (hA : 0 ≤ A) (hN : 0 < (N:ℝ)) (hL : 2 ≤ Real.log N)
    (hX : 0 ≤ X) (hXN : X ≤ 4*N) (hTN : T ≤ N)
    (hTS : (T:ℝ) ≤ 4*N*Real.log N^(-20*A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q:ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q:ℤ)) (herr : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2) :
    ∑ n ∈ Icc 1 T, phaseCap α X n ≤ 512*N*Real.log N^(1-20*A) := by
  let s : ℝ := N*Real.log N^(-20*A)
  have hLp : 0 < Real.log N := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow (by linarith) (by positivity)
  have hQp : 0 < Qof A N := by linarith
  have ht : τof A N = s := by
    dsimp [τof,Qof,s]
    rw [show -20*A=-(20*A) by ring,Real.rpow_neg hLp.le,div_eq_mul_inv]
  have hqS : (q:ℝ) ≤ s := by rwa [ht] at hqτ
  have hqp : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hqN : (q:ℝ) ≤ N := hqτ.trans (div_le_self hN.le hQ)
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hqp hqN
  have hlogT : Real.log T ≤ Real.log N := by
    by_cases hT : T=0
    · simp [hT]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast hTN)
  have hlogs : 1+Real.log q+Real.log T ≤ 3*Real.log N := by linarith
  have hlogs0 : 0 ≤ 1+Real.log q+Real.log T := by positivity
  have hNq : (N:ℝ)/q ≤ s := by
    calc
      _ ≤ (N:ℝ)/Qof A N := div_le_div_of_nonneg_left hN.le hQp hqQ.le
      _ = s := ht
  have hXq : 2*X/q ≤ 8*s := by
    calc
      _ ≤ 2*(4*(N:ℝ))/q := div_le_div_of_nonneg_right (by linarith) hqp.le
      _ = 8*((N:ℝ)/q) := by ring
      _ ≤ 8*s := mul_le_mul_of_nonneg_left hNq (by norm_num)
  have hT : (T:ℝ) ≤ 4*s := by simpa only [s,mul_assoc] using hTS
  have hc : 2*X/q+T+q ≤ 13*s := by linarith
  have hp := mul_le_mul hc hlogs hlogs0 (by positivity : 0≤13*s)
  have hm := phaseCap_sum_le hq hcop herr hX T
  apply hm.trans
  have hbound : 12*(2*X/q+T+q)*(1+Real.log q+Real.log T)+T ≤ 512*s*Real.log N := by
    nlinarith [mul_nonneg hs (show 0 ≤ Real.log N-1 by linarith)]
  apply hbound.trans_eq
  dsimp [s]
  rw [show 1-20*A=(-20*A)+(1:ℝ) by ring,Real.rpow_add hLp,Real.rpow_one]
  ring

/-- The weighted scalar phase sum has ample logarithmic saving.
This is the Cauchy and rational approximation combination in displays 61 to 62. -/
theorem divisorPhase_bound (A : ℝ) (N T q : ℕ) (a : ℤ) (α X : ℝ)
    (hA : 0 ≤ A) (hN : (1:ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hX : 0 ≤ X) (hXN : X ≤ 4*N) (hTN : T ≤ N)
    (hTS : (T:ℝ) ≤ 4*N*Real.log N^(-20*A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q:ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q:ℤ)) (herr : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2) :
    divisorPhase α X T ≤ 2^(520:ℕ)*N*Real.log N^(513-10*A) := by
  have hNp : (0:ℝ)<N := by linarith
  have hLp : 0 < Real.log N := by linarith
  have hH : Hn T ≤ 2*Real.log N := by
    have hl : Real.log T ≤ Real.log N := by
      by_cases hz : T=0
      · simp [hz]; linarith
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hTN)
    exact (Hn_le T).trans (by linarith)
  have hm := phase_mass_four A N T q a α X hA hNp hL hX hXN hTN hTS hq hqQ hqτ hcop herr
  have hTp : (T:ℝ) ≤ N := by exact_mod_cast hTN
  have hc : 2*X+T ≤ 9*N := by linarith
  have hphase0 : 0 ≤ ∑ n ∈ Icc 1 T, phaseCap α X n :=
    sum_nonneg (fun n hn => phaseCap_nonneg α X n hX)
  have hb := (divisorPhase_sq α X T hX).trans
    (mul_le_mul (pow_le_pow_left₀ (Hn_nonneg T) hH 1024)
      (mul_le_mul hc hm (sum_nonneg (fun n hn => phaseCap_nonneg α X n hX)) (by positivity))
      (by positivity) (by positivity))
  have he : (2*Real.log N)^(1024:ℕ)*(9*N*(512*N*Real.log N^(1-20*A))) =
      (9*512*2^(1024:ℕ))*(N:ℝ)^2*Real.log N^(1025-20*A) := by
    rw [mul_pow,← Real.rpow_natCast (Real.log N) 1024]
    rw [show 1025-20*A=(1024:ℝ)+(1-20*A) by ring,Real.rpow_add hLp]
    ring
  rw [he] at hb
  have hpow : Real.log N^(1025-20*A) ≤ Real.log N^(1026-20*A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hC : (9*512*2^(1024:ℕ):ℝ) ≤ (2^(520:ℕ):ℝ)^2 := by norm_num
  have hfin := hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hC (sq_nonneg (N:ℝ))) hpow
    (Real.rpow_nonneg hLp.le _) (by positivity))
  have ht : ((2^(520:ℕ):ℝ)^2*(N:ℝ)^2)*Real.log N^(1026-20*A) =
      (2^(520:ℕ)*N*Real.log N^(513-10*A))^2 := by
    have hsq : (Real.log N^(513-10*A))^(2:ℕ) = Real.log N^(1026-20*A) := by
      rw [← Real.rpow_mul_natCast hLp.le]
      congr 1
      push_cast
      ring
    rw [← hsq]
    ring
  rw [ht] at hfin
  exact (sq_le_sq₀ (divisorPhase_nonneg α X T hX) (by positivity)).mp hfin

/-- The difference times lcm endpoint stays inside the short reciprocal phase range.
This uses the exact third cutoff and the Type II upper scale in displays 51 and 54. -/
theorem phase_product_endpoint (A : ℝ) (N : ℕ) (x H : ℝ)
    (hA : 10000 ≤ A) (hN : (1:ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hx : 0 < x) (hxN : x ≤ N) (hH : 0 < H)
    (hHhi : H ≤ 2^(30:ℕ)*x^((1:ℝ)/3)) :
    let K := cutoff3 (10000*A) N
    let T := ⌊2*H⌋₊*(K*K)
    T ≤ N ∧ (T:ℝ) ≤ 4*N*Real.log N^(-20*A) := by
  let K := cutoff3 (10000*A) N
  let T := ⌊2*H⌋₊*(K*K)
  have hNp : (0:ℝ)<N := by linarith
  have hLp : 0<Real.log N := by linarith
  have hHupper : H ≤ 2^(30:ℕ)*(N:ℝ)^((1:ℝ)/3) :=
    hHhi.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num)) (by positivity))
  have hK : (K:ℝ) ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)) := Nat.floor_le (by positivity)
  have hKsq : (K:ℝ)^2 ≤ (N:ℝ)^((2:ℝ)/3)*Real.log N^(-20000*A) := by
    calc
      _ ≤ ((N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)))^2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
      _ = _ := by
        have hn : ((N:ℝ)^((1:ℝ)/3))^(2:ℕ) = (N:ℝ)^((2:ℝ)/3) := by
          rw [← Real.rpow_mul_natCast hNp.le]
          norm_num
        have hl : (Real.log N^(-(10000*A)))^(2:ℕ) = Real.log N^(-20000*A) := by
          rw [← Real.rpow_mul_natCast hLp.le]
          congr 1
          push_cast
          ring
        rw [mul_pow,hn,hl]
  have hT : (T:ℝ) ≤ 2^(31:ℕ)*(N:ℝ)*Real.log N^(-20000*A) := by
    have hf : (⌊2*H⌋₊:ℝ) ≤ 2*H := Nat.floor_le (by positivity)
    calc
      (T:ℝ) = (⌊2*H⌋₊:ℝ)*(K:ℝ)^2 := by dsimp [T]; push_cast; ring
      _ ≤ (2*H)*((N:ℝ)^((2:ℝ)/3)*Real.log N^(-20000*A)) :=
        mul_le_mul hf hKsq (sq_nonneg _) (by positivity)
      _ ≤ (2*(2^(30:ℕ)*(N:ℝ)^((1:ℝ)/3)))*
          ((N:ℝ)^((2:ℝ)/3)*Real.log N^(-20000*A)) := by gcongr
      _ = 2^(31:ℕ)*((N:ℝ)^((1:ℝ)/3)*(N:ℝ)^((2:ℝ)/3))*Real.log N^(-20000*A) := by ring
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hsmall : Real.log N^(-19980*A) ≤ (2:ℝ)^(-(31:ℝ)) := by
    calc
      _ ≤ Real.log N^(-(31:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
  have hbudget : (T:ℝ) ≤ (N:ℝ)*Real.log N^(-20*A) := by
    apply hT.trans
    rw [show -20000*A=(-20*A)+(-19980*A) by ring,Real.rpow_add hLp]
    calc
      _ = (2^(31:ℕ)*(N:ℝ)*Real.log N^(-20*A))*Real.log N^(-19980*A) := by ring
      _ ≤ (2^(31:ℕ)*(N:ℝ)*Real.log N^(-20*A))*(2:ℝ)^(-(31:ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by norm_num [Real.rpow_neg,Real.rpow_natCast]; ring
  have hone : Real.log N^(-20*A) ≤ (1:ℝ) :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by nlinarith)
  refine ⟨?_,?_⟩
  · exact_mod_cast hbudget.trans ((mul_le_mul_of_nonneg_left hone hNp.le).trans_eq (mul_one _))
  · exact hbudget.trans (by have := Real.rpow_nonneg hLp.le (-20*A); nlinarith)

end LeanLab.Tolev2009.OffDiagonal341
