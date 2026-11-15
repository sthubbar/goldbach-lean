module

public import LeanLab.Tolev2009.Diagonal341
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 page 84 display 56.
The diagonal is polynomially smaller than N squared before logarithmic absorption.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Decomp341b
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310b LeanLab.Tolev2009.Decomp341a
open LeanLab.Tolev2009.Diagonal341 LeanLab.HeathBrown1985

/-- The polynomial saving in the diagonal term of Tolev 1999 display 56.
The harmonic bounds and the lower second variable scale are explicit. -/
theorem diagonal_power_bound (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hN : (1 : ℝ) ≤ N) (hL : 1 ≤ Real.log N)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H)
    (hMH : M*H ≤ 2*N) (hHlo : (N : ℝ)^((1:ℝ)/2000) ≤ H)
    (hK : (K : ℝ)^2 ≤ (N : ℝ)^((2:ℝ)/3))
    (hHm : Hn ⌊2*H⌋₊ ≤ 33*Real.log N)
    (hHk : Hn (K*K) ≤ 33*Real.log N) :
    M * diagonal l₃ K N α x M M₁ H H₁ ≤
      (20 * 33^(40:ℕ)) * (N : ℝ)^((3999:ℝ)/2000) * Real.log N^(40:ℕ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hP : 0 < (N : ℝ)^((1:ℝ)/2000) := Real.rpow_pos_of_pos hN0 _
  have hML : M ≤ 2 * (N : ℝ)^((1999:ℝ)/2000) := by
    have hh : M ≤ 2*(N:ℝ)/(N:ℝ)^((1:ℝ)/2000) :=
      (le_div_iff₀ hP).mpr ((mul_le_mul_of_nonneg_left hHlo hM.le).trans hMH)
    convert hh using 1
    rw [mul_div_assoc]
    congr 1
    simpa only [show (1:ℝ)-(1:ℝ)/2000 = (1999:ℝ)/2000 by norm_num, Real.rpow_one] using
      Real.rpow_sub hN0 1 ((1:ℝ)/2000)
  have hKL : (K:ℝ)^2 ≤ (N:ℝ)^((1999:ℝ)/2000) :=
    hK.trans (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
  have hL0 : 0 ≤ Real.log N := by linarith
  have h33 : 1 ≤ 33*Real.log N := by linarith
  have h3316 : 1 ≤ (33*Real.log N)^(16:ℕ) := one_le_pow₀ h33
  have hbracket : 2*M*Hn (K*K)^(16:ℕ)+(K:ℝ)^2 ≤
      5*(N:ℝ)^((1999:ℝ)/2000)*(33*Real.log N)^(16:ℕ) := by
    have hh := pow_le_pow_left₀ (Hn_nonneg _) hHk 16
    have hb := mul_le_mul (mul_le_mul_of_nonneg_left hML (by norm_num : (0:ℝ)≤2)) hh
      (by positivity) (by positivity)
    have hk := mul_le_mul_of_nonneg_left h3316
      (Real.rpow_nonneg (Nat.cast_nonneg N) ((1999:ℝ)/2000))
    nlinarith
  have hHnon := Hn_nonneg ⌊2*H⌋₊
  have hf := diagonal_finite_bound l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
  calc
    _ ≤ M*((2*H*Hn ⌊2*H⌋₊^(24:ℕ))*(2*M*Hn (K*K)^(16:ℕ)+(K:ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hf hM.le
    _ = 2*(M*H)*Hn ⌊2*H⌋₊^(24:ℕ)*(2*M*Hn (K*K)^(16:ℕ)+(K:ℝ)^2) := by ring
    _ ≤ 2*(2*(N:ℝ))*(33*Real.log N)^(24:ℕ)*
        (5*(N:ℝ)^((1999:ℝ)/2000)*(33*Real.log N)^(16:ℕ)) := by
      gcongr
    _ = _ := by
      rw [show (3999:ℝ)/2000 = 1+(1999:ℝ)/2000 by norm_num, Real.rpow_add hN0, Real.rpow_one]
      ring

/-- Harmonic sums at these polynomial endpoints have one logarithmic loss.
This is the logarithmic bookkeeping in Tolev 1999 display 56. -/
theorem harmonic_endpoint (R N : ℕ) (hN : (0:ℝ) < N) (hL : 1 ≤ Real.log N)
    (hR : (R:ℝ) ≤ 2^(31:ℕ)*(N:ℝ)) : Hn R ≤ 33*Real.log N := by
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlogR : Real.log R ≤ 31+Real.log N := by
    by_cases hzero : R = 0
    · simp [hzero]
      linarith
    · have hRp : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero hzero
      have ht := Real.log_le_log hRp hR
      rw [Real.log_mul (by positivity : (2:ℝ)^(31:ℕ) ≠ 0) (ne_of_gt hN), Real.log_pow] at ht
      norm_num at ht
      linarith
  exact (Hn_le R).trans (by linarith)

/-- The two logarithmic powers needed for diagonal absorption are eventually small.
This uses the usual fact that logarithms grow slower than positive powers. -/
theorem eventual_diagonal_parameters (A : ℝ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧
      Real.log N^(4*A) ≤ (N:ℝ)^((1:ℝ)/2) ∧
      Real.log N^(8*A-592) ≤ (N:ℝ)^((1:ℝ)/2000) := by
  obtain ⟨X₁,h₁⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (4*A) (by norm_num : (0:ℝ)<1/2)).bound
      (by norm_num : (0:ℝ)<1))
  obtain ⟨X₂,h₂⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (8*A-592) (by norm_num : (0:ℝ)<1/2000)).bound
      (by norm_num : (0:ℝ)<1))
  refine ⟨max (max X₁ X₂) (Real.exp 2), ?_⟩
  intro N hN
  have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
  have hNp : (0:ℝ)<N := (Real.exp_pos 2).trans_le hNe
  have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hNp).mpr hNe
  have h₁' := h₁ (N:ℝ) ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
  have h₂' := h₂ (N:ℝ) ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), one_mul] at h₁' h₂'
  exact ⟨hL,h₁',h₂'⟩

/-- The sealed Type II shell gives the parameters used by the diagonal power bound.
This is the adaptation of Tolev 1999 displays 51 and 54. -/
theorem diagonal_shell_parameters (A : ℝ) (N : ℕ) (x H : ℝ)
    (hA : 0 ≤ A) (hN : (1:ℝ) ≤ N) (hL : 1 ≤ Real.log N)
    (hlog : Real.log N^(4*A) ≤ (N:ℝ)^((1:ℝ)/2))
    (hx : 0 < x) (hxlo : (N:ℝ)*Real.log N^(-4*A) ≤ x) (hxN : x ≤ N)
    (hHlo : x^((1:ℝ)/1000) ≤ H) (hHhi : H ≤ 2^(30:ℕ)*x^((1:ℝ)/3)) :
    let K := cutoff3 (10000*A) N
    (N:ℝ)^((1:ℝ)/2000) ≤ H ∧
      (K:ℝ)^2 ≤ (N:ℝ)^((2:ℝ)/3) ∧
      Hn ⌊2*H⌋₊ ≤ 33*Real.log N ∧ Hn (K*K) ≤ 33*Real.log N := by
  have hNp : (0:ℝ)<N := by linarith
  have hLp : 0 < Real.log N := by linarith
  have hsquare : ((N:ℝ)^((1:ℝ)/2))^2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    norm_num
  have hs : (N:ℝ)^((1:ℝ)/2) ≤ (N:ℝ)*Real.log N^(-4*A) := by
    rw [show -4*A = -(4*A) by ring, Real.rpow_neg hLp.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp _)).mpr
    exact (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hNp.le _)).trans_eq
      (by simpa only [pow_two] using hsquare)
  have hHlower : (N:ℝ)^((1:ℝ)/2000) ≤ H := by
    calc
      _ = ((N:ℝ)^((1:ℝ)/2))^((1:ℝ)/1000) := by
        rw [← Real.rpow_mul hNp.le]
        norm_num
      _ ≤ x^((1:ℝ)/1000) := Real.rpow_le_rpow (by positivity) (hs.trans hxlo) (by norm_num)
      _ ≤ H := hHlo
  have hNthird : (N:ℝ)^((1:ℝ)/3) ≤ N := by
    convert Real.rpow_le_rpow_of_exponent_le hN (show (1:ℝ)/3 ≤ 1 by norm_num) using 1 <;> simp
  have hHupper : H ≤ 2^(30:ℕ)*(N:ℝ) :=
    hHhi.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num))
      (by positivity)).trans (mul_le_mul_of_nonneg_left hNthird (by positivity)))
  let K := cutoff3 (10000*A) N
  have hK : (K:ℝ) ≤ (N:ℝ)^((1:ℝ)/3) := by
    have hf : (K:ℝ) ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)) :=
      Nat.floor_le (by positivity)
    have ht : Real.log N^(-(10000*A)) ≤ (1:ℝ) := Real.rpow_le_one_of_one_le_of_nonpos hL (by nlinarith)
    exact hf.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (mul_one _))
  have hKsq : (K:ℝ)^2 ≤ (N:ℝ)^((2:ℝ)/3) := by
    have ht := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
    convert ht using 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    norm_num
  refine ⟨hHlower,hKsq,?_,?_⟩
  · apply harmonic_endpoint _ N hNp hL
    have hHp : 0 < H := (Real.rpow_pos_of_pos hNp _).trans_le hHlower
    exact (Nat.floor_le (by positivity : 0 ≤ 2*H)).trans (by nlinarith)
  · apply harmonic_endpoint _ N hNp hL
    have ht : (N:ℝ)^((2:ℝ)/3) ≤ N := by
      convert Real.rpow_le_rpow_of_exponent_le hN (show (2:ℝ)/3 ≤ 1 by norm_num) using 1 <;> simp
    push_cast
    calc
      (K:ℝ)*(K:ℝ) = (K:ℝ)^2 := by ring
      _ ≤ (N:ℝ)^((2:ℝ)/3) := hKsq
      _ ≤ (N:ℝ) := ht
      _ ≤ _ := by nlinarith

/-- The diagonal scalar term has the required logarithmic saving.
Tolev 1999 page 84 display 56. No minor arc or coefficient input is used. -/
theorem diagonal_mean :
    ∀ A : ℝ, 10000 ≤ A → ∃ C N₀ : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ l₃ : ℕ, ∀ α x M M₁ H H₁ : ℝ,
        (N:ℝ)*Real.log N^(-4*A) ≤ x → x ≤ N → 2 < x →
        0 < M → M₁ ≤ 2*M → 0 < H → H₁ ≤ 2*H → M*H ≤ 2*x →
        x^((1:ℝ)/1000) ≤ H → H ≤ 2^(30:ℕ)*x^((1:ℝ)/3) →
        M * diagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁ ≤
          C*(N:ℝ)^2*Real.log N^(632-8*A) := by
  intro A hA
  obtain ⟨N₀,hparam⟩ := eventual_diagonal_parameters A
  refine ⟨20*33^(40:ℕ),max N₀ 3,by positivity,?_⟩
  intro N hN l₃ α x M M₁ H H₁ hxlo hxN hx hM hM₁ hH hH₁ hMH hHlo hHhi
  have hN3 : (3:ℝ) ≤ N := (le_max_right _ _).trans hN
  have hNp : (0:ℝ)<N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  obtain ⟨hL,hlog,habs⟩ := hparam N ((le_max_left _ _).trans hN)
  have hLp : 0 < Real.log N := by linarith
  obtain ⟨hHlower,hK,hHm,hHk⟩ := diagonal_shell_parameters A N x H (by linarith) hN1
    (by linarith) hlog (by linarith) hxlo hxN hHlo hHhi
  have hpower := diagonal_power_bound l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁
    hN1 (by linarith) hM hM₁ hH hH₁ (hMH.trans (by linarith)) hHlower hK hHm hHk
  have hlogs : Real.log N^(40:ℕ) = Real.log N^(8*A-592)*Real.log N^(632-8*A) := by
    rw [← Real.rpow_add hLp, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hfactor : (N:ℝ)^((3999:ℝ)/2000)*Real.log N^(40:ℕ) ≤
      (N:ℝ)^2*Real.log N^(632-8*A) := by
    rw [hlogs, ← mul_assoc]
    calc
      _ ≤ ((N:ℝ)^((3999:ℝ)/2000)*(N:ℝ)^((1:ℝ)/2000))*Real.log N^(632-8*A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg hNp.le _))
          (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        rw [← Real.rpow_add hNp]
        norm_num
  apply hpower.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfactor
    (show (0:ℝ) ≤ 20*33^(40:ℕ) by positivity)

end LeanLab.Tolev2009.Decomp341b
