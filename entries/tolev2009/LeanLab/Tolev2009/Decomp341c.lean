module

public import LeanLab.Tolev2009.OffDiagonal341
public import LeanLab.Tolev2009.Shifted341
public import LeanLab.Tolev2009.Product341
public import LeanLab.Tolev2009.Caps341

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 84 to 86 displays 59 to 63.
The exact row energy supply is proved with no cited input.
-/

@[expose] public section

set_option exponentiation.threshold 2048

open Finset Real
namespace LeanLab.Tolev2009.Decomp341c
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a LeanLab.Tolev2009.Decomp310b
open LeanLab.Tolev2009.Decomp336a LeanLab.Tolev2009.Decomp341a
open LeanLab.Tolev2009.Diagonal341 LeanLab.Tolev2009.Decomp341b
open LeanLab.Tolev2009.OffDiagonal341
open LeanLab.Tolev2009.Progressions341 LeanLab.Tolev2009.Shifted341
open LeanLab.Tolev2009.Product341 LeanLab.Tolev2009.Caps341

/-- Tolev 1999 pages 84 to 85 displays 59 to 61.
This finite regrouping uses the positive difference, the lcm fiber and the divisor product.
There is no minor arc premise, asymptotic threshold or arbitrary coefficient function. -/
theorem finite_offDiagonal_reduction (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H) :
    offDiagonal l₃ K N α x M M₁ H H₁ ≤
      2*(∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ)^2) *
        divisorPhase α (2*M*H) (⌊2*H⌋₊*(K*K)) := by
  classical
  let S := Ioc ⌊H⌋₊ ⌊H₁⌋₊
  let U := ⌊2*H⌋₊
  let ks := (Icc 1 K).filter (fun k => Nat.Coprime k l₃)
  let X := 2*M*H
  let F : ℕ → ℝ := fun r => ∑ h ∈ Icc 1 (K*K), (h.divisors.card:ℝ)^4*phaseCap α X (h*r)
  have hX : 0≤X := by dsimp [X]; positivity
  have hF : ∀ r, 0≤F r := fun r => sum_nonneg (fun h hh =>
    mul_nonneg (by positivity) (phaseCap_nonneg α X (h*r) hX))
  have hS : ∀ l ∈ S, l≤U := fun l hl =>
    (mem_Ioc.mp hl).2.trans (Nat.floor_le_floor hH₁)
  have he : offDiagonal l₃ K N α x M M₁ H H₁ =
      ∑ l ∈ S, ∑ j ∈ S, if l≠j then (tau5 l:ℝ)*tau5 j*
        ∑ k₁ ∈ ks, ∑ k₂ ∈ ks, ‖correlation l₃ N α x M M₁ (l,k₁) (j,k₂)‖ else 0 := by
    simp only [offDiagonal,indices,sum_product]
    apply sum_congr rfl
    intro l hl
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    by_cases hn : l≠j
    · simp [hn,ks,mul_sum]
    · simp [hn,ks]
  have hpoint (l j : ℕ) (hl : l∈S) (hj : j∈S) (hne : l≠j) :
      (∑ k₁ ∈ ks, ∑ k₂ ∈ ks, ‖correlation l₃ N α x M M₁ (l,k₁) (j,k₂)‖) ≤
        F (Nat.dist l j) := by
    let r := Nat.dist l j
    have hr : 1≤r := by dsimp [r,Nat.dist]; omega
    have hrU : r≤U := by have hlU := hS l hl; have hjU := hS j hj; dsimp [r,Nat.dist]; omega
    have hrH : (r:ℝ)≤2*H :=
      (show (r:ℝ)≤U by exact_mod_cast hrU).trans (Nat.floor_le (by positivity))
    calc
      _ ≤ ∑ k₁ ∈ ks, ∑ k₂ ∈ ks, phaseCap α X (Nat.lcm k₁ k₂*r) := by
        apply sum_le_sum
        intro k₁ hk₁
        apply sum_le_sum
        intro k₂ hk₂
        have hk₁' := mem_filter.mp hk₁
        have hk₂' := mem_filter.mp hk₂
        have hk₁p := (mem_Icc.mp hk₁'.1).1
        have hk₂p := (mem_Icc.mp hk₂'.1).1
        have hh : 1≤Nat.lcm k₁ k₂ := Nat.lcm_pos (by omega) (by omega)
        calc
          _ ≤ phaseCap (α*((l:ℝ)-j)) M (Nat.lcm k₁ k₂) :=
            correlation_bound l₃ N α x M M₁ (l,k₁) (j,k₂) hk₁p hk₂p hk₁'.2 hk₂'.2 hM hM₁
          _ = phaseCap (α*r) M (Nat.lcm k₁ k₂) := phaseCap_distance α M l j _
          _ ≤ _ := by simpa only [Nat.mul_comm] using phaseCap_product α M H r (Nat.lcm k₁ k₂) hM.le hH.le hr hh hrH
      _ ≤ ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, phaseCap α X (Nat.lcm k₁ k₂*r) := by
        apply (sum_le_sum (fun k₁ hk₁ =>
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₂ hk₂ hnot => phaseCap_nonneg α X _ hX))).trans
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₁ hk₁ hnot =>
          sum_nonneg (fun k₂ hk₂ => phaseCap_nonneg α X _ hX))
      _ ≤ _ := lcm_sum_bound K (fun h => phaseCap α X (h*r)) (fun h => phaseCap_nonneg α X _ hX)
  have hfirst : offDiagonal l₃ K N α x M M₁ H H₁ ≤
      ∑ l ∈ S, ∑ j ∈ S, if l≠j then (tau5 l:ℝ)*tau5 j*F (Nat.dist l j) else 0 := by
    rw [he]
    apply sum_le_sum
    intro l hl
    apply sum_le_sum
    intro j hj
    by_cases hn : l≠j
    · simp only [ne_eq,hn,ite_true]
      exact mul_le_mul_of_nonneg_left (hpoint l j hl hj hn) (by positivity)
    · simp only [ne_eq,hn,ite_false,le_refl]
  have hsecond := shifted_square_bound S U hS (fun l => (tau5 l:ℝ)) F hF
  have hthird : (∑ r ∈ Icc 1 U, F r) ≤ divisorPhase α X (U*(K*K)) := by
    dsimp [F,divisorPhase]
    rw [sum_comm]
    simp only [← mul_sum]
    exact divisor_product_bound U (K*K) (fun n => phaseCap α X n) (fun n => phaseCap_nonneg α X n hX)
  exact (hfirst.trans hsecond).trans (mul_le_mul_of_nonneg_left hthird (by positivity))

/-- The off diagonal scalar mean follows from the proved finite regrouping and phase sum. -/
theorem offDiagonal_mean :
    ∀ A : ℝ, 10000 ≤ A → ∃ C N₀ : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ l₃ : ℕ,
        ∀ α ∈ Set.Ioo (-1/τof A N) (1-1/τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N:ℝ)*Real.log N^(-4*A) ≤ x → x ≤ N → 2 < x →
          0 < M → M₁ ≤ 2*M → 0 < H → H₁ ≤ 2*H → M*H ≤ 2*x →
          x^((1:ℝ)/1000) ≤ H → H ≤ 2^(30:ℕ)*x^((1:ℝ)/3) →
          M * offDiagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁ ≤
            C*(N:ℝ)^2*Real.log N^(632-8*A) := by
  intro A hA
  obtain ⟨N₁,hparam₁⟩ := eventual_minor_arc_parameters A (by linarith)
  obtain ⟨N₂,hparam₂⟩ := eventual_diagonal_parameters A
  refine ⟨2^(523:ℕ)*33^(24:ℕ),max N₁ (max N₂ 3),by positivity,?_⟩
  intro N hN l₃ α hα hminor x M M₁ H H₁ hxlo hxN hx hM hM₁ hH hH₁ hMH hHlo hHhi
  have hN3 : (3:ℝ) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNp : (0:ℝ)<N := by linarith
  have hN1 : (1:ℝ)≤N := by linarith
  obtain ⟨hL,hτ⟩ := hparam₁ N ((le_max_left _ _).trans hN)
  obtain ⟨_,hlog,_⟩ := hparam₂ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hLp : 0<Real.log N := by linarith
  have hQ : 0≤Qof A N := Real.rpow_nonneg (by linarith) _
  have hτ1 : 1≤τof A N := by linarith
  obtain ⟨a,q,hq,hqQ,hqt,hcop,_,herr⟩ :=
    minor_arc_reduced_approximation (Qof A N) (τof A N) α hQ hτ hτ1 hα hminor
  let K := cutoff3 (10000*A) N
  let T := ⌊2*H⌋₊*(K*K)
  obtain ⟨hTN,hTS⟩ := phase_product_endpoint A N x H hA hN1 hL (by linarith) hxN hH hHhi
  have hX : 0≤2*M*H := by positivity
  have hXN : 2*M*H ≤ 4*N := by nlinarith
  have hphase := divisorPhase_bound A N T q a α (2*M*H) (by linarith) hN1 hL hX hXN
    hTN hTS hq hqQ hqt hcop herr
  obtain ⟨_,_,hHm,_⟩ := diagonal_shell_parameters A N x H (by linarith) hN1
    (by linarith) hlog (by linarith) hxlo hxN hHlo hHhi
  have hmass : (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l:ℝ)^2) ≤
      2*H*(33*Real.log N)^(24:ℕ) :=
    (tau5_square_sum H H₁ hH hH₁).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (LeanLab.HeathBrown1985.Hn_nonneg _) hHm 24)
        (by positivity))
  have hf := finite_offDiagonal_reduction l₃ K N α x M M₁ H H₁ hM hM₁ hH hH₁
  have hb := hf.trans (mul_le_mul (mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ)≤2)) hphase
    (divisorPhase_nonneg α (2*M*H) T hX) (by positivity))
  have he : M*(2*(2*H*(33*Real.log N)^(24:ℕ))*(2^(520:ℕ)*N*Real.log N^(513-10*A))) =
      (2^(522:ℕ)*33^(24:ℕ))*(M*H)*N*Real.log N^(537-10*A) := by
    rw [mul_pow,show 537-10*A=(24:ℝ)+(513-10*A) by ring,Real.rpow_add hLp]
    simp only [Real.rpow_ofNat]
    ring
  have hsave : Real.log N^(537-10*A) ≤ Real.log N^(632-8*A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hMHN : M*H ≤ 2*N := hMH.trans (by linarith)
  calc
    _ ≤ M*(2*(2*H*(33*Real.log N)^(24:ℕ))*(2^(520:ℕ)*N*Real.log N^(513-10*A))) :=
      mul_le_mul_of_nonneg_left hb hM.le
    _ = _ := he
    _ ≤ (2^(522:ℕ)*33^(24:ℕ))*(2*N)*N*Real.log N^(632-8*A) := by gcongr
    _ = _ := by ring

/-- The exact sealed row energy statement follows from the proved diagonal and phase bounds. -/
theorem row_energy :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ b : ℕ → ℂ,
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A) := by
  intro A hA l₃ hl₃
  have hA' : 10000 ≤ A := by norm_num at hA; exact hA
  obtain ⟨C₁,N₁,hC₁,h₁⟩ := diagonal_mean A hA'
  obtain ⟨C₂,N₂,hC₂,h₂⟩ := offDiagonal_mean A hA'
  refine ⟨C₁+C₂,max N₁ N₂,by positivity,?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁ hxlo hxN hx
    hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hHlo hHhi b hb
  have hd := h₁ N ((le_max_left _ _).trans hN) l₃ α x M M₁ H H₁
    hxlo hxN hx hM hM₁ hH hH₁ hprodhi hHlo hHhi
  have ho := h₂ N ((le_max_right _ _).trans hN) l₃ α hα hminor x M M₁ H H₁
    hxlo hxN hx hM hM₁ hH hH₁ hprodhi hHlo hHhi
  have hN2 : (1:ℝ)<N := lt_of_lt_of_le (by linarith : (1:ℝ)<x) hxN
  have hLp : 0<Real.log N := Real.log_pos hN2
  norm_num only [show (10^4:ℝ)=10000 by norm_num]
  have he := mul_le_mul_of_nonneg_left
    (energy_le_correlations lam l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁ b hlam hLp.le hb) hM.le
  calc
    _ ≤ Real.log N^(2:ℕ)*(M*diagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁+
        M*offDiagonal l₃ (cutoff3 (10000*A) N) N α x M M₁ H H₁) := by nlinarith [he]
    _ ≤ Real.log N^(2:ℕ)*(C₁*(N:ℝ)^2*Real.log N^(632-8*A)+
        C₂*(N:ℝ)^2*Real.log N^(632-8*A)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd ho) (sq_nonneg _)
    _ = _ := by
      rw [show 634-8*A=(2:ℝ)+(632-8*A) by ring,Real.rpow_add hLp]
      simp only [Real.rpow_ofNat]
      ring

end LeanLab.Tolev2009.Decomp341c
