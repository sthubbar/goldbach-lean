module

public import LeanLab.Tolev2009.Progressions341

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 84 to 85 displays 59 to 61.
The geometric cap is even and can be enlarged to the product scale.
-/

@[expose] public section

open Finset Real ComplexConjugate
namespace LeanLab.Tolev2009.Caps341
open LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Decomp336a

/-- Negating the frequency preserves the progression cap used in display 59. -/
theorem phaseCap_neg (α X : ℝ) (n : ℕ) : phaseCap (-α) X n = phaseCap α X n := by
  have he : ee ((-α)*n) = conj (ee (α*n)) := by rw [conj_ee]; congr 1; ring
  have hn : ‖conj (ee (α*n))-1‖ = ‖ee (α*n)-1‖ := by
    rw [← map_one (starRingEnd ℂ),← map_sub,Complex.norm_conj]
    simp only [map_one]
  have hi : conj (ee (α*n))=1 ↔ ee (α*n)=1 := by
    constructor
    · intro h
      have ht := congrArg conj h
      simpa using ht
    · intro h
      simp [h]
  simp only [phaseCap,he,hi,hn]

/-- A signed second variable difference can be replaced by its natural distance. -/
theorem phaseCap_distance (α M : ℝ) (l j h : ℕ) :
    phaseCap (α*((l:ℝ)-j)) M h = phaseCap (α*(Nat.dist l j:ℝ)) M h := by
  rcases le_total j l with hj|hl
  · rw [Nat.dist_eq_sub_of_le_right hj,Nat.cast_sub hj]
  · rw [Nat.dist_eq_sub_of_le hl,Nat.cast_sub hl]
    have he : α*((l:ℝ)-j) = -(α*((j:ℝ)-l)) := by ring
    rw [he,phaseCap_neg]

/-- Enlarge the progression count to the difference times lcm product.
This is the monotonic cap step between Tolev 1999 displays 60 and 61. -/
theorem phaseCap_product (α M H : ℝ) (r h : ℕ)
    (hM : 0≤M) (hH : 0≤H) (hr : 1≤r) (hh : 1≤h) (hrH : (r:ℝ)≤2*H) :
    phaseCap (α*r) M h ≤ phaseCap α (2*M*H) (r*h) := by
  have hrp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hhp : (0:ℝ)<h := by exact_mod_cast (show 0<h by omega)
  have he : (α*r)*(h:ℝ) = α*(r*h:ℕ) := by push_cast; ring
  have hc : 2*M/h+1 ≤ 2*(2*M*H)/(r*h:ℕ)+1 := by
    apply add_le_add _ le_rfl
    rw [Nat.cast_mul,div_le_div_iff₀ hhp (mul_pos hrp hhp)]
    have ht := mul_le_mul_of_nonneg_left hrH (show 0≤2*M by positivity)
    have ht' := mul_le_mul_of_nonneg_right ht hhp.le
    nlinarith
  simp only [phaseCap,he]
  split_ifs
  · exact hc
  · exact min_le_min hc le_rfl

end LeanLab.Tolev2009.Caps341
