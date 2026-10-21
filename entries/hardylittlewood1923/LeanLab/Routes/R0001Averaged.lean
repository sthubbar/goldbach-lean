module

public import LeanLab.Routes.R0001Parseval

/-!
Route R-0001 salvage, T2 FRONTIER bridge, U-0993.
Averaging over N removes the minor arc L2 barrier: the mean square over n of the minor arc
part of the binary count equals the minor arc L4 mass of the exponential sum.
AI wrote this Lean code. Goldbach is open; nothing here is progress on it.
-/

@[expose] public section

open ZMod Finset

namespace LeanLab.Routes.R0001

variable {N : ℕ} [NeZero N]

/-- Averaged minor arc identity on `ZMod N`. For a set `m` of frequencies, the minor arcs,
the sum over all residues `n` of the squared modulus of `∑_{k ∈ m} S(k)² e(nk/N)`, with
`S = 𝓕 Φ`, equals `N` times `∑_{k ∈ m} |S(k)|⁴`. -/
theorem averaged_minor (Φ : ZMod N → ℂ) (m : Finset (ZMod N)) :
    ∑ n : ZMod N, ‖∑ k ∈ m, 𝓕 Φ k ^ 2 * (stdAddChar (n * k) : ℂ)‖ ^ 2
      = (N : ℝ) * ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4 := by
  classical
  set g : ZMod N → ℂ := fun k => if k ∈ m then 𝓕 Φ k ^ 2 else 0 with hg
  have hinner : ∀ n : ZMod N,
      ∑ k ∈ m, 𝓕 Φ k ^ 2 * (stdAddChar (n * k) : ℂ) = 𝓕 g (-n) := by
    intro n
    rw [dft_apply]
    simp only [hg, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]; congr 2; ring
  simp_rw [hinner]
  rw [Fintype.sum_equiv (Equiv.neg (ZMod N)) (fun n => ‖𝓕 g (-n)‖ ^ 2) (fun n => ‖𝓕 g n‖ ^ 2)
    (fun n => by simp)]
  rw [dft_parseval_norm]
  congr 1
  simp only [hg]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ m)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun k => k ∉ m)) (fun k hk => by
    simp only [Finset.mem_filter] at hk; simp [hk.2])]
  rw [add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [hk, ite_true, norm_pow]; ring

/-- Vacuity test: with `m` empty both sides are 0, and with `m` everything the identity is
Parseval for `S²`; here the one-point case `N = 1`, `Φ = 1`, `m = univ`. -/
example : ∑ n : ZMod 1, ‖∑ k ∈ (Finset.univ : Finset (ZMod 1)),
    𝓕 (fun _ : ZMod 1 => (1 : ℂ)) k ^ 2 * (stdAddChar (n * k) : ℂ)‖ ^ 2 = 1 := by
  rw [averaged_minor]; simp [dft_apply]

end LeanLab.Routes.R0001
