module

public import LeanLab.PNTPort.BVMax.Primes

/-!
# The sifted sequence `{N - p}` and `π(N - 1; d, N)`

Lab proof, unit U-5333, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

* `goldbachSeq N = {N - p : p < N prime}`, the sequence whose primes are the Goldbach representations
  of `N`;
* `card_dvd_goldbachSeq`: for `d ≥ 1`, `#{m ∈ goldbachSeq N : d ∣ m} = π(N - 1; d, N)`, so the sieve
  remainders of `goldbachSeq N` are the errors `bvPi` and `bvPiPi` control, IDEAS I-5051.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset

/-- `{N - p : p < N, p prime}`. -/
def goldbachSeq (N : ℕ) : Finset ℕ := ((range N).filter Nat.Prime).image (fun p => N - p)

theorem card_dvd_goldbachSeq (N d : ℕ) :
    (((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) = piN (N - 1) d N := by
  unfold goldbachSeq piN
  rw [filter_image, card_image_of_injOn]
  · congr 2
    ext p
    simp only [mem_filter, mem_range, mem_Icc, Function.comp]
    constructor
    · rintro ⟨⟨hp, hpr⟩, hd⟩
      exact ⟨⟨hpr.one_lt.le, by omega⟩, ((Nat.modEq_iff_dvd' hp.le).mpr hd), hpr⟩
    · rintro ⟨⟨h1, h2⟩, hmod, hpr⟩
      exact ⟨⟨by omega, hpr⟩, (Nat.modEq_iff_dvd' (by omega)).mp hmod⟩
  · intro a ha b hb he
    simp only [coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at ha hb
    simp only at he
    omega

end LeanLab.PNTPort.BVMax

