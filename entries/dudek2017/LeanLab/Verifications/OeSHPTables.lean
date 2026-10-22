module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Kernel-checkable compositeness certificates, kept from the lab file of the same name, which
also held the records of Oliveira e Silva, Herzog and Pardi 2014. Only the two checkers used by
`Verifications/Top50/Base.lean` are kept here: `certOK m d`, a divisor `d` of `m`, and
`hasDiv p fuel d`, a bounded trial division search, each with its soundness theorem.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Verifications.OeSHP


/-- `d` certifies that `m` is composite. -/
def certOK (m d : ℕ) : Bool := 1 < d && d < m && m % d == 0

theorem not_prime_of_certOK {m d : ℕ} (h : certOK m d = true) : ¬ m.Prime := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro hp
  have := (Nat.Prime.eq_one_or_self_of_dvd hp d (Nat.dvd_of_mod_eq_zero h3))
  omega

/-- `true` when some `d' ≥ d` with `d' * d' ≤ p` divides `p`; fuel-bounded search. -/
def hasDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => if p < d * d then false else if p % d = 0 then true else hasDiv p fuel (d + 1)

theorem hasDiv_sound (p : ℕ) : ∀ fuel d, 2 ≤ d → hasDiv p fuel d = true → ¬ p.Prime := by
  intro fuel
  induction fuel with
  | zero => intro d _ h; simp [hasDiv] at h
  | succ k ih =>
    intro d hd h
    simp only [hasDiv] at h
    by_cases h1 : p < d * d
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : p % d = 0
      · intro hp
        have := hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h2)
        have : d < p := by nlinarith
        omega
      · rw [if_neg h2] at h; exact ih (d + 1) (by omega) h

end LeanLab.Verifications.OeSHP
