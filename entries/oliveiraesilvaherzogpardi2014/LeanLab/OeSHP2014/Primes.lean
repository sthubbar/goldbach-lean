module

public import Mathlib
public import LeanLab.OeSHP2014.Core

/-!
# The prime lists of the checker

`PL0` and `PL1` of `Core.lean` are proved to contain every prime below 20000, by a walk `cw`
over the integers that checks each prime against the next list entry, and every entry of `PL0`
is proved prime by trial division. Each walk covers 10000 integers.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

/-- `true` when some `d' ≥ d` with `d' * d' ≤ p` divides `p`; fuel bounded search. -/
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

/-- Walk `q = start, start + 1, ...`: each prime `q` must be the next entry of the list. -/
def cw : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, q, L =>
    if q < 2 || hasDiv q q 2 then cw fuel (q + 1) L else
      match L with
      | h :: t => h == q && cw fuel (q + 1) t
      | [] => false

theorem cw_sound : ∀ fuel q L, cw fuel q L = true →
    ∀ m, q ≤ m → m < q + fuel → m.Prime → m ∈ L := by
  intro fuel
  induction fuel with
  | zero => intro q L _ m h1 h2; omega
  | succ k ih =>
    intro q L h m h1 h2 hm
    simp only [cw] at h
    by_cases hc : (q < 2 || hasDiv q q 2) = true
    · rw [if_pos hc] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
        rcases hc with hc | hc
        · exact absurd hm (by interval_cases q <;> norm_num)
        · exact absurd hm (hasDiv_sound q q 2 le_rfl hc)
      · exact ih (q + 1) L h m hlt (by omega) hm
    · rw [if_neg hc] at h
      match L, h with
      | (a :: t), h =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨ha, hw⟩ := h
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · simp [ha]
        · exact List.mem_cons_of_mem _ (ih (q + 1) t hw m hlt (by omega) hm)

/-- `noDivFrom n fuel d` is `true` when no `m` with `d ≤ m` and `m * m ≤ n` divides `n`,
provided enough fuel. -/
def noDivFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else noDivFrom n fuel (d + 1)

/-- Boolean primality by trial division up to the square root. -/
def primeB (n : ℕ) : Bool := 2 ≤ n && noDivFrom n n 2

theorem noDivFrom_sound (n : ℕ) : ∀ fuel d, noDivFrom n fuel d = true →
    ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDivFrom] at h
  | succ k ih =>
    intro d h m hdm hmm hdiv
    simp only [noDivFrom] at h
    by_cases h1 : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : n % d = 0
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
        · exact h2 (Nat.mod_eq_zero_of_dvd hdiv)
        · exact ih (d + 1) h m hlt hmm hdiv

theorem primeB_sound {n : ℕ} (h : primeB n = true) : n.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms hdiv => ?_⟩
  exact noDivFrom_sound n n 2 hnd m hm (Nat.le_sqrt.mp hms) hdiv

theorem PL0_cw : cw 10000 0 PL0 = true := by decide +kernel

theorem PL1_cw : cw 10000 10000 PL1 = true := by decide +kernel

/-- `PL` holds every prime below 20000. -/
theorem PL_complete : ∀ m, m < 20000 → m.Prime → m ∈ PL := by
  intro m hm hp
  unfold PL
  rw [List.mem_append]
  by_cases h1 : m < 10000
  · exact Or.inl (cw_sound 10000 0 PL0 PL0_cw m (Nat.zero_le _) (by omega) hp)
  · exact Or.inr (cw_sound 10000 10000 PL1 PL1_cw m (by omega) (by omega) hp)

theorem PL0_allPrime : PL0.all (fun q => primeB q) = true := by decide +kernel

theorem PL0_tail_odd : PL0.tail.all (fun q => q % 2 == 1) = true := by decide +kernel

/-- Every entry of `QKo K` is an odd prime. -/
theorem QKo_prime (K : ℕ) : ∀ x ∈ QKo K, x.Prime ∧ x % 2 = 1 := by
  intro x hx
  have h1 : x ∈ PL0.tail := List.mem_of_mem_take hx
  refine ⟨primeB_sound (List.all_eq_true.mp PL0_allPrime x (List.mem_of_mem_tail h1)), ?_⟩
  have := List.all_eq_true.mp PL0_tail_odd x h1
  simpa using this

theorem PL_eq_cons : PL = 2 :: PL.tail := by decide +kernel

/-- `PL.tail` holds every odd prime below 20000. -/
theorem PL_tail_complete : ∀ m, m < 20000 → m.Prime → m ≠ 2 → m ∈ PL.tail := by
  intro m hm hp h2
  have h := PL_complete m hm hp
  rw [PL_eq_cons] at h
  rcases List.mem_cons.mp h with h | h
  · exact absurd h h2
  · exact h

end LeanLab.OeSHP2014
