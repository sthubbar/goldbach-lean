module

public import Mathlib
public import LeanLab.OeSHP2014.Sieve

/-!
# Least Goldbach primes and bounds on ranges of even numbers

* `minGB n`: the least prime `p` with `n - p` prime, and `0` when there is none.
* `GBBound A B q`: every even `n` in `[A, B]` is `p + (n - p)` with `p ≤ q` and both prime.
* `gbBound_of_owcheck`: one window equality of `Core.lean` gives such a bound.
* `minGB_eq_of_cert`: a bound `q` at `n` and a divisor of `n - x` for every prime `x < q`
  give `minGB n = q`.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

/-- The least prime `p` with `n - p` prime, and `0` when there is no such prime. -/
noncomputable def minGB (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, p.Prime ∧ (n - p).Prime then Nat.find h else 0

/-- With a Goldbach partition `n = p + (n - p)` in hand, `minGB n` is prime, `n - minGB n` is
prime and `minGB n ≤ p`. -/
theorem minGB_spec {n p : ℕ} (hp : p.Prime) (hnp : (n - p).Prime) :
    (minGB n).Prime ∧ (n - minGB n).Prime ∧ minGB n ≤ p := by
  classical
  have hex : ∃ p, p.Prime ∧ (n - p).Prime := ⟨p, hp, hnp⟩
  unfold minGB
  rw [dif_pos hex]
  exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, Nat.find_min' hex ⟨hp, hnp⟩⟩

/-- Every even `n` with `A ≤ n ≤ B` has a Goldbach partition whose smaller prime is at most
`q`. -/
def GBBound (A B q : ℕ) : Prop :=
  ∀ n : ℕ, Even n → A ≤ n → n ≤ B → ∃ p, p.Prime ∧ (n - p).Prime ∧ p ≤ q

theorem take_le (K q : ℕ) (h : (QKo K).all (fun x => decide (x ≤ q)) = true) :
    ∀ x ∈ QKo K, x ≤ q := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simpa using this

/-- One window check bounds the least Goldbach prime on `[A, B]`. -/
theorem gbBound_of_owcheck {lo Wb A B K q : ℕ} (h3 : 3 ≤ lo) (hlo1 : lo % 2 = 1)
    (hW : lo + 2 * Wb ≤ 20000 * 20000) (hlo : lo < A) (hAe : A % 2 = 0)
    (hq : ∀ x ∈ QKo K, x ≤ q)
    (h : oem lo A B &&& gmo (opm lo Wb) (QKo K) = oem lo A B) : GBBound A B q := by
  intro n hn hA hB
  obtain ⟨x, hx, hpr⟩ := partition_of_owcheck h3 hlo1 hW hlo hAe h n hA hB (Nat.even_iff.mp hn)
  exact ⟨x, (QKo_prime K x hx).1, hpr, hq x hx⟩

/-- Join two adjacent bounds. -/
theorem GBBound.join {A B A' C q : ℕ} (h1 : GBBound A B q) (h2 : GBBound A' C q)
    (hBA : B + 2 = A') (hB : Even B) : GBBound A C q := by
  intro n hn hA hC
  by_cases h : n ≤ B
  · exact h1 n hn hA h
  · apply h2 n hn _ hC
    obtain ⟨k, hk⟩ := hn
    obtain ⟨j, hj⟩ := hB
    omega

/-- A bound stays a bound for a larger `q`. -/
theorem GBBound.mono {A B q q' : ℕ} (h : GBBound A B q) (hq : q ≤ q') : GBBound A B q' := by
  intro n hn hA hB
  obtain ⟨p, hp, hnp, hpq⟩ := h n hn hA hB
  exact ⟨p, hp, hnp, le_trans hpq hq⟩

/-- A bound on a range is a bound on a smaller range. -/
theorem GBBound.sub {A B A' B' q : ℕ} (h : GBBound A B q) (hA : A ≤ A') (hB : B' ≤ B) :
    GBBound A' B' q := by
  intro n hn h1 h2
  exact h n hn (le_trans hA h1) (le_trans h2 hB)

/-- A bound on a range bounds `minGB` there, and the partition by `minGB` exists. -/
theorem minGB_of_bound {A B q n : ℕ} (h : GBBound A B q) (hn : Even n) (hA : A ≤ n)
    (hB : n ≤ B) : (minGB n).Prime ∧ (n - minGB n).Prime ∧ minGB n ≤ q := by
  obtain ⟨p, hp, hnp, hpq⟩ := h n hn hA hB
  obtain ⟨h1, h2, h3⟩ := minGB_spec hp hnp
  exact ⟨h1, h2, le_trans h3 hpq⟩

/-- Divisor certificate: each pair `(x, d)` has `2 ≤ d`, `d * d ≤ n - x` and `d ∣ n - x`, so
`n - x` is not prime. -/
def certOK (n : ℕ) (cert : List (ℕ × ℕ)) : Bool :=
  cert.all (fun c => decide (2 ≤ c.2) && decide (c.2 * c.2 ≤ n - c.1) && (n - c.1) % c.2 == 0)

/-- If `n` has a Goldbach partition with smaller prime at most `q`, and for every prime
`x < q` the number `n - x` has a divisor certified in `cert`, then `minGB n = q`. -/
theorem minGB_eq_of_cert {n q : ℕ} (cert : List (ℕ × ℕ)) (hq : q < 20000)
    (hcov : PL.filter (fun x => decide (x < q)) = cert.map Prod.fst)
    (hok : certOK n cert = true) (hb : GBBound n n q) (hn : Even n) : minGB n = q := by
  obtain ⟨h1, h2, h3⟩ := minGB_of_bound hb hn le_rfl le_rfl
  by_contra hne
  have hlt : minGB n < q := lt_of_le_of_ne h3 hne
  have hmem : minGB n ∈ PL.filter (fun x => decide (x < q)) :=
    List.mem_filter.mpr ⟨PL_complete _ (by omega) h1, by simpa using hlt⟩
  rw [hcov] at hmem
  obtain ⟨c, hc, hcx⟩ := List.mem_map.mp hmem
  have hc' := List.all_eq_true.mp hok c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc'
  obtain ⟨⟨hd2, hdd⟩, hdvd⟩ := hc'
  rw [hcx] at hdd hdvd
  have hdv : c.2 ∣ n - minGB n := Nat.dvd_of_mod_eq_zero hdvd
  rcases h2.eq_one_or_self_of_dvd c.2 hdv with h | h
  · omega
  · rw [← h] at hdd
    nlinarith

end LeanLab.OeSHP2014
