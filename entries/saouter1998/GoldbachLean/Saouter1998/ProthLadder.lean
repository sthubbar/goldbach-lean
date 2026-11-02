module

public import Mathlib
public import GoldbachLean.Saouter1998.Goldbach
public import GoldbachLean.Saouter1998.Proth
public import GoldbachLean.Saouter1998.Ladder

/-!
# Ternary Goldbach up to 10^20 from binary Goldbach up to 4e18

Saouter's prime ladder as in Helfgott and Platt, Section 3, at Saouter's range: 25 Proth primes `k 2^34 + 1` with
`k < 2^34`, rising from 3 with every gap at most `4e18 - 2`, give ternary Goldbach up to `10^20` from
binary Goldbach up to `4e18`, the computation of Oliveira e Silva, Herzog and Pardi, which is a
hypothesis here and never an axiom. This is not Saouter's computation: his ladder of about
`250 * 10^6` rungs on top of the even range `4 * 10^11` is not reverified beyond the 100 rungs of
Table 1. The range of the paper is reproduced by a different, shorter ladder on a much larger even
input. Each rung costs one modular power in the kernel.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.ProthLadder

open GoldbachLean.Saouter1998.Proth GoldbachLean.Saouter1998.Ladder

/-- The 25 rungs as pairs of the Proth multiplier `k` and a Proth base `a`, so the rung is
`k * 2^34 + 1` and `a^((N-1)/2)` is `-1` modulo it. -/
def rungsK : List (ℕ × ℕ) := [(232830553, 3), (465661177, 3), (698491779, 5), (931322415, 7),
  (1164153045, 7), (1396983685, 3), (1629814317, 11), (1862644839, 5), (2095475355, 7),
  (2328305925, 7), (2561136565, 3), (2793967113, 5), (3026797689, 5), (3259628295, 13),
  (3492458899, 3), (3725289523, 3), (3958120159, 3), (4190950765, 3), (4423781383, 3),
  (4656612025, 3), (4889442663, 5), (5122273297, 3), (5355103933, 3), (5587934515, 3),
  (5820765157, 3)]

/-- The 25 rungs, each `k * 2^34 + 1`. -/
def rungs : List ℕ := rungsK.map (fun x => x.1 * 2 ^ 34 + 1)

/-- The rungs in decimal. -/
theorem rungs_values : rungs = [3999998442578378753, 7999998104927469569, 11999997389319438337,
    15999997257826959361, 19999997023255265281, 23999996960482263041, 27999996760270307329,
    31999994670272741377, 35999992477195960321, 39999991211832115201, 43999991149059112961,
    47999989505738145793, 51999988343453515777, 55999987696564961281, 59999987015316668417,
    63999986677665759233, 67999986546173280257, 71999985899284725761, 75999985458554601473,
    79999985430141337601, 83999985333008596993, 87999985167156379649, 91999985035663900673,
    95999983976458485761, 99999983948045221889] := by decide +kernel

/-- Every Proth test passes, one modular power per rung. -/
theorem rungsK_proth : rungsK.all (fun x => prothB x.1 33 x.2) = true := by decide +kernel

/-- The rung primality leaf: every rung is prime, by Proth's theorem. -/
theorem rungs_prime : ∀ p ∈ rungs, p.Prime := by
  intro p hp
  simp only [rungs, List.mem_map] at hp
  obtain ⟨⟨k, a⟩, hmem, rfl⟩ := hp
  have h := List.all_eq_true.mp rungsK_proth (k, a) hmem
  exact prime_of_prothB (k := k) (m := 33) (a := a) h

instance (B : ℕ) : DecidableRel (Step2 B) := fun a b => by
  unfold Step2; infer_instance

/-- The ladder rises from 3 with every gap at most `4e18 - 2`. -/
theorem rungs_chain : (3 :: rungs).IsChain (Step2 (4 * 10 ^ 18)) := by decide +kernel

/-- The top rung plus `4e18` reaches past `10^20`. -/
theorem rungs_reach : 10 ^ 20 ≤ rungs.getLastD 3 + 4 * 10 ^ 18 := by decide +kernel

/-- Ternary Goldbach up to `10^20`, conditional on binary Goldbach up to `4e18` only. -/
theorem ternaryGoldbachUpTo_1e20_of_even (h : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    TernaryGoldbachUpTo (10 ^ 20) :=
  ternary_of_ladder2 h rungs rungs_prime rungs_chain rungs_reach

/-! ### Vacuity: the hypothesis shape is satisfiable, the same lemma at a small bound -/

/-- Binary Goldbach up to 100, kernel checked. -/
theorem evenGoldbachUpTo_100 : EvenGoldbachUpTo 100 := allEvenGB_sound 100 (by decide +kernel)

/-- A small ladder with the same shape, rungs 97 and 193, gaps at most 98. -/
theorem smallLadder_chain : [3, 97, 193].IsChain (Step2 100) := by decide +kernel

/-- Vacuity instance: the same ladder lemma at `B = 100` gives ternary Goldbach up to 293. -/
theorem ternaryGoldbachUpTo_293_vacuity : TernaryGoldbachUpTo 293 :=
  ternary_of_ladder2 evenGoldbachUpTo_100 [97, 193]
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> norm_num)
    smallLadder_chain (by decide)

end GoldbachLean.Saouter1998.ProthLadder
