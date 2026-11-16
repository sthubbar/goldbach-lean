module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 24 to 27, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 22, part 0: every even n in [3807404, 4797402] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_0 : oem 3806653 3807404 4797402 &&& gmo (opm 3806653 495375) (QKo 132) = oem 3806653 3807404 4797402 := by
  decide +kernel

/-- Segment 22, part 1: every even n in [4797404, 5787402] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_1 : oem 4796653 4797404 5787402 &&& gmo (opm 4796653 495375) (QKo 132) = oem 4796653 4797404 5787402 := by
  decide +kernel

/-- Segment 22, part 2: every even n in [5787404, 6777402] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_2 : oem 5786653 5787404 6777402 &&& gmo (opm 5786653 495375) (QKo 132) = oem 5786653 5787404 6777402 := by
  decide +kernel

/-- Segment 22, part 3: every even n in [6777404, 7767402] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_3 : oem 6776653 6777404 7767402 &&& gmo (opm 6776653 495375) (QKo 132) = oem 6776653 6777404 7767402 := by
  decide +kernel

end LeanLab.OeSHP2014
