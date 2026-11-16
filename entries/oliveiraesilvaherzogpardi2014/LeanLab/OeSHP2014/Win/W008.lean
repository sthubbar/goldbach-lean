module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 32 to 35, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 23, part 0: every even n in [10759922, 11749920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_0 : oem 10759093 10759922 11749920 &&& gmo (opm 10759093 495414) (QKo 144) = oem 10759093 10759922 11749920 := by
  decide +kernel

/-- Segment 23, part 1: every even n in [11749922, 12739920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_1 : oem 11749093 11749922 12739920 &&& gmo (opm 11749093 495414) (QKo 144) = oem 11749093 11749922 12739920 := by
  decide +kernel

/-- Segment 23, part 2: every even n in [12739922, 13729920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_2 : oem 12739093 12739922 13729920 &&& gmo (opm 12739093 495414) (QKo 144) = oem 12739093 12739922 13729920 := by
  decide +kernel

/-- Segment 23, part 3: every even n in [13729922, 14719920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_3 : oem 13729093 13729922 14719920 &&& gmo (opm 13729093 495414) (QKo 144) = oem 13729093 13729922 14719920 := by
  decide +kernel

end LeanLab.OeSHP2014
