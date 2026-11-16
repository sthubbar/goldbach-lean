module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 44 to 47, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 29, part 1: every even n in [31690002, 32680000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_29_1 : oem 31689191 31690002 32680000 &&& gmo (opm 31689191 495405) (QKo 140) = oem 31689191 31690002 32680000 := by
  decide +kernel

/-- Block 30, part 0: every even n in [32680002, 33670000] is x + y, x among the first 135 odd primes, y prime. -/
theorem chk_30_0 : oem 32679233 32680002 33670000 &&& gmo (opm 32679233 495384) (QKo 135) = oem 32679233 32680002 33670000 := by
  decide +kernel

/-- Block 30, part 1: every even n in [33670002, 34660000] is x + y, x among the first 135 odd primes, y prime. -/
theorem chk_30_1 : oem 33669233 33670002 34660000 &&& gmo (opm 33669233 495384) (QKo 135) = oem 33669233 33670002 34660000 := by
  decide +kernel

/-- Block 31, part 0: every even n in [34660002, 35650000] is x + y, x among the first 150 odd primes, y prime. -/
theorem chk_31_0 : oem 34659125 34660002 35650000 &&& gmo (opm 34659125 495438) (QKo 150) = oem 34659125 34660002 35650000 := by
  decide +kernel

end LeanLab.GvLtR1989
