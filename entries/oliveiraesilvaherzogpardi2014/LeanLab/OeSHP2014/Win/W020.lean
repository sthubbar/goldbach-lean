module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 80 to 83, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 26, part 19: every even n in [56808938, 57798936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_19 : oem 56807899 56808938 57798936 &&& gmo (opm 56807899 495519) (QKo 174) = oem 56807899 56808938 57798936 := by
  decide +kernel

/-- Segment 26, part 20: every even n in [57798938, 58788936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_20 : oem 57797899 57798938 58788936 &&& gmo (opm 57797899 495519) (QKo 174) = oem 57797899 57798938 58788936 := by
  decide +kernel

/-- Segment 26, part 21: every even n in [58788938, 59778936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_21 : oem 58787899 58788938 59778936 &&& gmo (opm 58787899 495519) (QKo 174) = oem 58787899 58788938 59778936 := by
  decide +kernel

/-- Segment 26, part 22: every even n in [59778938, 60119910] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_22 : oem 59777899 59778938 60119910 &&& gmo (opm 59777899 171006) (QKo 174) = oem 59777899 59778938 60119910 := by
  decide +kernel

end LeanLab.OeSHP2014
