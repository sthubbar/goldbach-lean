module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 116 to 119, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 32: every even n in [91799912, 92789910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_32 : oem 91798819 91799912 92789910 &&& gmo (opm 91798819 495546) (QKo 182) = oem 91798819 91799912 92789910 := by
  decide +kernel

/-- Segment 27, part 33: every even n in [92789912, 93779910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_33 : oem 92788819 92789912 93779910 &&& gmo (opm 92788819 495546) (QKo 182) = oem 92788819 92789912 93779910 := by
  decide +kernel

/-- Segment 27, part 34: every even n in [93779912, 94769910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_34 : oem 93778819 93779912 94769910 &&& gmo (opm 93778819 495546) (QKo 182) = oem 93778819 93779912 94769910 := by
  decide +kernel

/-- Segment 27, part 35: every even n in [94769912, 95759910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_35 : oem 94768819 94769912 95759910 &&& gmo (opm 94768819 495546) (QKo 182) = oem 94768819 94769912 95759910 := by
  decide +kernel

end LeanLab.OeSHP2014
