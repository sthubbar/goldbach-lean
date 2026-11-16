module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 112 to 115, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 28: every even n in [87839912, 88829910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_28 : oem 87838819 87839912 88829910 &&& gmo (opm 87838819 495546) (QKo 182) = oem 87838819 87839912 88829910 := by
  decide +kernel

/-- Segment 27, part 29: every even n in [88829912, 89819910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_29 : oem 88828819 88829912 89819910 &&& gmo (opm 88828819 495546) (QKo 182) = oem 88828819 88829912 89819910 := by
  decide +kernel

/-- Segment 27, part 30: every even n in [89819912, 90809910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_30 : oem 89818819 89819912 90809910 &&& gmo (opm 89818819 495546) (QKo 182) = oem 89818819 89819912 90809910 := by
  decide +kernel

/-- Segment 27, part 31: every even n in [90809912, 91799910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_31 : oem 90808819 90809912 91799910 &&& gmo (opm 90808819 495546) (QKo 182) = oem 90808819 90809912 91799910 := by
  decide +kernel

end LeanLab.OeSHP2014
