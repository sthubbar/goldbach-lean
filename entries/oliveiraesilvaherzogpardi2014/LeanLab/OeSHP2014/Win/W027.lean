module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 108 to 111, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 24: every even n in [83879912, 84869910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_24 : oem 83878819 83879912 84869910 &&& gmo (opm 83878819 495546) (QKo 182) = oem 83878819 83879912 84869910 := by
  decide +kernel

/-- Segment 27, part 25: every even n in [84869912, 85859910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_25 : oem 84868819 84869912 85859910 &&& gmo (opm 84868819 495546) (QKo 182) = oem 84868819 84869912 85859910 := by
  decide +kernel

/-- Segment 27, part 26: every even n in [85859912, 86849910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_26 : oem 85858819 85859912 86849910 &&& gmo (opm 85858819 495546) (QKo 182) = oem 85858819 85859912 86849910 := by
  decide +kernel

/-- Segment 27, part 27: every even n in [86849912, 87839910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_27 : oem 86848819 86849912 87839910 &&& gmo (opm 86848819 495546) (QKo 182) = oem 86848819 86849912 87839910 := by
  decide +kernel

end LeanLab.OeSHP2014
