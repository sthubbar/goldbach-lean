module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 88 to 91, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 4: every even n in [64079912, 65069910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_4 : oem 64078819 64079912 65069910 &&& gmo (opm 64078819 495546) (QKo 182) = oem 64078819 64079912 65069910 := by
  decide +kernel

/-- Segment 27, part 5: every even n in [65069912, 66059910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_5 : oem 65068819 65069912 66059910 &&& gmo (opm 65068819 495546) (QKo 182) = oem 65068819 65069912 66059910 := by
  decide +kernel

/-- Segment 27, part 6: every even n in [66059912, 67049910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_6 : oem 66058819 66059912 67049910 &&& gmo (opm 66058819 495546) (QKo 182) = oem 66058819 66059912 67049910 := by
  decide +kernel

/-- Segment 27, part 7: every even n in [67049912, 68039910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_7 : oem 67048819 67049912 68039910 &&& gmo (opm 67048819 495546) (QKo 182) = oem 67048819 67049912 68039910 := by
  decide +kernel

end LeanLab.OeSHP2014
