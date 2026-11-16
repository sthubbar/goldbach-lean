module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 56 to 59, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 25, part 6: every even n in [33729878, 34719876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_6 : oem 33728881 33729878 34719876 &&& gmo (opm 33728881 495498) (QKo 167) = oem 33728881 33729878 34719876 := by
  decide +kernel

/-- Segment 25, part 7: every even n in [34719878, 35709876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_7 : oem 34718881 34719878 35709876 &&& gmo (opm 34718881 495498) (QKo 167) = oem 34718881 34719878 35709876 := by
  decide +kernel

/-- Segment 25, part 8: every even n in [35709878, 36699876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_8 : oem 35708881 35709878 36699876 &&& gmo (opm 35708881 495498) (QKo 167) = oem 35708881 35709878 36699876 := by
  decide +kernel

/-- Segment 25, part 9: every even n in [36699878, 37689876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_9 : oem 36698881 36699878 37689876 &&& gmo (opm 36698881 495498) (QKo 167) = oem 36698881 36699878 37689876 := by
  decide +kernel

end LeanLab.OeSHP2014
