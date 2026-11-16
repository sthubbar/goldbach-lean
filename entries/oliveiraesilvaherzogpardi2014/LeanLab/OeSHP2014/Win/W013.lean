module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 52 to 55, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 25, part 2: every even n in [29769878, 30759876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_2 : oem 29768881 29769878 30759876 &&& gmo (opm 29768881 495498) (QKo 167) = oem 29768881 29769878 30759876 := by
  decide +kernel

/-- Segment 25, part 3: every even n in [30759878, 31749876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_3 : oem 30758881 30759878 31749876 &&& gmo (opm 30758881 495498) (QKo 167) = oem 30758881 30759878 31749876 := by
  decide +kernel

/-- Segment 25, part 4: every even n in [31749878, 32739876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_4 : oem 31748881 31749878 32739876 &&& gmo (opm 31748881 495498) (QKo 167) = oem 31748881 31749878 32739876 := by
  decide +kernel

/-- Segment 25, part 5: every even n in [32739878, 33729876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_5 : oem 32738881 32739878 33729876 &&& gmo (opm 32738881 495498) (QKo 167) = oem 32738881 32739878 33729876 := by
  decide +kernel

end LeanLab.OeSHP2014
