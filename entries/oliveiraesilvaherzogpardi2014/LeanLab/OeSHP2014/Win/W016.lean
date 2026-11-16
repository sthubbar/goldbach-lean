module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 64 to 67, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 26, part 3: every even n in [40968938, 41958936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_3 : oem 40967899 40968938 41958936 &&& gmo (opm 40967899 495519) (QKo 174) = oem 40967899 40968938 41958936 := by
  decide +kernel

/-- Segment 26, part 4: every even n in [41958938, 42948936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_4 : oem 41957899 41958938 42948936 &&& gmo (opm 41957899 495519) (QKo 174) = oem 41957899 41958938 42948936 := by
  decide +kernel

/-- Segment 26, part 5: every even n in [42948938, 43938936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_5 : oem 42947899 42948938 43938936 &&& gmo (opm 42947899 495519) (QKo 174) = oem 42947899 42948938 43938936 := by
  decide +kernel

/-- Segment 26, part 6: every even n in [43938938, 44928936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_6 : oem 43937899 43938938 44928936 &&& gmo (opm 43937899 495519) (QKo 174) = oem 43937899 43938938 44928936 := by
  decide +kernel

end LeanLab.OeSHP2014
