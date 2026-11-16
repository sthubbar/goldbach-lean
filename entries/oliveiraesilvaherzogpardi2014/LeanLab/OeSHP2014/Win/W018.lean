module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 72 to 75, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 26, part 11: every even n in [48888938, 49878936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_11 : oem 48887899 48888938 49878936 &&& gmo (opm 48887899 495519) (QKo 174) = oem 48887899 48888938 49878936 := by
  decide +kernel

/-- Segment 26, part 12: every even n in [49878938, 50868936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_12 : oem 49877899 49878938 50868936 &&& gmo (opm 49877899 495519) (QKo 174) = oem 49877899 49878938 50868936 := by
  decide +kernel

/-- Segment 26, part 13: every even n in [50868938, 51858936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_13 : oem 50867899 50868938 51858936 &&& gmo (opm 50867899 495519) (QKo 174) = oem 50867899 50868938 51858936 := by
  decide +kernel

/-- Segment 26, part 14: every even n in [51858938, 52848936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_14 : oem 51857899 51858938 52848936 &&& gmo (opm 51857899 495519) (QKo 174) = oem 51857899 51858938 52848936 := by
  decide +kernel

end LeanLab.OeSHP2014
