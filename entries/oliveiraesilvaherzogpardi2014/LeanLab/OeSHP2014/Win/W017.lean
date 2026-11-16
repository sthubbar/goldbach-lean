module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 68 to 71, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 26, part 7: every even n in [44928938, 45918936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_7 : oem 44927899 44928938 45918936 &&& gmo (opm 44927899 495519) (QKo 174) = oem 44927899 44928938 45918936 := by
  decide +kernel

/-- Segment 26, part 8: every even n in [45918938, 46908936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_8 : oem 45917899 45918938 46908936 &&& gmo (opm 45917899 495519) (QKo 174) = oem 45917899 45918938 46908936 := by
  decide +kernel

/-- Segment 26, part 9: every even n in [46908938, 47898936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_9 : oem 46907899 46908938 47898936 &&& gmo (opm 46907899 495519) (QKo 174) = oem 46907899 46908938 47898936 := by
  decide +kernel

/-- Segment 26, part 10: every even n in [47898938, 48888936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_10 : oem 47897899 47898938 48888936 &&& gmo (opm 47897899 495519) (QKo 174) = oem 47897899 47898938 48888936 := by
  decide +kernel

end LeanLab.OeSHP2014
