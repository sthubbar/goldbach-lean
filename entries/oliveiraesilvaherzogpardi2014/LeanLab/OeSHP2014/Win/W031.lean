module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 124 to 124, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 40: every even n in [99719912, 100000000] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_40 : oem 99718819 99719912 100000000 &&& gmo (opm 99718819 140591) (QKo 182) = oem 99718819 99719912 100000000 := by
  decide +kernel

end LeanLab.OeSHP2014
