module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 144 to 147, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 79, part 1: every even n in [130690002, 131680000] is x + y, x among the first 151 odd primes, y prime. -/
theorem chk_79_1 : oem 130689121 130690002 131680000 &&& gmo (opm 130689121 495440) (QKo 151) = oem 130689121 130690002 131680000 := by
  decide +kernel

/-- Block 80, part 0: every even n in [131680002, 132670000] is x + y, x among the first 152 odd primes, y prime. -/
theorem chk_80_0 : oem 131679119 131680002 132670000 &&& gmo (opm 131679119 495441) (QKo 152) = oem 131679119 131680002 132670000 := by
  decide +kernel

/-- Block 80, part 1: every even n in [132670002, 133660000] is x + y, x among the first 152 odd primes, y prime. -/
theorem chk_80_1 : oem 132669119 132670002 133660000 &&& gmo (opm 132669119 495441) (QKo 152) = oem 132669119 132670002 133660000 := by
  decide +kernel

/-- Block 81, part 0: every even n in [133660002, 134650000] is x + y, x among the first 147 odd primes, y prime. -/
theorem chk_81_0 : oem 133659145 133660002 134650000 &&& gmo (opm 133659145 495428) (QKo 147) = oem 133659145 133660002 134650000 := by
  decide +kernel

end LeanLab.GvLtR1989
