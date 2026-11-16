module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 252 to 255, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 133, part 1: every even n in [237610002, 238600000] is x + y, x among the first 166 odd primes, y prime. -/
theorem chk_133_1 : oem 237609011 237610002 238600000 &&& gmo (opm 237609011 495495) (QKo 166) = oem 237609011 237610002 238600000 := by
  decide +kernel

/-- Block 134, part 0: every even n in [238600002, 239590000] is x + y, x among the first 156 odd primes, y prime. -/
theorem chk_134_0 : oem 238599083 238600002 239590000 &&& gmo (opm 238599083 495459) (QKo 156) = oem 238599083 238600002 239590000 := by
  decide +kernel

/-- Block 134, part 1: every even n in [239590002, 240580000] is x + y, x among the first 156 odd primes, y prime. -/
theorem chk_134_1 : oem 239589083 239590002 240580000 &&& gmo (opm 239589083 495459) (QKo 156) = oem 239589083 239590002 240580000 := by
  decide +kernel

/-- Block 135, part 0: every even n in [240580002, 241570000] is x + y, x among the first 150 odd primes, y prime. -/
theorem chk_135_0 : oem 240579125 240580002 241570000 &&& gmo (opm 240579125 495438) (QKo 150) = oem 240579125 240580002 241570000 := by
  decide +kernel

end LeanLab.GvLtR1989
