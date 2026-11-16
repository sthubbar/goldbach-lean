module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 96 to 99, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 12: every even n in [71999912, 72989910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_12 : oem 71998819 71999912 72989910 &&& gmo (opm 71998819 495546) (QKo 182) = oem 71998819 71999912 72989910 := by
  decide +kernel

/-- Segment 27, part 13: every even n in [72989912, 73979910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_13 : oem 72988819 72989912 73979910 &&& gmo (opm 72988819 495546) (QKo 182) = oem 72988819 72989912 73979910 := by
  decide +kernel

/-- Segment 27, part 14: every even n in [73979912, 74969910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_14 : oem 73978819 73979912 74969910 &&& gmo (opm 73978819 495546) (QKo 182) = oem 73978819 73979912 74969910 := by
  decide +kernel

/-- Segment 27, part 15: every even n in [74969912, 75959910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_15 : oem 74968819 74969912 75959910 &&& gmo (opm 74968819 495546) (QKo 182) = oem 74968819 74969912 75959910 := by
  decide +kernel

end LeanLab.OeSHP2014
