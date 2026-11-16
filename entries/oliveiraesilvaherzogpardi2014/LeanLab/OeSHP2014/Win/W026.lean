module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 104 to 107, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 20: every even n in [79919912, 80909910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_20 : oem 79918819 79919912 80909910 &&& gmo (opm 79918819 495546) (QKo 182) = oem 79918819 79919912 80909910 := by
  decide +kernel

/-- Segment 27, part 21: every even n in [80909912, 81899910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_21 : oem 80908819 80909912 81899910 &&& gmo (opm 80908819 495546) (QKo 182) = oem 80908819 80909912 81899910 := by
  decide +kernel

/-- Segment 27, part 22: every even n in [81899912, 82889910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_22 : oem 81898819 81899912 82889910 &&& gmo (opm 81898819 495546) (QKo 182) = oem 81898819 81899912 82889910 := by
  decide +kernel

/-- Segment 27, part 23: every even n in [82889912, 83879910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_23 : oem 82888819 82889912 83879910 &&& gmo (opm 82888819 495546) (QKo 182) = oem 82888819 82889912 83879910 := by
  decide +kernel

end LeanLab.OeSHP2014
