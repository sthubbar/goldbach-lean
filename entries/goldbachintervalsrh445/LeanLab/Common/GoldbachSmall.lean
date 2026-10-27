module

public import LeanLab.Common.Goldbach

/-!
Kernel-checked binary Goldbach up to 1000, no native_decide.
AI-written Lean code, Claude, 2026-10-16.
Prior art: PNT+ proves the range up to 30; Mehta reported a Lean 3 check to 2e5 on Zulip.
This module is lab test infrastructure, not a new result. 20000 ran out of memory in the cloud.
-/

@[expose] public section

namespace LeanLab

theorem evenGoldbachUpTo_1000 : EvenGoldbachUpTo 1000 :=
  allEvenGB_sound 1000 (by decide +kernel)

end LeanLab
