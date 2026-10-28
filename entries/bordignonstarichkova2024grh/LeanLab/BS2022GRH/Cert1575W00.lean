module

public import LeanLab.BS2022GRH.Cert1575Defs

/-!
U-1575, run 20261027T0807Z-9485, I-0088: kernel window 0 of the `Eps1500` certificate, numbers
n ≡ 1, 5 mod 6 in [1501, 3001), sieve gcd(n, 1499!) = 1, bound Σ (⌊10²⁰/n²⌋ + 1) ≤ 4257878939378612.
Core only, `decide +kernel`, no native_decide. AI-written Lean code, Claude. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Cert1575Defs

theorem win00 : outer (fac 1499) (10 ^ 20) 4257878939378612 250 1 1501 0 = true := by decide +kernel

end LeanLab.BS2022GRH.Cert1575Defs
