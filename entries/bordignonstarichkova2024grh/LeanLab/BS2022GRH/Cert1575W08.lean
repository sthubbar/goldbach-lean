module

public import LeanLab.BS2022GRH.Cert1575Defs

/-!
U-1575, run 20261027T0807Z-9485, I-0088: kernel window 8 of the `Eps1500` certificate, numbers
n ≡ 1, 5 mod 6 in [6303001, 7203001), sieve gcd(n, 3000!) = 1, bound Σ (⌊10²⁰/n²⌋ + 1) ≤ 126064392415.
Core only, `decide +kernel`, no native_decide. AI-written Lean code, Claude. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Cert1575Defs

theorem win08 : outer (fac 3000) (10 ^ 20) 126064392415 1000 150 6303001 0 = true := by decide +kernel

end LeanLab.BS2022GRH.Cert1575Defs
