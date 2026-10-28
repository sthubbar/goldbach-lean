module

public import LeanLab.BS2022GRH.Cert1575Defs

/-!
U-1575, run 20261027T0807Z-9485, I-0088: kernel window 7 of the `Eps1500` certificate, numbers
n ≡ 1, 5 mod 6 in [5403001, 6303001), sieve gcd(n, 3000!) = 1, bound Σ (⌊10²⁰/n²⌋ + 1) ≤ 169529993149.
Core only, `decide +kernel`, no native_decide. AI-written Lean code, Claude. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Cert1575Defs

theorem win07 : outer (fac 3000) (10 ^ 20) 169529993149 1000 150 5403001 0 = true := by decide +kernel

end LeanLab.BS2022GRH.Cert1575Defs
