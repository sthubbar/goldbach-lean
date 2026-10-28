module


/-!
BS2022GRH, P0021, idea I-0088, unit U-1575, PC run 20261027T0807Z-9485: core only checker
definitions for the kernel certificate of `Eps1500`. No Mathlib, so the window modules stay light.

* `fac m` is m!, proved equal to `Nat.factorial m` in `Cert1575.lean`.
* `term F M n` is ⌊M/n²⌋ + 1 when gcd(F, n) = 1 and 0 otherwise.
* `T F M f n` sums `term` over n + 6i and n + 6i + 4 for i < f, the residues 1 and 5 mod 6 when
  n ≡ 1 mod 6.
* `inner` and `outer` compute the same sum in chunks of B steps, forcing the accumulator after
  each chunk; `outer F M S B K n 0 = true` says T F M (B·K) n ≤ S.

AI-written Lean code, Claude, unit U-1575. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.BS2022GRH.Cert1575Defs

def fac : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fac k

def term (F M n : Nat) : Nat := cond (Nat.beq (Nat.gcd F n) 1) (M / (n * n) + 1) 0

def T (F M : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => term F M n + term F M (n + 4) + T F M f (n + 6)

def inner (F M : Nat) : Nat → Nat → Nat → Nat
  | 0, _, s => s
  | f + 1, n, s => inner F M f (n + 6) (s + term F M n + term F M (n + 4))

def outer (F M S B : Nat) : Nat → Nat → Nat → Bool
  | 0, _, s => Nat.ble s S
  | k + 1, n, s =>
    let s' := inner F M B n s
    Nat.ble s' S && outer F M S B k (n + 6 * B) s'

end LeanLab.BS2022GRH.Cert1575Defs
