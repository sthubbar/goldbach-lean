module

public import Mathlib

/-!
# A fast modular power

`pm` is a binary modular power with fuel, proved equal to exponentiation in `ZMod`, so one
primality test costs one modular power in the kernel.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.ModPow

/-- Binary modular power with fuel. -/
def pm : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m else
      let h := pm fuel a (e / 2) m
      if e % 2 = 1 then h * h % m * a % m else h * h % m

theorem pm_cast : ∀ fuel a e m, e < 2 ^ fuel → ((pm fuel a e m : ℕ) : ZMod m) = (a : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero => intro a e m he; simp at he; subst he; simp [pm]
  | succ k ih =>
    intro a e m he
    simp only [pm]
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [if_neg h0]
      have hlt : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
      have IH := ih a (e / 2) m hlt
      have he2 : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1, pow_add, pow_mul, pow_one]
        ring
      · rw [if_neg h1]
        have h1' : e % 2 = 0 := by omega
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1', add_zero, pow_mul]
        ring

/-- The cast from `ZMod N` to `ZMod p`, for `p ∣ N`, sends `-1` to `-1`. This is stated with no
`Fact p.Prime` in context, since on v4.35.0-rc3 the field instance on `ZMod p` then blocks `map_neg`
at reducible transparency. -/
theorem castHom_neg_one {N p : ℕ} (h : p ∣ N) : ZMod.castHom h (ZMod p) (-1) = -1 := by
  simp only [map_neg, map_one]

end GoldbachLean.Saouter1998.ModPow
