module

public import LeanLab.DensityGoldbach.Statements
public import LeanLab.DensityGoldbach.Binary
public import LeanLab.DensityGoldbach.AlsetriShaoLocal
public import LeanLab.DensityGoldbach.PrimesAP

/-!
P0047 A. Alsetri, X. Shao 2024, Density versions of the binary Goldbach problem, arXiv 2405.18576 v2,
read 2026-10-21 by WebFetch of arxiv.org/html/2405.18576v2. Unit U-1446, run 20261021T2003Z-599.

Theorem 1.2 (Section 1): if every reduced class `b mod W` has relative lower density of `A` above
`1/2`, uniformly, then almost all even numbers are in `A + A`. The stub `AlsetriShao12` of
Statements.lean is proved here CONDITIONAL ON three cited analytic inputs, exactly those the paper's
Section 4 uses:

* `AS_Prop31`, the paper's transference principle, Proposition 3.1, Section 3: on `Z_N` with
  `E`-normalisation, `0 ≤ f_i ≤ ν_i`, `E f₁ + E f₂ ≥ 1 + δ`, `‖f̂_i‖_p ≤ M` for some `2 < p < 4`,
  and `|ν̂_i(r) - 1_{r=0}| ≤ c(δ, η, p, M)` give `f₁ * f₂(n) > δ³/1000` for all but `η N` of `n`.
* `Green62`, Green, Roth's theorem in the primes, Ann. Math. 2005, Lemma 6.2, cited in Section 4
  for the pseudorandomness of the majorant: `|ν̂_b(r)| ≤ c` for `r ≠ 0` once `z` is large,
  `W = ∏_{p ≤ z} p`, `ν_b(n) = (φ(W)/W) log(Wn + b) 1_{Wn+b prime}`.
* `Green66`, Green's Lemma 6.6, the restriction estimate, cited in Section 4 with `p = 3`:
  `0 ≤ f ≤ ν_b` gives `‖f̂‖_3 ≤ C` with `C` absolute.

All three are stated for prime `N` only and with an `N₀` threshold, which makes them weaker than,
or equal to, the published forms. Everything else is PROVED here from the lab: the `r = 0` Fourier
coefficient of `ν_b` and the density `E f_i ≥ 1/2 + δ/4` from the lab's PNT in progressions
`ap_sum_pow` (Siegel-Walfisz chain), primes in short intervals from the same, the local choice
`b₁ + b₂ ≡ r mod W` with units from `AlsetriShaoLocal.card_X_ge`, the wrap-around argument in
`Z_{WN}`, the pigeonhole over classes mod `W`, and the geometric covering from windows
`((1-κ)x, x]` to the density-zero conclusion.

Deviations, all harmless: the paper identifies `Z_N` with `{1, …, N}`, here with `{0, …, N-1}`
through `ZMod.val`, a shift that does not change `|ν̂(r)|`; the paper's window is
`[(1-δ^{10})M, M]` with cutoff `(1-δ^5)M`, here window `((1-κ)x, x]` and cutoff `(1-κ)x`, with
`WN ∈ [x, (1+κ)x]` and `N` prime, which avoids the paper's wrap-around corner case.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Filter
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1446

/-! ### Fourier analysis on `Z_N`, normalised as in Section 3 of the paper -/

/-- `f̂(r) = E_n f(n) e_N(-rn)`. -/
def hatE (N : ℕ) [NeZero N] (f : ZMod N → ℝ) (r : ZMod N) : ℂ :=
  (1 / (N : ℂ)) * ∑ n : ZMod N, (f n : ℂ) * ZMod.stdAddChar (-(r * n))

/-- `E_n f(n)`. -/
def avg (N : ℕ) [NeZero N] (f : ZMod N → ℝ) : ℝ := (1 / (N : ℝ)) * ∑ n : ZMod N, f n

/-- `‖f̂‖_p = (Σ_r |f̂(r)|^p)^{1/p}`. -/
def lpHat (N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℝ) : ℝ :=
  (∑ r : ZMod N, ‖hatE N f r‖ ^ p) ^ (1 / p)

/-- `f * g(n) = E_m f(m) g(n - m)`. -/
def convE (N : ℕ) [NeZero N] (f g : ZMod N → ℝ) (n : ZMod N) : ℝ :=
  (1 / (N : ℝ)) * ∑ m : ZMod N, f m * g (n - m)

/-- The majorant of Section 4, `ν_b(n) = (φ(W)/W) log(Wn + b)` if `Wn + b` is prime, else `0`. -/
def nuW (W b N : ℕ) [NeZero N] (n : ZMod N) : ℝ :=
  if (W * n.val + b).Prime then (Nat.totient W : ℝ) / W * Real.log (W * n.val + b) else 0

/-- The weight of Section 4, `f_b(n) = (φ(W)/W) log(Wn + b)` if `Wn + b ∈ A` and `Wn + b ≤ X`. -/
def fA (A : Set ℕ) (W b X N : ℕ) [NeZero N] (n : ZMod N) : ℝ :=
  if W * n.val + b ∈ A ∧ W * n.val + b ≤ X then (Nat.totient W : ℝ) / W * Real.log (W * n.val + b)
  else 0

/-! ### The three cited inputs -/

/-- **Alsetri-Shao, Proposition 3.1** (transference principle), Section 3 of arXiv 2405.18576v2.
Stated for prime `N ≥ N₀` and `δ < 1/2` only, which is weaker than the paper's form. -/
def AS_Prop31 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ η : ℝ, 0 < η → ∀ p : ℝ, 2 < p → p < 4 → ∀ Mc : ℝ, 1 ≤ Mc →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ f₁ f₂ ν₁ ν₂ : ZMod N → ℝ,
        (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ ν₁ n) → (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ ν₂ n) →
        1 + δ ≤ avg N f₁ + avg N f₂ →
        lpHat N p f₁ ≤ Mc → lpHat N p f₂ ≤ Mc →
        (∀ r, ‖hatE N ν₁ r - (if r = 0 then 1 else 0)‖ ≤ c) →
        (∀ r, ‖hatE N ν₂ r - (if r = 0 then 1 else 0)‖ ≤ c) →
        ((univ.filter (fun n => convE N f₁ f₂ n ≤ δ ^ 3 / 1000)).card : ℝ) ≤ η * N

/-- **Green 2005, Lemma 6.2** as used in Section 4: the nonzero Fourier coefficients of the
majorant are small once `z` is large; `W = z#`, `b` a reduced class, `N` a large prime. -/
def Green62 : Prop :=
  ∀ c : ℝ, 0 < c → ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ b : ℕ, b < primorial z →
    Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ r : ZMod N, r ≠ 0 → ‖hatE N (nuW (primorial z) b N) r‖ ≤ c

/-- **Green 2005, Lemma 6.6** with `p = 3`, the restriction estimate, as used in Section 4:
the constant does not depend on `z`, `b` or `N`. -/
def Green66 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z → ∀ b : ℕ, b < primorial z →
    Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) → lpHat N 3 f ≤ C

/-! ### Basic facts -/

lemma hatE_zero (N : ℕ) [NeZero N] (f : ZMod N → ℝ) : hatE N f 0 = (avg N f : ℂ) := by
  simp [hatE, avg]

lemma nuW_nonneg (W b N : ℕ) [NeZero N] (n : ZMod N) : 0 ≤ nuW W b N n := by
  unfold nuW
  split_ifs
  · exact mul_nonneg (by positivity) (by exact_mod_cast Real.log_natCast_nonneg (W * n.val + b))
  · exact le_rfl

lemma fA_nonneg (A : Set ℕ) (W b X N : ℕ) [NeZero N] (n : ZMod N) : 0 ≤ fA A W b X N n := by
  unfold fA
  split_ifs
  · exact mul_nonneg (by positivity) (by exact_mod_cast Real.log_natCast_nonneg (W * n.val + b))
  · exact le_rfl

lemma fA_le_nuW (A : Set ℕ) (hA : A ⊆ P) (W b X N : ℕ) [NeZero N] (n : ZMod N) :
    fA A W b X N n ≤ nuW W b N n := by
  unfold fA nuW
  by_cases h : W * n.val + b ∈ A ∧ W * n.val + b ≤ X
  · rw [if_pos h, if_pos (show (W * n.val + b).Prime from hA h.1)]
  · rw [if_neg h]; split_ifs
    · exact mul_nonneg (by positivity) (by exact_mod_cast Real.log_natCast_nonneg (W * n.val + b))
    · exact le_rfl

/-! ### Sums over `Z_N` against sums over a residue class -/

/-- `Σ_{n ∈ Z_N} F(Wn + b) = Σ_{p ≤ X, p ≡ b} F(p)` when `F` vanishes past `X < WN`. -/
lemma sum_zmod_eq (W b X N : ℕ) [NeZero N] (hb : b < W) (hX : X < W * N) (F : ℕ → ℝ)
    (hF : ∀ p, X < p → F p = 0) :
    ∑ n : ZMod N, F (W * n.val + b) =
      ∑ p ∈ (Finset.range (X + 1)).filter (fun p => p % W = b), F p := by
  have hW : 0 < W := by omega
  refine Finset.sum_bij_ne_zero (fun n _ _ => W * n.val + b) ?_ ?_ ?_ ?_
  · intro n _ hn
    rw [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · by_contra h; exact hn (hF _ (by omega))
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · intro n₁ _ _ n₂ _ _ h
    exact ZMod.val_injective N (Nat.eq_of_mul_eq_mul_left hW (by omega))
  · intro p hp hFp
    rw [mem_filter, mem_range] at hp
    have hpX : p ≤ X := by by_contra h; exact hFp (hF _ (by omega))
    have hq : p / W < N := by
      rw [Nat.div_lt_iff_lt_mul hW]; rw [Nat.mul_comm] at hX; omega
    refine ⟨(p / W : ℕ), mem_univ _, ?_, ?_⟩
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq]
      have := Nat.div_add_mod p W
      rw [hp.2] at this
      rw [this]; exact hFp
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq]
      have := Nat.div_add_mod p W
      rw [hp.2] at this; exact this
  · intro n _ _; rfl


/-! ### The local step: `r ≡ b₁ + b₂ mod W` with reduced `b₁, b₂`, via Theorem 2.1's count -/

lemma prime_dvd_primorial' {p z : ℕ} (hp : p.Prime) (hz : p ≤ z) : p ∣ primorial z :=
  Finset.dvd_prod_of_mem _ (by simp [Finset.mem_filter, hp]; omega)

lemma primorial_half {z : ℕ} (hz : 3 ≤ z) :
    ∃ W' : ℕ, primorial z = 2 * W' ∧ 0 < W' ∧ Odd W' ∧ Squarefree W' := by
  obtain ⟨m, hm⟩ := prime_dvd_primorial' Nat.prime_two (by omega : 2 ≤ z)
  have hsqm : Squarefree (2 * m) := hm ▸ squarefree_primorial z
  refine ⟨m, hm, ?_, ?_, hsqm.of_mul_right⟩
  · rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h] at hm; exact (primorial_pos z).ne' hm
    · exact h
  · rcases Nat.even_or_odd m with ⟨k, hk⟩ | h
    · exfalso
      have := hsqm 2 ⟨k, by rw [hk]; ring⟩
      have h21 := Nat.isUnit_iff.mp this
      omega
    · exact h

lemma exists_unit_pair (W' : ℕ) (hW' : 0 < W') (hodd : Odd W') (hsq : Squarefree W') (r : ℕ) :
    ∃ a c : ℕ, Nat.Coprime a W' ∧ Nat.Coprime c W' ∧ (a + c) % W' = r % W' := by
  haveI : NeZero W' := ⟨hW'.ne'⟩
  have hpos : 0 < ∏ p ∈ W'.primeFactors, (p - 2) := by
    apply Finset.prod_pos
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    have := hpp.two_le; omega
  have h := AlsetriShaoLocal.card_X_ge W' hW' hsq (r : ZMod W')
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le hpos h)
  simp only [AlsetriShaoLocal.Xset, mem_filter, mem_univ, true_and] at hx
  refine ⟨x.val, ((r : ZMod W') - x).val, ?_, ?_, ?_⟩
  · have := hx.1; rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at this; exact this
  · have := hx.2
    rw [← ZMod.natCast_zmod_val ((r : ZMod W') - x), ZMod.isUnit_iff_coprime] at this; exact this
  · rw [← ZMod.natCast_eq_natCast_iff']; push_cast; simp

lemma odd_lift (W' a : ℕ) (hW' : 0 < W') (hodd : Odd W') (ha : Nat.Coprime a W') :
    ∃ a' : ℕ, a' < 2 * W' ∧ Odd a' ∧ Nat.Coprime a' W' ∧ a' % W' = a % W' := by
  have hlt := Nat.mod_lt a hW'
  have hcop : Nat.Coprime (a % W') W' := by
    unfold Nat.Coprime; rw [← Nat.gcd_rec, Nat.gcd_comm]; exact ha
  rcases Nat.even_or_odd (a % W') with h | h
  · refine ⟨a % W' + W', by omega, Even.add_odd h hodd, ?_, ?_⟩
    · exact Nat.coprime_add_self_left.2 hcop
    · rw [Nat.add_mod_right, Nat.mod_mod]
  · exact ⟨a % W', by omega, h, hcop, Nat.mod_mod _ _⟩

/-- For even `r` there are reduced `b₁, b₂ < W = z#` with `b₁ + b₂ ≡ r mod W`. -/
lemma exists_b_pair {z : ℕ} (hz : 3 ≤ z) (r : ℕ) (hr : Even r) :
    ∃ b₁ b₂ : ℕ, b₁ < primorial z ∧ b₂ < primorial z ∧ Nat.Coprime b₁ (primorial z) ∧
      Nat.Coprime b₂ (primorial z) ∧ (b₁ + b₂) % primorial z = r % primorial z := by
  obtain ⟨W', hW, hW'0, hodd, hsq⟩ := primorial_half hz
  obtain ⟨a, c, ha, hc, hac⟩ := exists_unit_pair W' hW'0 hodd hsq r
  obtain ⟨a', ha'lt, ha'o, ha'c, ha'm⟩ := odd_lift W' a hW'0 hodd ha
  obtain ⟨c', hc'lt, hc'o, hc'c, hc'm⟩ := odd_lift W' c hW'0 hodd hc
  have h2W : Nat.Coprime 2 W' := Nat.coprime_two_left.mpr hodd
  refine ⟨a', c', hW ▸ ha'lt, hW ▸ hc'lt, ?_, ?_, ?_⟩
  · rw [hW]; exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr ha'o) ha'c
  · rw [hW]; exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hc'o) hc'c
  · rw [hW]
    have e1 : Nat.ModEq 2 (a' + c') r := by
      unfold Nat.ModEq
      rw [Nat.even_iff.mp (Odd.add_odd ha'o hc'o), Nat.even_iff.mp hr]
    have e2 : Nat.ModEq W' (a' + c') r := by
      unfold Nat.ModEq
      rw [Nat.add_mod, ha'm, hc'm, ← Nat.add_mod, hac]
    exact (Nat.modEq_and_modEq_iff_modEq_mul h2W).mp ⟨e1, e2⟩

/-! ### Primes in short intervals, from the lab's PNT -/

lemma theta_close (ε : ℝ) (hε : 0 < ε) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p - n| ≤ ε * n := by
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 1 le_rfl ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  have hT := hn₀ n hn 0 (Nat.coprime_zero_left 1 |>.2 rfl)
  simp only [pow_zero, mul_one, zero_add, pow_one, Nat.cast_zero, one_mul, Nat.totient_one,
    Nat.cast_one, div_one, Nat.mod_one, and_true] at hT
  exact hT

lemma exists_prime_between (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ Y₀ : ℝ, ∀ y : ℝ, Y₀ ≤ y → ∃ N : ℕ, N.Prime ∧ y ≤ N ∧ (N : ℝ) ≤ (1 + κ) * y := by
  obtain ⟨n₀, hn₀⟩ := theta_close (κ / 8) (by positivity)
  refine ⟨(n₀ : ℝ) + 1 + 8 / κ, fun y hy => ?_⟩
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  set n₁ := ⌊y⌋₊ with hn₁
  set n₂ := ⌊(1 + κ) * y⌋₊ with hn₂
  have hn₁0 : n₀ ≤ n₁ := Nat.le_floor (by have : (0:ℝ) ≤ 8 / κ := by positivity
                                          linarith)
  have hn12 : n₁ ≤ n₂ := Nat.floor_le_floor (by nlinarith)
  by_contra hno
  push Not at hno
  have hsame : (Finset.range (n₂ + 1)).filter Nat.Prime = (Finset.range (n₁ + 1)).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hp2, hp⟩
      refine ⟨?_, hp⟩
      by_contra hp1
      have hyp : y < p := by
        have := Nat.lt_floor_add_one y
        have : ((n₁ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast (show n₁ + 1 ≤ p by omega)
        push_cast at this; linarith
      have hpy : (p : ℝ) ≤ (1 + κ) * y := by
        have : (p : ℝ) ≤ n₂ := by exact_mod_cast (show p ≤ n₂ by omega)
        exact this.trans (Nat.floor_le (by positivity))
      have := hno p hp hyp.le
      linarith
    · rintro ⟨hp1, hp⟩; exact ⟨by omega, hp⟩
  have h1 := hn₀ n₁ hn₁0
  have h2 := hn₀ n₂ (hn₁0.trans hn12)
  rw [hsame] at h2
  rw [abs_le] at h1 h2
  have hf1 : (n₁ : ℝ) ≤ y := Nat.floor_le hy0
  have hf2 : (1 + κ) * y - 1 ≤ (n₂ : ℝ) := by
    have := Nat.lt_floor_add_one ((1 + κ) * y); linarith
  have hyκ : 8 / κ ≤ y := by have : (0:ℝ) ≤ n₀ := by positivity
                             linarith
  have hκy : 8 ≤ κ * y := by rwa [div_le_iff₀ hκ, mul_comm] at hyκ
  nlinarith

/-! ### Splitting a sum of `log p` at `X^(1-γ)` -/

lemma split_log (S : Finset ℕ) (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : γ < 1) :
    (1 - γ) * Real.log N * (S.card : ℝ) ≤
      (1 - γ) * Real.log N * ((N : ℝ) ^ (1 - γ) + 1) + ∑ p ∈ S, Real.log p := by
  set t : ℝ := (N : ℝ) ^ (1 - γ) with ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have hlogt : Real.log t = (1 - γ) * Real.log N := Real.log_rpow hN0 _
  have h1γ : 0 < 1 - γ := by linarith
  set Ps := S.filter (fun p : ℕ => (p : ℝ) < t)
  set Pb := S.filter (fun p : ℕ => ¬ (p : ℝ) < t)
  have hcard : (S.card : ℝ) = Ps.card + Pb.card := by
    rw [← card_filter_add_card_filter_not (s := S) (fun p : ℕ => (p : ℝ) < t)]; push_cast; rfl
  have hsmall : (Ps.card : ℝ) ≤ t + 1 := by
    have h2 : Ps.card ≤ ⌈t⌉₊ := by
      calc Ps.card ≤ (range ⌈t⌉₊).card := by
            refine card_le_card_of_injOn id (fun p hp => ?_) (fun _ _ _ _ h => h)
            exact mem_range.2 (Nat.lt_ceil.2 (mem_filter.1 hp).2)
        _ = ⌈t⌉₊ := card_range _
    exact le_trans (by exact_mod_cast h2) (Nat.ceil_lt_add_one ht0.le).le
  have hbig : (1 - γ) * Real.log N * Pb.card ≤ ∑ p ∈ S, Real.log p := by
    have e : (1 - γ) * Real.log N * Pb.card = ∑ _p ∈ Pb, (1 - γ) * Real.log N := by
      rw [sum_const, nsmul_eq_mul]; ring
    rw [e]
    refine le_trans (sum_le_sum fun p hp => ?_) (sum_le_sum_of_subset_of_nonneg
      (filter_subset _ S) fun p _ _ => Real.log_natCast_nonneg p)
    have htp : t ≤ p := not_lt.1 (mem_filter.1 hp).2
    exact hlogt ▸ Real.log_le_log ht0 htp
  have hA : 0 ≤ (1 - γ) * Real.log N := mul_nonneg h1γ.le hL
  have := mul_le_mul_of_nonneg_left hsmall hA
  rw [hcard]
  nlinarith

/-! ### The density step: `θ_A(X; W, b) ≥ c₀ (1 - ε) X / φ(W)` -/

lemma icc_filter_eq (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ n, Q n → n.Prime) :
    (Icc 1 N).filter Q = (range (N + 1)).filter Q := by
  ext n
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨_, h⟩, hq⟩; exact ⟨by omega, hq⟩
  · rintro ⟨h, hq⟩; exact ⟨⟨(hQ n hq).one_lt.le, by omega⟩, hq⟩

lemma theta_A_lower (A : Set ℕ) (hA : A ⊆ P) (W b : ℕ) (hW : 0 < W) (hb : Nat.Coprime b W)
    (c0 : ℝ) (hc0 : 0 < c0) (hd : c0 < lowerDensityRes A b W) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c0 * (1 - ε) * X / Nat.totient W ≤
        ∑ p ∈ (range (X + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧ p % W = b % W), Real.log p := by
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  set φ : ℝ := (Nat.totient W : ℝ) with hφdef
  -- eventually the ratio exceeds c0
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ =>
      (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime ∧ n % W = b % W} : ℝ) /
        #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W}) :=
    isBoundedUnder_of ⟨0, fun N => by positivity⟩
  have hev := eventually_lt_of_lt_liminf hd hbdd
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hev
  set γ := ε / 2
  set ε₁ := ε / (4 * φ)
  set ε₂ := c0 * ε / (4 * φ)
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 W hW ε₁ (by positivity)
  have hlog := (LeanLab.HardyLittlewood1923.eventually_log_le (ε₂ / 2) γ (by positivity)
    (by positivity)).and ((LeanLab.HardyLittlewood1923.eventually_log_le (ε₂ / 2) 1
    (by positivity) one_pos).and (eventually_ge_atTop 2))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hlog
  refine ⟨max n₀ (max n₁ n₂), fun X hX => ?_⟩
  obtain ⟨hl1, hl2, hX2⟩ := hn₂ X (le_of_max_le_right (le_of_max_le_right hX))
  rw [Real.rpow_one] at hl2
  have hS := hn₀ X (le_of_max_le_left hX) b hb
  simp only [pow_zero, mul_one, Nat.cast_zero, zero_add, one_mul, pow_one] at hS
  rw [← hφdef] at hS
  have hr := hn₁ X (le_of_max_le_left (le_of_max_le_right hX))
  rw [icc_filter_eq X _ (fun n h => hA h.1), icc_filter_eq X _ (fun n h => h.1)] at hr
  set SA := (range (X + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧ p % W = b % W)
  set SP := (range (X + 1)).filter (fun p => p.Prime ∧ p % W = b % W)
  set a : ℝ := (SA.card : ℝ)
  set d : ℝ := (SP.card : ℝ)
  have hd0 : 0 < d := by
    by_contra h
    have : d = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, div_zero] at hr; linarith
  have had : c0 * d < a := by rwa [lt_div_iff₀ hd0] at hr
  have hθ := LeanLab.DensityGoldbach.theta_ap_le X W b
  have hsplit := split_log SA X (by omega) γ (by simp only [γ]; linarith)
  set n : ℝ := (X : ℝ)
  have hn1 : (2 : ℝ) ≤ n := by simp only [n]; exact_mod_cast hX2
  have hn0 : 0 < n := by linarith
  set L := Real.log n
  have hL : 0 < L := Real.log_pos (by linarith)
  set t := n ^ (1 - γ)
  have htn : t * n ^ γ = n := by
    simp only [t]; rw [← Real.rpow_add hn0]; simp
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0.le _
  have hLt : L * (t + 1) ≤ ε₂ * n := by
    have := mul_le_mul_of_nonneg_left hl1 ht0
    nlinarith
  obtain ⟨hS1, hS2⟩ := abs_le.1 hS
  -- θ_b ≥ (1/φ - ε₁) n, so d L ≥ (1/φ - ε₁) n
  have hdL : (1 / φ - ε₁) * n ≤ d * L := by
    have : n / φ - ε₁ * n ≤ d * L := by linarith
    calc (1 / φ - ε₁) * n = n / φ - ε₁ * n := by ring
      _ ≤ d * L := this
  set TA := ∑ p ∈ SA, Real.log p
  have h1γ : 0 < 1 - γ := by simp only [γ]; linarith
  -- TA ≥ (1-γ) L a - (1-γ) L (t+1) ≥ (1-γ) (c0 d L - ε₂ n)
  have hT1 : (1 - γ) * (c0 * (d * L) - ε₂ * n) ≤ TA := by
    have e1 : c0 * (d * L) ≤ a * L := by nlinarith
    have e2 : (1 - γ) * L * a ≤ (1 - γ) * L * (t + 1) + TA := hsplit
    have e3 : (1 - γ) * (L * (t + 1)) ≤ (1 - γ) * (ε₂ * n) := mul_le_mul_of_nonneg_left hLt h1γ.le
    nlinarith
  have hT2 : (1 - γ) * (c0 * ((1 / φ - ε₁) * n) - ε₂ * n) ≤ TA := by
    have : c0 * ((1 / φ - ε₁) * n) ≤ c0 * (d * L) := mul_le_mul_of_nonneg_left hdL hc0.le
    nlinarith
  have hfin : c0 * (1 - ε) * n / φ ≤ (1 - γ) * (c0 * ((1 / φ - ε₁) * n) - ε₂ * n) := by
    simp only [γ, ε₁, ε₂]
    rw [div_le_iff₀ hφ]
    have : (1 - ε / 2) * (c0 * ((1 / φ - ε / (4 * φ)) * n) - c0 * ε / (4 * φ) * n) * φ =
        c0 * n * (1 - ε / 2) * (1 - ε / 2) := by field_simp; ring
    rw [this]
    have : 0 ≤ c0 * n := by positivity
    nlinarith [sq_nonneg ε]
  exact hfin.trans hT2

/-! ### Averages of the weights -/

lemma avg_fA (A : Set ℕ) (hA : A ⊆ P) (W b X N : ℕ) [NeZero N] (hb : b < W) (hX : X < W * N) :
    avg N (fA A W b X N) = (Nat.totient W : ℝ) / (W * N) *
      ∑ p ∈ (range (X + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧ p % W = b % W), Real.log p := by
  have hW : 0 < W := by omega
  set F : ℕ → ℝ := fun p => if p ∈ A ∧ p ≤ X then (Nat.totient W : ℝ) / W * Real.log p else 0
  have h1 : ∀ n : ZMod N, fA A W b X N n = F (W * n.val + b) := by
    intro n; simp only [fA, F]; push_cast; rfl
  have h2 := sum_zmod_eq W b X N hb hX F (fun p hp => by simp only [F]; rw [if_neg (by omega)])
  unfold avg
  rw [Finset.sum_congr rfl (fun n _ => h1 n), h2, sum_filter, sum_filter, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_range] at hp
  rw [Nat.mod_eq_of_lt hb]
  simp only [F]
  by_cases h : p % W = b
  · by_cases hpA : p ∈ A
    · rw [if_pos h, if_pos ⟨hpA, by omega⟩, if_pos ⟨hpA, hA hpA, h⟩]
      field_simp
    · rw [if_pos h, if_neg (by tauto), if_neg (by tauto)]; ring
  · rw [if_neg h, if_neg (by tauto)]; ring

lemma avg_nuW (W b N : ℕ) [NeZero N] (hb : b < W) :
    avg N (nuW W b N) = (Nat.totient W : ℝ) / (W * N) *
      ∑ p ∈ (range (W * (N - 1) + b + 1)).filter (fun p => p.Prime ∧ p % W = b % W),
        Real.log p := by
  have hW : 0 < W := by omega
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set X := W * (N - 1) + b
  have hX : X < W * N := by
    have : W * (N - 1) + W = W * N := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  set F : ℕ → ℝ := fun p => if p.Prime ∧ p ≤ X then (Nat.totient W : ℝ) / W * Real.log p else 0
  have h1 : ∀ n : ZMod N, nuW W b N n = F (W * n.val + b) := by
    intro n
    have hv : n.val ≤ N - 1 := by have := ZMod.val_lt n; omega
    have hle : W * n.val + b ≤ X := by
      have := Nat.mul_le_mul_left W hv; omega
    simp only [nuW, F]
    by_cases hp : (W * n.val + b).Prime
    · rw [if_pos hp, if_pos ⟨hp, hle⟩]; push_cast; rfl
    · rw [if_neg hp, if_neg (by tauto)]
  have h2 := sum_zmod_eq W b X N hb hX F (fun p hp => by simp only [F]; rw [if_neg (by omega)])
  unfold avg
  rw [Finset.sum_congr rfl (fun n _ => h1 n), h2, sum_filter, sum_filter, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_range] at hp
  rw [Nat.mod_eq_of_lt hb]
  simp only [F]
  by_cases h : p % W = b
  · by_cases hpp : p.Prime
    · rw [if_pos h, if_pos ⟨hpp, by omega⟩, if_pos ⟨hpp, h⟩]
      field_simp
    · rw [if_pos h, if_neg (by tauto), if_neg (by tauto)]; ring
  · rw [if_neg h, if_neg (by tauto)]; ring

/-- The `r = 0` coefficient: `|ν̂_b(0) - 1| ≤ c` for large `N`, from the lab's PNT in progressions. -/
lemma nu_avg_close (W b : ℕ) (hb : b < W) (hcop : Nat.Coprime b W) (c : ℝ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N₀ ≤ N → |avg N (nuW W b N) - 1| ≤ c := by
  have hW : 0 < W := by omega
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  set φ : ℝ := (Nat.totient W : ℝ) with hφdef
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 W hW (c / (2 * φ)) (by positivity)
  refine ⟨n₀ + 1 + ⌈2 / c⌉₊, fun N _ hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  set X := W * (N - 1) + b
  have hXn : n₀ ≤ X := by
    have : N - 1 ≤ W * (N - 1) := Nat.le_mul_of_pos_left _ hW
    omega
  have hS := hn₀ X hXn b hcop
  simp only [pow_zero, mul_one, Nat.cast_zero, zero_add, one_mul, pow_one] at hS
  rw [← hφdef] at hS
  rw [avg_nuW W b N hb]
  set θ := ∑ p ∈ (range (X + 1)).filter (fun p => p.Prime ∧ p % W = b % W), Real.log p
  have hXr : (X : ℝ) = (W : ℝ) * N - (W - b) := by
    simp only [X]; rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN1]; push_cast; ring
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbr : (b : ℝ) < W := by exact_mod_cast hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hNc : 2 / c ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (2 / c)
    have h2 : ((⌈2 / c⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (show ⌈2 / c⌉₊ ≤ N by omega)
    linarith
  have h1N : 1 / (N : ℝ) ≤ c / 2 := by
    rw [div_le_iff₀ hNr]; rw [div_le_iff₀ hc] at hNc; linarith
  obtain ⟨hS1, hS2⟩ := abs_le.1 hS
  rw [abs_le]
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hXle : (X : ℝ) ≤ W * N := by rw [hXr]; linarith
  have key : φ / (W * N) * θ - 1 = (φ * (θ - X / φ) - (W - b)) / (W * N) := by
    rw [hXr]; field_simp; ring
  rw [key]
  have hWN : (0 : ℝ) < W * N := by positivity
  have hb1 : ((W : ℝ) - b) / (W * N) ≤ c / 2 := by
    rw [div_le_iff₀ hWN]
    have : (W : ℝ) - b ≤ W := by linarith
    have : (W : ℝ) * (1 / N) * N = W := by field_simp
    nlinarith
  have hb2 : |φ * (θ - X / φ)| / (W * N) ≤ c / 2 := by
    rw [div_le_iff₀ hWN, abs_mul, abs_of_pos hφ]
    have : |θ - X / φ| ≤ c / (2 * φ) * X := abs_le.2 ⟨by linarith, by linarith⟩
    calc φ * |θ - ↑X / φ| ≤ φ * (c / (2 * φ) * X) := mul_le_mul_of_nonneg_left this hφ.le
      _ = c / 2 * X := by field_simp
      _ ≤ c / 2 * (W * N) := mul_le_mul_of_nonneg_left hXle (by positivity)
  have hWb : 0 ≤ ((W : ℝ) - b) / (W * N) := div_nonneg (by linarith) hWN.le
  have e1 := neg_abs_le (φ * (θ - X / φ))
  have e2 := le_abs_self (φ * (θ - X / φ))
  rw [sub_div]
  constructor
  · have : -|φ * (θ - X / φ)| / (W * N) ≤ φ * (θ - X / φ) / (W * N) :=
      div_le_div_of_nonneg_right e1 hWN.le
    rw [neg_div] at this; linarith
  · have : φ * (θ - X / φ) / (W * N) ≤ |φ * (θ - X / φ)| / (W * N) :=
      div_le_div_of_nonneg_right e2 hWN.le
    linarith

/-- Combined Fourier hypothesis (3) of Prop 3.1 for the majorant: `r ≠ 0` from Green 6.2,
`r = 0` from the lab's PNT. -/
lemma nu_fourier (H62 : Green62) (c : ℝ) (hc : 0 < c) : ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    ∀ b : ℕ, b < primorial z → Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N],
      N.Prime → N₀ ≤ N → ∀ r : ZMod N,
        ‖hatE N (nuW (primorial z) b N) r - (if r = 0 then 1 else 0)‖ ≤ c := by
  obtain ⟨z₀, hz₀⟩ := H62 c hc
  refine ⟨z₀, fun z hz b hb hcop => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hz₀ z hz b hb hcop
  obtain ⟨N₂, hN₂⟩ := nu_avg_close (primorial z) b hb hcop c hc
  refine ⟨max N₁ N₂, fun N _ hNp hN r => ?_⟩
  by_cases hr : r = 0
  · rw [if_pos hr, hr, hatE_zero]
    have := hN₂ N (le_of_max_le_right hN)
    rw [show ((avg N (nuW (primorial z) b N) : ℂ) - 1) =
      ((avg N (nuW (primorial z) b N) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact this
  · rw [if_neg hr, sub_zero]
    exact hN₁ N hNp (le_of_max_le_left hN) r hr


/-! ### The window bound: Section 4 of the paper -/

/-- The even `n ≤ x` that are not in `A + A`. -/
def excSet (A : Set ℕ) (x : ℝ) : Finset ℕ :=
  (Icc 1 ⌊x⌋₊).filter (fun n => Even n ∧ ¬ ∃ a ∈ A, ∃ b ∈ A, a + b = n)

/-- The wrap-around step: from `n₁ + n₂ = t` in `Z_N` and the size constraints, `p₁ + p₂ = m`. -/
lemma wrap (W N b₁ b₂ Xc m q : ℕ) [NeZero N] (n₁ n₂ : ZMod N) (hq : q < N)
    (hm : m = W * q + (b₁ + b₂)) (hsum : n₁ + n₂ = (q : ZMod N))
    (h1 : W * n₁.val + b₁ ≤ Xc) (h2 : W * n₂.val + b₂ ≤ Xc) (hXm : Xc < m) (hmW : m ≤ W * N) :
    (W * n₁.val + b₁) + (W * n₂.val + b₂) = m := by
  have hv := congrArg ZMod.val hsum
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hq] at hv
  set s := n₁.val + n₂.val
  have hs1 := ZMod.val_lt n₁
  have hs2 := ZMod.val_lt n₂
  by_cases hsN : s < N
  · rw [Nat.mod_eq_of_lt hsN] at hv
    rw [hm, ← hv]; ring
  · have hsub : s % N = s - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hv
    exfalso
    have : W * s = W * q + W * N := by
      rw [← Nat.mul_add]; congr 1; omega
    have e : (W * n₁.val + b₁) + (W * n₂.val + b₂) = W * s + (b₁ + b₂) := by
      simp only [s]; ring
    omega

set_option maxHeartbeats 1600000 in
theorem window_bound (A : Set ℕ) (hA : A ⊆ P) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hdens : ∀ W b : ℕ, 0 < W → Nat.Coprime b W → 1 / 2 + δ ≤ lowerDensityRes A b W)
    (H31 : AS_Prop31) (H62 : Green62) (H66 : Green66) (η : ℝ) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (((excSet A x).filter (fun m => ⌊(1 - δ / 16) * x⌋₊ < m)).card : ℝ) ≤ η * x := by
  set κ := δ / 16 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 / 64 := by simp only [κ]; linarith
  obtain ⟨C, hC, z₁, hG66⟩ := H66
  obtain ⟨c, hc, N₀', hP31⟩ := H31 (δ / 2) (by linarith) (by linarith) (η / 4) (by positivity) 3
    (by norm_num) (by norm_num) (max C 1) (le_max_right _ _)
  obtain ⟨z₀, hG62⟩ := nu_fourier H62 c hc
  set z := max (max z₀ z₁) 3 with hz
  have hz3 : 3 ≤ z := le_max_right _ _
  set W := primorial z with hWdef
  have hW : 0 < W := primorial_pos z
  have hW2 : 2 ∣ W := prime_dvd_primorial' Nat.prime_two (by omega)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  -- per-class thresholds
  have hcls : ∀ b, ∃ N₁ : ℕ, b < W → Nat.Coprime b W → ∀ N : ℕ, ∀ [NeZero N], N.Prime →
      N₁ ≤ N → (∀ r, ‖hatE N (nuW W b N) r - (if r = 0 then 1 else 0)‖ ≤ c) ∧
        (∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW W b N n) → lpHat N 3 f ≤ C) := by
    intro b
    by_cases hb : b < W ∧ Nat.Coprime b W
    · obtain ⟨Na, ha⟩ := hG62 z (le_trans (le_max_left _ _) (le_max_left _ _)) b hb.1 hb.2
      obtain ⟨Nb, hb'⟩ := hG66 z (le_trans (le_max_right _ _) (le_max_left _ _)) b hb.1 hb.2
      exact ⟨max Na Nb, fun _ _ N _ hNp hN =>
        ⟨ha N hNp (le_of_max_le_left hN), hb' N hNp (le_of_max_le_right hN)⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hb⟩
  have hden : ∀ b, ∃ X₁ : ℕ, b < W → Nat.Coprime b W → ∀ X : ℕ, X₁ ≤ X →
      (1 / 2 + δ / 2) * (1 - κ) * X / Nat.totient W ≤
        ∑ p ∈ (range (X + 1)).filter (fun p => p ∈ A ∧ p.Prime ∧ p % W = b % W), Real.log p := by
    intro b
    by_cases hb : b < W ∧ Nat.Coprime b W
    · obtain ⟨X₁, h⟩ := theta_A_lower A hA W b hW hb.2 (1 / 2 + δ / 2) (by positivity)
        (by linarith [hdens W b hW hb.2]) κ hκ0 (by linarith)
      exact ⟨X₁, fun _ _ => h⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hb⟩
  choose N₁ hN₁ using hcls
  choose X₁ hX₁ using hden
  have hpair : ∀ r, ∃ b₁ b₂ : ℕ, Even r → b₁ < W ∧ b₂ < W ∧ Nat.Coprime b₁ W ∧
      Nat.Coprime b₂ W ∧ (b₁ + b₂) % W = r % W := by
    intro r
    by_cases hr : Even r
    · obtain ⟨b₁, b₂, h⟩ := exists_b_pair hz3 r hr
      exact ⟨b₁, b₂, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hr⟩
  choose B₁ B₂ hB using hpair
  set Nmax := ((range W).sup N₁) ⊔ N₀' with hNmax
  set Xmax := (range W).sup X₁ with hXmax
  obtain ⟨Y₀, hY⟩ := exists_prime_between κ hκ0 (by linarith)
  refine ⟨max (max (Y₀ * W) ((Nmax : ℝ) * W)) (max (2 * ((Xmax : ℝ) + 2 * W + 1)) (1 / κ)),
    fun x hx => ?_⟩
  have hx1 : Y₀ * W ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : (Nmax : ℝ) * W ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 2 * ((Xmax : ℝ) + 2 * W + 1) ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : 1 / κ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by have : (0 : ℝ) < 1 / κ := by positivity
                         linarith
  have hκx : 1 ≤ κ * x := by rwa [div_le_iff₀ hκ0, mul_comm] at hx4
  obtain ⟨N, hNp, hyN, hNy⟩ := hY (x / W) (by rwa [le_div_iff₀ hWr])
  haveI : NeZero N := ⟨hNp.ne_zero⟩
  have hxWN : x ≤ W * N := by rw [div_le_iff₀ hWr] at hyN; linarith
  have hWNx : (W : ℝ) * N ≤ (1 + κ) * x := by
    have := mul_le_mul_of_nonneg_left hNy hWr.le
    rw [mul_comm (1 + κ), ← mul_assoc, mul_div_cancel₀ _ hWr.ne', mul_comm] at this
    linarith
  have hNbig : Nmax ≤ N := by
    have : (Nmax : ℝ) ≤ N := by
      rw [div_le_iff₀ hWr] at hyN
      exact le_of_mul_le_mul_right (by linarith) hWr
    exact_mod_cast this
  set Xc := ⌊(1 - κ) * x⌋₊ with hXc
  have hXcx : (Xc : ℝ) ≤ (1 - κ) * x := Nat.floor_le (by nlinarith)
  have hXclow : (1 - κ) * x - 1 ≤ (Xc : ℝ) := by
    have := Nat.lt_floor_add_one ((1 - κ) * x); linarith
  have hXcbig : Xmax + 2 * W ≤ Xc := by
    apply Nat.le_floor
    push_cast
    nlinarith
  have hXcWN : Xc < W * N := by
    have : (Xc : ℝ) < W * N := by nlinarith
    exact_mod_cast this
  have hfloorx : (⌊x⌋₊ : ℝ) ≤ W * N := (Nat.floor_le hx0.le).trans hxWN
  have hfloorxN : ⌊x⌋₊ ≤ W * N := by exact_mod_cast hfloorx
  -- density of each weight
  have havg : ∀ b, b < W → Nat.Coprime b W → 1 / 2 + δ / 4 ≤ avg N (fA A W b Xc N) := by
    intro b hb hcop
    rw [avg_fA A hA W b Xc N hb hXcWN]
    have hb0 : b ∈ range W := mem_range.2 hb
    have h := hX₁ b hb hcop Xc (le_trans (le_sup hb0) (by omega))
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNp.pos
    have hWN : (0 : ℝ) < W * N := by positivity
    have e : (Nat.totient W : ℝ) / (W * N) * ((1 / 2 + δ / 2) * (1 - κ) * Xc / Nat.totient W) =
        (1 / 2 + δ / 2) * (1 - κ) * Xc / (W * N) := by field_simp
    refine le_trans ?_ (le_trans (le_of_eq e.symm) (mul_le_mul_of_nonneg_left h (by positivity)))
    rw [le_div_iff₀ hWN]
    have h1 : (1 - 2 * κ) * x ≤ (Xc : ℝ) := by linarith
    have h2 : (1 / 2 + δ / 4) * ((W : ℝ) * N) ≤ (1 / 2 + δ / 4) * ((1 + κ) * x) :=
      mul_le_mul_of_nonneg_left hWNx (by positivity)
    have h3 : (1 / 2 + δ / 2) * (1 - κ) * ((1 - 2 * κ) * x) ≤ (1 / 2 + δ / 2) * (1 - κ) * Xc :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith) (by linarith))
    have h4 : (1 / 2 + δ / 4) * ((1 + κ) * x) ≤ (1 / 2 + δ / 2) * (1 - κ) * ((1 - 2 * κ) * x) := by
      have : (1 / 2 + δ / 4) * (1 + κ) ≤ (1 / 2 + δ / 2) * (1 - κ) * (1 - 2 * κ) := by
        rw [hκ]
        have e : (1 / 2 + δ / 2) * (1 - δ / 16) * (1 - 2 * (δ / 16)) - (1 / 2 + δ / 4) * (1 + δ / 16)
            = δ * (1 / 8 - 27 * δ / 256) + δ ^ 3 / 256 := by ring
        have e1 : 0 ≤ δ * (1 / 8 - 27 * δ / 256) := mul_nonneg hδ0.le (by linarith)
        have e2 : 0 ≤ δ ^ 3 / 256 := by positivity
        linarith
      calc (1 / 2 + δ / 4) * ((1 + κ) * x) = ((1 / 2 + δ / 4) * (1 + κ)) * x := by ring
        _ ≤ ((1 / 2 + δ / 2) * (1 - κ) * (1 - 2 * κ)) * x := mul_le_mul_of_nonneg_right this hx0.le
        _ = (1 / 2 + δ / 2) * (1 - κ) * ((1 - 2 * κ) * x) := by ring
    linarith
  -- the fibre over each class r mod W
  have hfib : ∀ r ∈ range W, ((((excSet A x).filter (fun m => Xc < m)).filter
      (fun m => m % W = r)).card : ℝ) ≤ η / 4 * N := by
    intro r hr
    rw [mem_range] at hr
    by_cases hre : Even r
    · obtain ⟨hb₁, hb₂, hc₁, hc₂, hbr⟩ := hB r hre
      set b₁ := B₁ r
      set b₂ := B₂ r
      have hW1 : 2 ≤ W := Nat.le_of_dvd hW hW2
      have hb₁0 : 0 < b₁ := by
        rcases Nat.eq_zero_or_pos b₁ with h | h
        · rw [h, Nat.coprime_zero_left] at hc₁; omega
        · exact h
      set f₁ := fA A W b₁ Xc N
      set f₂ := fA A W b₂ Xc N
      have hN1 := hN₁ b₁ hb₁ hc₁ N hNp (le_trans (le_sup (mem_range.2 hb₁))
        (le_trans le_sup_left hNbig))
      have hN2 := hN₁ b₂ hb₂ hc₂ N hNp (le_trans (le_sup (mem_range.2 hb₂))
        (le_trans le_sup_left hNbig))
      have hbad := hP31 N hNp (le_trans le_sup_right hNbig) f₁ f₂ (nuW W b₁ N) (nuW W b₂ N)
        (fun n => ⟨fA_nonneg _ _ _ _ _ n, fA_le_nuW A hA _ _ _ _ n⟩)
        (fun n => ⟨fA_nonneg _ _ _ _ _ n, fA_le_nuW A hA _ _ _ _ n⟩)
        (by linarith [havg b₁ hb₁ hc₁, havg b₂ hb₂ hc₂])
        ((hN1.2 f₁ (fun n => ⟨fA_nonneg _ _ _ _ _ n, fA_le_nuW A hA _ _ _ _ n⟩)).trans
          (le_max_left _ _))
        ((hN2.2 f₂ (fun n => ⟨fA_nonneg _ _ _ _ _ n, fA_le_nuW A hA _ _ _ _ n⟩)).trans
          (le_max_left _ _))
        hN1.1 hN2.1
      refine le_trans ?_ hbad
      -- injection m ↦ (m - b₁ - b₂)/W into the bad set
      have hthr : (0 : ℝ) ≤ (δ / 2) ^ 3 / 1000 := by positivity
      refine Nat.cast_le.2 (card_le_card_of_injOn (fun m => (((m - (b₁ + b₂)) / W : ℕ) : ZMod N))
        ?_ ?_)
      · intro m hm
        simp only [excSet, coe_filter, mem_filter, mem_Icc, Set.mem_setOf_eq] at hm
        obtain ⟨⟨⟨⟨hm1, hmx⟩, hmev, hmA⟩, hXm⟩, hmr⟩ := hm
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
        have hbm : b₁ + b₂ ≤ m := by omega
        have hdvd : W ∣ m - (b₁ + b₂) := by
          apply Nat.dvd_of_mod_eq_zero
          apply Nat.sub_mod_eq_zero_of_mod_eq
          rw [hmr, hbr, Nat.mod_eq_of_lt hr]
        set q := (m - (b₁ + b₂)) / W with hqdef
        have hmq : m = W * q + (b₁ + b₂) := by
          rw [hqdef, Nat.mul_div_cancel' hdvd]; omega
        have hqN : q < N := by
          by_contra h
          have : W * N ≤ W * q := Nat.mul_le_mul_left W (by omega)
          omega
        by_contra hgt
        push Not at hgt
        have hpos : 0 < ∑ n : ZMod N, f₁ n * f₂ ((q : ZMod N) - n) := by
          unfold convE at hgt
          have : 0 < (1 / (N : ℝ)) * ∑ n : ZMod N, f₁ n * f₂ ((q : ZMod N) - n) :=
            lt_of_le_of_lt hthr hgt
          have hN0 : (0 : ℝ) < 1 / (N : ℝ) := by
            have : (0 : ℝ) < N := by exact_mod_cast hNp.pos
            positivity
          exact pos_of_mul_pos_right this hN0.le
        obtain ⟨n₁, -, hn₁⟩ := Finset.exists_lt_of_sum_lt (s := univ)
          (f := fun _ => (0 : ℝ)) (by simpa using hpos)
        have hf1 : f₁ n₁ ≠ 0 := by intro h; rw [h, zero_mul] at hn₁; exact lt_irrefl _ hn₁
        have hf2 : f₂ ((q : ZMod N) - n₁) ≠ 0 := by
          intro h; rw [h, mul_zero] at hn₁; exact lt_irrefl _ hn₁
        have hc1 : W * n₁.val + b₁ ∈ A ∧ W * n₁.val + b₁ ≤ Xc := by
          by_contra h; exact hf1 (by simp only [f₁, fA]; rw [if_neg h])
        have hc2 : W * ((q : ZMod N) - n₁).val + b₂ ∈ A ∧
            W * ((q : ZMod N) - n₁).val + b₂ ≤ Xc := by
          by_contra h; exact hf2 (by simp only [f₂, fA]; rw [if_neg h])
        have heq := wrap W N b₁ b₂ Xc m q n₁ ((q : ZMod N) - n₁) hqN hmq (by ring) hc1.2 hc2.2
          hXm (hmx.trans hfloorxN)
        exact hmA ⟨_, hc1.1, _, hc2.1, heq⟩
      · intro m₁ hm₁ m₂ hm₂ he
        simp only [excSet, coe_filter, mem_filter, mem_Icc, Set.mem_setOf_eq] at hm₁ hm₂
        simp only at he
        have hq : ∀ m, m ≤ ⌊x⌋₊ → (m - (b₁ + b₂)) / W < N := by
          intro m hm
          rw [Nat.div_lt_iff_lt_mul hW]
          have : m - (b₁ + b₂) < W * N := by omega
          linarith [Nat.mul_comm W N]
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hq _ hm₁.1.1.1.2),
          Nat.mod_eq_of_lt (hq _ hm₂.1.1.1.2)] at he
        have hd1 : W ∣ m₁ - (b₁ + b₂) := Nat.dvd_of_mod_eq_zero
          (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hm₁.2, hbr, Nat.mod_eq_of_lt hr]))
        have hd2 : W ∣ m₂ - (b₁ + b₂) := Nat.dvd_of_mod_eq_zero
          (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hm₂.2, hbr, Nat.mod_eq_of_lt hr]))
        have e1 := Nat.mul_div_cancel' hd1
        have e2 := Nat.mul_div_cancel' hd2
        rw [he] at e1
        have : b₁ + b₂ ≤ m₁ := by omega
        have : b₁ + b₂ ≤ m₂ := by omega
        omega
    · have : ((excSet A x).filter (fun m => Xc < m)).filter (fun m => m % W = r) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro m hm
        simp only [excSet, mem_filter, mem_Icc] at hm
        apply hre
        rw [← hm.2, Nat.even_iff, Nat.mod_mod_of_dvd _ hW2]
        exact Nat.even_iff.mp hm.1.1.2.1
      rw [this, card_empty, Nat.cast_zero]; positivity
  -- sum over classes
  have hsplit := card_eq_sum_card_fiberwise (f := fun m => m % W) (t := range W)
    (s := (excSet A x).filter (fun m => Xc < m)) (fun m _ => by
      simp only [coe_range, Set.mem_Iio]; exact Nat.mod_lt _ hW)
  rw [hsplit]
  push_cast
  calc ∑ r ∈ range W, ((((excSet A x).filter (fun m => Xc < m)).filter
          (fun m => m % W = r)).card : ℝ)
      ≤ ∑ _r ∈ range W, η / 4 * N := sum_le_sum hfib
    _ = η / 4 * (W * N) := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ η / 4 * ((1 + κ) * x) := mul_le_mul_of_nonneg_left hWNx (by positivity)
    _ ≤ η * x := by nlinarith

/-! ### From windows to density zero -/

lemma excSet_le (A : Set ℕ) (y : ℝ) (hy : 0 ≤ y) : ((excSet A y).card : ℝ) ≤ y := by
  have : (excSet A y).card ≤ ⌊y⌋₊ := by
    calc (excSet A y).card ≤ (Icc 1 ⌊y⌋₊).card := card_filter_le _ _
      _ = ⌊y⌋₊ := by simp
  exact (Nat.cast_le.2 this).trans (Nat.floor_le hy)

lemma excSet_step (A : Set ℕ) (q x : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hx : 0 ≤ x) :
    ((excSet A x).card : ℝ) ≤ (excSet A (q * x)).card +
      ((excSet A x).filter (fun m => ⌊q * x⌋₊ < m)).card := by
  have hsub : excSet A x ⊆ excSet A (q * x) ∪ (excSet A x).filter (fun m => ⌊q * x⌋₊ < m) := by
    intro m hm
    by_cases h : ⌊q * x⌋₊ < m
    · exact mem_union_right _ (mem_filter.2 ⟨hm, h⟩)
    · apply mem_union_left
      simp only [excSet, mem_filter, mem_Icc] at hm ⊢
      exact ⟨⟨hm.1.1, by omega⟩, hm.2⟩
  exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)

lemma iterate_bound (E : ℝ → ℝ) (q η x₀ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη : 0 ≤ η)
    (hstep : ∀ x, x₀ ≤ x → 0 ≤ x → E x ≤ E (q * x) + η * x) :
    ∀ J : ℕ, ∀ x, 0 ≤ x → x₀ ≤ q ^ J * x → E x ≤ E (q ^ J * x) + J * η * x := by
  intro J
  induction J with
  | zero => intro x _ _; simp
  | succ J ih =>
    intro x hx hJ
    have hqJ : q ^ (J + 1) * x ≤ x := by
      have : q ^ (J + 1) ≤ 1 := pow_le_one₀ hq0 hq1
      nlinarith
    have h1 := hstep x (hJ.trans hqJ) hx
    have h2 := ih (q * x) (by positivity) (by rw [← mul_assoc, ← pow_succ]; exact hJ)
    rw [← mul_assoc, ← pow_succ] at h2
    have : (J : ℝ) * η * (q * x) ≤ J * η * x := by
      have : q * x ≤ x := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    push_cast
    nlinarith

/-- **Alsetri-Shao 2024, Theorem 1.2, CONDITIONAL ON `AS_Prop31`, `Green62`, `Green66`.** -/
theorem alsetriShao_1_2_of_cited (H31 : AS_Prop31) (H62 : Green62) (H66 : Green66) :
    AlsetriShao12 := by
  intro A hA η₀ hη₀ hdens
  set δ := min (η₀ - 1 / 2) (1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hd : ∀ W b : ℕ, 0 < W → Nat.Coprime b W → 1 / 2 + δ ≤ lowerDensityRes A b W :=
    fun W b h1 h2 => le_trans (by linarith [min_le_left (η₀ - 1 / 2) (1 / 4)]) (hdens W b h1 h2)
  set κ := δ / 16
  have hκ0 : 0 < κ := by positivity
  have hq0 : 0 ≤ 1 - κ := by simp only [κ]; linarith
  have hq1 : 1 - κ < 1 := by linarith
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (by positivity),
    fun a ha => ?_⟩
  set ε := a / 2
  have hε : 0 < ε := by positivity
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity) hq1
  set η := ε / (2 * (J + 1))
  have hη : 0 < η := by positivity
  obtain ⟨x₀, hx₀⟩ := window_bound A hA δ hδ0 hδ1 hd H31 H62 H66 η hη
  have hstep : ∀ x, x₀ ≤ x → 0 ≤ x → ((excSet A x).card : ℝ) ≤
      (excSet A ((1 - κ) * x)).card + η * x := fun x hx hx0 =>
    (excSet_step A (1 - κ) x hq0 hq1.le hx0).trans (by linarith [hx₀ x hx])
  have hqJ : 0 < (1 - κ) ^ J := pow_pos (by simp only [κ]; linarith) J
  rw [eventually_atTop]
  refine ⟨⌈max x₀ 1 / (1 - κ) ^ J⌉₊ + 1, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXbig : x₀ ≤ (1 - κ) ^ J * X := by
    have h1 : max x₀ 1 / (1 - κ) ^ J ≤ X := by
      have := Nat.le_ceil (max x₀ 1 / (1 - κ) ^ J)
      have h2 : ((⌈max x₀ 1 / (1 - κ) ^ J⌉₊ : ℕ) : ℝ) ≤ X := by
        exact_mod_cast (show ⌈max x₀ 1 / (1 - κ) ^ J⌉₊ ≤ X by omega)
      linarith
    rw [div_le_iff₀ hqJ] at h1
    linarith [le_max_left x₀ 1]
  have hit := iterate_bound (fun x => ((excSet A x).card : ℝ)) (1 - κ) η x₀ hq0 hq1.le hη.le
    hstep J X hXpos.le hXbig
  have hrest := excSet_le A ((1 - κ) ^ J * X) (by positivity)
  have hE : ((excSet A X).card : ℝ) ≤ ε * X := by
    have h1 : (1 - κ) ^ J * X ≤ ε / 2 * X := mul_le_mul_of_nonneg_right hJ.le hXpos.le
    have h2 : (J : ℝ) * η * X ≤ ε / 2 * X := by
      apply mul_le_mul_of_nonneg_right _ hXpos.le
      simp only [η]
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hfloor : excSet A (X : ℝ) = {n ∈ Icc 1 X | Even n ∧ ¬ ∃ a ∈ A, ∃ b ∈ A, a + b = n} := by
    simp [excSet, Nat.floor_natCast]
  rw [hfloor] at hE
  rw [div_lt_iff₀ hXpos]
  have : ε * X < a * X := by
    apply mul_lt_mul_of_pos_right _ hXpos; simp only [ε]; linarith
  linarith

/-! ### Vacuity tests -/

/-- Theorem 1.2's hypothesis holds for `A = P`, every class has density `1`. -/
theorem vacuity_thm12 : ∃ A : Set ℕ, A ⊆ P ∧ ∃ η : ℝ, 1 / 2 < η ∧
    ∀ W b : ℕ, 0 < W → Nat.Coprime b W → η ≤ lowerDensityRes A b W :=
  ⟨P, subset_rfl, 1, by norm_num, fun W b hW hb => (lowerDensityRes_P b W hW hb).ge⟩

lemma hatE_one (N : ℕ) [NeZero N] (r : ZMod N) :
    hatE N (fun _ => 1) r = if r = 0 then 1 else 0 := by
  unfold hatE
  have h := AddChar.sum_mulShift (-r) (ZMod.isPrimitive_stdAddChar N)
  have e : ∀ n : ZMod N, (((fun _ => (1 : ℝ)) n : ℝ) : ℂ) * ZMod.stdAddChar (-(r * n)) =
      ZMod.stdAddChar (n * -r) := by
    intro n; simp only [Complex.ofReal_one, one_mul]; congr 1; ring
  rw [Finset.sum_congr rfl (fun n _ => e n), h]
  by_cases hr : r = 0
  · simp [hr, ZMod.card]
  · simp [hr]

/-- The hypotheses of `AS_Prop31` hold, for every `N`, every `δ < 1/2`, `p`, `M ≥ 1`, `c > 0`:
`f_i = ν_i = 1`. -/
theorem vacuity_Prop31 (N : ℕ) [NeZero N] (δ : ℝ) (hδ : δ < 1 / 2) (p : ℝ) (hp : 2 < p)
    (Mc : ℝ) (hM : 1 ≤ Mc) (c : ℝ) (hc : 0 < c) :
    let f : ZMod N → ℝ := fun _ => 1
    (∀ n, 0 ≤ f n ∧ f n ≤ f n) ∧ 1 + δ ≤ avg N f + avg N f ∧ lpHat N p f ≤ Mc ∧
      (∀ r, ‖hatE N f r - (if r = 0 then 1 else 0)‖ ≤ c) := by
  intro f
  have havg : avg N f = 1 := by
    simp only [avg, f, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    field_simp
  refine ⟨fun n => ⟨by simp [f], le_rfl⟩, by rw [havg]; linarith, ?_, fun r => ?_⟩
  · unfold lpHat
    have hs : ∑ r : ZMod N, ‖hatE N f r‖ ^ p = 1 := by
      rw [Finset.sum_eq_single (0 : ZMod N)]
      · rw [hatE_one]; simp
      · intro r _ hr; rw [hatE_one, if_neg hr, norm_zero, Real.zero_rpow (by linarith)]
      · simp
    rw [hs, Real.one_rpow]; exact hM
  · rw [hatE_one, sub_self, norm_zero]; exact hc.le

/-- The hypotheses of `Green62` and `Green66` hold: `b = 1` is a reduced class below `z#` for
`z ≥ 2`, and `f = 0` lies under `ν_b`. -/
theorem vacuity_Green (z : ℕ) (hz : 2 ≤ z) (N : ℕ) [NeZero N] :
    1 < primorial z ∧ Nat.Coprime 1 (primorial z) ∧
      ∀ n : ZMod N, 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ nuW (primorial z) 1 N n := by
  refine ⟨?_, Nat.coprime_one_left _, fun n => ⟨le_rfl, nuW_nonneg _ _ _ n⟩⟩
  have h2 := prime_dvd_primorial' Nat.prime_two hz
  have := Nat.le_of_dvd (primorial_pos z) h2
  omega

end LeanLab.DensityGoldbach.U1446

