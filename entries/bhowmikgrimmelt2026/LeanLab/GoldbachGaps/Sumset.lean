module

public import Mathlib
public import LeanLab.GoldbachGaps.Unconditional

/-!
I-5020, unit U-5104, T2 FRONTIER, CLOUD 20261019T0314Z-cloud15. Unconditional explicit
Goldbach numbers in short intervals, by a sumset step on top of I-0018 (`Unconditional.lean`).

I-0018 used one prime: `p + 3` with `p` near `x`, so the gap is a prime gap,
`x/(5000 log² x)`. Here both summands move: a prime `p ∈ [x - M, x]` by Dusart, then a prime
`q` just above `g = x - p ≤ M`, either by the maximal prime gap `1476` below `4 · 10^18` or by
Dusart again at `g`. Then `p + q ∈ (x, x + H]` with
`H = max 1478 (1 + (M + 1)/(5000 log² (M + 1)))`, `M = x/(5000 log² (x/2))`.
So every interval `(x, x + 1478]` with `4 · 10^18 ≤ x` up to about `7 · 10^25` holds a Goldbach
number, and beyond that the length is about `x/(2.5 · 10^7 log⁴ x)`.

Inputs, cited, not proved here: `DusartCor55` from `Unconditional.lean`, and
`GapBound1476`, the maximal prime gap below `4 · 10^18` from Oliveira e Silva, Herzog, Pardi
2014, Table 8, P0005; the gap 1476 itself is kernel checked in Verifications/Top50, its
maximality is the cited part.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach stays OPEN.
-/

@[expose] public section

namespace LeanLab.GoldbachGaps.Sumset
open Real LeanLab.GoldbachGaps

/-- Cited, P0005 Table 8: no gap between consecutive primes below `4 · 10^18` exceeds `1476`,
read as: every interval `(a, a + 1476]` with `2 ≤ a` and `a + 1476 ≤ 4 · 10^18` holds a prime. -/
def GapBound1476 : Prop :=
  ∀ a : ℝ, 2 ≤ a → a + 1476 ≤ 4 * 10 ^ 18 → ∃ q : ℕ, q.Prime ∧ a < q ∧ (q : ℝ) ≤ a + 1476

/-- `t / log² t` is monotone once `log t ≥ 2`, from `eᵘ ≥ 1 + u + u²/2`. -/
theorem div_log_sq_mono {a b : ℝ} (ha0 : 0 < a) (ha : 2 ≤ log a) (hab : a ≤ b) :
    a / log a ^ 2 ≤ b / log b ^ 2 := by
  have hb0 : 0 < b := by linarith
  set u := log (b / a) with hu
  have hs : b / a = exp u := by rw [hu, exp_log (by positivity)]
  have hu0 : 0 ≤ u := log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  have hlb : log b = log a + u := by
    rw [hu, log_div hb0.ne' ha0.ne']; ring
  have hq := Real.quadratic_le_exp_of_nonneg hu0
  have hb : b = a * exp u := by rw [← hs]; field_simp
  have hlb2 : 0 < log b := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), hlb, hb]
  have key : (log a + u) ^ 2 ≤ exp u * log a ^ 2 := by
    have h1 : (1 + u + u ^ 2 / 2) * log a ^ 2 ≤ exp u * log a ^ 2 :=
      mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    nlinarith [mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ log a - 2), sq_nonneg u,
      mul_nonneg (sq_nonneg u) (by nlinarith : (0 : ℝ) ≤ log a ^ 2 / 2 - 1)]
  nlinarith [ha0]

/-- `M(x) = x / (5000 log² (x/2))`. -/
noncomputable def M (x : ℝ) : ℝ := x / (5000 * log (x / 2) ^ 2)

/-- `H(x) = max 1478 (1 + (M + 1)/(5000 log² (M + 1)))`. -/
noncomputable def H (x : ℝ) : ℝ := max 1478 (1 + (M x + 1) / (5000 * log (M x + 1) ^ 2))

theorem log_big {x : ℝ} (hx : 2e18 ≤ x) : 41 ≤ log x := by
  have h := Real.add_one_le_exp (41 : ℝ)
  have he : exp (41 : ℝ) ≤ 2e18 := by
    have h1 := Real.exp_one_lt_d9
    have : exp (41 : ℝ) = exp 1 ^ 41 := by rw [← exp_nat_mul]; norm_num
    rw [this]
    calc exp 1 ^ 41 ≤ (2.7182818286 : ℝ) ^ 41 := pow_le_pow_left₀ (exp_pos 1).le h1.le 41
      _ ≤ 2e18 := by norm_num
  rw [← exp_le_exp, exp_log (by linarith)]; linarith

/-- **I-5020, CONDITIONAL ON Dusart 2018 Corollary 5.5 and the maximal prime gap 1476 below
`4 · 10^18`**: for every real `x ≥ 4 · 10^18` there is a Goldbach number in `(x, x + H(x)]`. -/
theorem goldbach_gap_sumset (hD : DusartCor55) (hG : GapBound1476) {x : ℝ} (hx : 4e18 ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + H x := by
  have hx0 : 0 < x := by linarith
  have hlx2 : 41 ≤ log (x / 2) := log_big (by linarith)
  have hM0 : 0 < M x := by unfold M; positivity
  have hMx : M x ≤ x / 2 := by
    unfold M
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h2 : (2 : ℝ) ≤ 5000 * log (x / 2) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hx0.le]
  set X := x - M x with hX
  have hXx : x / 2 ≤ X := by linarith
  have hlX : log (x / 2) ≤ log X := log_le_log (by positivity) hXx
  -- a prime p ∈ [x - M, x]
  obtain ⟨p, hp, hpl, hpu⟩ := hD X (by linarith)
  have hpx : (p : ℝ) ≤ x := by
    have h1 : X * (1 + 1 / (5000 * log X ^ 2)) = X + X / (5000 * log X ^ 2) := by ring
    have h2 : X / (5000 * log X ^ 2) ≤ M x := by
      unfold M
      have hlX0 : 0 < log X := by linarith
      calc X / (5000 * log X ^ 2) ≤ x / (5000 * log X ^ 2) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ x / (5000 * log (x / 2) ^ 2) :=
            div_le_div_of_nonneg_left hx0.le (by positivity)
              (by nlinarith)
    linarith
  have hp3 : 3 ≤ p := by
    have : (3 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  set g := x - p with hg
  have hg0 : 0 ≤ g := by linarith
  have hgM : g ≤ M x := by linarith
  -- a prime q just above g
  have hq : ∃ q : ℕ, q.Prime ∧ 3 ≤ q ∧ g < q ∧ (q : ℝ) ≤ g + H x := by
    rcases le_or_gt (max g 2 + 1476) (4 * 10 ^ 18) with hs | hb
    · obtain ⟨q, hq, hql, hqu⟩ := hG (max g 2) (le_max_right _ _) hs
      refine ⟨q, hq, ?_, lt_of_le_of_lt (le_max_left _ _) hql, ?_⟩
      · have : (2 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hql
        have : 2 < q := by exact_mod_cast this
        omega
      · have : max g 2 ≤ g + 2 := max_le (by linarith) (by linarith)
        have := le_max_left (1478 : ℝ) (1 + (M x + 1) / (5000 * log (M x + 1) ^ 2))
        unfold H; linarith
    · have hgbig : 4e18 - 1478 < g := by
        have : max g 2 = g := max_eq_left (by
          by_contra h; push Not at h; rw [max_eq_right h.le] at hb; norm_num at hb)
        rw [this] at hb; norm_num at hb ⊢; linarith
      obtain ⟨q, hq, hql, hqu⟩ := hD (g + 1) (by linarith)
      refine ⟨q, hq, ?_, by linarith, ?_⟩
      · have : (3 : ℝ) ≤ q := by linarith
        exact_mod_cast this
      · have hl : 2 ≤ log (g + 1) := by have := log_big (x := g + 1) (by linarith); linarith
        have hmono := div_log_sq_mono (by linarith) hl (by linarith : g + 1 ≤ M x + 1)
        have e1 : (g + 1) * (1 + 1 / (5000 * log (g + 1) ^ 2)) =
            (g + 1) + (g + 1) / log (g + 1) ^ 2 / 5000 := by field_simp
        have e2 : (M x + 1) / (5000 * log (M x + 1) ^ 2) = (M x + 1) / log (M x + 1) ^ 2 / 5000 := by
          field_simp
        have := le_max_right (1478 : ℝ) (1 + (M x + 1) / (5000 * log (M x + 1) ^ 2))
        unfold H
        rw [e1] at hqu
        rw [e2] at this ⊢
        linarith
  obtain ⟨q, hq, hq3, hql, hqu⟩ := hq
  have hqo : Odd q := hq.odd_of_ne_two (by omega)
  refine ⟨p + q, ⟨hpo.add_odd hqo, p, q, hp, hq, rfl⟩, ?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith

/-- The plain consequence for the range `4 · 10^18 ≤ x` with `M(x) + 1478 ≤ 4 · 10^18`, which
holds up to about `7 · 10^25`: every `(x, x + 1478]` holds a Goldbach number. -/
theorem goldbach_gap_1478 (hD : DusartCor55) (hG : GapBound1476) {x : ℝ} (hx : 4e18 ≤ x)
    (hxM : M x + 1478 ≤ 4 * 10 ^ 18) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 := by
  -- rerun the first case: with g ≤ M, `max g 2 + 1476 ≤ 4e18`
  have hx0 : 0 < x := by linarith
  have hlx2 : 41 ≤ log (x / 2) := log_big (by linarith)
  have hM0 : 0 < M x := by unfold M; positivity
  have hMx : M x ≤ x / 2 := by
    unfold M
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h2 : (2 : ℝ) ≤ 5000 * log (x / 2) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hx0.le]
  set X := x - M x with hX
  have hXx : x / 2 ≤ X := by linarith
  have hlX : log (x / 2) ≤ log X := log_le_log (by positivity) hXx
  obtain ⟨p, hp, hpl, hpu⟩ := hD X (by linarith)
  have hpx : (p : ℝ) ≤ x := by
    have h1 : X * (1 + 1 / (5000 * log X ^ 2)) = X + X / (5000 * log X ^ 2) := by ring
    have h2 : X / (5000 * log X ^ 2) ≤ M x := by
      unfold M
      calc X / (5000 * log X ^ 2) ≤ x / (5000 * log X ^ 2) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ x / (5000 * log (x / 2) ^ 2) :=
            div_le_div_of_nonneg_left hx0.le (by positivity) (by nlinarith)
    linarith
  have hp3 : 3 ≤ p := by
    have : (3 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  set g := x - p with hg
  have hg0 : 0 ≤ g := by linarith
  have hs : max g 2 + 1476 ≤ 4 * 10 ^ 18 := by
    have : max g 2 ≤ M x + 2 := max_le (by linarith) (by linarith)
    linarith
  obtain ⟨q, hq, hql, hqu⟩ := hG (max g 2) (le_max_right _ _) hs
  have hq3 : 3 ≤ q := by
    have : (2 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hql
    have : 2 < q := by exact_mod_cast this
    omega
  have hqo : Odd q := hq.odd_of_ne_two (by omega)
  have hmax : max g 2 ≤ g + 2 := max_le (by linarith) (by linarith)
  refine ⟨p + q, ⟨hpo.add_odd hqo, p, q, hp, hq, rfl⟩, ?_, ?_⟩
  · push_cast; linarith [le_max_left g 2]
  · push_cast; linarith

/-- Vacuity test for `goldbach_gap_1478`: `x = 10^25` meets `M x + 1478 ≤ 4 · 10^18`. -/
theorem M_1e25 : M 1e25 + 1478 ≤ 4 * 10 ^ 18 := by
  have hl : 56 ≤ log ((1e25 : ℝ) / 2) := by
    have h := Real.add_one_le_exp (56 : ℝ)
    have he : exp (56 : ℝ) ≤ 1e25 / 2 := by
      have h1 := Real.exp_one_lt_d9
      have : exp (56 : ℝ) = exp 1 ^ 56 := by rw [← exp_nat_mul]; norm_num
      rw [this]
      calc exp 1 ^ 56 ≤ (2.7182818286 : ℝ) ^ 56 := pow_le_pow_left₀ (exp_pos 1).le h1.le 56
        _ ≤ 1e25 / 2 := by norm_num
    rw [← exp_le_exp, exp_log (by norm_num)]; linarith
  unfold M
  have : (1e25 : ℝ) / (5000 * log (1e25 / 2) ^ 2) ≤ 1e25 / (5000 * 56 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have : (1e25 : ℝ) / (5000 * 56 ^ 2) + 1478 ≤ 4 * 10 ^ 18 := by norm_num
  linarith

/-! ### All `x` up to `7.86 · 10^27`, from Kadiri-Lumley rows, the binary twin of their
Corollary 1.2 -/

/-- Core step: an odd prime `p` with `x - (4 · 10^18 - 1478) ≤ p ≤ x + 1475` gives a Goldbach
number in `(x, x + 1478]`. -/
theorem core (hG : GapBound1476) {x : ℝ} {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hlo : x - (4 * 10 ^ 18 - 1478) ≤ p) (hhi : (p : ℝ) ≤ x + 1475) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 := by
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  rcases le_or_gt (p : ℝ) x with hpx | hpx
  · set g := x - p with hg
    have hs : max g 2 + 1476 ≤ 4 * 10 ^ 18 := by
      have : max g 2 ≤ 4 * 10 ^ 18 - 1476 := max_le (by linarith) (by norm_num)
      linarith
    obtain ⟨q, hq, hql, hqu⟩ := hG (max g 2) (le_max_right _ _) hs
    have hq3 : 3 ≤ q := by
      have : (2 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hql
      have : 2 < q := by exact_mod_cast this
      omega
    have hqo : Odd q := hq.odd_of_ne_two (by omega)
    have hmax : max g 2 ≤ g + 2 := max_le (by linarith) (by linarith)
    refine ⟨p + q, ⟨hpo.add_odd hqo, p, q, hp, hq, rfl⟩, ?_, ?_⟩
    · push_cast; linarith [le_max_left g 2]
    · push_cast; linarith
  · refine ⟨p + 3, ⟨hpo.add_odd (by decide), p, 3, hp, Nat.prime_three, rfl⟩, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

theorem exp60_lt : Real.exp 60 < 1.15e26 := by
  have h1 := Real.exp_one_lt_d9
  have : Real.exp (60 : ℝ) = Real.exp 1 ^ 60 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 60 < (2.7182818286 : ℝ) ^ 60 :=
        pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
    _ ≤ 1.15e26 := by norm_num

/-- **I-5020, all-`x` form, CONDITIONAL ON the `4 · 10^18` even check, Kadiri-Lumley Table 2
rows `4 · 10^18` and `e^60`, and the maximal gap 1476 below `4 · 10^18`**: for every real
`x` with `2 ≤ x ≤ 7.86 · 10^27`, the interval `(x, x + 1478]` holds a Goldbach number. -/
theorem goldbach_gap_1478_all (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (h1 : LeanLab.KadiriLumley2014.KLRow (4 * 10 ^ 18) 36082898)
    (h2 : LeanLab.KadiriLumley2014.KLRow (Real.exp 60) 1966196911) (hG : GapBound1476)
    {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 7.86e27) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 := by
  rcases le_or_gt x (4 * 10 ^ 18 - 2) with hs | hb
  · obtain ⟨n, hev, hlo, hhi⟩ := even_above x (by linarith)
    have hn4 : 4 ≤ n := by
      have : (2 : ℝ) < n := by linarith
      have h2 : 2 < n := by exact_mod_cast this
      rcases hev with ⟨k, hk⟩; omega
    have hnN : n ≤ 4 * 10 ^ 18 := by
      have : (n : ℝ) ≤ 4 * 10 ^ 18 := by linarith
      exact_mod_cast this
    exact ⟨n, ⟨hev, hE n hev hn4 hnN⟩, hlo, by linarith⟩
  rcases le_or_gt x 1.44e26 with hm | hl
  · set y := max x (4 * 10 ^ 18 + 1) with hy
    obtain ⟨p, hp, hpl, hpu⟩ := h1 y (by
      have := le_max_right x (4 * 10 ^ 18 + 1); linarith)
    have hyx : y ≤ x + 3 := max_le (by linarith) (by linarith)
    have hxy : x ≤ y := le_max_left _ _
    have hy0 : y ≤ 1.44e26 := max_le hm (by norm_num)
    have hp3 : 3 ≤ p := by
      have : (3 : ℝ) ≤ p := by nlinarith
      exact_mod_cast this
    apply core hG hp hp3
    · have : (1 - 1 / 36082898 : ℝ) * y = y - y / 36082898 := by ring
      have : y / 36082898 ≤ 4 * 10 ^ 18 - 1478 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    · linarith
  · have hx60 : Real.exp 60 < x := by have := exp60_lt; linarith
    obtain ⟨p, hp, hpl, hpu⟩ := h2 x hx60
    have hp3 : 3 ≤ p := by
      have : (3 : ℝ) ≤ p := by nlinarith
      exact_mod_cast this
    apply core hG hp hp3
    · have : (1 - 1 / 1966196911 : ℝ) * x = x - x / 1966196911 := by ring
      have : x / 1966196911 ≤ 4 * 10 ^ 18 - 1478 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    · linarith

/-- **I-5020, every `x ≥ 2`, CONDITIONAL ON the same four inputs**: the interval
`(x, x + max 1478 (x / (7 · 10^16))]` holds a Goldbach number. Above `7.86 · 10^27` the prime
`p` near `x` comes from the `e^60` row, and the prime `q` just above `g = x - p < x/Δ₆₀` from
the gap table or from the `4 · 10^18` row at `g Δ/(Δ - 1)`. I-0018 had `x / 36082897`. -/
theorem goldbach_gap_all (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (h1 : LeanLab.KadiriLumley2014.KLRow (4 * 10 ^ 18) 36082898)
    (h2 : LeanLab.KadiriLumley2014.KLRow (Real.exp 60) 1966196911) (hG : GapBound1476)
    {x : ℝ} (hx : 2 ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + max 1478 (x / 7e16) := by
  rcases le_or_gt x 7.86e27 with hs | hb
  · obtain ⟨n, hn, h1', h2'⟩ := goldbach_gap_1478_all hE h1 h2 hG hx hs
    exact ⟨n, hn, h1', by have := le_max_left (1478 : ℝ) (x / 7e16); linarith⟩
  have hx60 : Real.exp 60 < x := by have := exp60_lt; linarith
  obtain ⟨p, hp, hpl, hpu⟩ := h2 x hx60
  have hp3 : 3 ≤ p := by
    have : (3 : ℝ) ≤ p := by nlinarith
    exact_mod_cast this
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  set g := x - p with hg
  have hg0 : 0 < g := by linarith
  have hgx : g < x / 1966196911 := by
    have : (1 - 1 / 1966196911 : ℝ) * x = x - x / 1966196911 := by ring
    linarith
  rcases le_or_gt g (4 * 10 ^ 18 - 1478) with hgs | hgb
  · obtain ⟨n, hn, hlo, hhi⟩ := core hG (x := x) hp hp3 (by linarith) (by linarith)
    exact ⟨n, hn, hlo, by have := le_max_left (1478 : ℝ) (x / 7e16); linarith⟩
  · set y := g * 36082898 / 36082897 with hy
    have hy4 : 4 * 10 ^ 18 < y := by rw [hy]; nlinarith
    obtain ⟨q, hq, hql, hqu⟩ := h1 y hy4
    have hyl : (1 - 1 / 36082898 : ℝ) * y = g := by rw [hy]; field_simp; ring
    rw [hyl] at hql
    have hq3 : 3 ≤ q := by
      have : (3 : ℝ) ≤ q := by linarith
      exact_mod_cast this
    have hqo : Odd q := hq.odd_of_ne_two (by omega)
    have hyg : y = g + g / 36082897 := by rw [hy]; field_simp; ring
    have hbound : g / 36082897 ≤ x / 7e16 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    refine ⟨p + q, ⟨hpo.add_odd hqo, p, q, hp, hq, rfl⟩, ?_, ?_⟩
    · push_cast; linarith
    · push_cast
      have := le_max_right (1478 : ℝ) (x / 7e16)
      linarith

end LeanLab.GoldbachGaps.Sumset

