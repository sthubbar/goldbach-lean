module

public import Mathlib
public import LeanLab.Linnik.Gallagher1975Thm2Count
public import LeanLab.PNTPort.StrongPNT.Bridge

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, Lemma 14, display (7),
p.139, read from the page image, PDF page 16. Unit U-7201, CLOUD MANUAL-N2, 2026-10-21.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Lemma 14: for fixed `k`, `Σ_{n ≤ N} r'_k(n) ~ N L^k / log N` as `N → ∞`, `L = [log₂ N]`.
Gallagher's proof: `Σ_{n ≤ N} r'_k(n) = Σ_{p ≤ N} f(N - p)`, display (8)
`π(N - N/L) f(N/L) ≤ Σ_{p ≤ N} f(N - p) ≤ π(N) f(N)`, the bounds `fL_le`, `fL_ge`, and the
prime number theorem.

* `sum_rk_eq`: PROVED, `Σ_{n ≤ N} r'_k(n) = Σ_{p ≤ N prime} f(N - p)`.
* `sum_rk_le`, `sum_rk_ge`: PROVED, the two sides of (8); the lower side with `N/2^t` in place
  of `N/L`, a fixed shift, which gives the same limit.
* `lemma14_of_pi`: PROVED, `PiAsymp → Lemma14`, where `PiAsymp` is `π(N) ~ N / log N`.
* `piAsymp`: PROVED from the lab's prime number theorem port, `psi_explicit_strong`.
* `lemma14`: PROVED, unconditional.
* `theorem2_of_theorem1`: Gallagher's Theorem 2, display (4), CONDITIONAL ON `Theorem1` alone.
-/

@[expose] public section

open Finset Real Filter
open scoped Topology

noncomputable section
namespace LeanLab.Linnik.U7201

open LeanLab.Linnik.Gallagher1975 LeanLab.Linnik.Gallagher1975Thm2
open LeanLab.LPZ2007 (tuples pow2sum card_tuples pow_le_pow2sum)

/-- `rk` as a double sum over primes below `N` and tuples, for `n ≤ N`. -/
theorem rk_eq_sum (k N n : ℕ) (hn : n ≤ N) :
    (rk k N n : ℝ) = ∑ p ∈ range (N + 1), ∑ ν ∈ tuples k (Nat.log 2 N),
      if p.Prime ∧ n = p + pow2sum ν then (1 : ℝ) else 0 := by
  have hsub : range (n + 1) ⊆ range (N + 1) := range_subset_range.mpr (by omega)
  unfold rk
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  push_cast
  apply Finset.sum_subset hsub
  intro p hp hp'
  apply sum_eq_zero
  intro ν _
  rw [if_neg]
  rintro ⟨_, h⟩
  simp only [mem_range] at hp hp'
  omega

/-- Gallagher p.139: `Σ_{n ≤ N} r'_k(n) = Σ_{p ≤ N} f(N - p)`. -/
theorem sum_rk_eq (k N : ℕ) :
    ∑ n ∈ range (N + 1), (rk k N n : ℝ) =
      ∑ p ∈ Nat.primesLE N, (fL k (Nat.log 2 N) (N - p) : ℝ) := by
  rw [sum_congr rfl fun n hn => rk_eq_sum k N n (by simp at hn; omega)]
  rw [sum_comm]
  rw [Nat.primesLE_eq_filter_range, sum_filter]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  have hpN : p ≤ N := by simp at hp; omega
  unfold fL
  rw [Finset.card_filter, Nat.cast_sum]
  split_ifs with hpr
  · apply sum_congr rfl
    intro ν _
    have : (∑ n ∈ range (N + 1), if p.Prime ∧ n = p + pow2sum ν then (1 : ℝ) else 0) =
        if p + pow2sum ν ∈ range (N + 1) then 1 else 0 := by
      simp only [hpr, true_and]
      rw [Finset.sum_ite_eq']
    rw [this]
    simp only [mem_range]
    by_cases h : pow2sum ν ≤ N - p
    · rw [if_pos (by omega), if_pos h]; simp
    · rw [if_neg (by omega), if_neg h]; simp
  · apply sum_eq_zero
    intro ν _
    apply sum_eq_zero
    intro n _
    rw [if_neg (fun h => hpr h.1)]

theorem fL_mono (k L : ℕ) {x y : ℕ} (h : x ≤ y) : fL k L x ≤ fL k L y := by
  unfold fL
  apply card_le_card
  intro ν hν
  simp only [mem_filter] at hν ⊢
  exact ⟨hν.1, hν.2.trans h⟩

/-- Upper side of (8): `Σ_{n ≤ N} r'_k(n) ≤ π(N) L^k`. -/
theorem sum_rk_le (k N : ℕ) :
    ∑ n ∈ range (N + 1), (rk k N n : ℝ) ≤ (Nat.primeCounting N : ℝ) * (Nat.log 2 N : ℝ) ^ k := by
  rw [sum_rk_eq, ← Nat.primesLE_card_eq_primeCounting]
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply sum_le_sum
  intro p _
  have h1 := fL_le k (Nat.log 2 N) (N - p)
  have h2 : Nat.log 2 (N - p) ^ k ≤ Nat.log 2 N ^ k :=
    Nat.pow_le_pow_left (Nat.log_mono_right (Nat.sub_le N p)) k
  exact_mod_cast h1.trans h2

/-- Lower side of (8), with any `x ≤ N`: `π(N - x) f(x) ≤ Σ_{n ≤ N} r'_k(n)`. -/
theorem sum_rk_ge (k N x : ℕ) (hx : x ≤ N) :
    (Nat.primeCounting (N - x) : ℝ) * (Nat.log 2 (x / k) : ℝ) ^ k ≤
      ∑ n ∈ range (N + 1), (rk k N n : ℝ) := by
  rw [sum_rk_eq, ← Nat.primesLE_card_eq_primeCounting]
  have hsub : Nat.primesLE (N - x) ⊆ Nat.primesLE N := by
    intro p hp
    simp only [Nat.primesLE_eq_filter_range, mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  calc (#(Nat.primesLE (N - x)) : ℝ) * (Nat.log 2 (x / k) : ℝ) ^ k
      = ∑ _p ∈ Nat.primesLE (N - x), ((Nat.log 2 (x / k) ^ k : ℕ) : ℝ) := by
        rw [sum_const, nsmul_eq_mul]; push_cast; ring
    _ ≤ ∑ p ∈ Nat.primesLE (N - x), (fL k (Nat.log 2 N) (N - p) : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hp' : p ≤ N - x := by
          simp only [Nat.primesLE_eq_filter_range, mem_filter, mem_range] at hp; omega
        have := (fL_ge_of_le k N x hx).trans (fL_mono k (Nat.log 2 N) (show x ≤ N - p by omega))
        exact_mod_cast this
    _ ≤ ∑ p ∈ Nat.primesLE N, (fL k (Nat.log 2 N) (N - p) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-! ### The prime number theorem in the form `π(N) ~ N / log N` -/

/-- `π(N) ~ N / log N`, in the `ε` form of `Lemma14`. -/
def PiAsymp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    |(Nat.primeCounting N : ℝ) - N / Real.log N| ≤ ε * (N / Real.log N)

/-- `θ(x) = x + o(x)`, from the lab port's `psi_explicit_strong`; the argument is the one of
`theta_pnt`, U-1389, LiLiuDisplay37PNT.lean, copied here to keep the import small. -/
theorem theta_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  have h1 : Tendsto (fun x : ℝ => K * Real.exp (-(c * Real.sqrt (Real.log x)))) atTop (nhds 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hc)).const_mul K
    simpa using this
  have ev1 : ∀ᶠ x : ℝ in atTop, K * Real.exp (-(c * Real.sqrt (Real.log x))) ≤ ε / 2 :=
    (h1.eventually (ge_mem_nhds (by linarith : (0:ℝ) < ε / 2)))
  have ev2 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ ε / 4 * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).bound (by linarith)
  filter_upwards [ev1, ev2, eventually_ge_atTop (2 : ℝ)] with x hA hB h2
  have hx0 : 0 < x := by linarith
  have hpsi := hK x h2
  have hpt := Chebyshev.psi_sub_theta_le (by linarith : (1:ℝ) ≤ x)
  have htp := Chebyshev.theta_le_psi x
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at hB
  have hs : 2 * √x * Real.log x ≤ ε / 2 * x := by
    have : √x * √x = x := Real.mul_self_sqrt hx0.le
    nlinarith [Real.sqrt_nonneg x]
  have hK' : K * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ ε / 2 * x := by
    rw [show K * x * Real.exp (-c * Real.sqrt (Real.log x)) =
      (K * Real.exp (-(c * Real.sqrt (Real.log x)))) * x by rw [neg_mul]; ring]
    exact mul_le_mul_of_nonneg_right hA hx0.le
  rw [abs_le] at hpsi ⊢
  constructor <;> nlinarith

/-- `θ(N) ≤ π(N) log N`. -/
theorem theta_le_pi_mul_log (N : ℕ) :
    Chebyshev.theta N ≤ (Nat.primeCounting N : ℝ) * Real.log N := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, ← Nat.primesLE_card_eq_primeCounting,
    ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro p hp
  simp only [Nat.primesLE_eq_filter_range, mem_filter, mem_range] at hp
  exact Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast (by omega : p ≤ N))

/-- The split at `y`: `π(N) log y ≤ y log y + θ(N)` for `y ≥ 1`. -/
theorem pi_split (N : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (Nat.primeCounting N : ℝ) * Real.log y ≤ y * Real.log y + Chebyshev.theta N := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, ← Nat.primesLE_card_eq_primeCounting]
  rw [← Finset.card_filter_add_card_filter_not (fun p : ℕ => (p : ℝ) ≤ y)]
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  have hA : (#((Nat.primesLE N).filter (fun p : ℕ => (p : ℝ) ≤ y)) : ℝ) ≤ y := by
    have hsub : (Nat.primesLE N).filter (fun p : ℕ => (p : ℝ) ≤ y) ⊆ Icc 1 ⌊y⌋₊ := by
      intro p hp
      simp only [Nat.primesLE_eq_filter_range, mem_filter, mem_range] at hp
      rw [mem_Icc]
      exact ⟨hp.1.2.one_lt.le, Nat.le_floor hp.2⟩
    have := card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    calc (#((Nat.primesLE N).filter (fun p : ℕ => (p : ℝ) ≤ y)) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ y := Nat.floor_le (by linarith)
  have hB : (#((Nat.primesLE N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)) : ℝ) * Real.log y ≤
      ∑ p ∈ Nat.primesLE N, Real.log p := by
    calc (#((Nat.primesLE N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)) : ℝ) * Real.log y
        = ∑ _p ∈ (Nat.primesLE N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), Real.log y := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), Real.log p := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter, not_le] at hp
          exact Real.log_le_log (by linarith) hp.2.le
      _ ≤ ∑ p ∈ Nat.primesLE N, Real.log p :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp _ => by
            simp only [Nat.primesLE_eq_filter_range, mem_filter] at hp
            exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hA hly]

/-- **The prime number theorem** `π(N) ~ N / log N`, PROVED from the lab port. -/
theorem piAsymp : PiAsymp := by
  intro ε hε
  set δ := min (1 / 2) (ε / 8) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 8 := min_le_right _ _
  have evθ := theta_eventually δ hδ0
  have ev2 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ δ * ‖x ^ δ‖ :=
    (isLittleO_log_rpow_atTop hδ0).bound hδ0
  have ev : ∀ᶠ x : ℝ in atTop, (|Chebyshev.theta x - x| ≤ δ * x ∧
      ‖Real.log x‖ ≤ δ * ‖x ^ δ‖) ∧ 3 ≤ x :=
    (evθ.and ev2).and (eventually_ge_atTop 3)
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually ev)
  refine ⟨X, fun N hN => ?_⟩
  obtain ⟨⟨hθ, hlog⟩, h3⟩ := hX N hN
  set x : ℝ := (N : ℝ) with hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hxd : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlx, abs_of_pos hxd] at hlog
  have hNL : 0 < x / Real.log x := div_pos hx0 hlx
  rw [abs_le]
  constructor
  · -- lower: θ(N) ≤ π(N) log N
    have h1 := theta_le_pi_mul_log N
    rw [← hx] at h1
    have h2 : (1 - δ) * x ≤ (Nat.primeCounting N : ℝ) * Real.log x := by
      rw [abs_le] at hθ; linarith
    have h3' : (1 - δ) * (x / Real.log x) ≤ (Nat.primeCounting N : ℝ) := by
      rw [mul_div_assoc', div_le_iff₀ hlx]; exact h2
    nlinarith [mul_le_mul_of_nonneg_right (show δ ≤ ε by linarith) hNL.le]
  · -- upper: split at y = x^(1-δ)
    set y := x ^ (1 - δ) with hy
    have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by linarith)
    have hly : Real.log y = (1 - δ) * Real.log x := Real.log_rpow hx0 _
    have hsp := pi_split N hy1
    rw [← hx, hly] at hsp
    have hyx : y * x ^ δ = x := by
      rw [hy, ← Real.rpow_add hx0]; simp
    -- y log x ≤ δ x
    have hylog : y * Real.log x ≤ δ * x := by
      have hy0 : 0 ≤ y := by linarith
      calc y * Real.log x ≤ y * (δ * x ^ δ) := mul_le_mul_of_nonneg_left hlog hy0
        _ = δ * (y * x ^ δ) := by ring
        _ = δ * x := by rw [hyx]
    have hθu : Chebyshev.theta x ≤ (1 + δ) * x := by rw [abs_le] at hθ; linarith
    -- π log x ≤ (y log x + θ)/(1-δ)
    have h1δ : 0 < 1 - δ := by linarith
    have hy0' : 0 ≤ y := by linarith
    have hpi : (Nat.primeCounting N : ℝ) * Real.log x * (1 - δ) ≤
        y * Real.log x * (1 - δ) + (1 + δ) * x := by nlinarith
    have hpi2 : (Nat.primeCounting N : ℝ) * Real.log x ≤ (1 + ε) * x := by
      have hyl : y * Real.log x * (1 - δ) ≤ δ * x := by
        have : y * Real.log x * (1 - δ) ≤ y * Real.log x :=
          mul_le_of_le_one_right (mul_nonneg hy0' hlx.le) (by linarith)
        linarith
      have : (Nat.primeCounting N : ℝ) * Real.log x * (1 - δ) ≤ (1 + 2 * δ) * x := by linarith
      have hkey : (1 + 2 * δ) ≤ (1 + ε) * (1 - δ) := by
        nlinarith [mul_le_mul_of_nonneg_left hδ1 hε.le]
      have hpi0 : 0 ≤ (Nat.primeCounting N : ℝ) * Real.log x := mul_nonneg (Nat.cast_nonneg _) hlx.le
      by_contra hc
      push_neg at hc
      nlinarith
    have : (Nat.primeCounting N : ℝ) ≤ (1 + ε) * (x / Real.log x) := by
      rw [mul_div_assoc', le_div_iff₀ hlx]; exact hpi2
    linarith

/-! ### Lemma 14 from the prime number theorem -/

/-- `[log₂ N] - [log₂ m] - 1 ≤ [log₂ (N / m)]`, truncated subtraction. -/
theorem log_div_ge (N m : ℕ) (hm : 0 < m) :
    Nat.log 2 N - (Nat.log 2 m + 1) ≤ Nat.log 2 (N / m) := by
  set a := Nat.log 2 m
  set L := Nat.log 2 N
  rcases Nat.eq_zero_or_pos (L - (a + 1)) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  apply Nat.le_log_of_pow_le one_lt_two
  rw [Nat.le_div_iff_mul_le hm]
  have hma : m < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self one_lt_two m
  have hN0 : N ≠ 0 := by
    intro h; simp [L, h] at hpos
  calc 2 ^ (L - (a + 1)) * m ≤ 2 ^ (L - (a + 1)) * 2 ^ (a + 1) :=
        Nat.mul_le_mul_left _ hma.le
    _ = 2 ^ L := by rw [← pow_add]; congr 1; omega
    _ ≤ N := Nat.pow_log_le_self 2 hN0

/-- `PiAsymp → Lemma14`: Gallagher's proof of Lemma 14, p.139, from display (8). -/
theorem lemma14_of_pi (hpi : PiAsymp) : Lemma14 := by
  intro k hk ε hε
  set η := min (ε / 4) (1 / 2) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hη1 : 0 ≤ 1 - η := by have : η ≤ 1 / 2 := min_le_right _ _; linarith
  obtain ⟨t0, ht0⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  set t := t0 + 1 with htdef
  have ht : (1 / 2 : ℝ) ^ t ≤ η := by
    have : (1 / 2 : ℝ) ^ t ≤ (1 / 2) ^ t0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  set c := Nat.log 2 (2 ^ t * k) + 1 with hcdef
  obtain ⟨N0, hN0⟩ := hpi η hη
  set M := c + ⌈(k : ℝ) * c / η⌉₊ + 1 with hMdef
  refine ⟨max (2 * (N0 + 2)) (2 ^ M), fun N hN => ?_⟩
  set L := Nat.log 2 N with hLdef
  have hLM : M ≤ L := Nat.le_log_of_pow_le one_lt_two (le_of_max_le_right hN)
  have hN2 : 2 * (N0 + 2) ≤ N := le_of_max_le_left hN
  set x := N / 2 ^ t with hxdef
  have hxN : x ≤ N / 2 := Nat.div_le_div_left
    (by calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
  have hNx : N0 + 2 ≤ N - x := by omega
  set S := ∑ n ∈ range (N + 1), (rk k N n : ℝ) with hSdef
  have hlow := sum_rk_ge k N x (Nat.div_le_self _ _)
  have hup := sum_rk_le k N
  have hlogx : L - c ≤ Nat.log 2 (x / k) := by
    rw [hxdef, Nat.div_div_eq_div_mul]
    exact log_div_ge N (2 ^ t * k) (by positivity)
  -- real facts
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hN0r : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hcL : c ≤ L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hkc : (k : ℝ) * c / η ≤ L := by
    have h1 := Nat.le_ceil ((k : ℝ) * c / η)
    have h2 : (⌈(k : ℝ) * c / η⌉₊ : ℝ) ≤ L := by exact_mod_cast (show ⌈(k : ℝ) * c / η⌉₊ ≤ L by omega)
    linarith
  set A := (N : ℝ) * (L : ℝ) ^ k / Real.log N with hAdef
  have hA : 0 < A := div_pos (by positivity) hlogN
  -- upper
  have hpiN := hN0 N (by omega)
  rw [abs_le] at hpiN
  have hU : S ≤ (1 + η) * A := by
    have : (Nat.primeCounting N : ℝ) ≤ (1 + η) * (N / Real.log N) := by linarith
    calc S ≤ (Nat.primeCounting N : ℝ) * (L : ℝ) ^ k := hup
      _ ≤ (1 + η) * (N / Real.log N) * (L : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (1 + η) * A := by rw [hAdef]; ring
  -- lower, the prime factor
  have hpix := hN0 (N - x) (by omega)
  rw [abs_le] at hpix
  have hNxr : ((N - x : ℕ) : ℝ) = N - x := by
    rw [Nat.cast_sub (by omega)]
  have hxr : (x : ℝ) ≤ η * N := by
    calc (x : ℝ) ≤ (N : ℝ) / (2 ^ t : ℕ) := Nat.cast_div_le
      _ = (1 / 2 : ℝ) ^ t * N := by push_cast; rw [one_div_pow]; ring
      _ ≤ η * N := mul_le_mul_of_nonneg_right ht hN0r.le
  have hNx2 : (2 : ℝ) ≤ ((N - x : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ N - x by omega)
  have hlogNx : 0 < Real.log ((N - x : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogNx' : Real.log ((N - x : ℕ) : ℝ) ≤ Real.log N :=
    Real.log_le_log (by linarith) (by exact_mod_cast (Nat.sub_le N x))
  have hP : (1 - η) ^ 2 * (N / Real.log N) ≤ (Nat.primeCounting (N - x) : ℝ) := by
    have e1 : (1 - η) * N ≤ ((N - x : ℕ) : ℝ) := by rw [hNxr]; linarith
    have e2 : ((N - x : ℕ) : ℝ) / Real.log N ≤ ((N - x : ℕ) : ℝ) / Real.log ((N - x : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hlogNx hlogNx'
    have e3 : (1 - η) * (((N - x : ℕ) : ℝ) / Real.log ((N - x : ℕ) : ℝ)) ≤
        (Nat.primeCounting (N - x) : ℝ) := by linarith
    calc (1 - η) ^ 2 * (N / Real.log N) = (1 - η) * ((1 - η) * N / Real.log N) := by ring
      _ ≤ (1 - η) * (((N - x : ℕ) : ℝ) / Real.log N) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e1 hlogN.le) hη1
      _ ≤ (1 - η) * (((N - x : ℕ) : ℝ) / Real.log ((N - x : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left e2 hη1
      _ ≤ _ := e3
  -- lower, the power of 2 factor
  have hQ : (1 - η) * (L : ℝ) ^ k ≤ (Nat.log 2 (x / k) : ℝ) ^ k := by
    have h1 : ((L - c : ℕ) : ℝ) = (L : ℝ) - c := by rw [Nat.cast_sub hcL]
    have h2 : ((L - c : ℕ) : ℝ) ^ k ≤ (Nat.log 2 (x / k) : ℝ) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hlogx) k
    have hcLr : (c : ℝ) ≤ L := by exact_mod_cast hcL
    have h3 : (L : ℝ) - c = L * (1 + (-(c / L))) := by field_simp; ring
    have hb : (-2 : ℝ) ≤ -(c / L) := by
      have : (c : ℝ) / L ≤ 1 := (div_le_one hLr).mpr hcLr
      linarith
    have h4 := one_add_mul_le_pow hb k
    have h5 : (k : ℝ) * (c / L) ≤ η := by
      rw [div_le_iff₀ hη] at hkc
      rw [mul_div_assoc', div_le_iff₀ hLr]; linarith
    have h6 : 1 - η ≤ (1 + (-(c / L))) ^ k := by linarith
    calc (1 - η) * (L : ℝ) ^ k ≤ (1 + (-(c / L))) ^ k * (L : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = ((L - c : ℕ) : ℝ) ^ k := by rw [h1, h3, mul_pow]; ring
      _ ≤ _ := h2
  have hL : (1 - η) ^ 3 * A ≤ S := by
    calc (1 - η) ^ 3 * A = ((1 - η) ^ 2 * (N / Real.log N)) * ((1 - η) * (L : ℝ) ^ k) := by
          rw [hAdef]; ring
      _ ≤ (Nat.primeCounting (N - x) : ℝ) * (Nat.log 2 (x / k) : ℝ) ^ k :=
          mul_le_mul hP hQ (mul_nonneg hη1 (by positivity)) (Nat.cast_nonneg _)
      _ ≤ S := hlow
  have hB : 1 - 3 * η ≤ (1 - η) ^ 3 := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -η by linarith) 3
    push_cast at this; linarith
  have h3η : (1 - ε) * A ≤ (1 - η) ^ 3 * A := mul_le_mul_of_nonneg_right (by linarith) hA.le
  have h3η' : (1 + η) * A ≤ (1 + ε) * A := mul_le_mul_of_nonneg_right (by linarith) hA.le
  rw [abs_le]
  constructor <;> nlinarith

/-- **Gallagher 1975, Lemma 14**, display (7), p.139: PROVED, unconditional, from the lab's
prime number theorem port. -/
theorem lemma14 : Lemma14 := lemma14_of_pi piAsymp

/-- **Gallagher 1975, Theorem 2**, display (4), p.125, CONDITIONAL ON `Theorem1` alone:
for `k ≥ 2` and even `N ≥ N_k`, `r''_k(N) = (2 N L^k / log² N)(1 + O(log² k / k))`, absolute `O`. -/
theorem theorem2_of_theorem1 (h1 : Theorem1) :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(rpp k N : ℝ) - 2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) :=
  theorem2 h1 lemma14

/-- Vacuity: `Σ_{n ≤ 8} r'_1(n)` is positive; `r'_1(5) > 0` by `5 = 3 + 2`. -/
theorem sum_rk_pos_example : 0 < ∑ n ∈ range 9, (rk 1 8 n : ℝ) := by
  have h : 0 < rk 1 8 5 := (rk_pos_iff (by norm_num)).mpr
    ⟨3, Nat.prime_three, fun _ => 1, fun _ => le_rfl, by simp⟩
  have h5 : (5 : ℕ) ∈ range 9 := by simp
  calc (0 : ℝ) < rk 1 8 5 := by exact_mod_cast h
    _ ≤ ∑ n ∈ range 9, (rk 1 8 n : ℝ) :=
      single_le_sum (f := fun n => (rk 1 8 n : ℝ)) (fun _ _ => Nat.cast_nonneg _) h5

end LeanLab.Linnik.U7201

