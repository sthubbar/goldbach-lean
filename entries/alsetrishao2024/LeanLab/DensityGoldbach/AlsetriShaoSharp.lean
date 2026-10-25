module

public import LeanLab.DensityGoldbach.PrimesAP

/-! AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5908, paper P0047.
Alsetri and Shao, arXiv 2405.18576, Remark 1.3: the constant `1/2` in their Theorem 1.2 is sharp.
Their construction takes `A` to be the primes in `[1, N1] ∪ [αN1, N2] ∪ [αN2, N3] ∪ ...` with the
`N_k` growing rapidly and `α > 2`. Then every reduced residue class keeps relative lower density
at least about `1/α` inside `A`, while `A + A` misses every even integer in `(2 N_k, α N_k)`, a
positive proportion of the even integers up to `α N_k`.
Here, for `c < 1/2`, we take `α = (2m+1)/m` with `m` so large that `c < m/(2m+1)`, and
`N_k = m T_k`, `α N_k = (2m+1) T_k`, `T_k = 2 S_k`, `S_0 = 2`, `S_(k+1) = 2 (2m+1)^2 S_k^2`,
so that `(α N_k)^2 ≤ N_(k+1)`. The removed primes are those in the open intervals
`(m T_k, (2m+1) T_k)`.
The density half uses `π(x; W, b) log x ~ x/φ(W)`, from the `k = 0` case of `ap_sum_pow`, which
rests on the lab's Siegel-Walfisz theorem. No cited input beyond what that proves.
Binary Goldbach is OPEN. -/

@[expose] public section

open Real Finset Filter

namespace LeanLab.DensityGoldbach.AlsetriShaoSharp

/-- Primes up to `y` in the class `b` mod `W`. -/
def piW (W b y : ℕ) : ℕ :=
  ((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p % W = b % W)).card

/-! ### Analytic input -/

/-- Splitting any finite set of naturals at `N^(1-δ)`. -/
lemma card_log_split (P : Finset ℕ) (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : δ < 1) :
    (1 - δ) * Real.log N * (P.card : ℝ) ≤
      (1 - δ) * Real.log N * ((N : ℝ) ^ (1 - δ) + 1) + ∑ p ∈ P, Real.log p := by
  set t : ℝ := (N : ℝ) ^ (1 - δ) with ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have hlogt : Real.log t = (1 - δ) * Real.log N := Real.log_rpow hN0 _
  have h1δ : 0 < 1 - δ := by linarith
  set Ps := P.filter (fun p : ℕ => (p : ℝ) < t)
  set Pb := P.filter (fun p : ℕ => ¬ (p : ℝ) < t)
  have hcard : (P.card : ℝ) = Ps.card + Pb.card := by
    rw [← card_filter_add_card_filter_not (s := P) (fun p : ℕ => (p : ℝ) < t)]; push_cast; rfl
  have hsmall : (Ps.card : ℝ) ≤ t + 1 := by
    have h2 : Ps.card ≤ ⌈t⌉₊ := by
      calc Ps.card ≤ (range ⌈t⌉₊).card := by
            refine card_le_card fun p hp => ?_
            exact mem_range.2 (Nat.lt_ceil.2 (mem_filter.1 hp).2)
        _ = ⌈t⌉₊ := card_range _
    exact le_trans (by exact_mod_cast h2) (Nat.ceil_lt_add_one ht0.le).le
  have hbig : (1 - δ) * Real.log N * Pb.card ≤ ∑ p ∈ P, Real.log p := by
    have e : (1 - δ) * Real.log N * Pb.card = ∑ _p ∈ Pb, (1 - δ) * Real.log N := by
      rw [sum_const, nsmul_eq_mul]; ring
    rw [e]
    refine le_trans (sum_le_sum fun p hp => ?_) (sum_le_sum_of_subset_of_nonneg
      (filter_subset _ P) fun p _ _ => Real.log_natCast_nonneg p)
    have htp : t ≤ p := not_lt.1 (mem_filter.1 hp).2
    exact hlogt ▸ Real.log_le_log ht0 htp
  have hA : 0 ≤ (1 - δ) * Real.log N := mul_nonneg h1δ.le hL
  have := mul_le_mul_of_nonneg_left hsmall hA
  rw [hcard]
  nlinarith

/-- Lower bound: `φ(W) π(y; W, b) log y ≥ (1 - ε) y` for large `y`. -/
lemma piW_lower (W b : ℕ) (hW : 1 ≤ W) (hb : Nat.Coprime b W) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ y : ℕ, N₀ ≤ y →
      (1 - ε) * (y : ℝ) ≤ (Nat.totient W : ℝ) * Real.log y * (piW W b y : ℝ) := by
  have hφ : (1 : ℝ) ≤ Nat.totient W := by exact_mod_cast Nat.totient_pos.2 (by omega)
  set φ : ℝ := (Nat.totient W : ℝ) with hφdef
  set ε₁ : ℝ := ε / φ with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 W hW ε₁ hε₁
  refine ⟨n₀, fun y hy => ?_⟩
  have hS := hn₀ y hy b hb
  simp only [pow_zero, mul_one, zero_add, pow_one, Nat.cast_zero, one_mul] at hS
  rw [← hφdef, abs_le] at hS
  have hlow := theta_ap_le y W b
  unfold piW
  set θ := ∑ p ∈ (range (y + 1)).filter (fun p => p.Prime ∧ p % W = b % W), Real.log p
  set f : ℝ := (((range (y + 1)).filter (fun p => p.Prime ∧ p % W = b % W)).card : ℝ)
  have h1 : (y : ℝ) / φ - ε₁ * y ≤ f * Real.log y := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ φ)
  have e : φ * ((y : ℝ) / φ - ε₁ * y) = (1 - ε) * y := by
    rw [hε₁def]; field_simp
  nlinarith

/-- Upper bound: `φ(W) π(x; W, b) log x ≤ (1 + ε) x` for large `x`. -/
lemma piW_upper (W b : ℕ) (hW : 1 ≤ W) (hb : Nat.Coprime b W) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
      (Nat.totient W : ℝ) * Real.log x * (piW W b x : ℝ) ≤ (1 + ε) * (x : ℝ) := by
  have hφ : (1 : ℝ) ≤ Nat.totient W := by exact_mod_cast Nat.totient_pos.2 (by omega)
  set φ : ℝ := (Nat.totient W : ℝ) with hφdef
  set ε₁ : ℝ := ε / (8 * φ) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 W hW ε₁ hε₁
  have hev := (LeanLab.HardyLittlewood1923.eventually_log_le ε₁ δ hε₁ hδ).and
    ((LeanLab.HardyLittlewood1923.eventually_log_le ε₁ 1 hε₁ one_pos).and (eventually_ge_atTop 2))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hev
  refine ⟨max n₀ n₂, fun x hx => ?_⟩
  obtain ⟨hl1, hl2, hx2⟩ := hn₂ x (le_of_max_le_right hx)
  have hS := hn₀ x (le_of_max_le_left hx) b hb
  simp only [pow_zero, mul_one, zero_add, pow_one, Nat.cast_zero, one_mul] at hS
  rw [← hφdef, abs_le] at hS
  rw [Real.rpow_one] at hl2
  unfold piW
  set n : ℝ := (x : ℝ) with hndef
  have hn1 : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast (show 1 ≤ x by omega)
  have hn0 : 0 < n := by linarith
  set L := Real.log n with hLdef
  have hL : 0 < L := Real.log_pos (by rw [hndef]; exact_mod_cast (show 1 < x by omega))
  have hsplit := card_log_split ((range (x + 1)).filter (fun p => p.Prime ∧ p % W = b % W)) x
    (by omega) δ (by rw [hδdef]; linarith)
  rw [← hndef, ← hLdef] at hsplit
  set θ := ∑ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ p % W = b % W), Real.log p
  set f : ℝ := (((range (x + 1)).filter (fun p => p.Prime ∧ p % W = b % W)).card : ℝ)
  set t := n ^ (1 - δ) with htdef
  have htn : t * n ^ δ = n := by
    rw [htdef, ← Real.rpow_add hn0]; simp
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0.le _
  have hLt : L * t ≤ ε₁ * n := by
    have := mul_le_mul_of_nonneg_left hl1 ht0
    nlinarith
  have h1δ : 0 < 1 - δ := by rw [hδdef]; linarith
  have hθ : θ ≤ n / φ + ε₁ * n := by linarith
  have hup : (1 - δ) * L * f ≤ n / φ + 3 * ε₁ * n := by
    have : (1 - δ) * L * (t + 1) ≤ L * (t + 1) := by
      have : 0 ≤ L * (t + 1) := by positivity
      nlinarith
    nlinarith
  have hup2 : (1 - δ) * (φ * L * f) ≤ (1 + 3 * ε / 8) * n := by
    have := mul_le_mul_of_nonneg_left hup (by linarith : (0 : ℝ) ≤ φ)
    have e : φ * (n / φ + 3 * ε₁ * n) = (1 + 3 * ε / 8) * n := by
      rw [hε₁def]; field_simp
    nlinarith
  have hZ : 0 ≤ φ * L * f := by positivity
  by_contra hcon
  push Not at hcon
  have : (1 + ε) * n * (1 - δ) < (φ * L * f) * (1 - δ) := mul_lt_mul_of_pos_right hcon h1δ
  rw [hδdef] at this hup2
  have hq : (1 + 3 * ε / 8) * n ≤ (1 + ε) * n * (1 - ε / 4) := by
    nlinarith [mul_nonneg (mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 1 - ε)) hn0.le]
  linarith

/-- Ratio form: `(1 - η) y π(x) ≤ x π(y)` for `N₀ ≤ y ≤ x`. -/
lemma piW_ratio (W b : ℕ) (hW : 1 ≤ W) (hb : Nat.Coprime b W) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ y x : ℕ, N₀ ≤ y → y ≤ x →
      (1 - η) * (y : ℝ) * (piW W b x : ℝ) ≤ (x : ℝ) * (piW W b y : ℝ) := by
  have hφ : (1 : ℝ) ≤ Nat.totient W := by exact_mod_cast Nat.totient_pos.2 (by omega)
  set φ : ℝ := (Nat.totient W : ℝ) with hφdef
  set ε : ℝ := min (η / 2) 1 with hεdef
  have hε : 0 < ε := lt_min (by positivity) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεη : ε ≤ η / 2 := min_le_left _ _
  obtain ⟨n₁, hn₁⟩ := piW_lower W b hW hb ε hε
  obtain ⟨n₂, hn₂⟩ := piW_upper W b hW hb ε hε hε1
  refine ⟨max (max n₁ n₂) 2, fun y x hy hyx => ?_⟩
  have hy1 : n₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy2 : n₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy3 : 2 ≤ y := le_trans (le_max_right _ _) hy
  have hlo := hn₁ y hy1
  have hup := hn₂ x (le_trans hy2 hyx)
  rw [← hφdef] at hlo hup
  set fy : ℝ := (piW W b y : ℝ)
  set fx : ℝ := (piW W b x : ℝ)
  have hfx : 0 ≤ fx := Nat.cast_nonneg _
  have hfy : 0 ≤ fy := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hyxr : (y : ℝ) ≤ x := by exact_mod_cast hyx
  have hLy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hLyx : Real.log y ≤ Real.log x := Real.log_le_log hy0 hyxr
  by_cases hη1 : 1 ≤ η
  · have : (1 - η) * (y : ℝ) * fx ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hy0.le) hfx
    exact le_trans this (mul_nonneg (by linarith) hfy)
  push Not at hη1
  have hP : 0 < φ * Real.log y := by positivity
  -- y fx φ Ly ≤ (1 + ε) x y
  have a1 : (y : ℝ) * fx * (φ * Real.log y) ≤ (1 + ε) * x * y := by
    have : φ * Real.log y * fx ≤ φ * Real.log x * fx :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLyx (by linarith)) hfx
    nlinarith
  have a2 : (1 - η) * (1 + ε) ≤ 1 - ε := by nlinarith
  have a3 : (1 - η) * ((y : ℝ) * fx * (φ * Real.log y)) ≤ (1 - ε) * x * y := by
    have := mul_le_mul_of_nonneg_left a1 (by linarith : (0 : ℝ) ≤ 1 - η)
    have h4 : (1 - η) * (1 + ε) * ((x : ℝ) * y) ≤ (1 - ε) * (x * y) :=
      mul_le_mul_of_nonneg_right a2 (by positivity)
    nlinarith
  have a4 : (1 - ε) * (x : ℝ) * y ≤ x * fy * (φ * Real.log y) := by
    have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ x)
    nlinarith
  have : (1 - η) * (y : ℝ) * fx * (φ * Real.log y) ≤ x * fy * (φ * Real.log y) := by nlinarith
  exact le_of_mul_le_mul_right this hP

/-- Small arguments: `π(z) ≤ η π(y)` when `z^2 ≤ y` and `y` is large. -/
lemma piW_small (W b : ℕ) (hW : 1 ≤ W) (hb : Nat.Coprime b W) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ y z : ℕ, N₀ ≤ y → 1 ≤ z → z ^ 2 ≤ y →
      (piW W b z : ℝ) ≤ η * (piW W b y : ℝ) := by
  have hφ : (1 : ℝ) ≤ Nat.totient W := by exact_mod_cast Nat.totient_pos.2 (by omega)
  set φ : ℝ := (Nat.totient W : ℝ) with hφdef
  set ε₂ : ℝ := η / (4 * φ) with hε₂def
  have hε₂ : 0 < ε₂ := by positivity
  obtain ⟨n₁, hn₁⟩ := piW_lower W b hW hb (1 / 2) (by norm_num)
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1
    ((LeanLab.HardyLittlewood1923.eventually_log_le ε₂ (1 / 2) hε₂ (by norm_num)).and
      (eventually_ge_atTop 2))
  refine ⟨max n₁ n₂, fun y z hy hz hzy => ?_⟩
  have hlo := hn₁ y (le_of_max_le_left hy)
  obtain ⟨hlog, hy2⟩ := hn₂ y (le_of_max_le_right hy)
  rw [← hφdef] at hlo
  set fy : ℝ := (piW W b y : ℝ)
  set fz : ℝ := (piW W b z : ℝ)
  have hfz : fz ≤ z + 1 := by
    have : piW W b z ≤ z + 1 := by
      unfold piW
      exact le_trans (card_filter_le _ _) (card_range _).le
    have h' : (piW W b z : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast this
    exact h'
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hLy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hsq : (z : ℝ) ≤ (y : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hzy
  have hs0 : 0 ≤ (y : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy0.le _
  have hss : (y : ℝ) ^ ((1 : ℝ) / 2) * (y : ℝ) ^ ((1 : ℝ) / 2) = y := by
    rw [← Real.rpow_add hy0]; norm_num
  have hzL : (z : ℝ) * Real.log y ≤ ε₂ * y := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ z)
    have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ ε₂ * (y : ℝ) ^ ((1 : ℝ) / 2))
    nlinarith
  have hP : 0 < φ * Real.log y := by positivity
  have k1 : fz * (φ * Real.log y) ≤ 2 * z * (φ * Real.log y) :=
    mul_le_mul_of_nonneg_right (by linarith) hP.le
  have k2 : 2 * (z : ℝ) * (φ * Real.log y) = 2 * φ * (z * Real.log y) := by ring
  have k3 : 2 * φ * ((z : ℝ) * Real.log y) ≤ 2 * φ * (ε₂ * y) :=
    mul_le_mul_of_nonneg_left hzL (by linarith)
  have k4 : 2 * φ * (ε₂ * (y : ℝ)) = η / 2 * y := by rw [hε₂def]; field_simp; ring
  have k5 : η / 2 * (y : ℝ) ≤ η * fy * (φ * Real.log y) := by
    have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ η)
    nlinarith
  have : fz * (φ * Real.log y) ≤ η * fy * (φ * Real.log y) := by linarith
  exact le_of_mul_le_mul_right this hP

/-! ### The construction -/

/-- `S_0 = 2`, `S_(k+1) = 2 (2m+1)^2 S_k^2`. -/
def S (m : ℕ) : ℕ → ℕ
  | 0 => 2
  | k + 1 => 2 * (2 * m + 1) ^ 2 * (S m k) ^ 2

/-- `N_k = m T_k` with `T_k = 2 S_k`. -/
def lo (m k : ℕ) : ℕ := m * (2 * S m k)

/-- `α N_k = (2m+1) T_k`. -/
def hi (m k : ℕ) : ℕ := (2 * m + 1) * (2 * S m k)

/-- The primes outside every open interval `(N_k, α N_k)`. -/
def Aset (m : ℕ) : Set ℕ := {p | p.Prime ∧ ∀ j, ¬ (lo m j < p ∧ p < hi m j)}

lemma S_two_le (m k : ℕ) : 2 ≤ S m k := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    simp only [S]
    have : 1 ≤ (2 * m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith

lemma S_lt_succ (m k : ℕ) : S m k < S m (k + 1) := by
  have h := S_two_le m k
  simp only [S]
  have : 1 ≤ (2 * m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

lemma S_strictMono (m : ℕ) : StrictMono (S m) := strictMono_nat_of_lt_succ (S_lt_succ m)

lemma lo_mono (m : ℕ) {j j' : ℕ} (h : j ≤ j') : lo m j ≤ lo m j' := by
  unfold lo
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((S_strictMono m).monotone h))

lemma hi_mono (m : ℕ) {j j' : ℕ} (h : j ≤ j') : hi m j ≤ hi m j' := by
  unfold hi
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((S_strictMono m).monotone h))

lemma le_lo (m k : ℕ) (hm : 1 ≤ m) : k ≤ lo m k := by
  have h1 : k ≤ S m k := (S_strictMono m).id_le k
  unfold lo
  nlinarith

lemma lo_le_hi (m k : ℕ) : lo m k ≤ hi m k := by
  unfold lo hi
  exact Nat.mul_le_mul_right _ (by omega)

lemma hi_eq (m k : ℕ) : hi m k = 2 * lo m k + 2 * S m k := by
  unfold hi lo; ring

lemma hi_sq_le (m k : ℕ) (hm : 1 ≤ m) : hi m k ^ 2 ≤ lo m (k + 1) := by
  unfold hi lo
  simp only [S]
  have e1 : ((2 * m + 1) * (2 * S m k)) ^ 2 = 4 * ((2 * m + 1) ^ 2 * S m k ^ 2) := by ring
  have e2 : m * (2 * (2 * (2 * m + 1) ^ 2 * S m k ^ 2)) = m * (4 * ((2 * m + 1) ^ 2 * S m k ^ 2)) := by
    ring
  rw [e1, e2]
  exact Nat.le_mul_of_pos_left _ (by omega)

lemma mem_Aset (m p : ℕ) (hp : p.Prime) (h : ∀ j, hi m j ≤ p ∨ p ≤ lo m j) : p ∈ Aset m :=
  ⟨hp, fun j hj => by rcases h j with h | h <;> omega⟩

/-! ### Counting -/

lemma card_split (P : ℕ → Prop) [DecidablePred P] {y x : ℕ} (h : y ≤ x) :
    ((range (x + 1)).filter P).card =
      ((range (y + 1)).filter P).card + ((Ico (y + 1) (x + 1)).filter P).card := by
  rw [← card_union_of_disjoint, ← filter_union, range_eq_Ico, range_eq_Ico,
    Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)]
  rw [range_eq_Ico]
  exact disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)

lemma piW_mono (W b : ℕ) {y x : ℕ} (h : y ≤ x) : piW W b y ≤ piW W b x := by
  unfold piW; rw [card_split _ h]; omega

/-- The combinatorial core: for `N_k ≤ N < N_(k+1)`, the primes of the class in
`(α N_(k-1), N_k]` and in `(min N (α N_k), N]` all lie in `A`. -/
lemma count_lower (m : ℕ) (hm : 1 ≤ m) (W b k N : ℕ) (hk : 1 ≤ k) (hkN : lo m k ≤ N)
    (hNk : N < lo m (k + 1)) [DecidablePred fun p => p ∈ Aset m ∧ p % W = b % W] :
    piW W b (lo m k) + piW W b N ≤ piW W b (hi m (k - 1)) + piW W b (min N (hi m k)) +
      ((range (N + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W)).card := by
  set a := lo m k with ha
  set b' := hi m (k - 1) with hb'
  set mn := min N (hi m k) with hmn
  have hb'a : b' ≤ a := by
    have h1 := hi_sq_le m (k - 1) hm
    rw [show k - 1 + 1 = k by omega] at h1
    exact le_trans (by nlinarith : b' ≤ b' ^ 2) h1
  have hamn : a ≤ mn := le_min hkN (lo_le_hi m k)
  have hmnN : mn ≤ N := min_le_left _ _
  unfold piW
  rw [card_split _ hb'a, card_split _ hmnN]
  have e1 : (Ico (b' + 1) (a + 1)).filter (fun p => p.Prime ∧ p % W = b % W) = (Ico (b' + 1) (a + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W) := by
    refine filter_congr fun p hp => ?_
    rw [mem_Ico] at hp
    refine ⟨fun h => ⟨mem_Aset m p h.1 fun j => ?_, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rcases le_or_gt j (k - 1) with hj | hj
    · left; have := hi_mono m hj; omega
    · right; have := lo_mono m (show k ≤ j by omega); omega
  have e2 : (Ico (mn + 1) (N + 1)).filter (fun p => p.Prime ∧ p % W = b % W) = (Ico (mn + 1) (N + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W) := by
    refine filter_congr fun p hp => ?_
    rw [mem_Ico] at hp
    have hpk : hi m k < p := by
      rcases le_total N (hi m k) with h | h
      · rw [hmn, min_eq_left h] at hp; omega
      · rw [hmn, min_eq_right h] at hp; omega
    refine ⟨fun h => ⟨mem_Aset m p h.1 fun j => ?_, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rcases le_or_gt j k with hj | hj
    · left; have := hi_mono m hj; omega
    · right; have := lo_mono m (show k + 1 ≤ j by omega); omega
  have hsub : (Ico (b' + 1) (a + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W) ∪ (Ico (mn + 1) (N + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W) ⊆
      (range (N + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W) := by
    intro p hp
    rw [mem_union, mem_filter, mem_filter, mem_Ico, mem_Ico] at hp
    rw [mem_filter, mem_range]
    rcases hp with hp | hp
    · exact ⟨by omega, hp.2⟩
    · exact ⟨by omega, hp.2⟩
  have hdisj : Disjoint ((Ico (b' + 1) (a + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W)) ((Ico (mn + 1) (N + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W)) := by
    rw [disjoint_left]
    intro p h1 h2
    rw [mem_filter, mem_Ico] at h1 h2
    omega
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at this
  rw [e1, e2]
  omega

/-! ### The two halves -/

/-- Density half: in every reduced class `A` keeps relative density at least about `m/(2m+1)`. -/
theorem density_half (m : ℕ) (hm : 1 ≤ m) (W b : ℕ) (hW : 1 ≤ W) (hb : Nat.Coprime b W)
    (η : ℝ) (hη : 0 < η) [DecidablePred fun p => p ∈ Aset m ∧ p % W = b % W] :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((1 - η) * ((m : ℝ) / (2 * m + 1)) - η) * (piW W b N : ℝ) ≤
        (((range (N + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W)).card : ℝ) := by
  obtain ⟨n₁, hn₁⟩ := piW_ratio W b hW hb η hη
  obtain ⟨n₂, hn₂⟩ := piW_small W b hW hb η hη
  set K := max n₁ n₂ + 1 with hK
  refine ⟨lo m K, fun N hN => ?_⟩
  have hex : ∃ j, N < lo m j := ⟨N + 1, by have := le_lo m (N + 1) hm; omega⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀spec : N < lo m j₀ := Nat.find_spec hex
  have hKj : K < j₀ := by
    by_contra hcon
    push Not at hcon
    have := lo_mono m hcon
    omega
  set k := j₀ - 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkK : K ≤ k := by omega
  have hkN : lo m k ≤ N := by
    have := Nat.find_min hex (show k < j₀ by omega)
    omega
  have hNk : N < lo m (k + 1) := by rw [show k + 1 = j₀ by omega]; exact hj₀spec
  have hc := count_lower m hm W b k N hk1 hkN hNk
  set a := lo m k with ha
  have haK : K ≤ a := le_trans hkK (le_lo m k hm)
  have hmn1 : a ≤ min N (hi m k) := le_min hkN (lo_le_hi m k)
  -- ratio at y = a, x = min N (hi m k)
  have hr := hn₁ a (min N (hi m k)) (by omega) hmn1
  -- small at y = a, z = hi m (k - 1)
  have hz1 : 1 ≤ hi m (k - 1) := by
    have := S_two_le m (k - 1); unfold hi; nlinarith
  have hzsq : hi m (k - 1) ^ 2 ≤ a := by
    have h1 := hi_sq_le m (k - 1) hm
    rwa [show k - 1 + 1 = k by omega] at h1
  have hs := hn₂ a (hi m (k - 1)) (by omega) hz1 hzsq
  have hmonoa : piW W b a ≤ piW W b N := piW_mono W b hkN
  have hmonom : piW W b (min N (hi m k)) ≤ piW W b N := piW_mono W b (min_le_left _ _)
  set fa : ℝ := (piW W b a : ℝ)
  set fN : ℝ := (piW W b N : ℝ)
  set fz : ℝ := (piW W b (hi m (k - 1)) : ℝ)
  set fm : ℝ := (piW W b (min N (hi m k)) : ℝ)
  set cA : ℝ := (((range (N + 1)).filter (fun p => p ∈ Aset m ∧ p % W = b % W)).card : ℝ)
  have hcR : fa + fN ≤ fz + fm + cA := by
    simp only [fa, fN, fz, fm, cA]; exact_mod_cast hc
  have hmaR : fa ≤ fN := by simp only [fa, fN]; exact_mod_cast hmonoa
  have hmmR : fm ≤ fN := by simp only [fm, fN]; exact_mod_cast hmonom
  have hfm0 : 0 ≤ fm := Nat.cast_nonneg _
  -- fa ≥ (1 - η) r fm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set T : ℝ := ((2 * S m k : ℕ) : ℝ) with hT
  have hT0 : 0 < T := by
    rw [hT]; have := S_two_le m k; exact_mod_cast (show 0 < 2 * S m k by omega)
  have haT : (a : ℝ) = m * T := by rw [ha, hT]; unfold lo; push_cast; ring
  have hhiT : ((hi m k : ℕ) : ℝ) = (2 * m + 1) * T := by rw [hT]; unfold hi; push_cast; ring
  have hxle : ((min N (hi m k) : ℕ) : ℝ) ≤ (2 * m + 1) * T := by
    rw [← hhiT]; exact_mod_cast min_le_right _ _
  have hfa0 : 0 ≤ fa := Nat.cast_nonneg _
  have hr2 : (1 - η) * (m * T) * fm ≤ (2 * m + 1) * T * fa := by
    rw [← haT]
    exact le_trans hr (mul_le_mul_of_nonneg_right hxle hfa0)
  set r : ℝ := (m : ℝ) / (2 * m + 1) with hrdef
  have hq : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hr3 : (1 - η) * r * fm ≤ fa := by
    have e : (1 - η) * (m * T) * fm = ((1 - η) * r * fm) * ((2 * m + 1) * T) := by
      rw [hrdef]; field_simp
    have e2 : (2 * m + 1) * T * fa = fa * ((2 * m + 1) * T) := by ring
    rw [e, e2] at hr2
    exact le_of_mul_le_mul_right hr2 (by positivity)
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hq]; linarith
  have hθ1 : (1 - η) * r ≤ 1 := by
    have : 0 ≤ r := by positivity
    nlinarith
  have hs2 : fz ≤ η * fN := le_trans hs (mul_le_mul_of_nonneg_left hmaR hη.le)
  have hk : 0 ≤ (1 - (1 - η) * r) * (fN - fm) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Exception half: no even `n` with `2 N_k < n < α N_k` is a sum of two elements of `A`. -/
lemma exc_card (m k : ℕ) [DecidablePred fun n => Even n ∧ ¬ ∃ p ∈ Aset m, ∃ q ∈ Aset m, n = p + q] :
    S m k - 1 ≤ ((range (hi m k + 1)).filter
      (fun n => Even n ∧ ¬ ∃ p ∈ Aset m, ∃ q ∈ Aset m, n = p + q)).card := by
  have hhi := hi_eq m k
  set a := lo m k
  set s := S m k
  have himg : (Ico 1 s).image (fun j => 2 * a + 2 * j) ⊆ (range (hi m k + 1)).filter
      (fun n => Even n ∧ ¬ ∃ p ∈ Aset m, ∃ q ∈ Aset m, n = p + q) := by
    intro n hn
    rw [mem_image] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    rw [mem_Ico] at hj
    rw [mem_filter, mem_range]
    refine ⟨by omega, ⟨a + j, by ring⟩, ?_⟩
    rintro ⟨p, hp, q, hq, hpq⟩
    have h1 := hp.2 k
    have h2 := hq.2 k
    have : p ≤ a := by by_contra h; exact h1 ⟨by omega, by omega⟩
    have : q ≤ a := by by_contra h; exact h2 ⟨by omega, by omega⟩
    omega
  have hinj : Set.InjOn (fun j => 2 * a + 2 * j) (Ico 1 s : Set ℕ) := by
    intro x _ y _ hxy; simp only at hxy; omega
  have := card_le_card himg
  rw [card_image_of_injOn hinj, Nat.card_Ico] at this
  exact this

/-! ### Remark 1.3 -/

open Classical in
/-- **Alsetri-Shao Remark 1.3.** The constant `1/2` in Theorem 1.2 is sharp: for every `c < 1/2`
there is a set `A` of primes with relative lower density above `c` in every reduced class, while
`A + A` misses a positive proportion of the even integers up to infinitely many `N`. -/
theorem remark1_3 : ∀ c : ℝ, c < 1 / 2 → ∃ A : Set ℕ, (∀ p ∈ A, p.Prime) ∧
    (∀ W b : ℕ, 1 ≤ W → Nat.Coprime b W → ∃ δ : ℝ, c < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      δ * (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % W = b % W)).card : ℝ) ≤
        (((Finset.range (N + 1)).filter (fun p => p ∈ A ∧ p % W = b % W)).card : ℝ)) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      κ * (N : ℝ) ≤ (((Finset.range (N + 1)).filter
        (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q)).card : ℝ)) := by
  intro c hc
  set d : ℝ := 1 / 2 - c with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  set m : ℕ := ⌈1 / d⌉₊ + 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmd : 1 ≤ d * m := by
    have h1 : 1 / d ≤ (⌈1 / d⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m : ℝ) = (⌈1 / d⌉₊ : ℝ) + 1 := by rw [hmdef]; push_cast; ring
    have h3 : d * (1 / d) = 1 := by field_simp
    nlinarith
  set r : ℝ := (m : ℝ) / (2 * m + 1) with hrdef
  have hq : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hcr : c < r := by
    rw [hrdef, lt_div_iff₀ hq]
    have : c = 1 / 2 - d := by rw [hddef]; ring
    rw [this]; nlinarith
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hq]; linarith
  set η : ℝ := (r - c) / 4 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  refine ⟨Aset m, fun p hp => hp.1, ?_, ?_⟩
  · intro W b hW hb
    obtain ⟨N₀, hN₀⟩ := density_half m hm W b hW hb η hη
    refine ⟨(1 - η) * r - η, ?_, N₀, fun N hN => ?_⟩
    · rw [hηdef]; nlinarith
    · exact hN₀ N hN
  · refine ⟨1 / (4 * (2 * m + 1)), by positivity, fun N₀ => ⟨hi m N₀, ?_, ?_⟩⟩
    · exact le_trans (le_lo m N₀ hm) (lo_le_hi m N₀)
    · have h := exc_card m N₀
      have hs2 := S_two_le m N₀
      have hR : ((S m N₀ - 1 : ℕ) : ℝ) = (S m N₀ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hhi : ((hi m N₀ : ℕ) : ℝ) = (2 * m + 1) * (2 * S m N₀) := by unfold hi; push_cast; ring
      have hs2R : (2 : ℝ) ≤ S m N₀ := by exact_mod_cast hs2
      refine le_trans ?_ (Nat.cast_le.mpr h : ((S m N₀ - 1 : ℕ) : ℝ) ≤ _)
      rw [hR, hhi]
      have e : 1 / (4 * (2 * (m : ℝ) + 1)) * ((2 * m + 1) * (2 * S m N₀)) = S m N₀ / 2 := by
        field_simp; ring
      rw [e]; linarith

end LeanLab.DensityGoldbach.AlsetriShaoSharp

