module

public import LeanLab.HardyLittlewood1923.TheoremD
public import LeanLab.ChebyshevExplicit.Psi30

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5712, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III, Theorem C, (3.51)

Read from `papers/P0004.pdf`, Acta Math. 44. Page 6, (1.45) and (1.46): `N_r(n)` is the number
of representations of `n` as a sum of `r` primes, order counted and repetitions allowed, and
`ν_r(n) = Σ_{ϖ₁ + ⋯ + ϖ_r = n} log ϖ₁ ⋯ log ϖ_r`. Page 30, Theorem C: if `r ≥ 3` and `n`, `r`
have like parity, then `N_r(n) ∼ ν_r(n)/(log n)^r`.

Proof, Hardy and Littlewood's own route on p. 30: `ν_r ≤ (log n)^r N_r` trivially; tuples whose
primes all exceed `n^{1-δ}` give `ν_r ≥ ((1-δ) log n)^r (N_r - E)` with
`E ≤ r n^{1-δ} (n+1)^{r-2}`; and `E = o(N_r)` from a lower bound `N_r(n) ≫ n^{r-1}/(log n)^r`.
Hardy and Littlewood get that lower bound, `ν_r(n) > B n^{r-1}`, from their Lemma 13; here it is PROVED
with no hypothesis, by induction on `r` from the lab's unconditional ternary lower bound
`LeanLab.PNTPort.Vinogradov.r3_lower`, by prepending an odd prime `p ≤ n/2` and counting such
primes with `LeanLab.ChebyshevExplicit.pi_ge_chebyshev30`.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter
open LeanLab.VanDerCorput1939 (I)

/-- N_r(n), (1.45): ordered r-tuples of primes with sum n. -/
noncomputable def Nr (r n : ℕ) : ℕ :=
  #((Fintype.piFinset fun _ : Fin r => Finset.range (n + 1)).filter
    (fun t => (∀ i, (t i).Prime) ∧ ∑ i, t i = n))

/-- ν_r(n), (1.46). -/
noncomputable def nur (r n : ℕ) : ℝ :=
  ∑ t ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (n + 1)).filter
    (fun t => (∀ i, (t i).Prime) ∧ ∑ i, t i = n), ∏ i, Real.log (t i)

/-- Theorem C, (3.51). -/
def theoremC_stmt : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → n % 2 = r % 2 →
    |(Nr r n : ℝ) * Real.log n ^ r - nur r n| ≤ ε * nur r n

/-- The set counted by `Nr`. -/
noncomputable def Sr (r n : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ : Fin r => Finset.range (n + 1)).filter
    (fun t => (∀ i, (t i).Prime) ∧ ∑ i, t i = n)

lemma Nr_eq (r n : ℕ) : Nr r n = #(Sr r n) := rfl

lemma nur_eq (r n : ℕ) : nur r n = ∑ t ∈ Sr r n, ∏ i, Real.log (t i) := rfl

lemma mem_Sr {r n : ℕ} {t : Fin r → ℕ} :
    t ∈ Sr r n ↔ (∀ i, t i < n + 1) ∧ (∀ i, (t i).Prime) ∧ ∑ i, t i = n := by
  simp [Sr, Fintype.mem_piFinset]

lemma nur_nonneg (r n : ℕ) : 0 ≤ nur r n := by
  rw [nur_eq]
  apply Finset.sum_nonneg
  intro t ht
  rw [mem_Sr] at ht
  apply Finset.prod_nonneg
  intro i _
  exact Real.log_nonneg (by exact_mod_cast (ht.2.1 i).one_lt.le)

/-- Step 1: `ν_r(n) ≤ (log n)^r N_r(n)`. -/
lemma nur_le (r n : ℕ) : nur r n ≤ (Nr r n : ℝ) * Real.log n ^ r := by
  rw [nur_eq, Nr_eq]
  have h : ∀ t ∈ Sr r n, ∏ i, Real.log (t i) ≤ Real.log n ^ r := by
    intro t ht
    rw [mem_Sr] at ht
    calc ∏ i, Real.log (t i) ≤ ∏ _i : Fin r, Real.log n := by
          apply Finset.prod_le_prod₀
          · intro i _; exact Real.log_nonneg (by exact_mod_cast (ht.2.1 i).one_lt.le)
          · intro i _
            apply Real.log_le_log (by exact_mod_cast (ht.2.1 i).pos)
            exact_mod_cast (by have := ht.1 i; omega : t i ≤ n)
      _ = Real.log n ^ r := by simp
  calc _ ≤ ∑ _t ∈ Sr r n, Real.log n ^ r := Finset.sum_le_sum h
    _ = _ := by simp

/-- Tuples in `range (n+1)` with a fixed sum are determined by their tail. -/
lemma card_fixsum_le (s n m : ℕ) :
    #((Fintype.piFinset fun _ : Fin (s + 1) => range (n + 1)).filter
      (fun u => ∑ i, u i = m)) ≤ (n + 1) ^ s := by
  calc _ ≤ #(Fintype.piFinset fun _ : Fin s => range (n + 1)) := by
        apply card_le_card_of_injOn Fin.tail
        · intro u hu
          simp only [mem_coe, mem_filter, Fintype.mem_piFinset] at hu ⊢
          exact fun i => hu.1 i.succ
        · intro u hu v hv huv
          simp only [mem_coe, mem_filter, Fintype.mem_piFinset] at hu hv
          have hs : ∑ i : Fin s, u i.succ = ∑ i : Fin s, v i.succ :=
            Finset.sum_congr rfl fun i _ => congrFun huv i
          have h0 : u 0 = v 0 := by
            have a := hu.2
            have b := hv.2
            rw [Fin.sum_univ_succ] at a b
            omega
          rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v, h0]
          exact congrArg _ huv
    _ = (n + 1) ^ s := by simp

/-- Tuples with sum `n` whose `i`-th entry is below `X`. -/
lemma card_small_le (s n X : ℕ) (i : Fin (s + 2)) :
    #((Fintype.piFinset fun _ : Fin (s + 2) => range (n + 1)).filter
      (fun t => ∑ j, t j = n ∧ t i < X)) ≤ X * (n + 1) ^ s := by
  set A := Fintype.piFinset fun _ : Fin (s + 1) => range (n + 1)
  calc _ ≤ #((range X).sigma fun a => A.filter (fun u => ∑ j, u j = n - a)) := by
        apply card_le_card_of_injOn
          (fun t => (⟨t i, Fin.removeNth i t⟩ : Σ _ : ℕ, Fin (s + 1) → ℕ))
        · intro t ht
          simp only [mem_coe, mem_filter, Fintype.mem_piFinset, mem_sigma, mem_range, A] at ht ⊢
          obtain ⟨h1, h2, h3⟩ := ht
          refine ⟨h3, fun j => h1 _, ?_⟩
          have h := Fin.sum_univ_succAbove t i
          rw [show (∑ j, Fin.removeNth i t j) = ∑ j, t (i.succAbove j) from rfl]
          have h' : t i + ∑ j, t (i.succAbove j) = n := h.symm.trans h2
          omega
        · intro t _ u _ h
          simp only [Sigma.mk.inj_iff] at h
          obtain ⟨h1, h2⟩ := h
          calc t = Fin.insertNth i (t i) (Fin.removeNth i t) :=
                (Fin.insertNth_self_removeNth i t).symm
            _ = Fin.insertNth i (u i) (Fin.removeNth i u) := by rw [h1, eq_of_heq h2]
            _ = u := Fin.insertNth_self_removeNth i u
    _ = ∑ a ∈ range X, #(A.filter fun u => ∑ j, u j = n - a) := card_sigma _ _
    _ ≤ ∑ _a ∈ range X, (n + 1) ^ s := sum_le_sum fun a _ => card_fixsum_le s n (n - a)
    _ = X * (n + 1) ^ s := by simp

/-- Tuples with some entry below `X`: at most `r X (n+1)^{r-2}`. -/
lemma card_small_union (s n X : ℕ) :
    #((Sr (s + 2) n).filter (fun t => ∃ i, t i < X)) ≤ (s + 2) * (X * (n + 1) ^ s) := by
  calc _ ≤ #(univ.biUnion fun i : Fin (s + 2) =>
        (Fintype.piFinset fun _ : Fin (s + 2) => range (n + 1)).filter
          (fun t => ∑ j, t j = n ∧ t i < X)) := by
        apply card_le_card
        intro t ht
        rw [mem_filter, mem_Sr] at ht
        obtain ⟨⟨h1, _, h3⟩, ⟨i, hi⟩⟩ := ht
        rw [mem_biUnion]
        refine ⟨i, mem_univ _, ?_⟩
        simp only [mem_filter, Fintype.mem_piFinset, mem_range]
        exact ⟨h1, h3, hi⟩
    _ ≤ ∑ i : Fin (s + 2), #((Fintype.piFinset fun _ : Fin (s + 2) => range (n + 1)).filter
          (fun t => ∑ j, t j = n ∧ t i < X)) := card_biUnion_le
    _ ≤ ∑ _i : Fin (s + 2), X * (n + 1) ^ s := sum_le_sum fun i _ => card_small_le s n X i
    _ = _ := by simp

/-- Step 2: tuples with every entry at least `X` give `ν_r ≥ (N_r - #small) a^r`. -/
lemma nur_ge (r n X : ℕ) (a : ℝ) (ha : 0 ≤ a) (hX : ∀ m : ℕ, X ≤ m → a ≤ Real.log m) :
    ((Nr r n : ℝ) - #((Sr r n).filter (fun t => ∃ i, t i < X))) * a ^ r ≤ nur r n := by
  set B := (Sr r n).filter (fun t => ∃ i, t i < X)
  have hBS : B ⊆ Sr r n := filter_subset _ _
  have hcard : ((#(Sr r n \ B) : ℕ) : ℝ) = (Nr r n : ℝ) - #B := by
    rw [card_sdiff_of_subset hBS, Nat.cast_sub (card_le_card hBS), Nr_eq]
  rw [← hcard, nur_eq]
  calc ((#(Sr r n \ B) : ℕ) : ℝ) * a ^ r = ∑ _t ∈ Sr r n \ B, a ^ r := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ Sr r n \ B, ∏ i, Real.log (t i) := by
        apply sum_le_sum
        intro t ht
        obtain ⟨ht1, ht2⟩ := Finset.mem_sdiff.mp ht
        have hbig : ∀ i, X ≤ t i := by
          intro i
          by_contra hlt
          exact ht2 (mem_filter.mpr ⟨ht1, i, by omega⟩)
        calc a ^ r = ∏ _i : Fin r, a := by simp
          _ ≤ ∏ i, Real.log (t i) :=
            Finset.prod_le_prod₀ (fun _ _ => ha) (fun i _ => hX _ (hbig i))
    _ ≤ ∑ t ∈ Sr r n, ∏ i, Real.log (t i) := by
        apply sum_le_sum_of_subset_of_nonneg sdiff_subset
        intro t ht _
        rw [mem_Sr] at ht
        apply Finset.prod_nonneg
        intro i _
        exact Real.log_nonneg (by exact_mod_cast (ht.2.1 i).one_lt.le)

/-- `I(n) ≤ N_3(n)`: van der Corput's count of ordered prime triples. -/
lemma I_le_Nr3 (n : ℕ) : I n ≤ Nr 3 n := by
  unfold I
  rw [Nr_eq]
  apply card_le_card_of_injOn (fun p : ℕ × ℕ => ![p.1, p.2, n - p.1 - p.2])
  · intro p hp
    simp only [mem_coe, mem_filter, mem_product, mem_range] at hp
    rw [mem_coe, mem_Sr]
    obtain ⟨⟨h1, h2⟩, hp1, hp2, _, hp3, hle⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp <;> omega
    · intro i
      fin_cases i <;> simpa
    · simp [Fin.sum_univ_three]
      omega
  · intro p _ q _ h
    have e1 := congrFun h 0
    have e2 := congrFun h 1
    simp at e1 e2
    exact Prod.ext e1 e2

/-- The base case `r = 3` of the lower bound, from Vinogradov's theorem in the lab. -/
lemma Nr3_lower : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → n % 2 = 1 →
    (1 / 80 : ℝ) * (n : ℝ) ^ 2 ≤ (Nr 3 n : ℝ) * Real.log n ^ 3 := by
  obtain ⟨N₀, hlow⟩ := LeanLab.PNTPort.Vinogradov.r3_lower
  obtain ⟨n₃, hup⟩ := LeanLab.VanDerCorput1939.r3_le_I (1 / 80) (by norm_num)
  refine ⟨max ⌈N₀⌉₊ n₃, fun n hn hodd => ?_⟩
  have hN0 : N₀ ≤ n := (Nat.le_ceil N₀).trans (by exact_mod_cast le_of_max_le_left hn)
  have hr := hlow n hN0 (Nat.odd_iff.mpr hodd)
  have hu := hup n (le_of_max_le_right hn)
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hI : (I n : ℝ) ≤ Nr 3 n := by exact_mod_cast I_le_Nr3 n
  have := mul_le_mul_of_nonneg_right hI (pow_nonneg hL 3)
  linarith

lemma log_small (x : ℝ) (hx : 900 ≤ x) : 6 * Real.log x ≤ 0.4 * x := by
  have hx0 : 0 < x := by linarith
  have hs : 30 ≤ √x := by
    rw [show (30 : ℝ) = √(30 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  have h1 : Real.log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
  have h3 : √x * √x = x := Real.mul_self_sqrt hx0.le
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ √x - 30) (by linarith : (0 : ℝ) ≤ √x)]

/-- At least `n/(8 log n)` odd primes up to `n/2`, for `n ≥ 1800`. -/
lemma oddPrimes_lower : ∀ n : ℕ, 1800 ≤ n →
    (n : ℝ) / 8 ≤ (#((Nat.primesBelow (n / 2 + 1)).erase 2) : ℝ) * Real.log n := by
  intro n hn
  set m := n / 2 with hm
  set P := (Nat.primesBelow (m + 1)).erase 2 with hP
  have hm900 : 900 ≤ m := by omega
  have hpc := LeanLab.ChebyshevExplicit.pi_ge_chebyshev30 m (by omega)
  have hcard : Nat.primeCounting m ≤ #P + 1 := by
    have h := Finset.pred_card_le_card_erase (s := Nat.primesBelow (m + 1)) (a := 2)
    rw [Nat.primesBelow_card_eq_primeCounting'] at h
    have : Nat.primeCounting m = Nat.primeCounting' (m + 1) := rfl
    have : #P = #((Nat.primesBelow (m + 1)).erase 2) := rfl
    omega
  have hmR : (900 : ℝ) ≤ m := by exact_mod_cast hm900
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hls := log_small m hmR
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n 2
  have h2m : (n : ℝ) ≤ 2 * m + 1 := by exact_mod_cast (by omega : n ≤ 2 * m + 1)
  have hlog : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmn
  rw [div_le_iff₀ hlogm] at hpc
  have hcR : (Nat.primeCounting m : ℝ) ≤ #P + 1 := by exact_mod_cast hcard
  have h1 : 0.9212 * (m : ℝ) - 5 * Real.log m ≤ (#P + 1) * Real.log m :=
    hpc.trans (mul_le_mul_of_nonneg_right hcR hlogm.le)
  have h2 : (#P : ℝ) * Real.log m ≤ #P * Real.log n :=
    mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
  nlinarith

/-- Prepending a prime: `Σ_{p ∈ P} N_r(n - p) ≤ N_{r+1}(n)`. -/
lemma Nr_succ_ge (r n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ n) :
    ∑ p ∈ P, Nr r (n - p) ≤ Nr (r + 1) n := by
  simp only [Nr_eq]
  rw [← card_sigma]
  apply card_le_card_of_injOn
    (fun x : Σ _ : ℕ, Fin r → ℕ => (Fin.cons x.1 x.2 : Fin (r + 1) → ℕ))
  · rintro ⟨p, t⟩ h
    simp only [mem_coe, mem_sigma] at h
    obtain ⟨hp, ht⟩ := h
    rw [mem_Sr] at ht
    rw [mem_coe, mem_Sr]
    obtain ⟨hpp, hpn⟩ := hP p hp
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]; omega
      · simp only [Fin.cons_succ]; have := ht.1 j; omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hpp
      · simpa using ht.2.1 j
    · rw [Fin.sum_cons, ht.2.2]
      omega
  · intro x _ y _ h
    have h' : (Fin.cons x.1 x.2 : Fin (r + 1) → ℕ) = Fin.cons y.1 y.2 := h
    obtain ⟨h1, h2⟩ := Fin.cons_inj.mp h'
    exact Sigma.ext h1 (heq_of_eq h2)

/-- Step 3: `N_r(n) (log n)^r ≥ c_r n^{r-1}` for large `n ≡ r mod 2`, `r = k + 3`. -/
theorem Nr_lower (k : ℕ) : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → n % 2 = (k + 3) % 2 →
    c * (n : ℝ) ^ (k + 2) ≤ (Nr (k + 3) n : ℝ) * Real.log n ^ (k + 3) := by
  induction k with
  | zero =>
    obtain ⟨n₀, h⟩ := Nr3_lower
    exact ⟨1 / 80, by norm_num, n₀, fun n hn hp => h n hn (by omega)⟩
  | succ k ih =>
    obtain ⟨c, hc, n₀, h⟩ := ih
    refine ⟨c / 2 ^ (k + 2) / 8, by positivity, max (2 * n₀ + 2) 1800, fun n hn hpar => ?_⟩
    show c / 2 ^ (k + 2) / 8 * (n : ℝ) ^ (k + 3) ≤
      (Nr (k + 3 + 1) n : ℝ) * Real.log n ^ (k + 3 + 1)
    have hn1 : 2 * n₀ + 2 ≤ n := le_of_max_le_left hn
    have hn2 : 1800 ≤ n := le_of_max_le_right hn
    set P := (Nat.primesBelow (n / 2 + 1)).erase 2 with hP
    have hPm : ∀ p ∈ P, p.Prime ∧ p % 2 = 1 ∧ p ≤ n / 2 := by
      intro p hp
      rw [hP, mem_erase, Nat.mem_primesBelow] at hp
      obtain ⟨h2, hlt, hpp⟩ := hp
      refine ⟨hpp, ?_, by omega⟩
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd h h2
      · exact h
    have hsum := Nr_succ_ge (k + 3) n P (fun p hp => ⟨(hPm p hp).1, by
      have := (hPm p hp).2.2; omega⟩)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hterm : ∀ p ∈ P, c * ((n : ℝ) / 2) ^ (k + 2) ≤
        (Nr (k + 3) (n - p) : ℝ) * Real.log n ^ (k + 3) := by
      intro p hp
      obtain ⟨_, hodd, hpm⟩ := hPm p hp
      have h1 := h (n - p) (by omega) (by omega)
      have hnp : (n : ℝ) / 2 ≤ ((n - p : ℕ) : ℝ) := by
        have : (n : ℝ) ≤ 2 * ((n - p : ℕ) : ℝ) := by
          exact_mod_cast (by omega : n ≤ 2 * (n - p))
        linarith
      have hnp1 : (1 : ℝ) ≤ ((n - p : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ n - p)
      have hlog : Real.log ((n - p : ℕ) : ℝ) ≤ Real.log n :=
        Real.log_le_log (by linarith) (by exact_mod_cast Nat.sub_le n p)
      calc c * ((n : ℝ) / 2) ^ (k + 2) ≤ c * ((n - p : ℕ) : ℝ) ^ (k + 2) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnp _) hc.le
        _ ≤ (Nr (k + 3) (n - p) : ℝ) * Real.log ((n - p : ℕ) : ℝ) ^ (k + 3) := h1
        _ ≤ (Nr (k + 3) (n - p) : ℝ) * Real.log n ^ (k + 3) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Real.log_nonneg hnp1) hlog _) (Nat.cast_nonneg _)
    have hS : (#P : ℝ) * (c * ((n : ℝ) / 2) ^ (k + 2)) ≤
        (∑ p ∈ P, (Nr (k + 3) (n - p) : ℝ)) * Real.log n ^ (k + 3) := by
      rw [sum_mul, ← nsmul_eq_mul]
      exact card_nsmul_le_sum _ _ _ hterm
    have hcast : (∑ p ∈ P, (Nr (k + 3) (n - p) : ℝ)) ≤ Nr (k + 3 + 1) n := by
      exact_mod_cast hsum
    have hPn := oddPrimes_lower n hn2
    rw [← hP] at hPn
    calc c / 2 ^ (k + 2) / 8 * (n : ℝ) ^ (k + 3)
        = ((n : ℝ) / 8) * (c * ((n : ℝ) / 2) ^ (k + 2)) := by rw [div_pow]; ring
      _ ≤ ((#P : ℝ) * Real.log n) * (c * ((n : ℝ) / 2) ^ (k + 2)) :=
          mul_le_mul_of_nonneg_right hPn (by positivity)
      _ = Real.log n * ((#P : ℝ) * (c * ((n : ℝ) / 2) ^ (k + 2))) := by ring
      _ ≤ Real.log n * ((∑ p ∈ P, (Nr (k + 3) (n - p) : ℝ)) * Real.log n ^ (k + 3)) :=
          mul_le_mul_of_nonneg_left hS hL
      _ ≤ Real.log n * ((Nr (k + 3 + 1) n : ℝ) * Real.log n ^ (k + 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcast (pow_nonneg hL _)) hL
      _ = (Nr (k + 3 + 1) n : ℝ) * Real.log n ^ (k + 3 + 1) := by ring
/-- The closing algebra of step 3. -/
lemma final_alg (A ν E q θ ε : ℝ) (hε : 0 < ε) (hθ : θ = ε / (4 * (1 + ε)))
    (hA0 : 0 ≤ A) (hup : ν ≤ A) (hE0 : 0 ≤ E) (hE : E ≤ θ * A)
    (hq : 1 - θ ≤ q) (hq1 : q ≤ 1) (h2 : q * A - q * E ≤ ν) : |A - ν| ≤ ε * ν := by
  have hqE : q * E ≤ E := mul_le_of_le_one_left hE0 hq1
  have hqA : (1 - θ) * A ≤ q * A := mul_le_mul_of_nonneg_right hq hA0
  have key : (1 - 2 * θ) * A ≤ ν := by nlinarith
  have hfac : (1 + ε) * (1 - 2 * θ) = 1 + ε / 2 := by
    rw [hθ]; field_simp; ring
  have hAν : A ≤ (1 + ε) * ν := by
    calc A ≤ (1 + ε) * (1 - 2 * θ) * A := by rw [hfac]; nlinarith
      _ = (1 + ε) * ((1 - 2 * θ) * A) := by ring
      _ ≤ (1 + ε) * ν := mul_le_mul_of_nonneg_left key (by linarith)
  rw [abs_le]
  constructor <;> nlinarith

/-- The error term: `E (log n)^r ≤ θ c n^{r-1}` once `r 2^{r-1} (log n)^r ≤ θ c n^δ`. -/
lemma error_alg (k : ℕ) (b L x n nδ θ c : ℝ) (hL : 0 ≤ L) (hx : 0 ≤ x) (hn : 0 ≤ n)
    (hb : b ≤ ((k : ℝ) + 3) * ((2 * x) * (2 * n) ^ (k + 1)))
    (hLC : ((k : ℝ) + 3) * 2 ^ (k + 2) * L ^ (k + 3) ≤ θ * c * nδ)
    (hxn : nδ * x = n) :
    b * L ^ (k + 3) ≤ θ * (c * n ^ (k + 2)) := by
  have hb' : b ≤ ((k : ℝ) + 3) * 2 ^ (k + 2) * (x * n ^ (k + 1)) := by
    calc b ≤ ((k : ℝ) + 3) * ((2 * x) * (2 * n) ^ (k + 1)) := hb
      _ = ((k : ℝ) + 3) * 2 ^ (k + 2) * (x * n ^ (k + 1)) := by rw [mul_pow]; ring
  calc b * L ^ (k + 3)
      ≤ ((k : ℝ) + 3) * 2 ^ (k + 2) * (x * n ^ (k + 1)) * L ^ (k + 3) :=
        mul_le_mul_of_nonneg_right hb' (pow_nonneg hL _)
    _ = (((k : ℝ) + 3) * 2 ^ (k + 2) * L ^ (k + 3)) * (x * n ^ (k + 1)) := by ring
    _ ≤ (θ * c * nδ) * (x * n ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right hLC (by positivity)
    _ = θ * (c * ((nδ * x) * n ^ (k + 1))) := by ring
    _ = θ * (c * n ^ (k + 2)) := by rw [hxn]; ring

/-- **Hardy-Littlewood 1923, Theorem C, (3.51)**: for `r ≥ 3` and `n ≡ r mod 2`,
`N_r(n) ∼ ν_r(n)/(log n)^r`. PROVED with no hypothesis. -/
theorem theoremC : theoremC_stmt := by
  intro r hr ε hε
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  obtain ⟨c, hc, n₀, hlow⟩ := Nr_lower k
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ε / (4 * (1 + ε)) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ < 1 / 4 := by
    rw [hθdef, div_lt_iff₀ (by positivity)]; linarith
  have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = θ / ((k : ℝ) + 3) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hkδ : ((k : ℝ) + 3) * δ = θ := by rw [hδdef]; field_simp
  have hδ1 : δ < 1 := by
    have : δ ≤ ((k : ℝ) + 3) * δ := le_mul_of_one_le_left hδ.le (by linarith)
    linarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = θ * c / (((k : ℝ) + 3) * 2 ^ (k + 2)) := ⟨_, rfl⟩
  have hC : 0 < C := by rw [hCdef]; positivity
  have ho := (isLittleO_log_rpow_rpow_atTop (((k + 3 : ℕ) : ℝ)) hδ).bound hC
  have ho' : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ) ^ (((k + 3 : ℕ) : ℝ))‖ ≤ C * ‖(n : ℝ) ^ δ‖ :=
    tendsto_natCast_atTop_atTop.eventually ho
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (ho'.and (eventually_ge_atTop (max n₀ 3)))
  refine ⟨n₁, fun n hn hpar => ?_⟩
  obtain ⟨hbd, hn3⟩ := hn₁ n hn
  have hn0 : n₀ ≤ n := le_of_max_le_left hn3
  have hn3' : 3 ≤ n := le_of_max_le_right hn3
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [Real.rpow_natCast, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL _),
    abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hbd
  have hLC : ((k : ℝ) + 3) * 2 ^ (k + 2) * Real.log n ^ (k + 3) ≤ θ * c * (n : ℝ) ^ δ := by
    have := mul_le_mul_of_nonneg_left hbd
      (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 3) * 2 ^ (k + 2))
    calc _ ≤ ((k : ℝ) + 3) * 2 ^ (k + 2) * (C * (n : ℝ) ^ δ) := this
      _ = θ * c * (n : ℝ) ^ δ := by rw [hCdef]; field_simp
  -- the cut `x = n^{1-δ}`
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (n : ℝ) ^ (1 - δ) := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by rw [hxdef]; exact Real.one_le_rpow hn1 (by linarith)
  have hxn : (n : ℝ) ^ δ * x = n := by
    rw [hxdef, ← Real.rpow_add hnpos, show δ + (1 - δ) = 1 by ring, Real.rpow_one]
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = ⌈x⌉₊ := ⟨_, rfl⟩
  have hX2 : (X : ℝ) ≤ 2 * x := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x)
    rw [hXdef]; linarith
  have ha : 0 ≤ (1 - δ) * Real.log n := mul_nonneg (by linarith) hL
  have hXa : ∀ m : ℕ, X ≤ m → (1 - δ) * Real.log n ≤ Real.log m := by
    intro m hm
    have hxm : x ≤ m := (Nat.le_ceil x).trans (by rw [← hXdef]; exact_mod_cast hm)
    calc (1 - δ) * Real.log n = Real.log x := by rw [hxdef, Real.log_rpow hnpos]
      _ ≤ Real.log m := Real.log_le_log (by linarith) hxm
  have hge := nur_ge (k + 3) n X _ ha hXa
  have h0 := card_small_union (k + 1) n X
  have hBcard : ((#((Sr (k + 3) n).filter (fun t => ∃ i, t i < X)) : ℕ) : ℝ) ≤
      ((k : ℝ) + 3) * (X * ((n : ℝ) + 1) ^ (k + 1)) := by
    have h1 : ((#((Sr (k + 3) n).filter (fun t => ∃ i, t i < X)) : ℕ) : ℝ) ≤
        ((k + 1 + 2 : ℕ) : ℝ) * ((X : ℝ) * ((n : ℝ) + 1) ^ (k + 1)) := by
      exact_mod_cast h0
    have h2 : ((k + 1 + 2 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    rw [h2] at h1
    exact h1
  have hcA := hlow n hn0 hpar
  have hb0 : (0 : ℝ) ≤ ((#((Sr (k + 3) n).filter (fun t => ∃ i, t i < X)) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  generalize ((#((Sr (k + 3) n).filter (fun t => ∃ i, t i < X)) : ℕ) : ℝ) = b at hge hBcard hb0
  have hn21 : ((n : ℝ) + 1) ^ (k + 1) ≤ (2 * n) ^ (k + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hb2 : b ≤ ((k : ℝ) + 3) * ((2 * x) * (2 * (n : ℝ)) ^ (k + 1)) := by
    refine hBcard.trans (mul_le_mul_of_nonneg_left ?_ hk.le)
    exact mul_le_mul hX2 hn21 (by positivity) (by positivity)
  have hup := nur_le (k + 3) n
  have hν0 := nur_nonneg (k + 3) n
  generalize nur (k + 3) n = ν at hge hup hν0 ⊢
  generalize ((Nr (k + 3) n : ℕ) : ℝ) = N at hge hup hcA ⊢
  generalize Real.log n = L at hge hup hcA hL hLC ha ⊢
  have hE := error_alg k b L x n ((n : ℝ) ^ δ) θ c hL (by linarith) hnpos.le
    hb2 hLC hxn
  have hq : 1 - θ ≤ (1 - δ) ^ (k + 3) := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) (k + 3)
    rw [show (1 : ℝ) + -δ = 1 - δ by ring] at this
    push_cast at this
    nlinarith
  have hq1 : (1 - δ) ^ (k + 3) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hA0 : 0 ≤ N * L ^ (k + 3) := le_trans (by positivity) hcA
  refine final_alg (N * L ^ (k + 3)) ν (b * L ^ (k + 3)) ((1 - δ) ^ (k + 3)) θ ε hε hθdef
    hA0 hup (mul_nonneg hb0 (pow_nonneg hL _))
    (hE.trans (mul_le_mul_of_nonneg_left hcA hθ.le)) hq hq1 ?_
  calc (1 - δ) ^ (k + 3) * (N * L ^ (k + 3)) - (1 - δ) ^ (k + 3) * (b * L ^ (k + 3))
      = (N - b) * ((1 - δ) * L) ^ (k + 3) := by rw [mul_pow]; ring
    _ ≤ ν := hge

end LeanLab.HardyLittlewood1923

