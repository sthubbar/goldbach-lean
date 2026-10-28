module

public import LeanLab.Halupczok2012.U1457SingSeries

/-!
# P0077 Halupczok 2012, toward `SingSeriesApprox`: CRT multiplicativity and the finite Euler
identification, unit U-1460

AI wrote the Lean code, Claude, run 20261022T0003Z-15508. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The weights. For a finite set `t` of primes, `s = ∏ t`, and `m : ℕ`,
`gW n t m = ∏_{p ∈ t} c_p(n - m)/(p - 1)²`, with `c_p(r) = p - 1` if `p ∣ r` and `-1` if not,
`r` an INTEGER, so the weight is honestly `s`-periodic in `m` for all `m`. The prime `2` is
allowed, `(2 - 1)² = 1`: this is the 2 adic factor.

* `sum_range_crt`: for coprime `m, k`, `∑_{b < mk} F(b mod m) G(b mod k) = ∑_{x<m} F x ∑_{y<k} G y`.
* `sum_range_prod_primes`: for a finite set `t` of primes,
  `∑_{b < ∏ t} ∏_{p ∈ t} h_p(b mod p) = ∏_{p ∈ t} ∑_{x < p} h_p(x)`. The CRT multiplicativity.
* `cPZ_full_sum`, `cPZ_reduced_sum`: `∑_{x mod p} c_p(n - x) = 0`, and over the reduced classes
  it is `-(p-1)` if `p ∣ n`, `1` if not. For every prime `p` and every integer `n`.
* `reduced_sum_squarefree`: the multiplicativity extension of U-1457's `cP_reduced_sum`:
  `∑_{b < s, (b,s)=1} ∏_{p ∣ s} c_p(n - b) = ∏_{p ∣ s} (-(p-1) if p ∣ n, else 1)`.
* `crtG_sum`: with `(a, q) = 1`, `∑_{b ∈ G(a,q,s)} gW n t b` is the product over `p ∈ t` of
  `c_p(n - a)/(p-1)²` if `p ∣ q` and `(-(p-1) or 1)/(p-1)²` if `p ∤ q`.
* `totient_lcm_prod`: `φ([q, ∏ t]) = φ(q) ∏_{p ∈ t, p ∤ q} (p - 1)`.
* `euler_finite`: THE FINITE EULER IDENTIFICATION. For every finite set `P` of primes,
  `∑_{t ⊆ P} 1/φ([q, ∏ t]) ∑_{b ∈ G(a,q,∏ t)} gW n t b = 1/φ(q) ∏_{p ∈ P} tF(p)`,
  where `tF(p)` is EXACTLY the local factor of the paper's `𝔗(n, q, a)`, so that
  `𝔗(n, q, a) = 1/φ(q) ∏'_p tF(p)` by definition, `T_eq_tprod`.

All PROVED. `SingSeriesApprox` itself is NOT proved; what remains is listed in PROGRESS.md.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-! ### The CRT product formula for sums -/

/-- **CRT for sums.** -/
theorem sum_range_crt {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (hc : Nat.Coprime m k)
    (F G : ℕ → ℝ) :
    ∑ b ∈ range (m * k), F (b % m) * G (b % k) =
      (∑ x ∈ range m, F x) * (∑ y ∈ range k, G y) := by
  have hinj : Set.InjOn (fun b => (b % m, b % k)) (range (m * k) : Set ℕ) := by
    intro b hb b' hb' he
    simp only [coe_range, Set.mem_Iio] at hb hb'
    simp only [Prod.mk.injEq] at he
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨he.1, he.2⟩
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h
  have himg : (range (m * k)).image (fun b => (b % m, b % k)) = range m ×ˢ range k := by
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image] at hx
      obtain ⟨b, -, rfl⟩ := hx
      simp [Nat.mod_lt _ hm, Nat.mod_lt _ hk]
    · rw [card_product, card_range, card_range, card_image_of_injOn hinj, card_range]
  rw [sum_mul_sum, ← sum_product', ← himg, sum_image hinj]

/-- **CRT multiplicativity over a finite set of primes.** -/
theorem sum_range_prod_primes (h : ℕ → ℕ → ℝ) :
    ∀ t : Finset ℕ, (∀ p ∈ t, p.Prime) →
    ∑ b ∈ range (∏ p ∈ t, p), ∏ p ∈ t, h p (b % p) = ∏ p ∈ t, ∑ x ∈ range p, h p x := by
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | insert p t hpt ih =>
    intro ht
    have hp : p.Prime := ht p (mem_insert_self p t)
    have ht' : ∀ r ∈ t, r.Prime := fun r hr => ht r (mem_insert_of_mem hr)
    have hcop : Nat.Coprime p (∏ r ∈ t, r) := by
      apply Nat.Coprime.prod_right
      intro r hr
      exact (Nat.coprime_primes hp (ht' r hr)).mpr (fun he => hpt (he ▸ hr))
    have hpos : 0 < ∏ r ∈ t, r := prod_pos (fun r hr => (ht' r hr).pos)
    rw [prod_insert hpt, prod_insert hpt]
    have hterm : ∀ b, ∏ r ∈ insert p t, h r (b % r) =
        h p (b % p) * (fun c => ∏ r ∈ t, h r (c % r)) (b % ∏ r ∈ t, r) := by
      intro b
      rw [prod_insert hpt]
      congr 1
      apply prod_congr rfl
      intro r hr
      rw [Nat.mod_mod_of_dvd b (dvd_prod_of_mem _ hr)]
    rw [sum_congr rfl (fun b _ => hterm b), ← ih ht']
    exact sum_range_crt hp.pos hpos hcop (h p) (fun c => ∏ r ∈ t, h r (c % r))

/-! ### The integer Ramanujan weight at a prime -/

/-- `c_p(r)` for a prime `p` and an integer `r`: `p - 1` if `p ∣ r`, else `-1`. -/
noncomputable def cPZ (p : ℕ) (r : ℤ) : ℝ := if (p : ℤ) ∣ r then (p : ℝ) - 1 else -1

theorem cPZ_natCast {p r : ℕ} : cPZ p (r : ℤ) = cP p r := by
  unfold cPZ cP; simp only [Int.natCast_dvd_natCast]

theorem dvd_emod_sub_iff (x a p : ℤ) : p ∣ x % p - a ↔ p ∣ x - a := by
  rw [Int.emod_def, show x - p * (x / p) - a = (x - a) - p * (x / p) by ring]
  exact dvd_sub_left (dvd_mul_right p _)

theorem cPZ_mod (p : ℕ) (n : ℤ) (b : ℕ) : cPZ p (n - ((b % p : ℕ) : ℤ)) = cPZ p (n - b) := by
  unfold cPZ
  have : (p : ℤ) ∣ n - ((b % p : ℕ) : ℤ) ↔ (p : ℤ) ∣ n - b := by
    rw [← dvd_neg, ← dvd_neg (b := n - (b : ℤ))]
    rw [show -(n - ((b % p : ℕ) : ℤ)) = ((b : ℤ) % p) - n by push_cast; ring,
      show -(n - (b : ℤ)) = (b : ℤ) - n by ring]
    exact dvd_emod_sub_iff _ _ _
  simp only [this]

/-- The unique `x < p` with `p ∣ x - a`. -/
theorem dvd_sub_iff_eq_emod {p : ℕ} (hp : 0 < p) {x : ℕ} (hx : x < p) (a : ℤ) :
    (p : ℤ) ∣ (x : ℤ) - a ↔ (x : ℤ) = a % p := by
  have hx' : (x : ℤ) % p = x := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)
  constructor
  · intro h
    have := Int.emod_emod_of_dvd (x : ℤ) (dvd_refl (p : ℤ))
    have e : (x : ℤ) ≡ a [ZMOD p] := (Int.modEq_iff_dvd.mpr (by
      rw [← dvd_neg]; simpa using h))
    unfold Int.ModEq at e
    rw [hx'] at e; exact e
  · intro h
    rw [h, ← dvd_neg, show -(a % (p : ℤ) - a) = a - a % p by ring, Int.emod_def]
    exact ⟨a / p, by ring⟩

/-- **The full sum vanishes.** `∑_{x < p} c_p(n - x) = 0`. -/
theorem cPZ_full_sum {p : ℕ} (hp : 0 < p) (n : ℤ) :
    ∑ x ∈ range p, cPZ p (n - x) = 0 := by
  have hset : (range p).filter (fun x : ℕ => (p : ℤ) ∣ n - x) = {(n % p).toNat} := by
    ext x
    simp only [mem_filter, mem_range, mem_singleton]
    have hn0 : 0 ≤ n % p := Int.emod_nonneg _ (by positivity)
    have hnp : n % p < p := Int.emod_lt_of_pos _ (by positivity)
    constructor
    · rintro ⟨hx, hd⟩
      have : (p : ℤ) ∣ (x : ℤ) - n := by rw [← dvd_neg]; simpa using hd
      rw [dvd_sub_iff_eq_emod hp hx] at this
      omega
    · intro hx
      have hx' : (x : ℤ) = n % p := by omega
      refine ⟨by omega, ?_⟩
      rw [← dvd_neg, show -(n - (x : ℤ)) = (x : ℤ) - n by ring, dvd_sub_iff_eq_emod hp (by omega)]
      exact hx'
  have e : ∀ x : ℕ, cPZ p (n - x) = -1 + (if (p : ℤ) ∣ n - x then (p : ℝ) else 0) := by
    intro x; unfold cPZ; split_ifs <;> ring
  rw [sum_congr rfl (fun x _ => e x), sum_add_distrib, ← sum_filter, hset, sum_singleton,
    sum_const, card_range, nsmul_eq_mul]
  ring

/-- **The reduced sum at a prime**, for every integer `n`. -/
theorem cPZ_reduced_sum {p : ℕ} (hp : 0 < p) (n : ℤ) :
    ∑ x ∈ range p, (if x = 0 then 0 else cPZ p (n - x)) =
      if (p : ℤ) ∣ n then -((p : ℝ) - 1) else 1 := by
  have e : ∀ x : ℕ, (if x = 0 then 0 else cPZ p (n - x)) =
      cPZ p (n - x) - (if x = 0 then cPZ p (n - x) else 0) := by
    intro x; split_ifs <;> simp
  rw [sum_congr rfl (fun x _ => e x), sum_sub_distrib, cPZ_full_sum hp, sum_ite_eq',
    if_pos (mem_range.mpr hp)]
  unfold cPZ
  simp only [Nat.cast_zero, sub_zero]
  split_ifs <;> ring

/-! ### The weights and the multiplicativity extension -/

/-- The weight `gW n t m = ∏_{p ∈ t} c_p(n - m)/(p - 1)²`. -/
noncomputable def gW (n : ℕ) (t : Finset ℕ) (m : ℕ) : ℝ :=
  ∏ p ∈ t, cPZ p ((n : ℤ) - m) / ((p : ℝ) - 1) ^ 2

/-- `gW` is `∏ t`-periodic, for all `m`. -/
theorem gW_periodic (n : ℕ) (t : Finset ℕ) (m : ℕ) :
    gW n t m = gW n t (m % ∏ p ∈ t, p) := by
  unfold gW
  apply prod_congr rfl
  intro p hp
  rw [← cPZ_mod p n m, ← cPZ_mod p n (m % ∏ p ∈ t, p), Nat.mod_mod_of_dvd m (dvd_prod_of_mem _ hp)]

theorem coprime_prod_iff {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) (b : ℕ) :
    Nat.gcd b (∏ p ∈ t, p) = 1 ↔ ∀ p ∈ t, b % p ≠ 0 := by
  change Nat.Coprime b _ ↔ _
  rw [Nat.coprime_prod_right_iff]
  apply forall₂_congr
  intro p hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (ht p hp), Nat.dvd_iff_mod_eq_zero]

/-- **The multiplicativity extension of `cP_reduced_sum` to squarefree moduli.** -/
theorem reduced_sum_squarefree (n : ℤ) {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    ∑ b ∈ (range (∏ p ∈ t, p)).filter (fun b => Nat.gcd b (∏ p ∈ t, p) = 1),
        ∏ p ∈ t, cPZ p (n - b) =
      ∏ p ∈ t, (if (p : ℤ) ∣ n then -((p : ℝ) - 1) else 1) := by
  rw [sum_filter]
  set H : ℕ → ℕ → ℝ := fun p x => if x = 0 then (0 : ℝ) else cPZ p (n - x) with hH
  have e : ∀ b ∈ range (∏ p ∈ t, p),
      (if Nat.gcd b (∏ p ∈ t, p) = 1 then ∏ p ∈ t, cPZ p (n - b) else 0) =
        ∏ p ∈ t, H p (b % p) := by
    intro b _
    split_ifs with h0
    · have h := (coprime_prod_iff ht b).mp h0
      apply prod_congr rfl
      intro p hp
      rw [hH]; dsimp only
      rw [if_neg (h p hp), cPZ_mod]
    · have h : ¬ ∀ p ∈ t, b % p ≠ 0 := fun hh => h0 ((coprime_prod_iff ht b).mpr hh)
      push_neg at h
      obtain ⟨p, hp, hz⟩ := h
      exact (prod_eq_zero hp (by rw [hz, hH]; simp)).symm
  rw [sum_congr rfl e, sum_range_prod_primes H t ht]
  apply prod_congr rfl
  intro p hp
  rw [hH]
  exact cPZ_reduced_sum (ht p hp).pos n

/-! ### The compatible classes `G(a, q, ∏ t)` -/

/-- `(q, ∏ t) ∣ x` iff every `p ∈ t` dividing `q` divides `x`. -/
theorem gcd_prod_dvd_iff {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) (q : ℕ) (x : ℤ) :
    ((Nat.gcd q (∏ p ∈ t, p) : ℕ) : ℤ) ∣ x ↔ ∀ p ∈ t, p ∣ q → (p : ℤ) ∣ x := by
  classical
  constructor
  · intro h p hp hpq
    have : p ∣ Nat.gcd q (∏ p ∈ t, p) := Nat.dvd_gcd hpq (dvd_prod_of_mem _ hp)
    exact (Int.natCast_dvd_natCast.mpr this).trans h
  · intro h
    have hsplit := prod_filter_mul_prod_filter_not t (fun p => p ∣ q) (fun p => p)
    have hcop : Nat.Coprime (∏ p ∈ t with ¬ p ∣ q, p) q := by
      apply Nat.Coprime.prod_left
      intro p hp
      rw [mem_filter] at hp
      exact (Nat.Prime.coprime_iff_not_dvd (ht p hp.1)).mpr hp.2
    have hg : Nat.gcd q (∏ p ∈ t, p) = Nat.gcd (∏ p ∈ t with p ∣ q, p) q := by
      rw [Nat.gcd_comm, ← hsplit, Nat.Coprime.gcd_mul_right_cancel _ hcop]
    rw [hg, Int.natCast_dvd]
    refine (Nat.gcd_dvd_left _ _).trans ?_
    apply prod_primes_dvd
    · intro p hp
      exact (ht p (mem_filter.mp hp).1).prime
    · intro p hp
      rw [mem_filter] at hp
      exact Int.natCast_dvd.mp (h p hp.1 hp.2)

/-- Membership in `G(a, q, ∏ t)` prime by prime. -/
theorem mem_crtG_prod {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) (a : ℤ) (q b : ℕ)
    (hb : b < ∏ p ∈ t, p) :
    b ∈ crtG a q (∏ p ∈ t, p) ↔
      ∀ p ∈ t, b % p ≠ 0 ∧ (p ∣ q → (p : ℤ) ∣ ((b % p : ℕ) : ℤ) - a) := by
  rw [mem_crtG, crt_exists_iff, gcd_prod_dvd_iff ht, coprime_prod_iff ht]
  constructor
  · rintro ⟨-, h1, h2⟩ p hp
    refine ⟨h1 p hp, fun hpq => ?_⟩
    push_cast
    rw [dvd_emod_sub_iff]
    exact h2 p hp hpq
  · intro h
    refine ⟨hb, fun p hp => (h p hp).1, fun p hp hpq => ?_⟩
    have := (h p hp).2 hpq
    push_cast at this
    rwa [dvd_emod_sub_iff] at this

/-- The local sum at `p ∣ q`: the single compatible class is `a mod p`. -/
theorem local_sum_dvd {p : ℕ} (hp : p.Prime) (n : ℕ) (a : ℤ) (hpa : ¬ (p : ℤ) ∣ a) :
    ∑ x ∈ range p, (if x ≠ 0 ∧ (p : ℤ) ∣ (x : ℤ) - a then (1 : ℝ) else 0) *
        (cPZ p ((n : ℤ) - x) / ((p : ℝ) - 1) ^ 2) =
      cPZ p ((n : ℤ) - a) / ((p : ℝ) - 1) ^ 2 := by
  have hp0 := hp.pos
  set x0 := (a % p).toNat with hx0
  have ha0 : 0 ≤ a % p := Int.emod_nonneg _ (by positivity)
  have hap : a % p < p := Int.emod_lt_of_pos _ (by positivity)
  have hx0' : (x0 : ℤ) = a % p := by rw [hx0]; omega
  have hx0p : x0 < p := by omega
  have hcond : ∀ x ∈ range p, (x ≠ 0 ∧ (p : ℤ) ∣ (x : ℤ) - a) ↔ x = x0 := by
    intro x hx
    rw [mem_range] at hx
    rw [dvd_sub_iff_eq_emod hp0 hx]
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h
      refine ⟨?_, by rw [h, hx0']⟩
      intro h0
      apply hpa
      have : a % p = 0 := by rw [← hx0', ← h, h0]; rfl
      exact Int.dvd_of_emod_eq_zero this
  rw [sum_congr rfl (fun x hx => by rw [if_congr (hcond x hx) rfl rfl])]
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq', if_pos (mem_range.mpr hx0p)]
  congr 1
  unfold cPZ
  have : (p : ℤ) ∣ (n : ℤ) - x0 ↔ (p : ℤ) ∣ (n : ℤ) - a := by
    rw [hx0', ← dvd_neg, ← dvd_neg (b := (n : ℤ) - a),
      show -((n : ℤ) - a % p) = a % p - n by ring, show -((n : ℤ) - a) = a - n by ring,
      dvd_emod_sub_iff]
  simp only [this]

/-- The local factor `loc_p`: `c_p(n - a)` if `p ∣ q`, else `-(p-1)` or `1` by `p ∣ n`. -/
noncomputable def locG (n q : ℕ) (a : ℤ) (p : ℕ) : ℝ :=
  if p ∣ q then cPZ p ((n : ℤ) - a) else if p ∣ n then -((p : ℝ) - 1) else 1

/-- **The `G(a,q,s)` sum of the weight factors over the primes of `s`.** -/
theorem crtG_sum {n q : ℕ} {a : ℤ} (ha : Int.gcd a q = 1) {t : Finset ℕ}
    (ht : ∀ p ∈ t, p.Prime) :
    ∑ b ∈ crtG a q (∏ p ∈ t, p), gW n t b = ∏ p ∈ t, locG n q a p / ((p : ℝ) - 1) ^ 2 := by
  classical
  have hsub := crtG_subset a q (∏ p ∈ t, p)
  have hconv : ∑ b ∈ crtG a q (∏ p ∈ t, p), gW n t b =
      ∑ b ∈ range (∏ p ∈ t, p), (if b ∈ crtG a q (∏ p ∈ t, p) then gW n t b else 0) := by
    rw [sum_ite_mem, inter_eq_right.mpr hsub]
  rw [hconv]
  set h : ℕ → ℕ → ℝ := fun p x =>
    (if x ≠ 0 ∧ (p ∣ q → (p : ℤ) ∣ (x : ℤ) - a) then (1 : ℝ) else 0) *
      (cPZ p ((n : ℤ) - x) / ((p : ℝ) - 1) ^ 2) with hh
  have e : ∀ b ∈ range (∏ p ∈ t, p),
      (if b ∈ crtG a q (∏ p ∈ t, p) then gW n t b else 0) = ∏ p ∈ t, h p (b % p) := by
    intro b hb
    rw [mem_range] at hb
    rw [hh, prod_mul_distrib, prod_boole]
    by_cases hc : b ∈ crtG a q (∏ p ∈ t, p)
    · rw [if_pos hc, if_pos ((mem_crtG_prod ht a q b hb).mp hc), one_mul, gW]
      apply prod_congr rfl
      intro p _
      rw [cPZ_mod]
    · rw [if_neg hc, if_neg (fun hh => hc ((mem_crtG_prod ht a q b hb).mpr hh)), zero_mul]
  rw [sum_congr rfl e, sum_range_prod_primes h t ht]
  apply prod_congr rfl
  intro p hp
  have hpp := ht p hp
  unfold locG
  by_cases hpq : p ∣ q
  · rw [if_pos hpq, hh]
    simp only [hpq, true_implies]
    apply local_sum_dvd hpp n a
    intro hpa
    have hco : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr ha
    have hu := hco.isUnit_of_dvd' hpa (Int.natCast_dvd_natCast.mpr hpq)
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · have : p = 1 := by exact_mod_cast h1
      exact hpp.one_lt.ne' this
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  · rw [if_neg hpq, hh]
    simp only [hpq, false_implies, and_true]
    have e2 : ∀ x ∈ range p, (if x ≠ 0 then (1 : ℝ) else 0) *
        (cPZ p ((n : ℤ) - x) / ((p : ℝ) - 1) ^ 2) =
        (if x = 0 then 0 else cPZ p ((n : ℤ) - x)) / ((p : ℝ) - 1) ^ 2 := by
      intro x _; split_ifs <;> simp_all
    rw [sum_congr rfl e2, ← sum_div, cPZ_reduced_sum hpp.pos]
    simp only [Int.natCast_dvd_natCast]

/-! ### The totient of `[q, ∏ t]` -/

theorem totient_prod_primes : ∀ t : Finset ℕ, (∀ p ∈ t, p.Prime) →
    ((∏ p ∈ t, p).totient : ℝ) = ∏ p ∈ t, ((p : ℝ) - 1) := by
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | insert p t hpt ih =>
    intro ht
    have hp : p.Prime := ht p (mem_insert_self p t)
    have ht' : ∀ r ∈ t, r.Prime := fun r hr => ht r (mem_insert_of_mem hr)
    have hcop : Nat.Coprime p (∏ r ∈ t, r) := by
      apply Nat.Coprime.prod_right
      intro r hr
      exact (Nat.coprime_primes hp (ht' r hr)).mpr (fun he => hpt (he ▸ hr))
    rw [prod_insert hpt, prod_insert hpt, Nat.totient_mul hcop, Nat.cast_mul, ih ht',
      Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]
    simp

theorem totient_lcm_prod {q : ℕ} {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    ((Nat.lcm q (∏ p ∈ t, p)).totient : ℝ) =
      (q.totient : ℝ) * ∏ p ∈ t with ¬ p ∣ q, ((p : ℝ) - 1) := by
  classical
  have hsplit := prod_filter_mul_prod_filter_not t (fun p => p ∣ q) (fun p => p)
  set A := ∏ p ∈ t with p ∣ q, p
  set B := ∏ p ∈ t with ¬ p ∣ q, p
  have htB : ∀ p ∈ t.filter (fun p => ¬ p ∣ q), p.Prime := fun p hp => ht p (mem_filter.mp hp).1
  have hBq : Nat.Coprime q B := by
    apply Nat.Coprime.prod_right
    intro p hp
    rw [mem_filter] at hp
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (ht p hp.1)).mpr hp.2)
  have hAq : A ∣ q := by
    apply prod_primes_dvd
    · intro p hp; exact (ht p (mem_filter.mp hp).1).prime
    · intro p hp; exact (mem_filter.mp hp).2
  have hAB : Nat.Coprime A B := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro r hr
    rw [mem_filter] at hp hr
    exact (Nat.coprime_primes (ht p hp.1) (ht r hr.1)).mpr (fun he => hr.2 (he ▸ hp.2))
  have hl : Nat.lcm q (∏ p ∈ t, p) = q * B := by
    rw [← hsplit, ← Nat.Coprime.lcm_eq_mul hAB, ← Nat.lcm_assoc, Nat.lcm_eq_left hAq,
      Nat.Coprime.lcm_eq_mul hBq]
  rw [hl, Nat.totient_mul hBq, Nat.cast_mul, totient_prod_primes _ htB]

/-! ### The finite Euler identification -/

/-- The local factor of the paper's `𝔗(n, q, a)` at `p`, verbatim from `T`. -/
noncomputable def tF (n q : ℕ) (a : ℤ) (p : ℕ) : ℝ :=
  if (p ∣ n ∧ ¬ p ∣ q) ∨ (¬ (p : ℤ) ∣ (n - a) ∧ p ∣ q) then 1 - 1 / ((p : ℝ) - 1) ^ 2
  else if ¬ p ∣ n ∧ ¬ p ∣ q then 1 + 1 / ((p : ℝ) - 1) ^ 3
  else (p : ℝ) / ((p : ℝ) - 1)

/-- `𝔗(n, q, a) = φ(q)⁻¹ ∏'_p tF(p)`, by definition. -/
theorem T_eq_tprod (n q : ℕ) (a : ℤ) :
    T n q a = (1 / (Nat.totient q : ℝ)) * ∏' p : Nat.Primes, tF n q a p := rfl

/-- The local term `ℓ_p`, so that `tF(p) = 1 + ℓ_p`. -/
noncomputable def ellT (n q : ℕ) (a : ℤ) (p : ℕ) : ℝ :=
  if p ∣ q then locG n q a p / ((p : ℝ) - 1) ^ 2 else locG n q a p / ((p : ℝ) - 1) ^ 3

theorem tF_eq_one_add {n q : ℕ} {a : ℤ} {p : ℕ} (hp : p.Prime) :
    tF n q a p = 1 + ellT n q a p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold tF ellT locG cPZ
  by_cases hq : p ∣ q <;> by_cases hn : p ∣ n <;> by_cases hna : (p : ℤ) ∣ ((n : ℤ) - a) <;>
    simp only [hq, hn, hna, not_true, not_false_eq_true, and_true, and_false, true_and,
      false_and, or_false, false_or, if_true, if_false] <;> field_simp <;> ring

/-- **THE FINITE EULER IDENTIFICATION.** For `(a, q) = 1` and any finite set `P` of primes,
`∑_{t ⊆ P} 1/φ([q, ∏ t]) ∑_{b ∈ G(a,q,∏ t)} gW n t b = φ(q)⁻¹ ∏_{p ∈ P} tF(p)`. -/
theorem euler_finite {n q : ℕ} {a : ℤ} (hq : 0 < q) (ha : Int.gcd a q = 1) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ t ∈ P.powerset, 1 / ((Nat.lcm q (∏ p ∈ t, p)).totient : ℝ) *
        ∑ b ∈ crtG a q (∏ p ∈ t, p), gW n t b =
      1 / (q.totient : ℝ) * ∏ p ∈ P, tF n q a p := by
  classical
  rw [prod_congr rfl (fun p hp => tF_eq_one_add (hP p hp)), euler_expand, mul_sum]
  apply sum_congr rfl
  intro t htP
  have ht : ∀ p ∈ t, p.Prime := fun p hp => hP p (mem_powerset.mp htP hp)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hne : ∀ p ∈ t, (p : ℝ) - 1 ≠ 0 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (ht p hp).two_le
    linarith
  rw [crtG_sum ha ht, totient_lcm_prod ht]
  have hell : ∏ p ∈ t, ellT n q a p =
      (∏ p ∈ t, locG n q a p / ((p : ℝ) - 1) ^ 2) *
        ∏ p ∈ t with ¬ p ∣ q, (1 / ((p : ℝ) - 1)) := by
    rw [prod_filter, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    unfold ellT
    have := hne p hp
    split_ifs <;> field_simp <;> ring
  rw [hell, prod_div_distrib (s := t.filter _) (f := fun _ => (1 : ℝ)), prod_const_one]
  field_simp

/-! ### Vacuity -/

/-- `euler_finite` at a concrete point: `P = {2, 3}`, `q = 1`, `a = 1`, `n = 7`; the right side
is `tF(2) tF(3) = 2 · (1 + 1/8) = 9/4`. -/
theorem euler_finite_instance :
    1 / ((1 : ℕ).totient : ℝ) * ∏ p ∈ ({2, 3} : Finset ℕ), tF 7 1 1 p = 9 / 4 := by
  rw [prod_insert (by decide), prod_singleton]
  unfold tF
  norm_num

/-- `reduced_sum_squarefree` at `t = {3, 5}`, `n = 10`: the right side is `1 · (-4) = -4`. -/
theorem reduced_sum_instance :
    ∏ p ∈ ({3, 5} : Finset ℕ), (if (p : ℤ) ∣ (10 : ℤ) then -((p : ℝ) - 1) else 1) = -4 := by
  rw [prod_insert (by decide), prod_singleton]
  norm_num

end LeanLab.Halupczok2012
