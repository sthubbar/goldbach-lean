module

public import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218

/-!
Journal pages 777 to 779, displays 20, 28 and 30.
The divisor tail is controlled by the Romanov series and a product remainder.
This adapts the lab D4Product, D4Support and D4SingleBound proofs to the sealed encoding.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007.Tail383

open Finset Real Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Journal page 778 display 28. Single exponent divisibility count. -/
def oneCount (d M m : ℕ) : ℕ := #{a ∈ Icc 1 M | d ∣ m - 2 ^ a}

/-- Journal page 777 display 20. The period error is paid only when a divisor occurs. -/
theorem oneCount_bound {d : ℕ} (hd : Odd d) (M m : ℕ)
    (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m) :
    (oneCount d M m : ℝ) ≤ (M : ℝ) / xi d + if 0 < oneCount d M m then 1 else 0 := by
  classical
  by_cases hc : oneCount d M m = 0
  · simpa [hc] using (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg (xi d)) :
      (0 : ℝ) ≤ (M : ℝ) / xi d)
  have hc0 : 0 < oneCount d M m := by omega
  rw [ite_eq_left hc0]
  have hn : oneCount d M m ≤ M / xi d + 1 := by
    have he : oneCount d M m = #{a ∈ Icc 1 M | 2 ^ a < m ∧ d ∣ m - 2 ^ a} := by
      unfold oneCount
      congr 1
      apply filter_congr
      intro a ha
      exact ⟨fun h => ⟨hpow a ha, h⟩, fun h => h.2⟩
    rw [he]
    exact card_nu_le hd hd.pos M m
  calc (oneCount d M m : ℝ) ≤ ((M / xi d + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    _ ≤ (M : ℝ) / xi d + 1 := by
      push_cast
      linarith [Nat.cast_div_le (m := M) (n := xi d) (α := ℝ)]

/-- The Euler product error is at most delta times L when L is sufficiently large. -/
theorem product_weight_small (V : Finset ℕ) (n : ℕ → ℕ) {X L δ : ℝ}
    (_hX : 0 < X) (hδ : 0 < δ) (hlog : log X = L * log 2)
    (hn : ∀ v ∈ V, n v ≠ 0) (hnX : ∀ v ∈ V, (n v : ℝ) ≤ X)
    (hcard : (V.card : ℝ) ≤ L)
    (hL : (6 * exp 27 / δ) ^ 2 + 1 ≤ L) :
    ∑ s ∈ (opf (∏ v ∈ V, n v)).powerset,
      W s ≤ δ * L := by
  classical
  let P := ∏ v ∈ V, n v
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * exp 27 / δ)]
  have hPX : (P : ℝ) ≤ X ^ V.card := by
    dsimp [P]
    rw [Nat.cast_prod, ← prod_const]
    exact prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hnX
  have hω : (P.primeFactors.card : ℝ) ≤ L ^ 2 := by
    have h2 : (2 : ℝ) ^ P.primeFactors.card ≤ X ^ V.card :=
      (show (2 : ℝ) ^ P.primeFactors.card ≤ (P : ℝ) by
        exact_mod_cast LeanLab.Romanov.two_pow_card_le P hP0).trans hPX
    have h4 := log_le_log (by positivity) h2
    rw [log_pow, log_pow, hlog] at h4
    have hωL : (P.primeFactors.card : ℝ) ≤ V.card * L := by
      have hl2 := log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    nlinarith
  let Y := ⌈L ^ 2⌉₊ + 4
  have hY : 4 ≤ Y := by omega
  have hωY : P.primeFactors.card ≤ Y := by
    have : (P.primeFactors.card : ℝ) ≤ (⌈L ^ 2⌉₊ : ℕ) := hω.trans (Nat.le_ceil _)
    have : P.primeFactors.card ≤ ⌈L ^ 2⌉₊ := by exact_mod_cast this
    omega
  have hlogY : log (Y : ℝ) ≤ 2 + 4 * √L := by
    apply le_trans _ (log_sq_add_le L hL1)
    apply log_le_log (by positivity)
    dsimp [Y]
    push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ L ^ 2)]
  exact (sum_W_opf_le P Y hY hωY).trans
    (aux_third (exp 27) δ L (log Y) (exp_pos _) hδ hL hlogY)

/-- Every occurring squarefree divisor divides the product of the positive differences. -/
theorem support_sum_le (F : Finset ℕ) (M m : ℕ)
    (hF : ∀ d ∈ F, OddSqf d) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m) :
    ∑ d ∈ F.filter (fun d => 0 < oneCount d M m), fd d ≤
      ∑ s ∈ (opf (∏ a ∈ Icc 1 M, (m - 2 ^ a))).powerset,
        W s := by
  classical
  let P := ∏ a ∈ Icc 1 M, (m - 2 ^ a)
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 (fun a ha => by have := hpow a ha; omega)
  have hinj : Set.InjOn Nat.primeFactors (↑(F.filter (fun d => 0 < oneCount d M m))) := by
    intro a ha b hb hab
    have ha' := (hF a (mem_filter.1 ha).1).2.2
    have hb' := (hF b (mem_filter.1 hb).1).2.2
    rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb', hab]
  have hsub : (F.filter (fun d => 0 < oneCount d M m)).image Nat.primeFactors ⊆
      (opf P).powerset := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hs
    obtain ⟨hdF, hcnt⟩ := mem_filter.1 hd
    have ho := hF d hdF
    obtain ⟨a, ha⟩ := card_pos.1 hcnt
    obtain ⟨haI, hda⟩ := mem_filter.1 ha
    have hdP : d ∣ P := hda.trans (dvd_prod_of_mem (fun a => m - 2 ^ a) haI)
    rw [mem_powerset]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp3 : 2 < p := by
      have hne : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 ho.2.1) (even_iff_two_dvd.2 hpd)
      have := hpp.two_le
      omega
    exact mem_filter.2 ⟨Nat.primeFactors_mono hdP hP0 hp, hp3⟩
  refine sum_le_sum_of_injOn Nat.primeFactors hinj hsub ?_ ?_
  · intro d hd
    exact le_of_eq (fd_eq (hF d (mem_filter.1 hd).1))
  · intro s hs _
    exact W_nonneg (fun p hp => (mem_filter.1 (mem_powerset.1 hs hp)).2)

/-- Sum the single exponent estimate before applying the product bound. -/
theorem weighted_one_le (F : Finset ℕ) (M m : ℕ)
    (hF : ∀ d ∈ F, OddSqf d) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m) :
    ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤
      (M : ℝ) * ∑ d ∈ F, seriesTerm d +
      ∑ s ∈ (opf (∏ a ∈ Icc 1 M, (m - 2 ^ a))).powerset,
        W s := by
  classical
  have hmain : ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤
      (M : ℝ) * ∑ d ∈ F, seriesTerm d +
      ∑ d ∈ F.filter (fun d => 0 < oneCount d M m), fd d := by
    calc ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤
        ∑ d ∈ F, fd d * ((M : ℝ) / xi d + if 0 < oneCount d M m then 1 else 0) :=
          sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left
            (oneCount_bound (hF d hd).2.1 M m hpow) (fd_nonneg (hF d hd)))
      _ = _ := by
        rw [mul_sum, sum_filter, ← sum_add_distrib]
        apply sum_congr rfl
        intro d hd
        rw [seriesTerm, ite_eq_left (hF d hd)]
        split_ifs <;> ring
  have hs := support_sum_le F M m hF hpow
  linarith

/-- The single exponent tail is at most two times delta times L. -/
theorem weighted_one_small (F : Finset ℕ) (M m : ℕ) {X L δ : ℝ}
    (hF : ∀ d ∈ F, OddSqf d) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m)
    (hX : 0 < X) (hδ : 0 < δ) (hlog : log X = L * log 2)
    (hmX : (m : ℝ) ≤ X) (hM : (M : ℝ) ≤ L)
    (hcoeff : ∑ d ∈ F, seriesTerm d ≤ δ)
    (hL : (6 * exp 27 / δ) ^ 2 + 1 ≤ L) :
    ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤ 2 * δ * L := by
  classical
  have hprod := product_weight_small (Icc 1 M) (fun a => m - 2 ^ a) hX hδ hlog
    (fun a ha => by have := hpow a ha; omega)
    (fun a _ => (show ((m - 2 ^ a : ℕ) : ℝ) ≤ m by exact_mod_cast Nat.sub_le m (2 ^ a)).trans hmX)
    (by simpa using hM) hL
  have hmain := weighted_one_le F M m hF hpow
  have hcoeff' : (M : ℝ) * ∑ d ∈ F, seriesTerm d ≤ δ * L := by
    calc (M : ℝ) * ∑ d ∈ F, seriesTerm d ≤ M * δ :=
        mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
      _ ≤ L * δ := mul_le_mul_of_nonneg_right hM hδ.le
      _ = δ * L := mul_comm _ _
  linarith

/-- Journal page 777 display 20. Fix all tuple coordinates except one,
then sum the single exponent divisibility counts. -/
theorem count_succ_eq (d j M N : ℕ) :
    (#{ν ∈ exponentTuples131 (j + 1) M | d ∣ N - tuplePower131 ν} : ℝ) =
      ∑ t ∈ exponentTuples131 j M, (oneCount d M (N - tuplePower131 t) : ℝ) := by
  classical
  have hpi : exponentTuples131 (j + 1) M =
      ((Icc 1 M) ×ˢ exponentTuples131 j M).map
        (Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding := by
    have := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (j + 1) => Icc 1 M)
      (fun _ => True)
    simp only [Finset.filter_true] at this
    exact this
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hpi, sum_map, sum_product_right]
  apply sum_congr rfl
  intro t _
  unfold oneCount
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro a _
  have he : tuplePower131 ((Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding (a, t)) =
      2 ^ a + tuplePower131 t := by
    simp only [tuplePower131, Equiv.toEmbedding_apply, Fin.consEquiv_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [he, show N - (2 ^ a + tuplePower131 t) = (N - tuplePower131 t) - 2 ^ a by omega]

/-- Journal pages 777 to 779, displays 20, 22 and 28 to 30.
The actual tuple count over every sufficiently large divisor cutoff is small.
The coefficient tail and product remainder are bounded separately. -/
theorem uniform_count_tail (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      ∑ d ∈ (Ico D (N + 1)).filter OddSqf,
        fd d * (#{ν ∈ tuples131 k X | d ∣ N - tuplePower131 ν} : ℝ) ≤ ε * Lg X ^ k := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let δ := ε / 2
  have hδ : 0 < δ := by positivity
  obtain ⟨D₀, hD₀⟩ := ((tendsto_order.1 (tendsto_sum_nat_add seriesTerm)).2 δ hδ).exists_forall_of_atTop
  refine ⟨D₀, fun D hD => ?_⟩
  have hLg : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := (hLg.eventually_ge_atTop ((6 * exp 27 / δ) ^ 2 + 1)).exists_forall_of_atTop
  obtain ⟨X₂, hX₂⟩ := tuple_window131 (j + 1)
  refine ⟨max X₁ (max X₂ 2), fun X hX N hN => ?_⟩
  obtain ⟨hL1, hw⟩ := hX₂ X (by omega)
  have hLδ := hX₁ X (by omega)
  let L := Lg X
  let M := ⌊Lg X - √(Lg X)⌋₊
  have hM : (M : ℝ) ≤ L := by
    have hs : √L ≤ L := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
    have hfloor : (M : ℝ) ≤ L - √L := Nat.floor_le (by linarith)
    linarith [Real.sqrt_nonneg L]
  let F := (Ico D (N + 1)).filter OddSqf
  have hF : ∀ d ∈ F, OddSqf d := fun d hd => (mem_filter.mp hd).2
  have hFd : ∀ d ∈ F, D ≤ d := fun d hd => (mem_Ico.mp (mem_filter.mp hd).1).1
  have hcoeff : ∑ d ∈ F, seriesTerm d ≤ δ := by
    have hs : Summable (fun n => seriesTerm (n + D)) := (summable_nat_add_iff D).mpr lemma61_proved
    have he : ∑ d ∈ F, seriesTerm d = ∑ n ∈ F.image (fun d => d - D), seriesTerm (n + D) := by
      rw [sum_image]
      · apply sum_congr rfl
        intro d hd
        rw [Nat.sub_add_cancel (hFd d hd)]
      · intro a ha b hb hab
        have := hFd a ha
        have := hFd b hb
        change a - D = b - D at hab
        omega
    rw [he]
    exact (hs.sum_le_tsum _ (fun n _ => seriesTerm_nonneg _)).trans (hD₀ D hD).le
  obtain ⟨hN1, hNX, _, hNJ⟩ := evenJ_nat131 hN
  have hsmall : ∀ ν ∈ exponentTuples131 (j + 1) M, tuplePower131 ν < N := by
    intro ν hν
    have hp := tuplePower_le131 hν
    have h6 : 6 * tuplePower131 ν ≤ X := by
      calc 6 * tuplePower131 ν ≤ 6 * ((j + 1) * 2 ^ M) := Nat.mul_le_mul_left _ hp
        _ = 6 * (j + 1) * 2 ^ M := by ring
        _ ≤ X := hw
    omega
  have hlog : log (X : ℝ) = L * log 2 := by
    dsimp [L, Lg, Real.logb]
    field_simp
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hsingle : ∀ t ∈ exponentTuples131 j M,
      ∑ d ∈ F, fd d * (oneCount d M (N - tuplePower131 t) : ℝ) ≤ ε * L := by
    intro t ht
    have hpow : ∀ a ∈ Icc 1 M, 2 ^ a < N - tuplePower131 t := by
      intro a ha
      have hcons : (Fin.cons a t : Fin (j + 1) → ℕ) ∈ exponentTuples131 (j + 1) M := by
        simp only [exponentTuples131, Fintype.mem_piFinset] at ht ⊢
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa using ha
        · simpa using ht i
      have hp := hsmall _ hcons
      have he : tuplePower131 (Fin.cons a t) = 2 ^ a + tuplePower131 t := by
        simp [tuplePower131, Fin.sum_univ_succ]
      rw [he] at hp
      omega
    have hmX : ((N - tuplePower131 t : ℕ) : ℝ) ≤ X := by exact_mod_cast (Nat.sub_le N _).trans hNX
    have h := weighted_one_small F M (N - tuplePower131 t) hF hpow hXpos hδ hlog hmX hM hcoeff hLδ
    dsimp [δ] at h
    linarith
  change ∑ d ∈ F, fd d * (#{ν ∈ exponentTuples131 (j + 1) M | d ∣ N - tuplePower131 ν} : ℝ) ≤
    ε * L ^ (j + 1)
  simp_rw [count_succ_eq, mul_sum]
  rw [sum_comm]
  calc ∑ t ∈ exponentTuples131 j M, ∑ d ∈ F, fd d * (oneCount d M (N - tuplePower131 t) : ℝ)
      ≤ ∑ _t ∈ exponentTuples131 j M, ε * L := sum_le_sum hsingle
    _ = (M : ℝ) ^ j * (ε * L) := by rw [sum_const, nsmul_eq_mul, exponentTuples_card131, Nat.cast_pow]
    _ ≤ L ^ j * (ε * L) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hM _) (mul_nonneg hε.le (by dsimp [L]; linarith))
    _ = ε * L ^ (j + 1) := by ring


end

end LeanLab.LPZ2007.Tail383

