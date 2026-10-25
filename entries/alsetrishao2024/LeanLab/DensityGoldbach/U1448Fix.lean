module

public import LeanLab.DensityGoldbach.U1446Thm12

/-!
U-1448, run 20261021T2003Z-599, VERIFY of U-1446. A fix: U1446's `AS_Prop31` concludes the strict
`f₁ * f₂(n) > δ³/1000` off an exceptional set, while Alsetri-Shao arXiv 2405.18576v2 Proposition 3.1
prints `f₁ * f₂(n) ≥ δ³/1000`. `AS_Prop31Printed` below has the printed `≥`, is implied by
`AS_Prop31`, and Theorem 1.2 is re-derived from it. The window bound and the main theorem are
copied from U1446Thm12.lean with only the use of Proposition 3.1 changed.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Filter
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1448
open LeanLab.DensityGoldbach.U1446

/-- Alsetri-Shao Proposition 3.1 with the printed conclusion `f₁ * f₂(n) ≥ δ³/1000` for all but
`η N` values, i.e. `#{n : f₁ * f₂(n) < δ³/1000} ≤ η N`. Restricted to prime `N ≥ N₀`, `δ < 1/2`. -/
def AS_Prop31Printed : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ η : ℝ, 0 < η → ∀ p : ℝ, 2 < p → p < 4 → ∀ Mc : ℝ, 1 ≤ Mc →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ f₁ f₂ ν₁ ν₂ : ZMod N → ℝ,
        (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ ν₁ n) → (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ ν₂ n) →
        1 + δ ≤ avg N f₁ + avg N f₂ →
        lpHat N p f₁ ≤ Mc → lpHat N p f₂ ≤ Mc →
        (∀ r, ‖hatE N ν₁ r - (if r = 0 then 1 else 0)‖ ≤ c) →
        (∀ r, ‖hatE N ν₂ r - (if r = 0 then 1 else 0)‖ ≤ c) →
        ((univ.filter (fun n => convE N f₁ f₂ n < δ ^ 3 / 1000)).card : ℝ) ≤ η * N

/-- U1446's form implies the printed form, so the printed form is the weaker cited input. -/
theorem printed_of_U1446 (H : AS_Prop31) : AS_Prop31Printed := by
  intro δ hδ hδ1 η hη p hp hp4 Mc hM
  obtain ⟨c, hc, N₀, h⟩ := H δ hδ hδ1 η hη p hp hp4 Mc hM
  refine ⟨c, hc, N₀, fun N _ hN hN₀ f₁ f₂ ν₁ ν₂ h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  refine le_trans ?_ (h N hN hN₀ f₁ f₂ ν₁ ν₂ h1 h2 h3 h4 h5 h6 h7)
  have hsub : univ.filter (fun n => convE N f₁ f₂ n < δ ^ 3 / 1000) ⊆
      univ.filter (fun n => convE N f₁ f₂ n ≤ δ ^ 3 / 1000) := fun n hn => by
    simp only [mem_filter] at hn ⊢; exact ⟨hn.1, hn.2.le⟩
  exact_mod_cast card_le_card hsub

set_option maxHeartbeats 1600000 in
theorem window_bound (A : Set ℕ) (hA : A ⊆ P) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hdens : ∀ W b : ℕ, 0 < W → Nat.Coprime b W → 1 / 2 + δ ≤ lowerDensityRes A b W)
    (H31 : AS_Prop31Printed) (H62 : Green62) (H66 : Green66) (η : ℝ) (hη : 0 < η) :
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
      have hthr : (0 : ℝ) < (δ / 2) ^ 3 / 1000 := by positivity
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
            lt_of_lt_of_le hthr hgt
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

/-- **Alsetri-Shao 2024, Theorem 1.2, CONDITIONAL ON `AS_Prop31Printed`, `Green62`, `Green66`.** -/
theorem alsetriShao_1_2_of_printed (H31 : AS_Prop31Printed) (H62 : Green62) (H66 : Green66) :
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

end LeanLab.DensityGoldbach.U1448

