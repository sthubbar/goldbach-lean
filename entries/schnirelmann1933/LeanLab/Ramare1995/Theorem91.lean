module

public import LeanLab.Ramare1995.Section9

/-!
Ramaré 1995, On Šnirel'man's constant, Ann. Sc. Norm. Pisa 22, 645-706, P0008.
Theorem 9.1 (Deshouillers' effective Ostmann theorem), page 701-703, and the
covering case of Dyson's theorem that its proof invokes.
Dyson's theorem follows Dyson 1945 as presented in M. B. Nathanson, "Additive number theory
and the Dyson transform", arXiv:2407.12253v4, Sections 3-5, specialised to `γ = 1`, rank `h`.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0803Z-2223. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.Ramare1995.Theorem91
open LeanLab.Ramare1995.Section9

/-! ### Counting function facts -/

lemma cnt_zero (A : Set ℕ) : cnt A 0 = 0 := by simp [cnt]

lemma cnt_split (A : Set ℕ) {k m : ℕ} (h : k ≤ m) :
    cnt A m = cnt A k + #{x ∈ Ioc k m | x ∈ A} := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · congr 1; ext a; simp only [mem_filter, mem_union, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hk : a ≤ k
      · exact Or.inl ⟨⟨h1, hk⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  · rw [disjoint_left]; intro a h1 h2
    simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2; omega

lemma cnt_mono_set {A B : Set ℕ} (h : A ⊆ B) (m : ℕ) : cnt A m ≤ cnt B m := by
  unfold cnt
  exact card_le_card (fun x hx => by
    simp only [mem_filter] at hx ⊢; exact ⟨hx.1, h hx.2⟩)

lemma cnt_mono (A : Set ℕ) {k m : ℕ} (h : k ≤ m) : cnt A k ≤ cnt A m := by
  rw [cnt_split A h]; omega

lemma cnt_le (A : Set ℕ) (m : ℕ) : cnt A m ≤ m := by
  unfold cnt
  calc #{a ∈ Icc 1 m | a ∈ A} ≤ #(Icc 1 m) := card_filter_le _ _
    _ = m := by simp

lemma cnt_eq_zero {A : Set ℕ} {m : ℕ} (h : ∀ x, 1 ≤ x → x ≤ m → x ∉ A) : cnt A m = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x hx; simp only [mem_Icc] at hx; exact h x hx.1 hx.2

lemma cnt_pos {A : Set ℕ} {m c : ℕ} (hc : c ∈ A) (h1 : 1 ≤ c) (h2 : c ≤ m) : 1 ≤ cnt A m := by
  unfold cnt
  rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
  exact ⟨c, by simp [hc, h1, h2]⟩

lemma cnt_diff {B T : Set ℕ} (hT : T ⊆ B) (m : ℕ) : cnt (B \ T) m + cnt T m = cnt B m := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · congr 1; ext a; simp only [mem_filter, mem_union, Set.mem_sdiff]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨h1, hT h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : a ∈ T
      · exact Or.inr ⟨h1, h3⟩
      · exact Or.inl ⟨h1, h2, h3⟩
  · rw [disjoint_left]; intro a h1 h2
    simp only [mem_filter, Set.mem_sdiff] at h1 h2; exact h1.2.2 h2.2

lemma cnt_sub_le (S : Set ℕ) (m k : ℕ) : cnt S m ≤ cnt S (m - k) + k := by
  rw [cnt_split S (Nat.sub_le m k)]
  have : #{x ∈ Ioc (m - k) m | x ∈ S} ≤ k :=
    (card_filter_le _ _).trans (by simp; omega)
  omega

/-- The last point. -/
lemma cnt_last {A : Set ℕ} {n : ℕ} (hn : 1 ≤ n) (h : n ∉ A) : cnt A n ≤ n - 1 := by
  rw [cnt_split A (Nat.sub_le n 1)]
  have : #{x ∈ Ioc (n - 1) n | x ∈ A} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x hx; simp only [mem_Ioc] at hx
    have : x = n := by omega
    rwa [this]
  have := cnt_le A (n - 1)
  omega

/-! ### Sums over `range` changed at one or two indices -/

lemma sum_two {s : Finset ℕ} {f g : ℕ → ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (h : ∀ i ∈ s, i ≠ a → i ≠ b → f i = g i) :
    ∑ i ∈ s, f i + (g a + g b) = ∑ i ∈ s, g i + (f a + f b) := by
  have hb' : b ∈ s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  rw [← add_sum_erase s f ha, ← add_sum_erase s g ha, ← add_sum_erase _ f hb',
    ← add_sum_erase _ g hb']
  have : ∑ i ∈ (s.erase a).erase b, f i = ∑ i ∈ (s.erase a).erase b, g i := by
    apply sum_congr rfl
    intro i hi
    simp only [mem_erase] at hi
    exact h i hi.2.2 hi.2.1 hi.1
  rw [this]; ring

lemma sum_one {s : Finset ℕ} {f g : ℕ → ℕ} {a : ℕ} (ha : a ∈ s)
    (h : ∀ i ∈ s, i ≠ a → f i = g i) :
    ∑ i ∈ s, f i + g a = ∑ i ∈ s, g i + f a := by
  rw [← add_sum_erase s f ha, ← add_sum_erase s g ha]
  have : ∑ i ∈ s.erase a, f i = ∑ i ∈ s.erase a, g i := by
    apply sum_congr rfl
    intro i hi
    simp only [mem_erase] at hi
    exact h i hi.2 hi.1
  rw [this]; ring

/-! ### Dyson's theorem, covering case

Families are `A : ℕ → Set ℕ`, of which the first `k` sets are used. `Rep A k p`: `p` is a sum
`f 0 + ⋯ + f (k-1)` with `f i ∈ A i ∪ {0}`. -/

def Rep (A : ℕ → Set ℕ) (k p : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < k, f i = 0 ∨ f i ∈ A i) ∧ ∑ i ∈ range k, f i = p

/-- The rank one counting function `A_0(m) + ⋯ + A_{k-1}(m)`. -/
noncomputable def phi (A : ℕ → Set ℕ) (k m : ℕ) : ℕ := ∑ i ∈ range k, cnt (A i) m

/-- Dyson's hypothesis with `γ = 1` on `[1, n]`. -/
def DysonHyp (A : ℕ → Set ℕ) (k n : ℕ) : Prop := ∀ m, 1 ≤ m → m ≤ n → m ≤ phi A k m

section transform
variable (A : ℕ → Set ℕ) (h n : ℕ)

/-- Dyson triple for the family `A 0, …, A (h+1)`, the last set being `A (h+1)`. -/
def Trip (a ℓ c : ℕ) : Prop :=
  ℓ ≤ h ∧ (a = 0 ∨ a ∈ A ℓ) ∧ a ≤ n ∧ c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ n ∧
    (c + a ≤ n → c + a ∉ A ℓ)

/-- The set `T(a, ℓ)`. -/
def Tset (a ℓ : ℕ) : Set ℕ :=
  {c | c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ n ∧ (c + a ≤ n → c + a ∉ A ℓ)}

/-- `T + a`. -/
def Tsh (a ℓ : ℕ) : Set ℕ := {x | a ≤ x ∧ x - a ∈ Tset A h n a ℓ}

/-- The Dyson transform. -/
def tr (a ℓ : ℕ) : ℕ → Set ℕ := fun i =>
  if i = h + 1 then A (h + 1) \ Tset A h n a ℓ
  else if i = ℓ then A ℓ ∪ Tsh A h n a ℓ else A i

end transform

lemma tr_last (A : ℕ → Set ℕ) (h n a ℓ : ℕ) :
    tr A h n a ℓ (h + 1) = A (h + 1) \ Tset A h n a ℓ := by simp [tr]

lemma tr_l (A : ℕ → Set ℕ) {h n a ℓ : ℕ} (hℓ : ℓ ≤ h) :
    tr A h n a ℓ ℓ = A ℓ ∪ Tsh A h n a ℓ := by
  simp [tr, show ℓ ≠ h + 1 by omega]

lemma tr_ne (A : ℕ → Set ℕ) {h n a ℓ i : ℕ} (h1 : i ≠ h + 1) (h2 : i ≠ ℓ) :
    tr A h n a ℓ i = A i := by simp [tr, h1, h2]

/-- Lemma 1 of Nathanson: sums of the transformed family below `n` are sums of the family. -/
lemma rep_back {A : ℕ → Set ℕ} {h n a ℓ p : ℕ} (hℓ : ℓ ≤ h) (ha : a = 0 ∨ a ∈ A ℓ)
    (hp : p ≤ n) (hr : Rep (tr A h n a ℓ) (h + 2) p) : Rep A (h + 2) p := by
  obtain ⟨f, hf, hs⟩ := hr
  have hne : ℓ ≠ h + 1 := by omega
  have hmemL : h + 1 ∈ range (h + 2) := mem_range.2 (by omega)
  have hmeml : ℓ ∈ range (h + 2) := mem_range.2 (by omega)
  have htwo : f ℓ + f (h + 1) ≤ p := by
    rw [← hs, ← add_sum_erase _ f hmeml, ← add_sum_erase _ f (mem_erase.2 ⟨hne.symm, hmemL⟩)]
    omega
  have hL := hf (h + 1) (by omega)
  have hl := hf ℓ (by omega)
  rw [tr_last] at hL
  rw [tr_l A hℓ] at hl
  have hy : f (h + 1) = 0 ∨ f (h + 1) ∈ A (h + 1) := by
    rcases hL with h0 | h0
    · exact Or.inl h0
    · exact Or.inr h0.1
  have hother : ∀ i < h + 2, i ≠ h + 1 → i ≠ ℓ → f i = 0 ∨ f i ∈ A i := by
    intro i hi h1 h2
    have := hf i hi; rwa [tr_ne A h1 h2] at this
  rcases hl with hx | hx | hx
  · refine ⟨f, fun i hi => ?_, hs⟩
    by_cases h1 : i = h + 1
    · subst h1; exact hy
    by_cases h2 : i = ℓ
    · subst h2; exact Or.inl hx
    · exact hother i hi h1 h2
  · refine ⟨f, fun i hi => ?_, hs⟩
    by_cases h1 : i = h + 1
    · subst h1; exact hy
    by_cases h2 : i = ℓ
    · subst h2; exact Or.inr hx
    · exact hother i hi h1 h2
  · obtain ⟨hax, hT⟩ := hx
    have hay : a + f (h + 1) = 0 ∨ a + f (h + 1) ∈ A ℓ := by
      rcases hL with h0 | ⟨h0, h0'⟩
      · rw [h0, add_zero]; exact ha
      · by_cases hy0 : f (h + 1) = 0
        · rw [hy0, add_zero]; exact ha
        · right
          have hnT : ¬ (f (h + 1) + a ≤ n → f (h + 1) + a ∉ A ℓ) := by
            intro hc; exact h0' ⟨h0, by omega, by omega, hc⟩
          push Not at hnT
          rw [add_comm]; exact hnT.2
    set g : ℕ → ℕ := Function.update (Function.update f ℓ (a + f (h + 1))) (h + 1) (f ℓ - a)
      with hg
    have g1 : g (h + 1) = f ℓ - a := by simp [hg]
    have g2 : g ℓ = a + f (h + 1) := by simp [hg, hne]
    have g3 : ∀ i, i ≠ h + 1 → i ≠ ℓ → g i = f i := by
      intro i h1 h2; simp [hg, h1, h2]
    refine ⟨g, fun i hi => ?_, ?_⟩
    · by_cases h1 : i = h + 1
      · subst h1; rw [g1]; exact Or.inr hT.1
      by_cases h2 : i = ℓ
      · subst h2; rw [g2]; exact hay
      · rw [g3 i h1 h2]; exact hother i hi h1 h2
    · have := sum_two (f := f) (g := g) hmeml hmemL hne
        (fun i _ h1 h2 => (g3 i h2 h1).symm)
      rw [g1, g2] at this
      omega

/-- `B(m) + T(m - a) ≤ (B ∪ (T + a))(m)` when `T + a` misses `B` below `n`. -/
lemma cnt_union_shift (B T : Set ℕ) (a m n : ℕ) (hm : m ≤ n)
    (hT : ∀ c ∈ T, c + a ≤ n → c + a ∉ B) :
    cnt B m + cnt T (m - a) ≤ cnt (B ∪ {x | a ≤ x ∧ x - a ∈ T}) m := by
  unfold cnt
  have hinj : #(({c ∈ Icc 1 (m - a) | c ∈ T}).image (· + a)) = #{c ∈ Icc 1 (m - a) | c ∈ T} :=
    card_image_of_injective _ (add_left_injective a)
  rw [← hinj, ← card_union_of_disjoint]
  · apply card_le_card
    intro x hx
    simp only [mem_union, mem_filter, mem_image, mem_Icc] at hx ⊢
    rcases hx with ⟨⟨h1, h2⟩, h3⟩ | ⟨c, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    · exact ⟨⟨h1, h2⟩, Or.inl h3⟩
    · refine ⟨⟨by omega, by omega⟩, Or.inr ⟨by omega, ?_⟩⟩
      simpa using h3
  · rw [disjoint_left]
    intro x h1 h2
    simp only [mem_filter, mem_image, mem_Icc] at h1 h2
    obtain ⟨c, ⟨⟨c1, c2⟩, c3⟩, rfl⟩ := h2
    exact hT c c3 (by omega) h1.2

/-- Lemma 6 of Nathanson, counting form. -/
lemma cnt_shift_lower (B : Set ℕ) {c m : ℕ} (hc : 1 ≤ c) (hcm : c ≤ m)
    (hB : ∀ a, a ≤ m - c → (a = 0 ∨ a ∈ B) → a + c ∈ B) :
    cnt B (m - c) + 1 + cnt B (c - 1) ≤ cnt B m := by
  rw [cnt_split B (show c - 1 ≤ m by omega)]
  have e : #{a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B} = cnt B (m - c) + 1 := by
    unfold cnt
    have : ({a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B} : Finset ℕ) =
        insert 0 {a ∈ Icc 1 (m - c) | a ∈ B} := by
      ext x; simp only [mem_filter, mem_range, mem_insert, mem_Icc]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact Or.inl h2
        · by_cases hx : x = 0
          · exact Or.inl hx
          · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
      · rintro (h1 | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨by omega, Or.inl h1⟩
        · exact ⟨by omega, Or.inr h3⟩
    rw [this, card_insert_of_notMem (by simp)]
  have hinj : #(({a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B}).image (· + c)) =
      #{a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B} :=
    card_image_of_injective _ (add_left_injective c)
  have hsub : ({a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B}).image (· + c) ⊆
      {x ∈ Ioc (c - 1) m | x ∈ B} := by
    intro x hx
    simp only [mem_image, mem_filter, mem_range] at hx
    obtain ⟨a, ⟨h1, h2⟩, rfl⟩ := hx
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hB a (by omega) h2⟩
  have := card_le_card hsub
  omega

/-- Theorem 6 of Nathanson with `γ = δ = 1`: a minimal Dyson transform keeps the hypothesis. -/
lemma hyp_tr {A : ℕ → Set ℕ} {h n a₀ ℓ₀ : ℕ} (hℓ : ℓ₀ ≤ h)
    (hmin : ∀ a < a₀, ∀ ℓ c, ¬ Trip A h n a ℓ c) (hyp : DysonHyp A (h + 2) n) :
    DysonHyp (tr A h n a₀ ℓ₀) (h + 2) n := by
  set T := Tset A h n a₀ ℓ₀ with hTdef
  set ψ : ℕ → ℕ := fun m => phi A (h + 1) m with hψ
  have hTsub : T ⊆ A (h + 1) := fun c hc => hc.1
  have F1 : ∀ m, phi A (h + 2) m = ψ m + cnt (A (h + 1)) m := by
    intro m; simp [hψ, phi, sum_range_succ]
  have F2 : ∀ m, phi (tr A h n a₀ ℓ₀) (h + 2) m =
      phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A (h + 1) \ T) m := by
    intro m; simp only [phi, sum_range_succ (n := h + 1), tr_last, hTdef]
  have F3 : ∀ m, phi (tr A h n a₀ ℓ₀) (h + 1) m + cnt (A ℓ₀) m =
      ψ m + cnt (A ℓ₀ ∪ Tsh A h n a₀ ℓ₀) m := by
    intro m
    have := sum_one (s := range (h + 1)) (f := fun i => cnt (tr A h n a₀ ℓ₀ i) m)
      (g := fun i => cnt (A i) m) (a := ℓ₀) (mem_range.2 (by omega))
      (fun i hi h2 => by rw [tr_ne A (by simp at hi; omega) h2])
    simpa [phi, hψ, tr_l A hℓ] using this
  have F4 : ∀ m, m ≤ n → cnt (A ℓ₀) m + cnt T (m - a₀) ≤ cnt (A ℓ₀ ∪ Tsh A h n a₀ ℓ₀) m := by
    intro m hm
    exact cnt_union_shift (A ℓ₀) T a₀ m n hm (fun c hc => hc.2.2.2)
  have F5 : ∀ m, cnt (A (h + 1) \ T) m + cnt T m = cnt (A (h + 1)) m :=
    fun m => cnt_diff hTsub m
  -- Lemma 6, summed
  have L6 : ∀ m c, c ∈ A (h + 1) → 1 ≤ c → m - a₀ < c → c ≤ m → m ≤ n →
      ψ (m - c) + (h + 1) + ψ (c - 1) ≤ ψ m := by
    intro m c hc hc1 hca hcm hmn
    have each : ∀ ℓ ∈ range (h + 1),
        cnt (A ℓ) (m - c) + 1 + cnt (A ℓ) (c - 1) ≤ cnt (A ℓ) m := by
      intro ℓ hℓ'
      simp only [mem_range] at hℓ'
      apply cnt_shift_lower (A ℓ) hc1 hcm
      intro a ha hmem
      by_contra hno
      apply hmin a (by omega) ℓ c
      exact ⟨by omega, hmem, by omega, hc, hc1, by omega, fun _ => by rwa [add_comm]⟩
    have := sum_le_sum each
    simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one] at this
    simp only [hψ, phi]; omega
  -- no deficiency below `a₀`
  have Z : ∀ z, z < a₀ → z ≤ n → z ≤ ψ z := by
    intro z
    induction z using Nat.strong_induction_on with
    | _ z ih =>
      intro hz hzn
      by_cases hc : ∃ c, c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ z
      · obtain ⟨c, hc, hc1, hcz⟩ := hc
        have := L6 z c hc hc1 (by omega) hcz hzn
        have i1 := ih (z - c) (by omega) (by omega) (by omega)
        have i2 := ih (c - 1) (by omega) (by omega) (by omega)
        omega
      · push Not at hc
        have h0 : cnt (A (h + 1)) z = 0 := cnt_eq_zero (fun x h1 h2 hx => by
          have := hc x hx h1; omega)
        rcases Nat.eq_zero_or_pos z with rfl | hzpos
        · omega
        · have := hyp z hzpos hzn
          rw [F1, h0] at this; omega
  intro m hm1 hmn
  rw [F2]
  have f3 := F3 m
  have f4 := F4 m hmn
  have f5 := F5 m
  by_cases hb : ∃ b, b ∈ A (h + 1) ∧ m - a₀ < b ∧ b ≤ m
  · set b := Nat.find hb with hbdef
    obtain ⟨hbA, hb1, hb2⟩ := Nat.find_spec hb
    have F7 : cnt T m + cnt (A (h + 1)) (b - 1) ≤ cnt (A (h + 1)) m + cnt T (m - a₀) := by
      rw [cnt_split T (show m - a₀ ≤ m by omega),
        cnt_split (A (h + 1)) (show b - 1 ≤ m by omega)]
      have : #{x ∈ Ioc (m - a₀) m | x ∈ T} ≤ #{x ∈ Ioc (b - 1) m | x ∈ A (h + 1)} := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_Ioc] at hx ⊢
        have hxA := hTsub hx.2
        have : b ≤ x := Nat.find_min' hb ⟨hxA, hx.1.1, hx.1.2⟩
        exact ⟨⟨by omega, hx.1.2⟩, hxA⟩
      omega
    have l6 := L6 m b hbA (by omega) hb1 hb2 hmn
    have z := Z (m - b) (by omega) (by omega)
    have hb0 : b - 1 ≤ ψ (b - 1) + cnt (A (h + 1)) (b - 1) := by
      rcases Nat.eq_zero_or_pos (b - 1) with h0 | h0
      · omega
      · have := hyp (b - 1) h0 (by omega); rw [F1] at this; exact this
    omega
  · push Not at hb
    have F6 : cnt T m ≤ cnt T (m - a₀) := by
      rw [cnt_split T (show m - a₀ ≤ m by omega)]
      have : #{x ∈ Ioc (m - a₀) m | x ∈ T} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro x hx hxT
        simp only [mem_Ioc] at hx
        have := hb x (hTsub hxT) hx.1; omega
      omega
    have := hyp m hm1 hmn
    rw [F1] at this
    omega

/-- **Dyson's theorem, covering case** (`γ = 1`, rank `h`): if `0 ∈`-padded sets
`A 0, …, A (h-1)` satisfy `A_0(m) + ⋯ + A_{h-1}(m) ≥ m` for `1 ≤ m ≤ n`, then `n` is a sum
`a_0 + ⋯ + a_{h-1}` with `a_i ∈ A_i ∪ {0}`. Stated for `h + 1` sets. -/
theorem dyson : ∀ (h n : ℕ) (A : ℕ → Set ℕ), DysonHyp A (h + 1) n → Rep A (h + 1) n := by
  intro h
  induction h with
  | zero =>
    intro n A hyp
    refine ⟨fun _ => n, fun i hi => ?_, by simp⟩
    have hi0 : i = 0 := by omega
    subst hi0
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      by_contra hnA
      have h1 := hyp n (by omega) le_rfl
      have h2 := cnt_last (A := A 0) (n := n) (by omega) hnA
      simp [phi] at h1
      omega
  | succ h ih =>
    intro n
    suffices H : ∀ k (A : ℕ → Set ℕ), cnt (A (h + 1)) n = k → DysonHyp A (h + 2) n →
        Rep A (h + 2) n from fun A hyp => H _ A rfl hyp
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro A hk hyp
      by_cases hc : ∃ c, c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ n
      · obtain ⟨c, hcA, hc1, hcn⟩ := hc
        have hex : ∃ a, ∃ ℓ c, Trip A h n a ℓ c := by
          set a := Nat.findGreatest (fun a => a = 0 ∨ a ∈ A 0) n with ha
          have hP : a = 0 ∨ a ∈ A 0 := by
            rcases Nat.eq_zero_or_pos a with h0 | h0
            · exact Or.inl h0
            · exact Nat.findGreatest_of_ne_zero rfl h0.ne'
          refine ⟨a, 0, c, by omega, hP, Nat.findGreatest_le n, hcA, hc1, hcn, ?_⟩
          intro hle hmem
          have := Nat.le_findGreatest (P := fun a => a = 0 ∨ a ∈ A 0) hle (Or.inr hmem)
          omega
        set a₀ := Nat.find hex with ha₀
        obtain ⟨ℓ₀, c₀, htrip⟩ := Nat.find_spec hex
        have hmin : ∀ a < a₀, ∀ ℓ c, ¬ Trip A h n a ℓ c := by
          intro a ha ℓ c ht
          exact Nat.find_min hex ha ⟨ℓ, c, ht⟩
        obtain ⟨hℓ, ha, -, hcA0, hc01, hc0n, hc0⟩ := htrip
        have hyp' := hyp_tr hℓ hmin hyp
        have hlt : cnt (tr A h n a₀ ℓ₀ (h + 1)) n < k := by
          rw [tr_last]
          have e := cnt_diff (B := A (h + 1)) (T := Tset A h n a₀ ℓ₀) (fun x hx => hx.1) n
          have p := cnt_pos (A := Tset A h n a₀ ℓ₀) (m := n) (c := c₀)
            ⟨hcA0, hc01, hc0n, hc0⟩ hc01 hc0n
          omega
        exact rep_back hℓ ha le_rfl (ihk _ hlt _ rfl hyp')
      · push Not at hc
        have h0 : ∀ m, m ≤ n → cnt (A (h + 1)) m = 0 := fun m hm =>
          cnt_eq_zero (fun x h1 h2 hx => by have := hc x hx h1; omega)
        have hyp1 : DysonHyp A (h + 1) n := by
          intro m hm1 hmn
          have := hyp m hm1 hmn
          simp only [phi, sum_range_succ (n := h + 1), h0 m hmn] at this
          simpa [phi] using this
        obtain ⟨f, hf, hs⟩ := ih n A hyp1
        refine ⟨Function.update f (h + 1) 0, fun i hi => ?_, ?_⟩
        · by_cases hi' : i = h + 1
          · subst hi'; simp
          · simp only [Function.update_of_ne hi']; exact hf i (by omega)
        · rw [sum_range_succ, Function.update_self, add_zero, ← hs]
          apply sum_congr rfl
          intro i hi
          simp at hi
          exact Function.update_of_ne (by omega) _ _

/-! ### Theorem 9.1, the transforms of page 701

`stepT B (k, j)` is the transform of Lemma 9.1 applied to `B 0` (the paper's `𝒜₁`) and `B j`
with `e = k`: `B 0 ∪ (B j + k)` and `B j ∩ (B 0 - k)`. -/

def stepT (B : ℕ → Set ℕ) (p : ℕ × ℕ) : ℕ → Set ℕ := fun i =>
  if i = 0 then B 0 ∪ {x | p.1 ≤ x ∧ x - p.1 ∈ B p.2}
  else if i = p.2 then {y | y ∈ B p.2 ∧ y + p.1 ∈ B 0} else B i

lemma stepT_zero (B : ℕ → Set ℕ) (p : ℕ × ℕ) :
    stepT B p 0 = B 0 ∪ {x | p.1 ≤ x ∧ x - p.1 ∈ B p.2} := by simp [stepT]

lemma stepT_j (B : ℕ → Set ℕ) {k j : ℕ} (hj : 1 ≤ j) :
    stepT B (k, j) j = {y | y ∈ B j ∧ y + k ∈ B 0} := by
  simp [stepT, show j ≠ 0 by omega]

lemma stepT_ne (B : ℕ → Set ℕ) {p : ℕ × ℕ} {i : ℕ} (h0 : i ≠ 0) (hj : i ≠ p.2) :
    stepT B p i = B i := by simp [stepT, h0, hj]

lemma rep_stepT {B : ℕ → Set ℕ} {H k j p : ℕ} (hj : 1 ≤ j) (hjH : j < H) (hk : k ∈ B 0)
    (hr : Rep (stepT B (k, j)) H p) : Rep B H p := by
  obtain ⟨f, hf, hs⟩ := hr
  have hne : (0 : ℕ) ≠ j := by omega
  have hm0 : 0 ∈ range H := mem_range.2 (by omega)
  have hmj : j ∈ range H := mem_range.2 hjH
  have h0 := hf 0 (by omega)
  have hjj := hf j hjH
  rw [stepT_zero] at h0
  rw [stepT_j B hj] at hjj
  have hother : ∀ i < H, i ≠ 0 → i ≠ j → f i = 0 ∨ f i ∈ B i := by
    intro i hi h1 h2
    have := hf i hi; rwa [stepT_ne B h1 h2] at this
  have hy : f j = 0 ∨ f j ∈ B j := by
    rcases hjj with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  rcases h0 with hx | hx | hx
  · refine ⟨f, fun i hi => ?_, hs⟩
    by_cases h1 : i = 0
    · subst h1; exact Or.inl hx
    by_cases h2 : i = j
    · subst h2; exact hy
    · exact hother i hi h1 h2
  · refine ⟨f, fun i hi => ?_, hs⟩
    by_cases h1 : i = 0
    · subst h1; exact Or.inr hx
    by_cases h2 : i = j
    · subst h2; exact hy
    · exact hother i hi h1 h2
  · obtain ⟨hkx, hxj⟩ := hx
    have hyk : f j + k ∈ B 0 := by
      rcases hjj with h | h
      · rw [h, zero_add]; exact hk
      · exact h.2
    set g : ℕ → ℕ := Function.update (Function.update f 0 (f j + k)) j (f 0 - k) with hg
    have g1 : g j = f 0 - k := by simp [hg]
    have g2 : g 0 = f j + k := by simp [hg, hne]
    have g3 : ∀ i, i ≠ j → i ≠ 0 → g i = f i := by
      intro i h1 h2; simp [hg, h1, h2]
    refine ⟨g, fun i hi => ?_, ?_⟩
    · by_cases h1 : i = 0
      · subst h1; rw [g2]; exact Or.inr hyk
      by_cases h2 : i = j
      · subst h2; rw [g1]; exact Or.inr hxj
      · rw [g3 i h2 h1]; exact hother i hi h1 h2
    · have := sum_two (f := f) (g := g) hm0 hmj hne (fun i _ h1 h2 => (g3 i h2 h1).symm)
      rw [g1, g2] at this
      omega

lemma cnt_stepT {B : ℕ → Set ℕ} {H k j : ℕ} (hj : 1 ≤ j) (hjH : j < H) (m : ℕ) :
    ∑ i ∈ range H, cnt (B i) m ≤ ∑ i ∈ range H, cnt (stepT B (k, j) i) m + k := by
  have hne : (0 : ℕ) ≠ j := by omega
  have hs := sum_two (s := range H) (f := fun i => cnt (B i) m)
    (g := fun i => cnt (stepT B (k, j) i) m) (mem_range.2 (by omega)) (mem_range.2 hjH) hne
    (fun i _ h1 h2 => by rw [stepT_ne B h1 h2])
  set L : Set ℕ := {y | y ∈ B j ∧ y + k ∉ B 0} with hL
  have hLsub : L ⊆ B j := fun y hy => hy.1
  have e1 : stepT B (k, j) j = B j \ L := by
    rw [stepT_j B hj]; ext y; simp [hL]
  have d := cnt_diff hLsub m
  have u := cnt_union_shift (B 0) L k m m le_rfl (fun c hc _ => hc.2)
  have u2 : cnt (B 0 ∪ {x | k ≤ x ∧ x - k ∈ L}) m ≤ cnt (stepT B (k, j) 0) m := by
    rw [stepT_zero]
    apply cnt_mono_set
    intro x hx
    rcases hx with hx | ⟨h1, h2⟩
    · exact Or.inl hx
    · exact Or.inr ⟨h1, h2.1⟩
  have sp : cnt L m ≤ cnt L (m - k) + k := cnt_sub_le L m k
  rw [e1] at hs
  omega

/-- The family after the transforms listed in `L`, starting from `A, A, …`. -/
def famT (A : Set ℕ) : List (ℕ × ℕ) → ℕ → Set ℕ
  | [] => fun _ => A
  | p :: L => stepT (famT A L) p

/-- Invariants of the transforms, for pairs `(k, j)` with `k ≤ K`, `1 ≤ j < H`. -/
lemma famT_inv (A : Set ℕ) (H K n₀ : ℕ) (hA0 : 0 ∈ A) (hb1 : ∀ i ≤ K, i ∈ A)
    (hb2 : ∀ i ≤ K, n₀ + i ∈ A) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 ≤ K ∧ 1 ≤ p.2 ∧ p.2 < H) →
      (A ⊆ famT A L 0) ∧ (∀ i, 0 ∈ famT A L i ∧ n₀ ∈ famT A L i) ∧
      (∀ i, famT A L i ⊆ famT A L 0) ∧
      (∀ p ∈ L, ∀ y ∈ famT A L p.2, y + p.1 ∈ famT A L 0) ∧
      (∀ q, Rep (famT A L) H q → Rep (fun _ => A) H q) ∧
      (∀ m, H * cnt A m ≤ ∑ i ∈ range H, cnt (famT A L i) m + K * L.length) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨fun x hx => hx, fun i => ⟨hA0, ?_⟩, fun i x hx => hx, by simp, fun q hq => hq, ?_⟩
    · simpa [famT] using hb2 0 (Nat.zero_le _)
    · intro m; simp [famT]
  | cons p L ih =>
    intro hL
    obtain ⟨k, j⟩ := p
    obtain ⟨hk, hj1, hjH⟩ := hL (k, j) (by simp)
    obtain ⟨I1, I2, I3, I4, I5, I6⟩ := ih (fun q hq => hL q (by simp [hq]))
    set B := famT A L with hB
    have hfam : famT A ((k, j) :: L) = stepT B (k, j) := rfl
    rw [hfam]
    have s0 : B 0 ⊆ stepT B (k, j) 0 := by
      rw [stepT_zero]; exact Set.subset_union_left
    have sj : ∀ i, i ≠ 0 → stepT B (k, j) i ⊆ B i := by
      intro i h0
      by_cases hij : i = j
      · subst hij; rw [stepT_j B hj1]; exact fun y hy => hy.1
      · rw [stepT_ne B h0 (by simpa using hij)]
    have hkB : k ∈ B 0 := I1 (hb1 k hk)
    refine ⟨I1.trans s0, fun i => ?_, fun i => ?_, fun q hq => ?_, fun q hq => ?_, fun m => ?_⟩
    · by_cases h0 : i = 0
      · subst h0; exact ⟨s0 (I2 0).1, s0 (I2 0).2⟩
      by_cases hij : i = j
      · subst hij; rw [stepT_j B hj1]
        exact ⟨⟨(I2 i).1, by simpa using hkB⟩, ⟨(I2 i).2, I1 (hb2 k hk)⟩⟩
      · rw [stepT_ne B h0 (by simpa using hij)]; exact I2 i
    · by_cases h0 : i = 0
      · subst h0; exact le_rfl
      · exact ((sj i h0).trans (I3 i)).trans s0
    · intro y hy
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [stepT_j B hj1] at hy; exact s0 hy.2
      · have hq2 := (hL q (by simp [hq])).2.1
        exact s0 (I4 q hq y (sj q.2 (by omega) hy))
    · exact I5 q (rep_stepT hj1 hjH hkB hq)
    · have := I6 m
      have := cnt_stepT (B := B) (k := k) hj1 hjH m
      simp only [List.length_cons]
      nlinarith

/-! ### Theorem 9.1, the end of the proof, pages 702-703 -/

lemma list_sum_range (f : ℕ → ℕ) (H : ℕ) :
    ((List.range H).map f).sum = ∑ i ∈ range H, f i := by
  induction H with
  | zero => simp
  | succ n ih => simp [List.range_succ, sum_range_succ, ih]

lemma sumOfAtMost_of_rep {A : Set ℕ} {H p : ℕ} (hA0 : 0 ∈ A) (hr : Rep (fun _ => A) H p) :
    SumOfAtMost A H p := by
  obtain ⟨f, hf, hs⟩ := hr
  refine ⟨(List.range H).map f, by simp, ?_, by rw [list_sum_range, hs]⟩
  intro a ha
  simp only [List.mem_map, List.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rcases hf i hi with h | h
  · rw [h]; exact hA0
  · exact h

/-- Count of `B ∩ [0, n]` when `0 ∈ B`. -/
lemma icc_count_zero {B : Set ℕ} (h0 : 0 ∈ B) (n : ℕ) :
    #{x ∈ Icc 0 n | x ∈ B} = cnt B n + 1 := by
  unfold cnt
  have : ({x ∈ Icc 0 n | x ∈ B} : Finset ℕ) = insert 0 {a ∈ Icc 1 n | a ∈ B} := by
    ext x; simp only [mem_filter, mem_Icc, mem_insert]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨le_rfl, Nat.zero_le _⟩, h0⟩
      · exact ⟨⟨Nat.zero_le _, h2⟩, h3⟩
  rw [this, card_insert_of_notMem (by simp)]

/-- Count of `B ∩ [a, a + n]` for `a ≥ 1`. -/
lemma icc_count_split (B : Set ℕ) {a : ℕ} (n : ℕ) (ha : 1 ≤ a) :
    #{x ∈ Icc a (a + n) | x ∈ B} + cnt B (a - 1) = cnt B (a + n) := by
  rw [cnt_split B (show a - 1 ≤ a + n by omega)]
  have : (Ioc (a - 1) (a + n) : Finset ℕ) = Icc a (a + n) := by
    ext x; simp only [mem_Ioc, mem_Icc]; omega
  rw [this]; ring

/-- (9.3) from (a) and (c), in integers. -/
lemma good_of (σ : ℝ) (h K n a S : ℕ)
    (h1 : σ * n + (K * (K + 1) / 2 : ℝ) * (((h + 1 : ℕ) : ℝ) - 1) ≤ a)
    (h2 : (h + 1) * a ≤ S + K * (K * h))
    (hc : ((K : ℝ) + (h + 1 : ℕ)) ≤ (K + 1) * (h + 1 : ℕ) * σ) :
    (K + (h + 1)) * n ≤ (K + 1) * S := by
  have h2' : ((h : ℝ) + 1) * a ≤ S + K * (K * h) := by exact_mod_cast h2
  push_cast at h1 hc
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- S ≥ (h+1) σ n + Q with Q ≥ 0
  have hQ : (0 : ℝ) ≤ ((h : ℝ) + 1) * (K * (K + 1) / 2 * h) - K * (K * h) := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; simp
    · have : (1 : ℝ) ≤ h := by exact_mod_cast h0
      have : ((h : ℝ) + 1) * (K * (K + 1) / 2 * h) - K * (K * h) =
          K * h * (((h : ℝ) - 1) * (K + 1) + 2) / 2 := by ring
      rw [this]
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg (mul_nonneg hK hh)
      nlinarith
  have e1 : ((h : ℝ) + 1) * (σ * n + K * (K + 1) / 2 * ((h : ℝ) + 1 - 1)) ≤ ((h : ℝ) + 1) * a :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hS : ((h : ℝ) + 1) * σ * n ≤ S := by nlinarith
  have hcn : ((K : ℝ) + (h + 1)) * n ≤ (K + 1) * (h + 1) * σ * n :=
    mul_le_mul_of_nonneg_right hc hn
  have : ((K : ℝ) + (h + 1)) * n ≤ (K + 1) * S := by
    have := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ K + 1 by positivity)
    nlinarith
  exact_mod_cast this

/-- **Theorem 9.1** of Ramaré 1995 (Deshouillers), with `1 ≤ H`. Proof as on pages 701-703:
`K(H-1)` transforms of Lemma 9.1, then shifts by `n_h`, then Dyson's theorem. Two changes
to the write-up: each transform is charged a loss of `K`, not `k`, which (a) still pays for
when `H ≥ 2`; and the three cases A, B, C are replaced by `n ≤ K` (where `[n₁, n₁ + K] ⊆ 𝔅₁`,
shown from (9.2) and (9.5)) and `n ≥ K` (case C's computation), so no reordering of the
`n_h` is needed. -/
theorem theorem91 : Theorem91 := by
  intro A σ H K n₀ hH hA0 ha hb1 hb2 hc m hm
  obtain ⟨h, rfl⟩ : ∃ h, H = h + 1 := ⟨H - 1, by omega⟩
  set L : List (ℕ × ℕ) := (Finset.Icc 1 K ×ˢ Finset.Icc 1 h).toList with hLdef
  have hL : ∀ p ∈ L, p.1 ≤ K ∧ 1 ≤ p.2 ∧ p.2 < h + 1 := by
    intro p hp
    simp only [hLdef, mem_toList, mem_product, mem_Icc] at hp
    omega
  have hlen : L.length = K * h := by simp [hLdef]
  obtain ⟨I1, I2, I3, I4, I5, I6⟩ := famT_inv A (h + 1) K n₀ hA0 hb1 hb2 L hL
  set B := famT A L with hB
  have P3 : ∀ j, 1 ≤ j → j < h + 1 → ∀ k ≤ K, ∀ y ∈ B j, y + k ∈ B 0 := by
    intro j hj1 hjH k hk y hy
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simpa using I3 j hy
    · exact I4 (k, j) (by simp only [hLdef, mem_toList, mem_product, mem_Icc]; omega) y hy
  set Φ : ℕ → ℕ := fun n => ∑ i ∈ range (h + 1), cnt (B i) n with hΦ
  have good : ∀ n, n₀ ≤ n → (K + (h + 1)) * n ≤ (K + 1) * Φ n := by
    intro n hn
    have h2 := I6 n
    rw [hlen] at h2
    exact good_of σ h K n (cnt A n) (Φ n) (ha n hn) h2 hc
  have hex : ∃ s, ∀ n, s ≤ n → (K + (h + 1)) * n ≤ (K + 1) * Φ n := ⟨n₀, good⟩
  set n₁ := Nat.find hex with hn₁def
  have hn₁ : ∀ n, n₁ ≤ n → (K + (h + 1)) * n ≤ (K + 1) * Φ n := Nat.find_spec hex
  have hn₁le : n₁ ≤ n₀ := Nat.find_min' hex good
  set R : ℕ → ℕ → ℕ := fun i n => #{x ∈ Icc n₁ (n₁ + n) | x ∈ B i} with hR
  have P95 : ∀ n, (K + (h + 1)) * (n + 1) ≤ (K + 1) * ∑ i ∈ range (h + 1), R i n := by
    intro n
    rcases Nat.eq_zero_or_pos n₁ with h0 | hpos
    · have e : ∑ i ∈ range (h + 1), R i n = Φ n + (h + 1) := by
        have : ∑ i ∈ range (h + 1), R i n = ∑ i ∈ range (h + 1), (cnt (B i) n + 1) := by
          apply sum_congr rfl
          intro i _
          simp only [hR, h0, zero_add]
          exact icc_count_zero (I2 i).1 n
        rw [this, sum_add_distrib]; simp [hΦ]
      have := hn₁ n (by omega)
      rw [e]; nlinarith
    · obtain ⟨q, hq⟩ : ∃ q, n₁ = q + 1 := ⟨n₁ - 1, by omega⟩
      have hnot : ¬ ((K + (h + 1)) * q ≤ (K + 1) * Φ q) := by
        intro hgood
        have hall : ∀ n, q ≤ n → (K + (h + 1)) * n ≤ (K + 1) * Φ n := by
          intro n hn
          rcases Nat.eq_or_lt_of_le hn with rfl | hlt
          · exact hgood
          · exact hn₁ n (by omega)
        exact Nat.find_min hex (show q < n₁ by omega) hall
      have hsplit : ∑ i ∈ range (h + 1), R i n + Φ q = Φ (n₁ + n) := by
        simp only [hΦ, hR]
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        have := icc_count_split (B i) (a := n₁) n (by omega)
        rwa [show n₁ - 1 = q by omega] at this
      have hg := hn₁ (n₁ + n) (by omega)
      rw [← hsplit, hq] at hg
      push Not at hnot
      nlinarith
  have full : ∀ x, n₁ ≤ x → x ≤ n₁ + K → x ∈ B 0 := by
    intro x hx1 hx2
    by_contra hx
    have hR0 : R 0 (x - n₁) ≤ x - n₁ := by
      simp only [hR]
      have hsub : ({y ∈ Icc n₁ (n₁ + (x - n₁)) | y ∈ B 0} : Finset ℕ) ⊆
          (Icc n₁ (n₁ + (x - n₁))).erase x := by
        intro y hy
        simp only [mem_filter, mem_erase, mem_Icc] at hy ⊢
        refine ⟨fun hyx => hx (hyx ▸ hy.2), hy.1⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (by simp only [mem_Icc]; omega), Nat.card_Icc] at this
      omega
    have hRi : ∀ i ∈ range (h + 1), i ≠ 0 → R i (x - n₁) = 0 := by
      intro i hi hi0
      simp only [hR]
      rw [card_eq_zero, filter_eq_empty_iff]
      intro z hz hzB
      simp only [mem_Icc] at hz
      have := P3 i (by omega) (by simpa using hi) (x - z) (by omega) z hzB
      rw [show z + (x - z) = x by omega] at this
      exact hx this
    have hsum : ∑ i ∈ range (h + 1), R i (x - n₁) = R 0 (x - n₁) := by
      rw [← add_sum_erase _ _ (mem_range.2 (by omega : 0 < h + 1))]
      rw [sum_eq_zero (fun i hi => hRi i (mem_of_mem_erase hi) (ne_of_mem_erase hi))]
      simp
    have := P95 (x - n₁)
    rw [hsum] at this
    nlinarith
  have hexh : ∀ i, ∃ y, n₁ ≤ y ∧ y ∈ B i := fun i => ⟨n₀, hn₁le, (I2 i).2⟩
  set s : ℕ → ℕ := fun i => if i = 0 then n₁ else Nat.find (hexh i) with hsdef
  have hs : ∀ i, n₁ ≤ s i ∧ s i ≤ n₀ ∧ s i ∈ B i ∧ ∀ y, n₁ ≤ y → y ∈ B i → s i ≤ y := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simp only [hsdef, ite_true]
      exact ⟨le_rfl, hn₁le, full n₁ le_rfl (by omega), fun y hy _ => hy⟩
    · simp only [hsdef, hi, ite_false]
      obtain ⟨h1, h2⟩ := Nat.find_spec (hexh i)
      exact ⟨h1, Nat.find_min' (hexh i) ⟨hn₁le, (I2 i).2⟩, h2,
        fun y hy hyB => Nat.find_min' (hexh i) ⟨hy, hyB⟩⟩
  set D : ℕ → Set ℕ := fun i => {x | x + s i ∈ B i} with hD
  have keyR : ∀ i n, R i n ≤ cnt (D i) n + 1 := by
    intro i n
    obtain ⟨hs1, -, hs3, hs4⟩ := hs i
    simp only [hR]
    unfold cnt
    have hinj : #(({x ∈ Icc 1 n | x ∈ D i}).image (· + s i)) = #{x ∈ Icc 1 n | x ∈ D i} :=
      card_image_of_injective _ (add_left_injective (s i))
    have hsub : ({x ∈ Icc n₁ (n₁ + n) | x ∈ B i} : Finset ℕ) ⊆
        insert (s i) (({x ∈ Icc 1 n | x ∈ D i}).image (· + s i)) := by
      intro y hy
      simp only [mem_filter, mem_Icc] at hy
      have hsy := hs4 y hy.1.1 hy.2
      rw [mem_insert]
      by_cases hys : y = s i
      · exact Or.inl hys
      · right
        simp only [mem_image, mem_filter, mem_Icc]
        refine ⟨y - s i, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
        show y - s i + s i ∈ B i
        rw [show y - s i + s i = y by omega]; exact hy.2
    have := card_le_card hsub
    have := card_insert_le (s i) (({x ∈ Icc 1 n | x ∈ D i}).image (· + s i))
    omega
  have dhyp : ∀ M, DysonHyp D (h + 1) M := by
    intro M n hn1 _
    by_cases hnK : n ≤ K
    · have h0 : n ≤ cnt (D 0) n := by
        unfold cnt
        have : (Icc 1 n : Finset ℕ) ⊆ {x ∈ Icc 1 n | x ∈ D 0} := by
          intro j hj
          simp only [mem_filter, mem_Icc] at hj ⊢
          refine ⟨hj, ?_⟩
          show j + s 0 ∈ B 0
          have : s 0 = n₁ := by simp [hsdef]
          rw [this]
          exact full _ (by omega) (by omega)
        simpa using card_le_card this
      have : cnt (D 0) n ≤ phi D (h + 1) n := by
        unfold phi
        exact single_le_sum (f := fun i => cnt (D i) n) (fun i _ => Nat.zero_le _)
          (mem_range.2 (by omega))
      omega
    · have p := P95 n
      have hle : ∑ i ∈ range (h + 1), R i n ≤ ∑ i ∈ range (h + 1), (cnt (D i) n + 1) :=
        sum_le_sum (fun i _ => keyR i n)
      rw [sum_add_distrib] at hle
      simp only [sum_const, card_range, smul_eq_mul, mul_one] at hle
      change ∑ i ∈ range (h + 1), R i n ≤ phi D (h + 1) n + (h + 1) at hle
      by_contra hlt
      push Not at hlt
      have hmul := Nat.mul_le_mul_left (K + 1) (show phi D (h + 1) n + 1 ≤ n by omega)
      have hmul2 := Nat.mul_le_mul_left (K + 1) hle
      have hmul3 := Nat.mul_le_mul_left h (show K + 1 ≤ n by omega)
      nlinarith
  have hsum_s : ∑ i ∈ range (h + 1), s i ≤ (h + 1) * n₀ := by
    calc ∑ i ∈ range (h + 1), s i ≤ ∑ i ∈ range (h + 1), n₀ := sum_le_sum (fun i _ => (hs i).2.1)
      _ = (h + 1) * n₀ := by simp
  obtain ⟨f, hf, hfs⟩ := dyson h (m - ∑ i ∈ range (h + 1), s i) D (dhyp _)
  have hrep : Rep B (h + 1) m := by
    refine ⟨fun i => f i + s i, fun i hi => Or.inr ?_, ?_⟩
    · rcases hf i hi with h0 | h0
      · simp only [h0, zero_add]; exact (hs i).2.2.1
      · exact h0
    · rw [sum_add_distrib, hfs]; omega
  exact sumOfAtMost_of_rep hA0 (I5 m hrep)

end LeanLab.Ramare1995.Theorem91
