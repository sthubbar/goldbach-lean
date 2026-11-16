module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W071
public import LeanLab.GvLtR1989.Win.W072
public import LeanLab.GvLtR1989.Win.W073
public import LeanLab.GvLtR1989.Win.W074
public import LeanLab.GvLtR1989.Win.W075
public import LeanLab.GvLtR1989.Win.W076
public import LeanLab.GvLtR1989.Win.W077
public import LeanLab.GvLtR1989.Win.W078

/-!
Blocks 150 to 164, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_150 : GBBound 270280002 272260000 947 := by
  have hq : ∀ x ∈ QKo 160, x ≤ 947 := take_le 160 947 (by decide +kernel)
  have w0 : GBBound 270280002 271270000 947 :=
    gbBound_of_owcheck (lo := 270279055) (Wb := 495473) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_150_0
  have w1 : GBBound 271270002 272260000 947 :=
    gbBound_of_owcheck (lo := 271269055) (Wb := 495473) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_150_1
  have v1 : GBBound 270280002 272260000 947 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_150 : (19 + 51871/125000 : ℝ) ≤ Real.log ((270280002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((270280002 : ℕ) : ℝ)) 19 (f := (51871/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_150 : (2 + 966043/1000000 : ℝ) ≤ Real.log (19 + 51871/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 51871/125000 : ℝ)) 2 (f := (966043/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_150 : ∀ n, Even n → 270280002 ≤ n → n ≤ 272260000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_150 ls_150 (by norm_num) (by norm_num) bnd_150

theorem bnd_151 : GBBound 272260002 274240000 1129 := by
  have hq : ∀ x ∈ QKo 188, x ≤ 1129 := take_le 188 1129 (by decide +kernel)
  have w0 : GBBound 272260002 273250000 1129 :=
    gbBound_of_owcheck (lo := 272258873) (Wb := 495564) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_151_0
  have w1 : GBBound 273250002 274240000 1129 :=
    gbBound_of_owcheck (lo := 273248873) (Wb := 495564) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_151_1
  have v1 : GBBound 272260002 274240000 1129 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_151 : (19 + 422267/1000000 : ℝ) ≤ Real.log ((272260002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((272260002 : ℕ) : ℝ)) 19 (f := (422267/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_151 : (2 + 966419/1000000 : ℝ) ≤ Real.log (19 + 422267/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 422267/1000000 : ℝ)) 2 (f := (966419/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_151 : ∀ n, Even n → 272260002 ≤ n → n ≤ 274240000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_151 ls_151 (by norm_num) (by norm_num) bnd_151

theorem bnd_152 : GBBound 274240002 276220000 991 := by
  have hq : ∀ x ∈ QKo 166, x ≤ 991 := take_le 166 991 (by decide +kernel)
  have w0 : GBBound 274240002 275230000 991 :=
    gbBound_of_owcheck (lo := 274239011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_152_0
  have w1 : GBBound 275230002 276220000 991 :=
    gbBound_of_owcheck (lo := 275229011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_152_1
  have v1 : GBBound 274240002 276220000 991 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_152 : (19 + 429513/1000000 : ℝ) ≤ Real.log ((274240002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((274240002 : ℕ) : ℝ)) 19 (f := (429513/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_152 : (2 + 120849/125000 : ℝ) ≤ Real.log (19 + 429513/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 429513/1000000 : ℝ)) 2 (f := (120849/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_152 : ∀ n, Even n → 274240002 ≤ n → n ≤ 276220000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_152 ls_152 (by norm_num) (by norm_num) bnd_152

theorem bnd_153 : GBBound 276220002 278200000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 276220002 277210000 823 :=
    gbBound_of_owcheck (lo := 276219179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_153_0
  have w1 : GBBound 277210002 278200000 823 :=
    gbBound_of_owcheck (lo := 277209179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_153_1
  have v1 : GBBound 276220002 278200000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_153 : (19 + 436707/1000000 : ℝ) ≤ Real.log ((276220002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((276220002 : ℕ) : ℝ)) 19 (f := (436707/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_153 : (2 + 483581/500000 : ℝ) ≤ Real.log (19 + 436707/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 436707/1000000 : ℝ)) 2 (f := (483581/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_153 : ∀ n, Even n → 276220002 ≤ n → n ≤ 278200000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_153 ls_153 (by norm_num) (by norm_num) bnd_153

theorem bnd_154 : GBBound 278200002 280180000 997 := by
  have hq : ∀ x ∈ QKo 167, x ≤ 997 := take_le 167 997 (by decide +kernel)
  have w0 : GBBound 278200002 279190000 997 :=
    gbBound_of_owcheck (lo := 278199005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_154_0
  have w1 : GBBound 279190002 280180000 997 :=
    gbBound_of_owcheck (lo := 279189005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_154_1
  have v1 : GBBound 278200002 280180000 997 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_154 : (19 + 443849/1000000 : ℝ) ≤ Real.log ((278200002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((278200002 : ℕ) : ℝ)) 19 (f := (443849/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_154 : (2 + 967529/1000000 : ℝ) ≤ Real.log (19 + 443849/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 443849/1000000 : ℝ)) 2 (f := (967529/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_154 : ∀ n, Even n → 278200002 ≤ n → n ≤ 280180000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_154 ls_154 (by norm_num) (by norm_num) bnd_154

theorem bnd_155 : GBBound 280180002 282160000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 280180002 281170000 907 :=
    gbBound_of_owcheck (lo := 280179095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_155_0
  have w1 : GBBound 281170002 282160000 907 :=
    gbBound_of_owcheck (lo := 281169095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_155_1
  have v1 : GBBound 280180002 282160000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_155 : (19 + 450941/1000000 : ℝ) ≤ Real.log ((280180002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((280180002 : ℕ) : ℝ)) 19 (f := (450941/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_155 : (2 + 483947/500000 : ℝ) ≤ Real.log (19 + 450941/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 450941/1000000 : ℝ)) 2 (f := (483947/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_155 : ∀ n, Even n → 280180002 ≤ n → n ≤ 282160000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_155 ls_155 (by norm_num) (by norm_num) bnd_155

theorem bnd_156 : GBBound 282160002 284140000 877 := by
  have hq : ∀ x ∈ QKo 150, x ≤ 877 := take_le 150 877 (by decide +kernel)
  have w0 : GBBound 282160002 283150000 877 :=
    gbBound_of_owcheck (lo := 282159125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_156_0
  have w1 : GBBound 283150002 284140000 877 :=
    gbBound_of_owcheck (lo := 283149125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_156_1
  have v1 : GBBound 282160002 284140000 877 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_156 : (19 + 457983/1000000 : ℝ) ≤ Real.log ((282160002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((282160002 : ℕ) : ℝ)) 19 (f := (457983/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_156 : (2 + 15129/15625 : ℝ) ≤ Real.log (19 + 457983/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 457983/1000000 : ℝ)) 2 (f := (15129/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_156 : ∀ n, Even n → 282160002 ≤ n → n ≤ 284140000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_156 ls_156 (by norm_num) (by norm_num) bnd_156

theorem bnd_157 : GBBound 284140002 286120000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 284140002 285130000 907 :=
    gbBound_of_owcheck (lo := 284139095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_157_0
  have w1 : GBBound 285130002 286120000 907 :=
    gbBound_of_owcheck (lo := 285129095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_157_1
  have v1 : GBBound 284140002 286120000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_157 : (19 + 29061/62500 : ℝ) ≤ Real.log ((284140002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((284140002 : ℕ) : ℝ)) 19 (f := (29061/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_157 : (2 + 193723/200000 : ℝ) ≤ Real.log (19 + 29061/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 29061/62500 : ℝ)) 2 (f := (193723/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_157 : ∀ n, Even n → 284140002 ≤ n → n ≤ 286120000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_157 ls_157 (by norm_num) (by norm_num) bnd_157

theorem bnd_158 : GBBound 286120002 288100000 997 := by
  have hq : ∀ x ∈ QKo 167, x ≤ 997 := take_le 167 997 (by decide +kernel)
  have w0 : GBBound 286120002 287110000 997 :=
    gbBound_of_owcheck (lo := 286119005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_158_0
  have w1 : GBBound 287110002 288100000 997 :=
    gbBound_of_owcheck (lo := 287109005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_158_1
  have v1 : GBBound 286120002 288100000 997 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_158 : (19 + 5899/12500 : ℝ) ≤ Real.log ((286120002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((286120002 : ℕ) : ℝ)) 19 (f := (5899/12500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_158 : (2 + 242243/250000 : ℝ) ≤ Real.log (19 + 5899/12500 : ℝ) := by
  have h := le_log_of (x := (19 + 5899/12500 : ℝ)) 2 (f := (242243/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_158 : ∀ n, Even n → 286120002 ≤ n → n ≤ 288100000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_158 ls_158 (by norm_num) (by norm_num) bnd_158

theorem bnd_159 : GBBound 288100002 290080000 881 := by
  have hq : ∀ x ∈ QKo 151, x ≤ 881 := take_le 151 881 (by decide +kernel)
  have w0 : GBBound 288100002 289090000 881 :=
    gbBound_of_owcheck (lo := 288099121) (Wb := 495440) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_159_0
  have w1 : GBBound 289090002 290080000 881 :=
    gbBound_of_owcheck (lo := 289089121) (Wb := 495440) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_159_1
  have v1 : GBBound 288100002 290080000 881 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_159 : (19 + 478817/1000000 : ℝ) ≤ Real.log ((288100002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((288100002 : ℕ) : ℝ)) 19 (f := (478817/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_159 : (2 + 484663/500000 : ℝ) ≤ Real.log (19 + 478817/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 478817/1000000 : ℝ)) 2 (f := (484663/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_159 : ∀ n, Even n → 288100002 ≤ n → n ≤ 290080000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_159 ls_159 (by norm_num) (by norm_num) bnd_159

theorem bnd_160 : GBBound 290080002 292060000 853 := by
  have hq : ∀ x ∈ QKo 146, x ≤ 853 := take_le 146 853 (by decide +kernel)
  have w0 : GBBound 290080002 291070000 853 :=
    gbBound_of_owcheck (lo := 290079149) (Wb := 495426) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_160_0
  have w1 : GBBound 291070002 292060000 853 :=
    gbBound_of_owcheck (lo := 291069149) (Wb := 495426) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_160_1
  have v1 : GBBound 290080002 292060000 853 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_160 : (19 + 242833/500000 : ℝ) ≤ Real.log ((290080002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((290080002 : ℕ) : ℝ)) 19 (f := (242833/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_160 : (2 + 484839/500000 : ℝ) ≤ Real.log (19 + 242833/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 242833/500000 : ℝ)) 2 (f := (484839/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_160 : ∀ n, Even n → 290080002 ≤ n → n ≤ 292060000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_160 ls_160 (by norm_num) (by norm_num) bnd_160

theorem bnd_161 : GBBound 292060002 294040000 859 := by
  have hq : ∀ x ∈ QKo 148, x ≤ 859 := take_le 148 859 (by decide +kernel)
  have w0 : GBBound 292060002 293050000 859 :=
    gbBound_of_owcheck (lo := 292059143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_161_0
  have w1 : GBBound 293050002 294040000 859 :=
    gbBound_of_owcheck (lo := 293049143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_161_1
  have v1 : GBBound 292060002 294040000 859 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_161 : (19 + 123117/250000 : ℝ) ≤ Real.log ((292060002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((292060002 : ℕ) : ℝ)) 19 (f := (123117/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_161 : (2 + 970027/1000000 : ℝ) ≤ Real.log (19 + 123117/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 123117/250000 : ℝ)) 2 (f := (970027/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_161 : ∀ n, Even n → 292060002 ≤ n → n ≤ 294040000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_161 ls_161 (by norm_num) (by norm_num) bnd_161

theorem bnd_162 : GBBound 294040002 296020000 1033 := by
  have hq : ∀ x ∈ QKo 173, x ≤ 1033 := take_le 173 1033 (by decide +kernel)
  have w0 : GBBound 294040002 295030000 1033 :=
    gbBound_of_owcheck (lo := 294038969) (Wb := 495516) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_162_0
  have w1 : GBBound 295030002 296020000 1033 :=
    gbBound_of_owcheck (lo := 295028969) (Wb := 495516) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_162_1
  have v1 : GBBound 294040002 296020000 1033 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_162 : (19 + 19969/40000 : ℝ) ≤ Real.log ((294040002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((294040002 : ℕ) : ℝ)) 19 (f := (19969/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_162 : (2 + 970373/1000000 : ℝ) ≤ Real.log (19 + 19969/40000 : ℝ) := by
  have h := le_log_of (x := (19 + 19969/40000 : ℝ)) 2 (f := (970373/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_162 : ∀ n, Even n → 294040002 ≤ n → n ≤ 296020000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_162 ls_162 (by norm_num) (by norm_num) bnd_162

theorem bnd_163 : GBBound 296020002 298000000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 296020002 297010000 823 :=
    gbBound_of_owcheck (lo := 296019179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_163_0
  have w1 : GBBound 297010002 298000000 823 :=
    gbBound_of_owcheck (lo := 297009179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_163_1
  have v1 : GBBound 296020002 298000000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_163 : (19 + 31621/62500 : ℝ) ≤ Real.log ((296020002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((296020002 : ℕ) : ℝ)) 19 (f := (31621/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_163 : (2 + 970717/1000000 : ℝ) ≤ Real.log (19 + 31621/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 31621/62500 : ℝ)) 2 (f := (970717/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_163 : ∀ n, Even n → 296020002 ≤ n → n ≤ 298000000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_163 ls_163 (by norm_num) (by norm_num) bnd_163

theorem bnd_164 : GBBound 298000002 299980000 1031 := by
  have hq : ∀ x ∈ QKo 172, x ≤ 1031 := take_le 172 1031 (by decide +kernel)
  have w0 : GBBound 298000002 298990000 1031 :=
    gbBound_of_owcheck (lo := 297998971) (Wb := 495515) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_164_0
  have w1 : GBBound 298990002 299980000 1031 :=
    gbBound_of_owcheck (lo := 298988971) (Wb := 495515) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_164_1
  have v1 : GBBound 298000002 299980000 1031 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_164 : (19 + 512603/1000000 : ℝ) ≤ Real.log ((298000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((298000002 : ℕ) : ℝ)) 19 (f := (512603/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_164 : (2 + 971059/1000000 : ℝ) ≤ Real.log (19 + 512603/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 512603/1000000 : ℝ)) 2 (f := (971059/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_164 : ∀ n, Even n → 298000002 ≤ n → n ≤ 299980000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_164 ls_164 (by norm_num) (by norm_num) bnd_164

end LeanLab.GvLtR1989
