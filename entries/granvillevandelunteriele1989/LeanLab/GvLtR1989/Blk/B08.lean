module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W056
public import LeanLab.GvLtR1989.Win.W057
public import LeanLab.GvLtR1989.Win.W058
public import LeanLab.GvLtR1989.Win.W059
public import LeanLab.GvLtR1989.Win.W060
public import LeanLab.GvLtR1989.Win.W061
public import LeanLab.GvLtR1989.Win.W062
public import LeanLab.GvLtR1989.Win.W063

/-!
Blocks 120 to 134, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_120 : GBBound 210880002 212860000 1123 := by
  have hq : ∀ x ∈ QKo 187, x ≤ 1123 := take_le 187 1123 (by decide +kernel)
  have w0 : GBBound 210880002 211870000 1123 :=
    gbBound_of_owcheck (lo := 210878879) (Wb := 495561) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_120_0
  have w1 : GBBound 211870002 212860000 1123 :=
    gbBound_of_owcheck (lo := 211868879) (Wb := 495561) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_120_1
  have v1 : GBBound 210880002 212860000 1123 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_120 : (19 + 83399/500000 : ℝ) ≤ Real.log ((210880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((210880002 : ℕ) : ℝ)) 19 (f := (83399/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_120 : (2 + 476589/500000 : ℝ) ≤ Real.log (19 + 83399/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 83399/500000 : ℝ)) 2 (f := (476589/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_120 : ∀ n, Even n → 210880002 ≤ n → n ≤ 212860000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_120 ls_120 (by norm_num) (by norm_num) bnd_120

theorem bnd_121 : GBBound 212860002 214840000 997 := by
  have hq : ∀ x ∈ QKo 167, x ≤ 997 := take_le 167 997 (by decide +kernel)
  have w0 : GBBound 212860002 213850000 997 :=
    gbBound_of_owcheck (lo := 212859005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_121_0
  have w1 : GBBound 213850002 214840000 997 :=
    gbBound_of_owcheck (lo := 213849005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_121_1
  have v1 : GBBound 212860002 214840000 997 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_121 : (19 + 11009/62500 : ℝ) ≤ Real.log ((212860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((212860002 : ℕ) : ℝ)) 19 (f := (11009/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_121 : (2 + 476833/500000 : ℝ) ≤ Real.log (19 + 11009/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 11009/62500 : ℝ)) 2 (f := (476833/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_121 : ∀ n, Even n → 212860002 ≤ n → n ≤ 214840000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_121 ls_121 (by norm_num) (by norm_num) bnd_121

theorem bnd_122 : GBBound 214840002 216820000 1021 := by
  have hq : ∀ x ∈ QKo 171, x ≤ 1021 := take_le 171 1021 (by decide +kernel)
  have w0 : GBBound 214840002 215830000 1021 :=
    gbBound_of_owcheck (lo := 214838981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_122_0
  have w1 : GBBound 215830002 216820000 1021 :=
    gbBound_of_owcheck (lo := 215828981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_122_1
  have v1 : GBBound 214840002 216820000 1021 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_122 : (19 + 185403/1000000 : ℝ) ≤ Real.log ((214840002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((214840002 : ℕ) : ℝ)) 19 (f := (185403/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_122 : (2 + 238537/250000 : ℝ) ≤ Real.log (19 + 185403/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 185403/1000000 : ℝ)) 2 (f := (238537/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_122 : ∀ n, Even n → 214840002 ≤ n → n ≤ 216820000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_122 ls_122 (by norm_num) (by norm_num) bnd_122

theorem bnd_123 : GBBound 216820002 218800000 877 := by
  have hq : ∀ x ∈ QKo 150, x ≤ 877 := take_le 150 877 (by decide +kernel)
  have w0 : GBBound 216820002 217810000 877 :=
    gbBound_of_owcheck (lo := 216819125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_123_0
  have w1 : GBBound 217810002 218800000 877 :=
    gbBound_of_owcheck (lo := 217809125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_123_1
  have v1 : GBBound 216820002 218800000 877 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_123 : (19 + 194577/1000000 : ℝ) ≤ Real.log ((216820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((216820002 : ℕ) : ℝ)) 19 (f := (194577/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_123 : (2 + 477313/500000 : ℝ) ≤ Real.log (19 + 194577/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 194577/1000000 : ℝ)) 2 (f := (477313/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_123 : ∀ n, Even n → 216820002 ≤ n → n ≤ 218800000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_123 ls_123 (by norm_num) (by norm_num) bnd_123

theorem bnd_124 : GBBound 218800002 220780000 1033 := by
  have hq : ∀ x ∈ QKo 173, x ≤ 1033 := take_le 173 1033 (by decide +kernel)
  have w0 : GBBound 218800002 219790000 1033 :=
    gbBound_of_owcheck (lo := 218798969) (Wb := 495516) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_124_0
  have w1 : GBBound 219790002 220780000 1033 :=
    gbBound_of_owcheck (lo := 219788969) (Wb := 495516) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_124_1
  have v1 : GBBound 218800002 220780000 1033 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_124 : (19 + 203667/1000000 : ℝ) ≤ Real.log ((218800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((218800002 : ℕ) : ℝ)) 19 (f := (203667/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_124 : (2 + 9551/10000 : ℝ) ≤ Real.log (19 + 203667/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 203667/1000000 : ℝ)) 2 (f := (9551/10000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_124 : ∀ n, Even n → 218800002 ≤ n → n ≤ 220780000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_124 ls_124 (by norm_num) (by norm_num) bnd_124

theorem bnd_125 : GBBound 220780002 222760000 883 := by
  have hq : ∀ x ∈ QKo 152, x ≤ 883 := take_le 152 883 (by decide +kernel)
  have w0 : GBBound 220780002 221770000 883 :=
    gbBound_of_owcheck (lo := 220779119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_125_0
  have w1 : GBBound 221770002 222760000 883 :=
    gbBound_of_owcheck (lo := 221769119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_125_1
  have v1 : GBBound 220780002 222760000 883 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_125 : (19 + 53169/250000 : ℝ) ≤ Real.log ((220780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((220780002 : ℕ) : ℝ)) 19 (f := (53169/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_125 : (2 + 955569/1000000 : ℝ) ≤ Real.log (19 + 53169/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 53169/250000 : ℝ)) 2 (f := (955569/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_125 : ∀ n, Even n → 220780002 ≤ n → n ≤ 222760000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_125 ls_125 (by norm_num) (by norm_num) bnd_125

theorem bnd_126 : GBBound 222760002 224740000 1009 := by
  have hq : ∀ x ∈ QKo 168, x ≤ 1009 := take_le 168 1009 (by decide +kernel)
  have w0 : GBBound 222760002 223750000 1009 :=
    gbBound_of_owcheck (lo := 222758993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_126_0
  have w1 : GBBound 223750002 224740000 1009 :=
    gbBound_of_owcheck (lo := 223748993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_126_1
  have v1 : GBBound 222760002 224740000 1009 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_126 : (19 + 55401/250000 : ℝ) ≤ Real.log ((222760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((222760002 : ℕ) : ℝ)) 19 (f := (55401/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_126 : (2 + 956033/1000000 : ℝ) ≤ Real.log (19 + 55401/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 55401/250000 : ℝ)) 2 (f := (956033/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_126 : ∀ n, Even n → 222760002 ≤ n → n ≤ 224740000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_126 ls_126 (by norm_num) (by norm_num) bnd_126

theorem bnd_127 : GBBound 224740002 226720000 991 := by
  have hq : ∀ x ∈ QKo 166, x ≤ 991 := take_le 166 991 (by decide +kernel)
  have w0 : GBBound 224740002 225730000 991 :=
    gbBound_of_owcheck (lo := 224739011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_127_0
  have w1 : GBBound 225730002 226720000 991 :=
    gbBound_of_owcheck (lo := 225729011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_127_1
  have v1 : GBBound 224740002 226720000 991 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_127 : (19 + 230453/1000000 : ℝ) ≤ Real.log ((224740002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((224740002 : ℕ) : ℝ)) 19 (f := (230453/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_127 : (2 + 478247/500000 : ℝ) ≤ Real.log (19 + 230453/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 230453/1000000 : ℝ)) 2 (f := (478247/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_127 : ∀ n, Even n → 224740002 ≤ n → n ≤ 226720000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_127 ls_127 (by norm_num) (by norm_num) bnd_127

theorem bnd_128 : GBBound 226720002 228700000 941 := by
  have hq : ∀ x ∈ QKo 159, x ≤ 941 := take_le 159 941 (by decide +kernel)
  have w0 : GBBound 226720002 227710000 941 :=
    gbBound_of_owcheck (lo := 226719061) (Wb := 495470) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_128_0
  have w1 : GBBound 227710002 228700000 941 :=
    gbBound_of_owcheck (lo := 227709061) (Wb := 495470) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_128_1
  have v1 : GBBound 226720002 228700000 941 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_128 : (19 + 9569/40000 : ℝ) ≤ Real.log ((226720002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((226720002 : ℕ) : ℝ)) 19 (f := (9569/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_128 : (2 + 19139/20000 : ℝ) ≤ Real.log (19 + 9569/40000 : ℝ) := by
  have h := le_log_of (x := (19 + 9569/40000 : ℝ)) 2 (f := (19139/20000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_128 : ∀ n, Even n → 226720002 ≤ n → n ≤ 228700000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_128 ls_128 (by norm_num) (by norm_num) bnd_128

theorem bnd_129 : GBBound 228700002 230680000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 228700002 229690000 823 :=
    gbBound_of_owcheck (lo := 228699179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_129_0
  have w1 : GBBound 229690002 230680000 823 :=
    gbBound_of_owcheck (lo := 229689179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_129_1
  have v1 : GBBound 228700002 230680000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_129 : (19 + 3099/12500 : ℝ) ≤ Real.log ((228700002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((228700002 : ℕ) : ℝ)) 19 (f := (3099/12500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_129 : (2 + 478701/500000 : ℝ) ≤ Real.log (19 + 3099/12500 : ℝ) := by
  have h := le_log_of (x := (19 + 3099/12500 : ℝ)) 2 (f := (478701/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_129 : ∀ n, Even n → 228700002 ≤ n → n ≤ 230680000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_129 ls_129 (by norm_num) (by norm_num) bnd_129

theorem bnd_130 : GBBound 230680002 232660000 991 := by
  have hq : ∀ x ∈ QKo 166, x ≤ 991 := take_le 166 991 (by decide +kernel)
  have w0 : GBBound 230680002 231670000 991 :=
    gbBound_of_owcheck (lo := 230679011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_130_0
  have w1 : GBBound 231670002 232660000 991 :=
    gbBound_of_owcheck (lo := 231669011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_130_1
  have v1 : GBBound 230680002 232660000 991 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_130 : (19 + 256541/1000000 : ℝ) ≤ Real.log ((230680002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((230680002 : ℕ) : ℝ)) 19 (f := (256541/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_130 : (2 + 957849/1000000 : ℝ) ≤ Real.log (19 + 256541/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 256541/1000000 : ℝ)) 2 (f := (957849/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_130 : ∀ n, Even n → 230680002 ≤ n → n ≤ 232660000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_130 ls_130 (by norm_num) (by norm_num) bnd_130

theorem bnd_131 : GBBound 232660002 234640000 1063 := by
  have hq : ∀ x ∈ QKo 178, x ≤ 1063 := take_le 178 1063 (by decide +kernel)
  have w0 : GBBound 232660002 233650000 1063 :=
    gbBound_of_owcheck (lo := 232658939) (Wb := 495531) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_131_0
  have w1 : GBBound 233650002 234640000 1063 :=
    gbBound_of_owcheck (lo := 233648939) (Wb := 495531) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_131_1
  have v1 : GBBound 232660002 234640000 1063 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_131 : (19 + 265087/1000000 : ℝ) ≤ Real.log ((232660002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((232660002 : ℕ) : ℝ)) 19 (f := (265087/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_131 : (2 + 958293/1000000 : ℝ) ≤ Real.log (19 + 265087/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 265087/1000000 : ℝ)) 2 (f := (958293/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_131 : ∀ n, Even n → 232660002 ≤ n → n ≤ 234640000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_131 ls_131 (by norm_num) (by norm_num) bnd_131

theorem bnd_132 : GBBound 234640002 236620000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 234640002 235630000 907 :=
    gbBound_of_owcheck (lo := 234639095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_132_0
  have w1 : GBBound 235630002 236620000 907 :=
    gbBound_of_owcheck (lo := 235629095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_132_1
  have v1 : GBBound 234640002 236620000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_132 : (19 + 273561/1000000 : ℝ) ≤ Real.log ((234640002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((234640002 : ℕ) : ℝ)) 19 (f := (273561/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_132 : (2 + 958733/1000000 : ℝ) ≤ Real.log (19 + 273561/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 273561/1000000 : ℝ)) 2 (f := (958733/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_132 : ∀ n, Even n → 234640002 ≤ n → n ≤ 236620000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_132 ls_132 (by norm_num) (by norm_num) bnd_132

theorem bnd_133 : GBBound 236620002 238600000 991 := by
  have hq : ∀ x ∈ QKo 166, x ≤ 991 := take_le 166 991 (by decide +kernel)
  have w0 : GBBound 236620002 237610000 991 :=
    gbBound_of_owcheck (lo := 236619011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_133_0
  have w1 : GBBound 237610002 238600000 991 :=
    gbBound_of_owcheck (lo := 237609011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_133_1
  have v1 : GBBound 236620002 238600000 991 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_133 : (19 + 56393/200000 : ℝ) ≤ Real.log ((236620002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((236620002 : ℕ) : ℝ)) 19 (f := (56393/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_133 : (2 + 959169/1000000 : ℝ) ≤ Real.log (19 + 56393/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 56393/200000 : ℝ)) 2 (f := (959169/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_133 : ∀ n, Even n → 236620002 ≤ n → n ≤ 238600000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_133 ls_133 (by norm_num) (by norm_num) bnd_133

theorem bnd_134 : GBBound 238600002 240580000 919 := by
  have hq : ∀ x ∈ QKo 156, x ≤ 919 := take_le 156 919 (by decide +kernel)
  have w0 : GBBound 238600002 239590000 919 :=
    gbBound_of_owcheck (lo := 238599083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_134_0
  have w1 : GBBound 239590002 240580000 919 :=
    gbBound_of_owcheck (lo := 239589083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_134_1
  have v1 : GBBound 238600002 240580000 919 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_134 : (19 + 145149/500000 : ℝ) ≤ Real.log ((238600002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((238600002 : ℕ) : ℝ)) 19 (f := (145149/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_134 : (2 + 959601/1000000 : ℝ) ≤ Real.log (19 + 145149/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 145149/500000 : ℝ)) 2 (f := (959601/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_134 : ∀ n, Even n → 238600002 ≤ n → n ≤ 240580000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_134 ls_134 (by norm_num) (by norm_num) bnd_134

end LeanLab.GvLtR1989
