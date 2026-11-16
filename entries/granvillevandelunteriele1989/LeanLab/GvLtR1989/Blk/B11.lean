module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W078
public import LeanLab.GvLtR1989.Win.W079
public import LeanLab.GvLtR1989.Win.W080
public import LeanLab.GvLtR1989.Win.W081
public import LeanLab.GvLtR1989.Win.W082
public import LeanLab.GvLtR1989.Win.W083
public import LeanLab.GvLtR1989.Win.W084

/-!
Blocks 165 to 176, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_165 : GBBound 299980002 301960000 1069 := by
  have hq : ∀ x ∈ QKo 179, x ≤ 1069 := take_le 179 1069 (by decide +kernel)
  have w0 : GBBound 299980002 300970000 1069 :=
    gbBound_of_owcheck (lo := 299978933) (Wb := 495534) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_165_0
  have w1 : GBBound 300970002 301960000 1069 :=
    gbBound_of_owcheck (lo := 300968933) (Wb := 495534) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_165_1
  have v1 : GBBound 299980002 301960000 1069 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_165 : (19 + 20769/40000 : ℝ) ≤ Real.log ((299980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((299980002 : ℕ) : ℝ)) 19 (f := (20769/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_165 : (2 + 485699/500000 : ℝ) ≤ Real.log (19 + 20769/40000 : ℝ) := by
  have h := le_log_of (x := (19 + 20769/40000 : ℝ)) 2 (f := (485699/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_165 : ∀ n, Even n → 299980002 ≤ n → n ≤ 301960000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_165 ls_165 (by norm_num) (by norm_num) bnd_165

theorem bnd_166 : GBBound 301960002 303940000 829 := by
  have hq : ∀ x ∈ QKo 144, x ≤ 829 := take_le 144 829 (by decide +kernel)
  have w0 : GBBound 301960002 302950000 829 :=
    gbBound_of_owcheck (lo := 301959173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_166_0
  have w1 : GBBound 302950002 303940000 829 :=
    gbBound_of_owcheck (lo := 302949173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_166_1
  have v1 : GBBound 301960002 303940000 829 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_166 : (19 + 131451/250000 : ℝ) ≤ Real.log ((301960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((301960002 : ℕ) : ℝ)) 19 (f := (131451/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_166 : (2 + 194347/200000 : ℝ) ≤ Real.log (19 + 131451/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 131451/250000 : ℝ)) 2 (f := (194347/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_166 : ∀ n, Even n → 301960002 ≤ n → n ≤ 303940000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_166 ls_166 (by norm_num) (by norm_num) bnd_166

theorem bnd_167 : GBBound 303940002 305920000 883 := by
  have hq : ∀ x ∈ QKo 152, x ≤ 883 := take_le 152 883 (by decide +kernel)
  have w0 : GBBound 303940002 304930000 883 :=
    gbBound_of_owcheck (lo := 303939119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_167_0
  have w1 : GBBound 304930002 305920000 883 :=
    gbBound_of_owcheck (lo := 304929119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_167_1
  have v1 : GBBound 303940002 305920000 883 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_167 : (19 + 532339/1000000 : ℝ) ≤ Real.log ((303940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((303940002 : ℕ) : ℝ)) 19 (f := (532339/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_167 : (2 + 97207/100000 : ℝ) ≤ Real.log (19 + 532339/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 532339/1000000 : ℝ)) 2 (f := (97207/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_167 : ∀ n, Even n → 303940002 ≤ n → n ≤ 305920000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_167 ls_167 (by norm_num) (by norm_num) bnd_167

theorem bnd_168 : GBBound 305920002 307900000 1021 := by
  have hq : ∀ x ∈ QKo 171, x ≤ 1021 := take_le 171 1021 (by decide +kernel)
  have w0 : GBBound 305920002 306910000 1021 :=
    gbBound_of_owcheck (lo := 305918981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_168_0
  have w1 : GBBound 306910002 307900000 1021 :=
    gbBound_of_owcheck (lo := 306908981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_168_1
  have v1 : GBBound 305920002 307900000 1021 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_168 : (19 + 538833/1000000 : ℝ) ≤ Real.log ((305920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((305920002 : ℕ) : ℝ)) 19 (f := (538833/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_168 : (2 + 486201/500000 : ℝ) ≤ Real.log (19 + 538833/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 538833/1000000 : ℝ)) 2 (f := (486201/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_168 : ∀ n, Even n → 305920002 ≤ n → n ≤ 307900000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_168 ls_168 (by norm_num) (by norm_num) bnd_168

theorem bnd_169 : GBBound 307900002 309880000 797 := by
  have hq : ∀ x ∈ QKo 138, x ≤ 797 := take_le 138 797 (by decide +kernel)
  have w0 : GBBound 307900002 308890000 797 :=
    gbBound_of_owcheck (lo := 307899205) (Wb := 495398) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_169_0
  have w1 : GBBound 308890002 309880000 797 :=
    gbBound_of_owcheck (lo := 308889205) (Wb := 495398) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_169_1
  have v1 : GBBound 307900002 309880000 797 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_169 : (19 + 136321/250000 : ℝ) ≤ Real.log ((307900002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((307900002 : ℕ) : ℝ)) 19 (f := (136321/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_169 : (2 + 972733/1000000 : ℝ) ≤ Real.log (19 + 136321/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 136321/250000 : ℝ)) 2 (f := (972733/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_169 : ∀ n, Even n → 307900002 ≤ n → n ≤ 309880000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_169 ls_169 (by norm_num) (by norm_num) bnd_169

theorem bnd_170 : GBBound 309880002 311860000 1021 := by
  have hq : ∀ x ∈ QKo 171, x ≤ 1021 := take_le 171 1021 (by decide +kernel)
  have w0 : GBBound 309880002 310870000 1021 :=
    gbBound_of_owcheck (lo := 309878981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_170_0
  have w1 : GBBound 310870002 311860000 1021 :=
    gbBound_of_owcheck (lo := 310868981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_170_1
  have v1 : GBBound 309880002 311860000 1021 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_170 : (19 + 275847/500000 : ℝ) ≤ Real.log ((309880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((309880002 : ℕ) : ℝ)) 19 (f := (275847/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_170 : (2 + 48653/50000 : ℝ) ≤ Real.log (19 + 275847/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 275847/500000 : ℝ)) 2 (f := (48653/50000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_170 : ∀ n, Even n → 309880002 ≤ n → n ≤ 311860000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_170 ls_170 (by norm_num) (by norm_num) bnd_170

theorem bnd_171 : GBBound 311860002 313840000 1087 := by
  have hq : ∀ x ∈ QKo 180, x ≤ 1087 := take_le 180 1087 (by decide +kernel)
  have w0 : GBBound 311860002 312850000 1087 :=
    gbBound_of_owcheck (lo := 311858915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_171_0
  have w1 : GBBound 312850002 313840000 1087 :=
    gbBound_of_owcheck (lo := 312848915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_171_1
  have v1 : GBBound 311860002 313840000 1087 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_171 : (19 + 558063/1000000 : ℝ) ≤ Real.log ((311860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((311860002 : ℕ) : ℝ)) 19 (f := (558063/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_171 : (2 + 486693/500000 : ℝ) ≤ Real.log (19 + 558063/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 558063/1000000 : ℝ)) 2 (f := (486693/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_171 : ∀ n, Even n → 311860002 ≤ n → n ≤ 313840000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_171 ls_171 (by norm_num) (by norm_num) bnd_171

theorem bnd_172 : GBBound 313840002 315820000 877 := by
  have hq : ∀ x ∈ QKo 150, x ≤ 877 := take_le 150 877 (by decide +kernel)
  have w0 : GBBound 313840002 314830000 877 :=
    gbBound_of_owcheck (lo := 313839125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_172_0
  have w1 : GBBound 314830002 315820000 877 :=
    gbBound_of_owcheck (lo := 314829125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_172_1
  have v1 : GBBound 313840002 315820000 877 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_172 : (19 + 70549/125000 : ℝ) ≤ Real.log ((313840002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((313840002 : ℕ) : ℝ)) 19 (f := (70549/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_172 : (2 + 97371/100000 : ℝ) ≤ Real.log (19 + 70549/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 70549/125000 : ℝ)) 2 (f := (97371/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_172 : ∀ n, Even n → 313840002 ≤ n → n ≤ 315820000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_172 ls_172 (by norm_num) (by norm_num) bnd_172

theorem bnd_173 : GBBound 315820002 317800000 829 := by
  have hq : ∀ x ∈ QKo 144, x ≤ 829 := take_le 144 829 (by decide +kernel)
  have w0 : GBBound 315820002 316810000 829 :=
    gbBound_of_owcheck (lo := 315819173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_173_0
  have w1 : GBBound 316810002 317800000 829 :=
    gbBound_of_owcheck (lo := 316809173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_173_1
  have v1 : GBBound 315820002 317800000 829 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_173 : (19 + 570681/1000000 : ℝ) ≤ Real.log ((315820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((315820002 : ℕ) : ℝ)) 19 (f := (570681/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_173 : (2 + 974031/1000000 : ℝ) ≤ Real.log (19 + 570681/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 570681/1000000 : ℝ)) 2 (f := (974031/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_173 : ∀ n, Even n → 315820002 ≤ n → n ≤ 317800000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_173 ls_173 (by norm_num) (by norm_num) bnd_173

theorem bnd_174 : GBBound 317800002 319780000 977 := by
  have hq : ∀ x ∈ QKo 164, x ≤ 977 := take_le 164 977 (by decide +kernel)
  have w0 : GBBound 317800002 318790000 977 :=
    gbBound_of_owcheck (lo := 317799025) (Wb := 495488) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_174_0
  have w1 : GBBound 318790002 319780000 977 :=
    gbBound_of_owcheck (lo := 318789025) (Wb := 495488) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_174_1
  have v1 : GBBound 317800002 319780000 977 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_174 : (19 + 576931/1000000 : ℝ) ≤ Real.log ((317800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((317800002 : ℕ) : ℝ)) 19 (f := (576931/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_174 : (2 + 19487/20000 : ℝ) ≤ Real.log (19 + 576931/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 576931/1000000 : ℝ)) 2 (f := (19487/20000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_174 : ∀ n, Even n → 317800002 ≤ n → n ≤ 319780000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_174 ls_174 (by norm_num) (by norm_num) bnd_174

theorem bnd_175 : GBBound 319780002 321760000 1009 := by
  have hq : ∀ x ∈ QKo 168, x ≤ 1009 := take_le 168 1009 (by decide +kernel)
  have w0 : GBBound 319780002 320770000 1009 :=
    gbBound_of_owcheck (lo := 319778993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_175_0
  have w1 : GBBound 320770002 321760000 1009 :=
    gbBound_of_owcheck (lo := 320768993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_175_1
  have v1 : GBBound 319780002 321760000 1009 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_175 : (19 + 291571/500000 : ℝ) ≤ Real.log ((319780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((319780002 : ℕ) : ℝ)) 19 (f := (291571/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_175 : (2 + 243667/250000 : ℝ) ≤ Real.log (19 + 291571/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 291571/500000 : ℝ)) 2 (f := (243667/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_175 : ∀ n, Even n → 319780002 ≤ n → n ≤ 321760000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_175 ls_175 (by norm_num) (by norm_num) bnd_175

theorem bnd_176 : GBBound 321760002 323740000 971 := by
  have hq : ∀ x ∈ QKo 163, x ≤ 971 := take_le 163 971 (by decide +kernel)
  have w0 : GBBound 321760002 322750000 971 :=
    gbBound_of_owcheck (lo := 321759031) (Wb := 495485) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_176_0
  have w1 : GBBound 322750002 323740000 971 :=
    gbBound_of_owcheck (lo := 322749031) (Wb := 495485) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_176_1
  have v1 : GBBound 321760002 323740000 971 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_176 : (19 + 117863/200000 : ℝ) ≤ Real.log ((321760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((321760002 : ℕ) : ℝ)) 19 (f := (117863/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_176 : (2 + 974983/1000000 : ℝ) ≤ Real.log (19 + 117863/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 117863/200000 : ℝ)) 2 (f := (974983/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_176 : ∀ n, Even n → 321760002 ≤ n → n ≤ 323740000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_176 ls_176 (by norm_num) (by norm_num) bnd_176

end LeanLab.GvLtR1989
