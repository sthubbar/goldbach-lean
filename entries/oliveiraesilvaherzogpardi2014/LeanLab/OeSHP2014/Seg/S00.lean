module

public import LeanLab.OeSHP2014.Base
public import LeanLab.OeSHP2014.Win.W000
public import LeanLab.OeSHP2014.Win.W001
public import LeanLab.OeSHP2014.Win.W002
public import LeanLab.OeSHP2014.Win.W003
public import LeanLab.OeSHP2014.Win.W004
public import LeanLab.OeSHP2014.Win.W005
public import LeanLab.OeSHP2014.Win.W006
public import LeanLab.OeSHP2014.Win.W007

/-!
Segments 0 to 22, generated: for the Table 4 row n, p of each segment, the
window checks are joined to a bound p on the least Goldbach prime of every even number from n
up to the number before the next row, or up to 10^8.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

theorem seg_0 : GBBound 6 10 3 := by
  have hq : ∀ x ∈ QKo 1, x ≤ 3 := take_le 1 3 (by decide +kernel)
  have w0 : GBBound 6 10 3 :=
    gbBound_of_owcheck (lo := 3) (Wb := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_0_0
  exact w0

theorem seg_1 : GBBound 12 28 5 := by
  have hq : ∀ x ∈ QKo 2, x ≤ 5 := take_le 2 5 (by decide +kernel)
  have w0 : GBBound 12 28 5 :=
    gbBound_of_owcheck (lo := 7) (Wb := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_1_0
  exact w0

theorem seg_2 : GBBound 30 96 7 := by
  have hq : ∀ x ∈ QKo 3, x ≤ 7 := take_le 3 7 (by decide +kernel)
  have w0 : GBBound 30 96 7 :=
    gbBound_of_owcheck (lo := 23) (Wb := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_2_0
  exact w0

theorem seg_3 : GBBound 98 218 19 := by
  have hq : ∀ x ∈ QKo 7, x ≤ 19 := take_le 7 19 (by decide +kernel)
  have w0 : GBBound 98 218 19 :=
    gbBound_of_owcheck (lo := 79) (Wb := 70) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_3_0
  exact w0

theorem seg_4 : GBBound 220 306 23 := by
  have hq : ∀ x ∈ QKo 8, x ≤ 23 := take_le 8 23 (by decide +kernel)
  have w0 : GBBound 220 306 23 :=
    gbBound_of_owcheck (lo := 197) (Wb := 55) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_4_0
  exact w0

theorem seg_5 : GBBound 308 554 31 := by
  have hq : ∀ x ∈ QKo 10, x ≤ 31 := take_le 10 31 (by decide +kernel)
  have w0 : GBBound 308 554 31 :=
    gbBound_of_owcheck (lo := 277) (Wb := 139) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_5_0
  exact w0

theorem seg_6 : GBBound 556 990 47 := by
  have hq : ∀ x ∈ QKo 14, x ≤ 47 := take_le 14 47 (by decide +kernel)
  have w0 : GBBound 556 990 47 :=
    gbBound_of_owcheck (lo := 509) (Wb := 241) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_6_0
  exact w0

theorem seg_7 : GBBound 992 2640 73 := by
  have hq : ∀ x ∈ QKo 20, x ≤ 73 := take_le 20 73 (by decide +kernel)
  have w0 : GBBound 992 2640 73 :=
    gbBound_of_owcheck (lo := 919) (Wb := 861) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_7_0
  exact w0

theorem seg_8 : GBBound 2642 5370 103 := by
  have hq : ∀ x ∈ QKo 26, x ≤ 103 := take_le 26 103 (by decide +kernel)
  have w0 : GBBound 2642 5370 103 :=
    gbBound_of_owcheck (lo := 2539) (Wb := 1416) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_8_0
  exact w0

theorem seg_9 : GBBound 5372 7424 139 := by
  have hq : ∀ x ∈ QKo 33, x ≤ 139 := take_le 33 139 (by decide +kernel)
  have w0 : GBBound 5372 7424 139 :=
    gbBound_of_owcheck (lo := 5233) (Wb := 1096) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_9_0
  exact w0

theorem seg_10 : GBBound 7426 43530 173 := by
  have hq : ∀ x ∈ QKo 39, x ≤ 173 := take_le 39 173 (by decide +kernel)
  have w0 : GBBound 7426 43530 173 :=
    gbBound_of_owcheck (lo := 7253) (Wb := 18139) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_10_0
  exact w0

theorem seg_11 : GBBound 43532 54242 211 := by
  have hq : ∀ x ∈ QKo 46, x ≤ 211 := take_le 46 211 (by decide +kernel)
  have w0 : GBBound 43532 54242 211 :=
    gbBound_of_owcheck (lo := 43321) (Wb := 5461) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_11_0
  exact w0

theorem seg_12 : GBBound 54244 63272 233 := by
  have hq : ∀ x ∈ QKo 50, x ≤ 233 := take_le 50 233 (by decide +kernel)
  have w0 : GBBound 54244 63272 233 :=
    gbBound_of_owcheck (lo := 54011) (Wb := 4631) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_12_0
  exact w0

theorem seg_13 : GBBound 63274 113670 293 := by
  have hq : ∀ x ∈ QKo 61, x ≤ 293 := take_le 61 293 (by decide +kernel)
  have w0 : GBBound 63274 113670 293 :=
    gbBound_of_owcheck (lo := 62981) (Wb := 25345) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_13_0
  exact w0

theorem seg_14 : GBBound 113672 128166 313 := by
  have hq : ∀ x ∈ QKo 64, x ≤ 313 := take_le 64 313 (by decide +kernel)
  have w0 : GBBound 113672 128166 313 :=
    gbBound_of_owcheck (lo := 113359) (Wb := 7404) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_14_0
  exact w0

theorem seg_15 : GBBound 128168 194426 331 := by
  have hq : ∀ x ∈ QKo 66, x ≤ 331 := take_le 66 331 (by decide +kernel)
  have w0 : GBBound 128168 194426 331 :=
    gbBound_of_owcheck (lo := 127837) (Wb := 33295) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_15_0
  exact w0

theorem seg_16 : GBBound 194428 194468 359 := by
  have hq : ∀ x ∈ QKo 71, x ≤ 359 := take_le 71 359 (by decide +kernel)
  have w0 : GBBound 194428 194468 359 :=
    gbBound_of_owcheck (lo := 194069) (Wb := 200) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_16_0
  exact w0

theorem seg_17 : GBBound 194470 413570 383 := by
  have hq : ∀ x ∈ QKo 75, x ≤ 383 := take_le 75 383 (by decide +kernel)
  have w0 : GBBound 194470 413570 383 :=
    gbBound_of_owcheck (lo := 194087) (Wb := 109742) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_17_0
  exact w0

theorem seg_18 : GBBound 413572 503220 389 := by
  have hq : ∀ x ∈ QKo 76, x ≤ 389 := take_le 76 389 (by decide +kernel)
  have w0 : GBBound 413572 503220 389 :=
    gbBound_of_owcheck (lo := 413183) (Wb := 45019) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_18_0
  exact w0

theorem seg_19 : GBBound 503222 1077420 523 := by
  have hq : ∀ x ∈ QKo 98, x ≤ 523 := take_le 98 523 (by decide +kernel)
  have w0 : GBBound 503222 1077420 523 :=
    gbBound_of_owcheck (lo := 502699) (Wb := 287361) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_19_0
  exact w0

theorem seg_20 : GBBound 1077422 3526956 601 := by
  have hq : ∀ x ∈ QKo 109, x ≤ 601 := take_le 109 601 (by decide +kernel)
  have w0 : GBBound 1077422 2067420 601 :=
    gbBound_of_owcheck (lo := 1076821) (Wb := 495300) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_20_0
  have w1 : GBBound 2067422 3057420 601 :=
    gbBound_of_owcheck (lo := 2066821) (Wb := 495300) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_20_1
  have w2 : GBBound 3057422 3526956 601 :=
    gbBound_of_owcheck (lo := 3056821) (Wb := 235068) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_20_2
  have v1 : GBBound 1077422 3057420 601 := GBBound.join w0 w1 (by norm_num) (by decide)
  have v2 : GBBound 1077422 3526956 601 := GBBound.join v1 w2 (by norm_num) (by decide)
  exact v2

theorem seg_21 : GBBound 3526958 3807402 727 := by
  have hq : ∀ x ∈ QKo 128, x ≤ 727 := take_le 128 727 (by decide +kernel)
  have w0 : GBBound 3526958 3807402 727 :=
    gbBound_of_owcheck (lo := 3526231) (Wb := 140586) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_21_0
  exact w0

theorem seg_22 : GBBound 3807404 10759920 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 3807404 4797402 751 :=
    gbBound_of_owcheck (lo := 3806653) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_0
  have w1 : GBBound 4797404 5787402 751 :=
    gbBound_of_owcheck (lo := 4796653) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_1
  have w2 : GBBound 5787404 6777402 751 :=
    gbBound_of_owcheck (lo := 5786653) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_2
  have w3 : GBBound 6777404 7767402 751 :=
    gbBound_of_owcheck (lo := 6776653) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_3
  have w4 : GBBound 7767404 8757402 751 :=
    gbBound_of_owcheck (lo := 7766653) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_4
  have w5 : GBBound 8757404 9747402 751 :=
    gbBound_of_owcheck (lo := 8756653) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_5
  have w6 : GBBound 9747404 10737402 751 :=
    gbBound_of_owcheck (lo := 9746653) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_6
  have w7 : GBBound 10737404 10759920 751 :=
    gbBound_of_owcheck (lo := 10736653) (Wb := 11634) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_7
  have v1 : GBBound 3807404 5787402 751 := GBBound.join w0 w1 (by norm_num) (by decide)
  have v2 : GBBound 3807404 6777402 751 := GBBound.join v1 w2 (by norm_num) (by decide)
  have v3 : GBBound 3807404 7767402 751 := GBBound.join v2 w3 (by norm_num) (by decide)
  have v4 : GBBound 3807404 8757402 751 := GBBound.join v3 w4 (by norm_num) (by decide)
  have v5 : GBBound 3807404 9747402 751 := GBBound.join v4 w5 (by norm_num) (by decide)
  have v6 : GBBound 3807404 10737402 751 := GBBound.join v5 w6 (by norm_num) (by decide)
  have v7 : GBBound 3807404 10759920 751 := GBBound.join v6 w7 (by norm_num) (by decide)
  exact v7

end LeanLab.OeSHP2014
