module

public import LeanLab.OeSHP2014.Base
public import LeanLab.OeSHP2014.Win.W015
public import LeanLab.OeSHP2014.Win.W016
public import LeanLab.OeSHP2014.Win.W017
public import LeanLab.OeSHP2014.Win.W018
public import LeanLab.OeSHP2014.Win.W019
public import LeanLab.OeSHP2014.Win.W020

/-!
Segments 26 to 26, generated: for the Table 4 row n, p of each segment, the
window checks are joined to a bound p on the least Goldbach prime of every even number from n
up to the number before the next row, or up to 10^8.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

theorem seg_26 : GBBound 37998938 60119910 1039 := by
  have hq : ∀ x ∈ QKo 174, x ≤ 1039 := take_le 174 1039 (by decide +kernel)
  have w0 : GBBound 37998938 38988936 1039 :=
    gbBound_of_owcheck (lo := 37997899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_0
  have w1 : GBBound 38988938 39978936 1039 :=
    gbBound_of_owcheck (lo := 38987899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_1
  have w2 : GBBound 39978938 40968936 1039 :=
    gbBound_of_owcheck (lo := 39977899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_2
  have w3 : GBBound 40968938 41958936 1039 :=
    gbBound_of_owcheck (lo := 40967899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_3
  have w4 : GBBound 41958938 42948936 1039 :=
    gbBound_of_owcheck (lo := 41957899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_4
  have w5 : GBBound 42948938 43938936 1039 :=
    gbBound_of_owcheck (lo := 42947899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_5
  have w6 : GBBound 43938938 44928936 1039 :=
    gbBound_of_owcheck (lo := 43937899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_6
  have w7 : GBBound 44928938 45918936 1039 :=
    gbBound_of_owcheck (lo := 44927899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_7
  have w8 : GBBound 45918938 46908936 1039 :=
    gbBound_of_owcheck (lo := 45917899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_8
  have w9 : GBBound 46908938 47898936 1039 :=
    gbBound_of_owcheck (lo := 46907899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_9
  have w10 : GBBound 47898938 48888936 1039 :=
    gbBound_of_owcheck (lo := 47897899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_10
  have w11 : GBBound 48888938 49878936 1039 :=
    gbBound_of_owcheck (lo := 48887899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_11
  have w12 : GBBound 49878938 50868936 1039 :=
    gbBound_of_owcheck (lo := 49877899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_12
  have w13 : GBBound 50868938 51858936 1039 :=
    gbBound_of_owcheck (lo := 50867899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_13
  have w14 : GBBound 51858938 52848936 1039 :=
    gbBound_of_owcheck (lo := 51857899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_14
  have w15 : GBBound 52848938 53838936 1039 :=
    gbBound_of_owcheck (lo := 52847899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_15
  have w16 : GBBound 53838938 54828936 1039 :=
    gbBound_of_owcheck (lo := 53837899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_16
  have w17 : GBBound 54828938 55818936 1039 :=
    gbBound_of_owcheck (lo := 54827899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_17
  have w18 : GBBound 55818938 56808936 1039 :=
    gbBound_of_owcheck (lo := 55817899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_18
  have w19 : GBBound 56808938 57798936 1039 :=
    gbBound_of_owcheck (lo := 56807899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_19
  have w20 : GBBound 57798938 58788936 1039 :=
    gbBound_of_owcheck (lo := 57797899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_20
  have w21 : GBBound 58788938 59778936 1039 :=
    gbBound_of_owcheck (lo := 58787899) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_21
  have w22 : GBBound 59778938 60119910 1039 :=
    gbBound_of_owcheck (lo := 59777899) (Wb := 171006) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_22
  have v1 : GBBound 37998938 39978936 1039 := GBBound.join w0 w1 (by norm_num) (by decide)
  have v2 : GBBound 37998938 40968936 1039 := GBBound.join v1 w2 (by norm_num) (by decide)
  have v3 : GBBound 37998938 41958936 1039 := GBBound.join v2 w3 (by norm_num) (by decide)
  have v4 : GBBound 37998938 42948936 1039 := GBBound.join v3 w4 (by norm_num) (by decide)
  have v5 : GBBound 37998938 43938936 1039 := GBBound.join v4 w5 (by norm_num) (by decide)
  have v6 : GBBound 37998938 44928936 1039 := GBBound.join v5 w6 (by norm_num) (by decide)
  have v7 : GBBound 37998938 45918936 1039 := GBBound.join v6 w7 (by norm_num) (by decide)
  have v8 : GBBound 37998938 46908936 1039 := GBBound.join v7 w8 (by norm_num) (by decide)
  have v9 : GBBound 37998938 47898936 1039 := GBBound.join v8 w9 (by norm_num) (by decide)
  have v10 : GBBound 37998938 48888936 1039 := GBBound.join v9 w10 (by norm_num) (by decide)
  have v11 : GBBound 37998938 49878936 1039 := GBBound.join v10 w11 (by norm_num) (by decide)
  have v12 : GBBound 37998938 50868936 1039 := GBBound.join v11 w12 (by norm_num) (by decide)
  have v13 : GBBound 37998938 51858936 1039 := GBBound.join v12 w13 (by norm_num) (by decide)
  have v14 : GBBound 37998938 52848936 1039 := GBBound.join v13 w14 (by norm_num) (by decide)
  have v15 : GBBound 37998938 53838936 1039 := GBBound.join v14 w15 (by norm_num) (by decide)
  have v16 : GBBound 37998938 54828936 1039 := GBBound.join v15 w16 (by norm_num) (by decide)
  have v17 : GBBound 37998938 55818936 1039 := GBBound.join v16 w17 (by norm_num) (by decide)
  have v18 : GBBound 37998938 56808936 1039 := GBBound.join v17 w18 (by norm_num) (by decide)
  have v19 : GBBound 37998938 57798936 1039 := GBBound.join v18 w19 (by norm_num) (by decide)
  have v20 : GBBound 37998938 58788936 1039 := GBBound.join v19 w20 (by norm_num) (by decide)
  have v21 : GBBound 37998938 59778936 1039 := GBBound.join v20 w21 (by norm_num) (by decide)
  have v22 : GBBound 37998938 60119910 1039 := GBBound.join v21 w22 (by norm_num) (by decide)
  exact v22

end LeanLab.OeSHP2014
