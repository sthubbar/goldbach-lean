module

public import LeanLab.OeSHP2014.Base
public import LeanLab.OeSHP2014.Win.W021
public import LeanLab.OeSHP2014.Win.W022
public import LeanLab.OeSHP2014.Win.W023
public import LeanLab.OeSHP2014.Win.W024
public import LeanLab.OeSHP2014.Win.W025
public import LeanLab.OeSHP2014.Win.W026
public import LeanLab.OeSHP2014.Win.W027
public import LeanLab.OeSHP2014.Win.W028
public import LeanLab.OeSHP2014.Win.W029
public import LeanLab.OeSHP2014.Win.W030
public import LeanLab.OeSHP2014.Win.W031

/-!
Segments 27 to 27, generated: for the Table 4 row n, p of each segment, the
window checks are joined to a bound p on the least Goldbach prime of every even number from n
up to the number before the next row, or up to 10^8.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

theorem seg_27 : GBBound 60119912 100000000 1093 := by
  have hq : ∀ x ∈ QKo 182, x ≤ 1093 := take_le 182 1093 (by decide +kernel)
  have w0 : GBBound 60119912 61109910 1093 :=
    gbBound_of_owcheck (lo := 60118819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_0
  have w1 : GBBound 61109912 62099910 1093 :=
    gbBound_of_owcheck (lo := 61108819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_1
  have w2 : GBBound 62099912 63089910 1093 :=
    gbBound_of_owcheck (lo := 62098819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_2
  have w3 : GBBound 63089912 64079910 1093 :=
    gbBound_of_owcheck (lo := 63088819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_3
  have w4 : GBBound 64079912 65069910 1093 :=
    gbBound_of_owcheck (lo := 64078819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_4
  have w5 : GBBound 65069912 66059910 1093 :=
    gbBound_of_owcheck (lo := 65068819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_5
  have w6 : GBBound 66059912 67049910 1093 :=
    gbBound_of_owcheck (lo := 66058819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_6
  have w7 : GBBound 67049912 68039910 1093 :=
    gbBound_of_owcheck (lo := 67048819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_7
  have w8 : GBBound 68039912 69029910 1093 :=
    gbBound_of_owcheck (lo := 68038819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_8
  have w9 : GBBound 69029912 70019910 1093 :=
    gbBound_of_owcheck (lo := 69028819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_9
  have w10 : GBBound 70019912 71009910 1093 :=
    gbBound_of_owcheck (lo := 70018819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_10
  have w11 : GBBound 71009912 71999910 1093 :=
    gbBound_of_owcheck (lo := 71008819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_11
  have w12 : GBBound 71999912 72989910 1093 :=
    gbBound_of_owcheck (lo := 71998819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_12
  have w13 : GBBound 72989912 73979910 1093 :=
    gbBound_of_owcheck (lo := 72988819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_13
  have w14 : GBBound 73979912 74969910 1093 :=
    gbBound_of_owcheck (lo := 73978819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_14
  have w15 : GBBound 74969912 75959910 1093 :=
    gbBound_of_owcheck (lo := 74968819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_15
  have w16 : GBBound 75959912 76949910 1093 :=
    gbBound_of_owcheck (lo := 75958819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_16
  have w17 : GBBound 76949912 77939910 1093 :=
    gbBound_of_owcheck (lo := 76948819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_17
  have w18 : GBBound 77939912 78929910 1093 :=
    gbBound_of_owcheck (lo := 77938819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_18
  have w19 : GBBound 78929912 79919910 1093 :=
    gbBound_of_owcheck (lo := 78928819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_19
  have w20 : GBBound 79919912 80909910 1093 :=
    gbBound_of_owcheck (lo := 79918819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_20
  have w21 : GBBound 80909912 81899910 1093 :=
    gbBound_of_owcheck (lo := 80908819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_21
  have w22 : GBBound 81899912 82889910 1093 :=
    gbBound_of_owcheck (lo := 81898819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_22
  have w23 : GBBound 82889912 83879910 1093 :=
    gbBound_of_owcheck (lo := 82888819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_23
  have w24 : GBBound 83879912 84869910 1093 :=
    gbBound_of_owcheck (lo := 83878819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_24
  have w25 : GBBound 84869912 85859910 1093 :=
    gbBound_of_owcheck (lo := 84868819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_25
  have w26 : GBBound 85859912 86849910 1093 :=
    gbBound_of_owcheck (lo := 85858819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_26
  have w27 : GBBound 86849912 87839910 1093 :=
    gbBound_of_owcheck (lo := 86848819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_27
  have w28 : GBBound 87839912 88829910 1093 :=
    gbBound_of_owcheck (lo := 87838819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_28
  have w29 : GBBound 88829912 89819910 1093 :=
    gbBound_of_owcheck (lo := 88828819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_29
  have w30 : GBBound 89819912 90809910 1093 :=
    gbBound_of_owcheck (lo := 89818819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_30
  have w31 : GBBound 90809912 91799910 1093 :=
    gbBound_of_owcheck (lo := 90808819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_31
  have w32 : GBBound 91799912 92789910 1093 :=
    gbBound_of_owcheck (lo := 91798819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_32
  have w33 : GBBound 92789912 93779910 1093 :=
    gbBound_of_owcheck (lo := 92788819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_33
  have w34 : GBBound 93779912 94769910 1093 :=
    gbBound_of_owcheck (lo := 93778819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_34
  have w35 : GBBound 94769912 95759910 1093 :=
    gbBound_of_owcheck (lo := 94768819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_35
  have w36 : GBBound 95759912 96749910 1093 :=
    gbBound_of_owcheck (lo := 95758819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_36
  have w37 : GBBound 96749912 97739910 1093 :=
    gbBound_of_owcheck (lo := 96748819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_37
  have w38 : GBBound 97739912 98729910 1093 :=
    gbBound_of_owcheck (lo := 97738819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_38
  have w39 : GBBound 98729912 99719910 1093 :=
    gbBound_of_owcheck (lo := 98728819) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_39
  have w40 : GBBound 99719912 100000000 1093 :=
    gbBound_of_owcheck (lo := 99718819) (Wb := 140591) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_40
  have v1 : GBBound 60119912 62099910 1093 := GBBound.join w0 w1 (by norm_num) (by decide)
  have v2 : GBBound 60119912 63089910 1093 := GBBound.join v1 w2 (by norm_num) (by decide)
  have v3 : GBBound 60119912 64079910 1093 := GBBound.join v2 w3 (by norm_num) (by decide)
  have v4 : GBBound 60119912 65069910 1093 := GBBound.join v3 w4 (by norm_num) (by decide)
  have v5 : GBBound 60119912 66059910 1093 := GBBound.join v4 w5 (by norm_num) (by decide)
  have v6 : GBBound 60119912 67049910 1093 := GBBound.join v5 w6 (by norm_num) (by decide)
  have v7 : GBBound 60119912 68039910 1093 := GBBound.join v6 w7 (by norm_num) (by decide)
  have v8 : GBBound 60119912 69029910 1093 := GBBound.join v7 w8 (by norm_num) (by decide)
  have v9 : GBBound 60119912 70019910 1093 := GBBound.join v8 w9 (by norm_num) (by decide)
  have v10 : GBBound 60119912 71009910 1093 := GBBound.join v9 w10 (by norm_num) (by decide)
  have v11 : GBBound 60119912 71999910 1093 := GBBound.join v10 w11 (by norm_num) (by decide)
  have v12 : GBBound 60119912 72989910 1093 := GBBound.join v11 w12 (by norm_num) (by decide)
  have v13 : GBBound 60119912 73979910 1093 := GBBound.join v12 w13 (by norm_num) (by decide)
  have v14 : GBBound 60119912 74969910 1093 := GBBound.join v13 w14 (by norm_num) (by decide)
  have v15 : GBBound 60119912 75959910 1093 := GBBound.join v14 w15 (by norm_num) (by decide)
  have v16 : GBBound 60119912 76949910 1093 := GBBound.join v15 w16 (by norm_num) (by decide)
  have v17 : GBBound 60119912 77939910 1093 := GBBound.join v16 w17 (by norm_num) (by decide)
  have v18 : GBBound 60119912 78929910 1093 := GBBound.join v17 w18 (by norm_num) (by decide)
  have v19 : GBBound 60119912 79919910 1093 := GBBound.join v18 w19 (by norm_num) (by decide)
  have v20 : GBBound 60119912 80909910 1093 := GBBound.join v19 w20 (by norm_num) (by decide)
  have v21 : GBBound 60119912 81899910 1093 := GBBound.join v20 w21 (by norm_num) (by decide)
  have v22 : GBBound 60119912 82889910 1093 := GBBound.join v21 w22 (by norm_num) (by decide)
  have v23 : GBBound 60119912 83879910 1093 := GBBound.join v22 w23 (by norm_num) (by decide)
  have v24 : GBBound 60119912 84869910 1093 := GBBound.join v23 w24 (by norm_num) (by decide)
  have v25 : GBBound 60119912 85859910 1093 := GBBound.join v24 w25 (by norm_num) (by decide)
  have v26 : GBBound 60119912 86849910 1093 := GBBound.join v25 w26 (by norm_num) (by decide)
  have v27 : GBBound 60119912 87839910 1093 := GBBound.join v26 w27 (by norm_num) (by decide)
  have v28 : GBBound 60119912 88829910 1093 := GBBound.join v27 w28 (by norm_num) (by decide)
  have v29 : GBBound 60119912 89819910 1093 := GBBound.join v28 w29 (by norm_num) (by decide)
  have v30 : GBBound 60119912 90809910 1093 := GBBound.join v29 w30 (by norm_num) (by decide)
  have v31 : GBBound 60119912 91799910 1093 := GBBound.join v30 w31 (by norm_num) (by decide)
  have v32 : GBBound 60119912 92789910 1093 := GBBound.join v31 w32 (by norm_num) (by decide)
  have v33 : GBBound 60119912 93779910 1093 := GBBound.join v32 w33 (by norm_num) (by decide)
  have v34 : GBBound 60119912 94769910 1093 := GBBound.join v33 w34 (by norm_num) (by decide)
  have v35 : GBBound 60119912 95759910 1093 := GBBound.join v34 w35 (by norm_num) (by decide)
  have v36 : GBBound 60119912 96749910 1093 := GBBound.join v35 w36 (by norm_num) (by decide)
  have v37 : GBBound 60119912 97739910 1093 := GBBound.join v36 w37 (by norm_num) (by decide)
  have v38 : GBBound 60119912 98729910 1093 := GBBound.join v37 w38 (by norm_num) (by decide)
  have v39 : GBBound 60119912 99719910 1093 := GBBound.join v38 w39 (by norm_num) (by decide)
  have v40 : GBBound 60119912 100000000 1093 := GBBound.join v39 w40 (by norm_num) (by decide)
  exact v40

end LeanLab.OeSHP2014
