import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open scoped BigOperators

namespace ADMMCycleData

abbrev I := Fin 128

def zZ : I → ℤ := fun i =>
  if i.val < 64 then
    if i.val < 32 then
      if i.val < 16 then
        if i.val < 8 then
          if i.val < 4 then
            if i.val < 2 then
              if i.val < 1 then
                3101378045
              else
                -15255423491
            else
              if i.val < 3 then
                3134412925
              else
                -4886036355
          else
            if i.val < 6 then
              if i.val < 5 then
                2866773629
              else
                3397089405
            else
              if i.val < 7 then
                1995424125
              else
                3852450813
        else
          if i.val < 12 then
            if i.val < 10 then
              if i.val < 9 then
                1110695549
              else
                2734376573
            else
              if i.val < 11 then
                909711741
              else
                3987755645
          else
            if i.val < 14 then
              if i.val < 13 then
                1230285949
              else
                3903750141
            else
              if i.val < 15 then
                1588614013
              else
                1734533629
      else
        if i.val < 24 then
          if i.val < 20 then
            if i.val < 18 then
              if i.val < 17 then
                1974621181
              else
                2046374525
            else
              if i.val < 19 then
                2386058877
              else
                4084864125
          else
            if i.val < 22 then
              if i.val < 21 then
                2339174781
              else
                1460059133
            else
              if i.val < 23 then
                1672401533
              else
                -5152066179
        else
          if i.val < 28 then
            if i.val < 26 then
              if i.val < 25 then
                1123690365
              else
                -7217901699
            else
              if i.val < 27 then
                1252499709
              else
                -2709100675
          else
            if i.val < 30 then
              if i.val < 29 then
                1478588029
              else
                622175997
            else
              if i.val < 31 then
                1088355837
              else
                -1131804419
    else
      if i.val < 48 then
        if i.val < 40 then
          if i.val < 36 then
            if i.val < 34 then
              if i.val < 33 then
                508140029
              else
                -2796585219
            else
              if i.val < 35 then
                545613693
              else
                -1328457219
          else
            if i.val < 38 then
              if i.val < 37 then
                907067517
              else
                -933981059
            else
              if i.val < 39 then
                575016445
              else
                -3651158147
        else
          if i.val < 44 then
            if i.val < 42 then
              if i.val < 41 then
                -610237187
              else
                -5250251267
            else
              if i.val < 43 then
                -1698129923
              else
                -3865354371
          else
            if i.val < 46 then
              if i.val < 45 then
                -1833483907
              else
                -3181208579
            else
              if i.val < 47 then
                -1013374083
              else
                -4197965955
      else
        if i.val < 56 then
          if i.val < 52 then
            if i.val < 50 then
              if i.val < 49 then
                194652669
              else
                -3002432387
            else
              if i.val < 51 then
                1123382269
              else
                733014781
          else
            if i.val < 54 then
              if i.val < 53 then
                1400112765
              else
                1927998845
            else
              if i.val < 55 then
                1309243261
              else
                -835653891
        else
          if i.val < 60 then
            if i.val < 58 then
              if i.val < 57 then
                1492860925
              else
                -2744483971
            else
              if i.val < 59 then
                2017711357
              else
                -1262247683
          else
            if i.val < 62 then
              if i.val < 61 then
                2240075005
              else
                578521981
            else
              if i.val < 63 then
                1894626557
              else
                776000637
  else
    if i.val < 96 then
      if i.val < 80 then
        if i.val < 72 then
          if i.val < 68 then
            if i.val < 66 then
              if i.val < 65 then
                1615743357
              else
                776000637
            else
              if i.val < 67 then
                1894626557
              else
                578521981
          else
            if i.val < 70 then
              if i.val < 69 then
                2240075005
              else
                -1262247683
            else
              if i.val < 71 then
                2017711357
              else
                -2744483971
        else
          if i.val < 76 then
            if i.val < 74 then
              if i.val < 73 then
                1492860925
              else
                -835653891
            else
              if i.val < 75 then
                1309243261
              else
                1927998845
          else
            if i.val < 78 then
              if i.val < 77 then
                1400112765
              else
                733014781
            else
              if i.val < 79 then
                1123382269
              else
                -3002432387
      else
        if i.val < 88 then
          if i.val < 84 then
            if i.val < 82 then
              if i.val < 81 then
                194652669
              else
                -4197965955
            else
              if i.val < 83 then
                -1013374083
              else
                -3181208579
          else
            if i.val < 86 then
              if i.val < 85 then
                -1833483907
              else
                -3865354371
            else
              if i.val < 87 then
                -1698129923
              else
                -5250251267
        else
          if i.val < 92 then
            if i.val < 90 then
              if i.val < 89 then
                -610237187
              else
                -3651158147
            else
              if i.val < 91 then
                575016445
              else
                -933981059
          else
            if i.val < 94 then
              if i.val < 93 then
                907067517
              else
                -1328457219
            else
              if i.val < 95 then
                545613693
              else
                -2796585219
    else
      if i.val < 112 then
        if i.val < 104 then
          if i.val < 100 then
            if i.val < 98 then
              if i.val < 97 then
                508140029
              else
                -1131804419
            else
              if i.val < 99 then
                1088355837
              else
                622175997
          else
            if i.val < 102 then
              if i.val < 101 then
                1478588029
              else
                -2709100675
            else
              if i.val < 103 then
                1252499709
              else
                -7217901699
        else
          if i.val < 108 then
            if i.val < 106 then
              if i.val < 105 then
                1123690365
              else
                -5152066179
            else
              if i.val < 107 then
                1672401533
              else
                1460059133
          else
            if i.val < 110 then
              if i.val < 109 then
                2339174781
              else
                4084864125
            else
              if i.val < 111 then
                2386058877
              else
                2046374525
      else
        if i.val < 120 then
          if i.val < 116 then
            if i.val < 114 then
              if i.val < 113 then
                1974621181
              else
                1734533629
            else
              if i.val < 115 then
                1588614013
              else
                3903750141
          else
            if i.val < 118 then
              if i.val < 117 then
                1230285949
              else
                3987755645
            else
              if i.val < 119 then
                909711741
              else
                2734376573
        else
          if i.val < 124 then
            if i.val < 122 then
              if i.val < 121 then
                1110695549
              else
                3852450813
            else
              if i.val < 123 then
                1995424125
              else
                3397089405
          else
            if i.val < 126 then
              if i.val < 125 then
                2866773629
              else
                -4886036355
            else
              if i.val < 127 then
                3134412925
              else
                -15255423491

def vZ : I → ℤ := fun i =>
  if i.val < 64 then
    if i.val < 32 then
      if i.val < 16 then
        if i.val < 8 then
          if i.val < 4 then
            if i.val < 2 then
              if i.val < 1 then
                -47131814916
              else
                -14357750276
            else
              if i.val < 3 then
                -33431421444
              else
                -18626515332
          else
            if i.val < 6 then
              if i.val < 5 then
                -9693015172
              else
                -7295622148
            else
              if i.val < 7 then
                3800333564
              else
                2768709500
        else
          if i.val < 12 then
            if i.val < 10 then
              if i.val < 9 then
                5763901436
              else
                2535391484
            else
              if i.val < 11 then
                6755591292
              else
                1556620540
          else
            if i.val < 14 then
              if i.val < 13 then
                7592333948
              else
                4847730940
            else
              if i.val < 15 then
                3221835388
              else
                4081519996
      else
        if i.val < 24 then
          if i.val < 20 then
            if i.val < 18 then
              if i.val < 17 then
                -2399926148
              else
                -2419169028
            else
              if i.val < 19 then
                -3654187140
              else
                -4483063556
          else
            if i.val < 22 then
              if i.val < 21 then
                -6696190724
              else
                -1039550084
            else
              if i.val < 23 then
                -18292407300
              else
                -3906016260
        else
          if i.val < 28 then
            if i.val < 26 then
              if i.val < 25 then
                -29646241796
              else
                -14576981380
            else
              if i.val < 27 then
                -28374952580
              else
                -19031646084
          else
            if i.val < 30 then
              if i.val < 29 then
                -18891333124
              else
                -12006318340
            else
              if i.val < 31 then
                -14247696132
              else
                -5306229764
    else
      if i.val < 48 then
        if i.val < 40 then
          if i.val < 36 then
            if i.val < 34 then
              if i.val < 33 then
                -14951742980
              else
                -5515481604
            else
              if i.val < 35 then
                -12336890500
              else
                -4165113604
          else
            if i.val < 38 then
              if i.val < 37 then
                -6418991876
              else
                3041277436
            else
              if i.val < 39 then
                -4064164228
              else
                7334326012
        else
          if i.val < 44 then
            if i.val < 42 then
              if i.val < 41 then
                -4602216964
              else
                4727950332
            else
              if i.val < 43 then
                -2260059012
              else
                4116622076
          else
            if i.val < 46 then
              if i.val < 45 then
                1799815164
              else
                10136178428
            else
              if i.val < 47 then
                3300510716
              else
                15155186428
      else
        if i.val < 56 then
          if i.val < 52 then
            if i.val < 50 then
              if i.val < 49 then
                5352127612
              else
                15001991164
            else
              if i.val < 51 then
                12244602364
              else
                16180598396
          else
            if i.val < 54 then
              if i.val < 53 then
                18343921532
              else
                21226642428
            else
              if i.val < 55 then
                15831531260
              else
                22580223356
        else
          if i.val < 60 then
            if i.val < 58 then
              if i.val < 57 then
                8265803260
              else
                16847381116
            else
              if i.val < 59 then
                4600735356
              else
                10740039420
          else
            if i.val < 62 then
              if i.val < 61 then
                4961688188
              else
                8251271804
            else
              if i.val < 63 then
                3359228540
              else
                5546282748
  else
    if i.val < 96 then
      if i.val < 80 then
        if i.val < 72 then
          if i.val < 68 then
            if i.val < 66 then
              if i.val < 65 then
                -935737348
              else
                1550072572
            else
              if i.val < 67 then
                -4951442948
              else
                1560572
          else
            if i.val < 70 then
              if i.val < 69 then
                -9180364292
              else
                -621702532
            else
              if i.val < 71 then
                -13952484484
              else
                -5378295812
        else
          if i.val < 76 then
            if i.val < 74 then
              if i.val < 73 then
                -15022891268
              else
                -10767364868
            else
              if i.val < 75 then
                -11148118276
              else
                -8760939780
          else
            if i.val < 78 then
              if i.val < 77 then
                -8812658052
              else
                -2243254404
            else
              if i.val < 79 then
                -11727813636
              else
                -1286086532
      else
        if i.val < 88 then
          if i.val < 84 then
            if i.val < 82 then
              if i.val < 81 then
                -14039384580
              else
                -5313886980
            else
              if i.val < 83 then
                -11252695940
              else
                -4765909892
          else
            if i.val < 86 then
              if i.val < 85 then
                -8003388676
              else
                1280337404
            else
              if i.val < 87 then
                -7400233732
              else
                5538045564
        else
          if i.val < 92 then
            if i.val < 90 then
              if i.val < 89 then
                -3794109060
              else
                8169452796
            else
              if i.val < 91 then
                5496504572
              else
                14918106876
          else
            if i.val < 94 then
              if i.val < 93 then
                12901899132
              else
                22342406780
            else
              if i.val < 95 then
                13661546364
              else
                22614438012
    else
      if i.val < 112 then
        if i.val < 104 then
          if i.val < 100 then
            if i.val < 98 then
              if i.val < 97 then
                13911771644
              else
                19835169404
            else
              if i.val < 99 then
                17032946172
              else
                23154775036
          else
            if i.val < 102 then
              if i.val < 101 then
                15539843580
              else
                27586375676
            else
              if i.val < 103 then
                6547367932
              else
                21597359868
        else
          if i.val < 108 then
            if i.val < 106 then
              if i.val < 105 then
                1134601596
              else
                9899711612
            else
              if i.val < 107 then
                6766197500
              else
                7257657596
          else
            if i.val < 110 then
              if i.val < 109 then
                13938930812
              else
                12702939132
            else
              if i.val < 111 then
                12264879996
              else
                12053215484
      else
        if i.val < 120 then
          if i.val < 116 then
            if i.val < 114 then
              if i.val < 113 then
                6493149564
              else
                3584886012
            else
              if i.val < 115 then
                4440053244
              else
                -1438223364
          else
            if i.val < 118 then
              if i.val < 117 then
                2624692988
              else
                -1554693636
            else
              if i.val < 119 then
                -3523660676
              else
                -5046637188
        else
          if i.val < 124 then
            if i.val < 122 then
              if i.val < 121 then
                -9029609220
              else
                -9134718980
            else
              if i.val < 123 then
                -11814265220
              else
                -3763622148
          else
            if i.val < 126 then
              if i.val < 125 then
                -21014136580
              else
                4918483068
            else
              if i.val < 127 then
                -38530277636
              else
                402035452

def xZ : I → ℤ := fun i =>
  if i.val < 64 then
    if i.val < 32 then
      if i.val < 16 then
        if i.val < 8 then
          if i.val < 4 then
            if i.val < 2 then
              if i.val < 1 then
                -44432472323
              else
                17518641149
            else
              if i.val < 3 then
                -15939258243
              else
                9918869757
          else
            if i.val < 6 then
              if i.val < 5 then
                11800273789
              else
                5794482429
            else
              if i.val < 7 then
                13091379837
              else
                2820826749
        else
          if i.val < 12 then
            if i.val < 10 then
              if i.val < 9 then
                4105887485
              else
                -494133379
            else
              if i.val < 11 then
                5129911549
              else
                -1211215107
          else
            if i.val < 14 then
              if i.val < 13 then
                7265999357
              else
                1159147133
            else
              if i.val < 15 then
                -37281539
              else
                2594218237
      else
        if i.val < 24 then
          if i.val < 20 then
            if i.val < 18 then
              if i.val < 17 then
                -4506824963
              else
                2027131645
            else
              if i.val < 19 then
                1151040765
              else
                3255987709
          else
            if i.val < 22 then
              if i.val < 21 then
                126047613
              else
                7116699773
            else
              if i.val < 23 then
                -15580455683
              else
                9234324861
        else
          if i.val < 28 then
            if i.val < 26 then
              if i.val < 25 then
                -24616535171
              else
                7851358717
            else
              if i.val < 27 then
                -12545471491
              else
                6634205821
          else
            if i.val < 30 then
              if i.val < 29 then
                1618900989
              else
                7507190781
            else
              if i.val < 31 then
                -1153021955
              else
                7809661949
    else
      if i.val < 48 then
        if i.val < 40 then
          if i.val < 36 then
            if i.val < 34 then
              if i.val < 33 then
                -9137373187
              else
                6639676157
            else
              if i.val < 35 then
                -6275795203
              else
                6843319677
          else
            if i.val < 38 then
              if i.val < 37 then
                -1346810755
              else
                8526288253
            else
              if i.val < 39 then
                -6530425219
              else
                7747332093
        else
          if i.val < 44 then
            if i.val < 42 then
              if i.val < 41 then
                -12546780163
              else
                4079916029
            else
              if i.val < 43 then
                -8686139267
              else
                2511326717
          else
            if i.val < 46 then
              if i.val < 45 then
                -4150290819
              else
                5155154685
            else
              if i.val < 47 then
                -7849041795
              else
                7656709757
      else
        if i.val < 56 then
          if i.val < 52 then
            if i.val < 50 then
              if i.val < 49 then
                -9608406147
              else
                6647431165
            else
              if i.val < 51 then
                -1634006531
              else
                4669010813
          else
            if i.val < 54 then
              if i.val < 53 then
                3563435901
              else
                4810719741
            else
              if i.val < 55 then
                -4085867907
              else
                5913038205
        else
          if i.val < 60 then
            if i.val < 58 then
              if i.val < 57 then
                -12821559171
              else
                5837093885
            else
              if i.val < 59 then
                -10228934403
              else
                4877056381
          else
            if i.val < 62 then
              if i.val < 61 then
                -3538276227
              else
                3868105597
            else
              if i.val < 63 then
                -2997416707
              else
                2963054845
  else
    if i.val < 96 then
      if i.val < 80 then
        if i.val < 72 then
          if i.val < 68 then
            if i.val < 66 then
              if i.val < 65 then
                -4866276739
              else
                3261810557
            else
              if i.val < 67 then
                -4606888963
              else
                5531525501
          else
            if i.val < 70 then
              if i.val < 69 then
                -6941849859
              else
                7296414077
            else
              if i.val < 71 then
                -11313070595
              else
                5829704701
        else
          if i.val < 76 then
            if i.val < 74 then
              if i.val < 73 then
                -8151734531
              else
                3419872509
            else
              if i.val < 75 then
                928489853
              else
                4315177341
          else
            if i.val < 78 then
              if i.val < 77 then
                1348394493
              else
                7302418429
            else
              if i.val < 79 then
                -8361176963
              else
                7439294717
      else
        if i.val < 88 then
          if i.val < 84 then
            if i.val < 82 then
              if i.val < 81 then
                -12558645379
              else
                4527531645
            else
              if i.val < 83 then
                -6952183043
              else
                3305577469
          else
            if i.val < 86 then
              if i.val < 85 then
                -5070962691
              else
                5418371709
            else
              if i.val < 87 then
                -10378701059
              else
                7688028029
        else
          if i.val < 92 then
            if i.val < 90 then
              if i.val < 89 then
                -9942391811
              else
                8312403709
            else
              if i.val < 91 then
                -2097931779
              else
                8487621245
          else
            if i.val < 94 then
              if i.val < 93 then
                -1109140227
              else
                8112050429
            else
              if i.val < 95 then
                -8135246723
              else
                6156306429
    else
      if i.val < 112 then
        if i.val < 104 then
          if i.val < 100 then
            if i.val < 98 then
              if i.val < 97 then
                -8194526339
              else
                4791593341
            else
              if i.val < 99 then
                -1713867395
              else
                6744004861
          else
            if i.val < 102 then
              if i.val < 101 then
                -6136343427
              else
                9337431421
            else
              if i.val < 103 then
                -19786508035
              else
                7832090237
        else
          if i.val < 108 then
            if i.val < 106 then
              if i.val < 105 then
                -19339067907
              else
                3613043837
            else
              if i.val < 107 then
                -1461112579
              else
                1951519229
          else
            if i.val < 110 then
              if i.val < 109 then
                9020447997
              else
                2848872445
            else
              if i.val < 111 then
                1947999741
              else
                1834710013
      else
        if i.val < 120 then
          if i.val < 116 then
            if i.val < 114 then
              if i.val < 113 then
                -3585444739
              else
                -1173729923
            else
              if i.val < 115 then
                2443781245
              else
                -1974526467
          else
            if i.val < 118 then
              if i.val < 117 then
                5293202301
              else
                -191630979
            else
              if i.val < 119 then
                -1059255299
              else
                1211400061
        else
          if i.val < 124 then
            if i.val < 122 then
              if i.val < 121 then
                -2872276483
              else
                3747341053
            else
              if i.val < 123 then
                -684122115
              else
                11447732477
          else
            if i.val < 126 then
              if i.val < 125 then
                -14383740803
              else
                21046583293
            else
              if i.val < 127 then
                -40314347779
              else
                23676889597

def shiftZ (i : I) (a : I → ℤ) : I → ℤ := fun j => a (i + j)
def dotZ (a b : I → ℤ) : ℤ := ∑ k, a k * b k
def zmZ : I → ℤ := shiftZ (-1) zZ
def vmZ : I → ℤ := shiftZ (-1) vZ
def fIntercept (j : I) : ℤ := dotZ (zmZ - xZ) (xZ - shiftZ j xZ)
def fSlope (j : I) : ℤ := -dotZ vmZ (xZ - shiftZ j xZ)
def gIntercept (j : I) : ℤ := dotZ (xZ - zZ) (zZ - shiftZ j zZ)
def gSlope (j : I) : ℤ := dotZ vmZ (zZ - shiftZ j zZ)

def numerator : ℤ := 897744153596994489
def denominator : ℤ := 475778439151265168

theorem denominator_pos : 0 < denominator := by decide
theorem numerator_pos : 0 < numerator := by decide

theorem xZ_identity_0 : xZ 0 = zZ 0 + vZ 0 - vmZ 0 := by decide
theorem xZ_identity_1 : xZ 1 = zZ 1 + vZ 1 - vmZ 1 := by decide
theorem xZ_identity_2 : xZ 2 = zZ 2 + vZ 2 - vmZ 2 := by decide
theorem xZ_identity_3 : xZ 3 = zZ 3 + vZ 3 - vmZ 3 := by decide
theorem xZ_identity_4 : xZ 4 = zZ 4 + vZ 4 - vmZ 4 := by decide
theorem xZ_identity_5 : xZ 5 = zZ 5 + vZ 5 - vmZ 5 := by decide
theorem xZ_identity_6 : xZ 6 = zZ 6 + vZ 6 - vmZ 6 := by decide
theorem xZ_identity_7 : xZ 7 = zZ 7 + vZ 7 - vmZ 7 := by decide
theorem xZ_identity_8 : xZ 8 = zZ 8 + vZ 8 - vmZ 8 := by decide
theorem xZ_identity_9 : xZ 9 = zZ 9 + vZ 9 - vmZ 9 := by decide
theorem xZ_identity_10 : xZ 10 = zZ 10 + vZ 10 - vmZ 10 := by decide
theorem xZ_identity_11 : xZ 11 = zZ 11 + vZ 11 - vmZ 11 := by decide
theorem xZ_identity_12 : xZ 12 = zZ 12 + vZ 12 - vmZ 12 := by decide
theorem xZ_identity_13 : xZ 13 = zZ 13 + vZ 13 - vmZ 13 := by decide
theorem xZ_identity_14 : xZ 14 = zZ 14 + vZ 14 - vmZ 14 := by decide
theorem xZ_identity_15 : xZ 15 = zZ 15 + vZ 15 - vmZ 15 := by decide
theorem xZ_identity_16 : xZ 16 = zZ 16 + vZ 16 - vmZ 16 := by decide
theorem xZ_identity_17 : xZ 17 = zZ 17 + vZ 17 - vmZ 17 := by decide
theorem xZ_identity_18 : xZ 18 = zZ 18 + vZ 18 - vmZ 18 := by decide
theorem xZ_identity_19 : xZ 19 = zZ 19 + vZ 19 - vmZ 19 := by decide
theorem xZ_identity_20 : xZ 20 = zZ 20 + vZ 20 - vmZ 20 := by decide
theorem xZ_identity_21 : xZ 21 = zZ 21 + vZ 21 - vmZ 21 := by decide
theorem xZ_identity_22 : xZ 22 = zZ 22 + vZ 22 - vmZ 22 := by decide
theorem xZ_identity_23 : xZ 23 = zZ 23 + vZ 23 - vmZ 23 := by decide
theorem xZ_identity_24 : xZ 24 = zZ 24 + vZ 24 - vmZ 24 := by decide
theorem xZ_identity_25 : xZ 25 = zZ 25 + vZ 25 - vmZ 25 := by decide
theorem xZ_identity_26 : xZ 26 = zZ 26 + vZ 26 - vmZ 26 := by decide
theorem xZ_identity_27 : xZ 27 = zZ 27 + vZ 27 - vmZ 27 := by decide
theorem xZ_identity_28 : xZ 28 = zZ 28 + vZ 28 - vmZ 28 := by decide
theorem xZ_identity_29 : xZ 29 = zZ 29 + vZ 29 - vmZ 29 := by decide
theorem xZ_identity_30 : xZ 30 = zZ 30 + vZ 30 - vmZ 30 := by decide
theorem xZ_identity_31 : xZ 31 = zZ 31 + vZ 31 - vmZ 31 := by decide
theorem xZ_identity_32 : xZ 32 = zZ 32 + vZ 32 - vmZ 32 := by decide
theorem xZ_identity_33 : xZ 33 = zZ 33 + vZ 33 - vmZ 33 := by decide
theorem xZ_identity_34 : xZ 34 = zZ 34 + vZ 34 - vmZ 34 := by decide
theorem xZ_identity_35 : xZ 35 = zZ 35 + vZ 35 - vmZ 35 := by decide
theorem xZ_identity_36 : xZ 36 = zZ 36 + vZ 36 - vmZ 36 := by decide
theorem xZ_identity_37 : xZ 37 = zZ 37 + vZ 37 - vmZ 37 := by decide
theorem xZ_identity_38 : xZ 38 = zZ 38 + vZ 38 - vmZ 38 := by decide
theorem xZ_identity_39 : xZ 39 = zZ 39 + vZ 39 - vmZ 39 := by decide
theorem xZ_identity_40 : xZ 40 = zZ 40 + vZ 40 - vmZ 40 := by decide
theorem xZ_identity_41 : xZ 41 = zZ 41 + vZ 41 - vmZ 41 := by decide
theorem xZ_identity_42 : xZ 42 = zZ 42 + vZ 42 - vmZ 42 := by decide
theorem xZ_identity_43 : xZ 43 = zZ 43 + vZ 43 - vmZ 43 := by decide
theorem xZ_identity_44 : xZ 44 = zZ 44 + vZ 44 - vmZ 44 := by decide
theorem xZ_identity_45 : xZ 45 = zZ 45 + vZ 45 - vmZ 45 := by decide
theorem xZ_identity_46 : xZ 46 = zZ 46 + vZ 46 - vmZ 46 := by decide
theorem xZ_identity_47 : xZ 47 = zZ 47 + vZ 47 - vmZ 47 := by decide
theorem xZ_identity_48 : xZ 48 = zZ 48 + vZ 48 - vmZ 48 := by decide
theorem xZ_identity_49 : xZ 49 = zZ 49 + vZ 49 - vmZ 49 := by decide
theorem xZ_identity_50 : xZ 50 = zZ 50 + vZ 50 - vmZ 50 := by decide
theorem xZ_identity_51 : xZ 51 = zZ 51 + vZ 51 - vmZ 51 := by decide
theorem xZ_identity_52 : xZ 52 = zZ 52 + vZ 52 - vmZ 52 := by decide
theorem xZ_identity_53 : xZ 53 = zZ 53 + vZ 53 - vmZ 53 := by decide
theorem xZ_identity_54 : xZ 54 = zZ 54 + vZ 54 - vmZ 54 := by decide
theorem xZ_identity_55 : xZ 55 = zZ 55 + vZ 55 - vmZ 55 := by decide
theorem xZ_identity_56 : xZ 56 = zZ 56 + vZ 56 - vmZ 56 := by decide
theorem xZ_identity_57 : xZ 57 = zZ 57 + vZ 57 - vmZ 57 := by decide
theorem xZ_identity_58 : xZ 58 = zZ 58 + vZ 58 - vmZ 58 := by decide
theorem xZ_identity_59 : xZ 59 = zZ 59 + vZ 59 - vmZ 59 := by decide
theorem xZ_identity_60 : xZ 60 = zZ 60 + vZ 60 - vmZ 60 := by decide
theorem xZ_identity_61 : xZ 61 = zZ 61 + vZ 61 - vmZ 61 := by decide
theorem xZ_identity_62 : xZ 62 = zZ 62 + vZ 62 - vmZ 62 := by decide
theorem xZ_identity_63 : xZ 63 = zZ 63 + vZ 63 - vmZ 63 := by decide
theorem xZ_identity_64 : xZ 64 = zZ 64 + vZ 64 - vmZ 64 := by decide
theorem xZ_identity_65 : xZ 65 = zZ 65 + vZ 65 - vmZ 65 := by decide
theorem xZ_identity_66 : xZ 66 = zZ 66 + vZ 66 - vmZ 66 := by decide
theorem xZ_identity_67 : xZ 67 = zZ 67 + vZ 67 - vmZ 67 := by decide
theorem xZ_identity_68 : xZ 68 = zZ 68 + vZ 68 - vmZ 68 := by decide
theorem xZ_identity_69 : xZ 69 = zZ 69 + vZ 69 - vmZ 69 := by decide
theorem xZ_identity_70 : xZ 70 = zZ 70 + vZ 70 - vmZ 70 := by decide
theorem xZ_identity_71 : xZ 71 = zZ 71 + vZ 71 - vmZ 71 := by decide
theorem xZ_identity_72 : xZ 72 = zZ 72 + vZ 72 - vmZ 72 := by decide
theorem xZ_identity_73 : xZ 73 = zZ 73 + vZ 73 - vmZ 73 := by decide
theorem xZ_identity_74 : xZ 74 = zZ 74 + vZ 74 - vmZ 74 := by decide
theorem xZ_identity_75 : xZ 75 = zZ 75 + vZ 75 - vmZ 75 := by decide
theorem xZ_identity_76 : xZ 76 = zZ 76 + vZ 76 - vmZ 76 := by decide
theorem xZ_identity_77 : xZ 77 = zZ 77 + vZ 77 - vmZ 77 := by decide
theorem xZ_identity_78 : xZ 78 = zZ 78 + vZ 78 - vmZ 78 := by decide
theorem xZ_identity_79 : xZ 79 = zZ 79 + vZ 79 - vmZ 79 := by decide
theorem xZ_identity_80 : xZ 80 = zZ 80 + vZ 80 - vmZ 80 := by decide
theorem xZ_identity_81 : xZ 81 = zZ 81 + vZ 81 - vmZ 81 := by decide
theorem xZ_identity_82 : xZ 82 = zZ 82 + vZ 82 - vmZ 82 := by decide
theorem xZ_identity_83 : xZ 83 = zZ 83 + vZ 83 - vmZ 83 := by decide
theorem xZ_identity_84 : xZ 84 = zZ 84 + vZ 84 - vmZ 84 := by decide
theorem xZ_identity_85 : xZ 85 = zZ 85 + vZ 85 - vmZ 85 := by decide
theorem xZ_identity_86 : xZ 86 = zZ 86 + vZ 86 - vmZ 86 := by decide
theorem xZ_identity_87 : xZ 87 = zZ 87 + vZ 87 - vmZ 87 := by decide
theorem xZ_identity_88 : xZ 88 = zZ 88 + vZ 88 - vmZ 88 := by decide
theorem xZ_identity_89 : xZ 89 = zZ 89 + vZ 89 - vmZ 89 := by decide
theorem xZ_identity_90 : xZ 90 = zZ 90 + vZ 90 - vmZ 90 := by decide
theorem xZ_identity_91 : xZ 91 = zZ 91 + vZ 91 - vmZ 91 := by decide
theorem xZ_identity_92 : xZ 92 = zZ 92 + vZ 92 - vmZ 92 := by decide
theorem xZ_identity_93 : xZ 93 = zZ 93 + vZ 93 - vmZ 93 := by decide
theorem xZ_identity_94 : xZ 94 = zZ 94 + vZ 94 - vmZ 94 := by decide
theorem xZ_identity_95 : xZ 95 = zZ 95 + vZ 95 - vmZ 95 := by decide
theorem xZ_identity_96 : xZ 96 = zZ 96 + vZ 96 - vmZ 96 := by decide
theorem xZ_identity_97 : xZ 97 = zZ 97 + vZ 97 - vmZ 97 := by decide
theorem xZ_identity_98 : xZ 98 = zZ 98 + vZ 98 - vmZ 98 := by decide
theorem xZ_identity_99 : xZ 99 = zZ 99 + vZ 99 - vmZ 99 := by decide
theorem xZ_identity_100 : xZ 100 = zZ 100 + vZ 100 - vmZ 100 := by decide
theorem xZ_identity_101 : xZ 101 = zZ 101 + vZ 101 - vmZ 101 := by decide
theorem xZ_identity_102 : xZ 102 = zZ 102 + vZ 102 - vmZ 102 := by decide
theorem xZ_identity_103 : xZ 103 = zZ 103 + vZ 103 - vmZ 103 := by decide
theorem xZ_identity_104 : xZ 104 = zZ 104 + vZ 104 - vmZ 104 := by decide
theorem xZ_identity_105 : xZ 105 = zZ 105 + vZ 105 - vmZ 105 := by decide
theorem xZ_identity_106 : xZ 106 = zZ 106 + vZ 106 - vmZ 106 := by decide
theorem xZ_identity_107 : xZ 107 = zZ 107 + vZ 107 - vmZ 107 := by decide
theorem xZ_identity_108 : xZ 108 = zZ 108 + vZ 108 - vmZ 108 := by decide
theorem xZ_identity_109 : xZ 109 = zZ 109 + vZ 109 - vmZ 109 := by decide
theorem xZ_identity_110 : xZ 110 = zZ 110 + vZ 110 - vmZ 110 := by decide
theorem xZ_identity_111 : xZ 111 = zZ 111 + vZ 111 - vmZ 111 := by decide
theorem xZ_identity_112 : xZ 112 = zZ 112 + vZ 112 - vmZ 112 := by decide
theorem xZ_identity_113 : xZ 113 = zZ 113 + vZ 113 - vmZ 113 := by decide
theorem xZ_identity_114 : xZ 114 = zZ 114 + vZ 114 - vmZ 114 := by decide
theorem xZ_identity_115 : xZ 115 = zZ 115 + vZ 115 - vmZ 115 := by decide
theorem xZ_identity_116 : xZ 116 = zZ 116 + vZ 116 - vmZ 116 := by decide
theorem xZ_identity_117 : xZ 117 = zZ 117 + vZ 117 - vmZ 117 := by decide
theorem xZ_identity_118 : xZ 118 = zZ 118 + vZ 118 - vmZ 118 := by decide
theorem xZ_identity_119 : xZ 119 = zZ 119 + vZ 119 - vmZ 119 := by decide
theorem xZ_identity_120 : xZ 120 = zZ 120 + vZ 120 - vmZ 120 := by decide
theorem xZ_identity_121 : xZ 121 = zZ 121 + vZ 121 - vmZ 121 := by decide
theorem xZ_identity_122 : xZ 122 = zZ 122 + vZ 122 - vmZ 122 := by decide
theorem xZ_identity_123 : xZ 123 = zZ 123 + vZ 123 - vmZ 123 := by decide
theorem xZ_identity_124 : xZ 124 = zZ 124 + vZ 124 - vmZ 124 := by decide
theorem xZ_identity_125 : xZ 125 = zZ 125 + vZ 125 - vmZ 125 := by decide
theorem xZ_identity_126 : xZ 126 = zZ 126 + vZ 126 - vmZ 126 := by decide
theorem xZ_identity_127 : xZ 127 = zZ 127 + vZ 127 - vmZ 127 := by decide

theorem xZ_identity (j : I) : xZ j = zZ j + vZ j - vmZ j := by
  fin_cases j
  · exact xZ_identity_0
  · exact xZ_identity_1
  · exact xZ_identity_2
  · exact xZ_identity_3
  · exact xZ_identity_4
  · exact xZ_identity_5
  · exact xZ_identity_6
  · exact xZ_identity_7
  · exact xZ_identity_8
  · exact xZ_identity_9
  · exact xZ_identity_10
  · exact xZ_identity_11
  · exact xZ_identity_12
  · exact xZ_identity_13
  · exact xZ_identity_14
  · exact xZ_identity_15
  · exact xZ_identity_16
  · exact xZ_identity_17
  · exact xZ_identity_18
  · exact xZ_identity_19
  · exact xZ_identity_20
  · exact xZ_identity_21
  · exact xZ_identity_22
  · exact xZ_identity_23
  · exact xZ_identity_24
  · exact xZ_identity_25
  · exact xZ_identity_26
  · exact xZ_identity_27
  · exact xZ_identity_28
  · exact xZ_identity_29
  · exact xZ_identity_30
  · exact xZ_identity_31
  · exact xZ_identity_32
  · exact xZ_identity_33
  · exact xZ_identity_34
  · exact xZ_identity_35
  · exact xZ_identity_36
  · exact xZ_identity_37
  · exact xZ_identity_38
  · exact xZ_identity_39
  · exact xZ_identity_40
  · exact xZ_identity_41
  · exact xZ_identity_42
  · exact xZ_identity_43
  · exact xZ_identity_44
  · exact xZ_identity_45
  · exact xZ_identity_46
  · exact xZ_identity_47
  · exact xZ_identity_48
  · exact xZ_identity_49
  · exact xZ_identity_50
  · exact xZ_identity_51
  · exact xZ_identity_52
  · exact xZ_identity_53
  · exact xZ_identity_54
  · exact xZ_identity_55
  · exact xZ_identity_56
  · exact xZ_identity_57
  · exact xZ_identity_58
  · exact xZ_identity_59
  · exact xZ_identity_60
  · exact xZ_identity_61
  · exact xZ_identity_62
  · exact xZ_identity_63
  · exact xZ_identity_64
  · exact xZ_identity_65
  · exact xZ_identity_66
  · exact xZ_identity_67
  · exact xZ_identity_68
  · exact xZ_identity_69
  · exact xZ_identity_70
  · exact xZ_identity_71
  · exact xZ_identity_72
  · exact xZ_identity_73
  · exact xZ_identity_74
  · exact xZ_identity_75
  · exact xZ_identity_76
  · exact xZ_identity_77
  · exact xZ_identity_78
  · exact xZ_identity_79
  · exact xZ_identity_80
  · exact xZ_identity_81
  · exact xZ_identity_82
  · exact xZ_identity_83
  · exact xZ_identity_84
  · exact xZ_identity_85
  · exact xZ_identity_86
  · exact xZ_identity_87
  · exact xZ_identity_88
  · exact xZ_identity_89
  · exact xZ_identity_90
  · exact xZ_identity_91
  · exact xZ_identity_92
  · exact xZ_identity_93
  · exact xZ_identity_94
  · exact xZ_identity_95
  · exact xZ_identity_96
  · exact xZ_identity_97
  · exact xZ_identity_98
  · exact xZ_identity_99
  · exact xZ_identity_100
  · exact xZ_identity_101
  · exact xZ_identity_102
  · exact xZ_identity_103
  · exact xZ_identity_104
  · exact xZ_identity_105
  · exact xZ_identity_106
  · exact xZ_identity_107
  · exact xZ_identity_108
  · exact xZ_identity_109
  · exact xZ_identity_110
  · exact xZ_identity_111
  · exact xZ_identity_112
  · exact xZ_identity_113
  · exact xZ_identity_114
  · exact xZ_identity_115
  · exact xZ_identity_116
  · exact xZ_identity_117
  · exact xZ_identity_118
  · exact xZ_identity_119
  · exact xZ_identity_120
  · exact xZ_identity_121
  · exact xZ_identity_122
  · exact xZ_identity_123
  · exact xZ_identity_124
  · exact xZ_identity_125
  · exact xZ_identity_126
  · exact xZ_identity_127
theorem sum_zZ : ∑ j, zZ j = 0 := by decide
theorem sum_vZ : ∑ j, vZ j = 0 := by decide
theorem sum_xZ : ∑ j, xZ j = 0 := by decide
theorem residual_squared : dotZ (xZ - zZ) (xZ - zZ) = 16383999960516622876672 := by decide


end ADMMCycleData
