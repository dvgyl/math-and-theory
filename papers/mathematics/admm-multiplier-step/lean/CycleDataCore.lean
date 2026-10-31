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
                28912073552004
              else
                -160608501067260
            else
              if i.val < 3 then
                28696040108676
              else
                -50174884475132
          else
            if i.val < 6 then
              if i.val < 5 then
                26123740533636
              else
                39103947573252
            else
              if i.val < 7 then
                20173615300228
              else
                44415700770820
        else
          if i.val < 12 then
            if i.val < 10 then
              if i.val < 9 then
                14853196714628
              else
                29946952573444
            else
              if i.val < 11 then
                13320173108868
              else
                39845090181380
          else
            if i.val < 14 then
              if i.val < 13 then
                13355453411460
              else
                38490551995140
            else
              if i.val < 15 then
                13420416449156
              else
                16316740153988
      else
        if i.val < 24 then
          if i.val < 20 then
            if i.val < 18 then
              if i.val < 17 then
                16461920689156
              else
                17650914045316
            else
              if i.val < 19 then
                22237984876036
              else
                36691405055236
          else
            if i.val < 22 then
              if i.val < 21 then
                23636980075652
              else
                12001475582468
            else
              if i.val < 23 then
                17659160485380
              else
                -50101791045244
        else
          if i.val < 28 then
            if i.val < 26 then
              if i.val < 25 then
                12260737407236
              else
                -67723262262524
            else
              if i.val < 27 then
                14028555531780
              else
                -23238293668220
          else
            if i.val < 30 then
              if i.val < 29 then
                16848114359172
              else
                6759483102980
            else
              if i.val < 31 then
                12563811736452
              else
                -13992027521276
    else
      if i.val < 48 then
        if i.val < 40 then
          if i.val < 36 then
            if i.val < 34 then
              if i.val < 33 then
                5467992473348
              else
                -32276389868540
            else
              if i.val < 35 then
                4536892382084
              else
                -17761644734332
          else
            if i.val < 38 then
              if i.val < 37 then
                7042913987716
              else
                -12520169160956
            else
              if i.val < 39 then
                2706164346628
              else
                -36854375215996
        else
          if i.val < 44 then
            if i.val < 42 then
              if i.val < 41 then
                -8944346413820
              else
                -49298491548668
            else
              if i.val < 43 then
                -17322649973756
              else
                -32476897466108
          else
            if i.val < 46 then
              if i.val < 45 then
                -15647529536764
              else
                -24383532875004
            else
              if i.val < 47 then
                -7167834110076
              else
                -36637897742332
      else
        if i.val < 56 then
          if i.val < 52 then
            if i.val < 50 then
              if i.val < 49 then
                2335775623044
              else
                -31048103456252
            else
              if i.val < 51 then
                9709476568068
              else
                -1043508640380
          else
            if i.val < 54 then
              if i.val < 53 then
                13248152647428
              else
                9620918247812
            else
              if i.val < 55 then
                13639103497988
              else
                -10168729449340
        else
          if i.val < 60 then
            if i.val < 58 then
              if i.val < 57 then
                14848447936644
              else
                -19110060946812
            else
              if i.val < 59 then
                18771263887492
              else
                -2644148588412
          else
            if i.val < 62 then
              if i.val < 61 then
                21798144520068
              else
                6604831275268
            else
              if i.val < 63 then
                21141970353668
              else
                -1613495440380
  else
    if i.val < 96 then
      if i.val < 80 then
        if i.val < 72 then
          if i.val < 68 then
            if i.val < 66 then
              if i.val < 65 then
                19936637725572
              else
                -1613495440380
            else
              if i.val < 67 then
                21141970353668
              else
                6604831275268
          else
            if i.val < 70 then
              if i.val < 69 then
                21798144520068
              else
                -2644148588412
            else
              if i.val < 71 then
                18771263887492
              else
                -19110060946812
        else
          if i.val < 76 then
            if i.val < 74 then
              if i.val < 73 then
                14848447936644
              else
                -10168729449340
            else
              if i.val < 75 then
                13639103497988
              else
                9620918247812
          else
            if i.val < 78 then
              if i.val < 77 then
                13248152647428
              else
                -1043508640380
            else
              if i.val < 79 then
                9709476568068
              else
                -31048103456252
      else
        if i.val < 88 then
          if i.val < 84 then
            if i.val < 82 then
              if i.val < 81 then
                2335775623044
              else
                -36637897742332
            else
              if i.val < 83 then
                -7167834110076
              else
                -24383532875004
          else
            if i.val < 86 then
              if i.val < 85 then
                -15647529536764
              else
                -32476897466108
            else
              if i.val < 87 then
                -17322649973756
              else
                -49298491548668
        else
          if i.val < 92 then
            if i.val < 90 then
              if i.val < 89 then
                -8944346413820
              else
                -36854375215996
            else
              if i.val < 91 then
                2706164346628
              else
                -12520169160956
          else
            if i.val < 94 then
              if i.val < 93 then
                7042913987716
              else
                -17761644734332
            else
              if i.val < 95 then
                4536892382084
              else
                -32276389868540
    else
      if i.val < 112 then
        if i.val < 104 then
          if i.val < 100 then
            if i.val < 98 then
              if i.val < 97 then
                5467992473348
              else
                -13992027521276
            else
              if i.val < 99 then
                12563811736452
              else
                6759483102980
          else
            if i.val < 102 then
              if i.val < 101 then
                16848114359172
              else
                -23238293668220
            else
              if i.val < 103 then
                14028555531780
              else
                -67723262262524
        else
          if i.val < 108 then
            if i.val < 106 then
              if i.val < 105 then
                12260737407236
              else
                -50101791045244
            else
              if i.val < 107 then
                17659160485380
              else
                12001475582468
          else
            if i.val < 110 then
              if i.val < 109 then
                23636980075652
              else
                36691405055236
            else
              if i.val < 111 then
                22237984876036
              else
                17650914045316
      else
        if i.val < 120 then
          if i.val < 116 then
            if i.val < 114 then
              if i.val < 113 then
                16461920689156
              else
                16316740153988
            else
              if i.val < 115 then
                13420416449156
              else
                38490551995140
          else
            if i.val < 118 then
              if i.val < 117 then
                13355453411460
              else
                39845090181380
            else
              if i.val < 119 then
                13320173108868
              else
                29946952573444
        else
          if i.val < 124 then
            if i.val < 122 then
              if i.val < 121 then
                14853196714628
              else
                44415700770820
            else
              if i.val < 123 then
                20173615300228
              else
                39103947573252
          else
            if i.val < 126 then
              if i.val < 125 then
                26123740533636
              else
                -50174884475132
            else
              if i.val < 127 then
                28696040108676
              else
                -160608501067260

def vZ : I → ℤ := fun i =>
  if i.val < 64 then
    if i.val < 32 then
      if i.val < 16 then
        if i.val < 8 then
          if i.val < 4 then
            if i.val < 2 then
              if i.val < 1 then
                -492340548561414
              else
                -158092459393286
            else
              if i.val < 3 then
                -347452735474950
              else
                -205336021667334
          else
            if i.val < 6 then
              if i.val < 5 then
                -97867658039942
              else
                -82863030300422
            else
              if i.val < 7 then
                43122533359610
              else
                33396213905018
        else
          if i.val < 12 then
            if i.val < 10 then
              if i.val < 9 then
                62971157803258
              else
                38522745796602
            else
              if i.val < 11 then
                72297957431034
              else
                23403094322682
          else
            if i.val < 14 then
              if i.val < 13 then
                79789829707642
              else
                46661086909946
            else
              if i.val < 15 then
                31895885065082
              else
                34295979719162
      else
        if i.val < 24 then
          if i.val < 20 then
            if i.val < 18 then
              if i.val < 17 then
                -31778896408838
              else
                -30023358774534
            else
              if i.val < 19 then
                -50103718775174
              else
                -49786717148038
          else
            if i.val < 22 then
              if i.val < 21 then
                -79525980005382
              else
                -16504351385990
            else
              if i.val < 23 then
                -188095592815878
              else
                -45057550509190
        else
          if i.val < 28 then
            if i.val < 26 then
              if i.val < 25 then
                -293997653600134
              else
                -147425598136198
            else
              if i.val < 27 then
                -279291609355654
              else
                -186366082126982
          else
            if i.val < 30 then
              if i.val < 29 then
                -188291214690822
              else
                -115068980064262
            else
              if i.val < 31 then
                -147721768987270
              else
                -52724468411398
    else
      if i.val < 48 then
        if i.val < 40 then
          if i.val < 36 then
            if i.val < 34 then
              if i.val < 33 then
                -159761310642438
              else
                -61045765046790
            else
              if i.val < 35 then
                -136361290753926
              else
                -52378465292038
          else
            if i.val < 38 then
              if i.val < 37 then
                -76242781574150
              else
                16116328071930
            else
              if i.val < 39 then
                -48159762231302
              else
                58039526087034
        else
          if i.val < 44 then
            if i.val < 42 then
              if i.val < 41 then
                -47971978182918
              else
                36424928081018
            else
              if i.val < 43 then
                -19334546817670
              else
                38884570236282
          else
            if i.val < 46 then
              if i.val < 45 then
                26823209912570
              else
                105916996502138
            else
              if i.val < 47 then
                44598897739386
              else
                157828785037306
      else
        if i.val < 56 then
          if i.val < 52 then
            if i.val < 50 then
              if i.val < 49 then
                57644246766458
              else
                154067896020090
            else
              if i.val < 51 then
                109100801600378
              else
                160201316095610
          else
            if i.val < 54 then
              if i.val < 53 then
                157437803914490
              else
                201307901101306
            else
              if i.val < 55 then
                139064841177850
              else
                207102051878266
        else
          if i.val < 60 then
            if i.val < 58 then
              if i.val < 57 then
                83963039739002
              else
                153044065890042
            else
              if i.val < 59 then
                59716043081722
              else
                107240098492922
          else
            if i.val < 62 then
              if i.val < 61 then
                54725014022010
              else
                96641559377786
            else
              if i.val < 63 then
                20539886357370
              else
                68835807678330
  else
    if i.val < 96 then
      if i.val < 80 then
        if i.val < 72 then
          if i.val < 68 then
            if i.val < 66 then
              if i.val < 65 then
                -28007474651270
              else
                14822686420602
            else
              if i.val < 67 then
                -53793142530438
              else
                -11159098348038
          else
            if i.val < 70 then
              if i.val < 69 then
                -76613278275718
              else
                -11412350975494
            else
              if i.val < 71 then
                -119159567471366
              else
                -42965082018182
        else
          if i.val < 76 then
            if i.val < 74 then
              if i.val < 73 then
                -141665852137862
              else
                -89210905628038
            else
              if i.val < 75 then
                -117400850602758
              else
                -77732897361926
          else
            if i.val < 78 then
              if i.val < 77 then
                -97806168036998
              else
                -25318183886214
            else
              if i.val < 79 then
                -119329296134662
              else
                -16894489748358
      else
        if i.val < 88 then
          if i.val < 84 then
            if i.val < 82 then
              if i.val < 81 then
                -130272458816390
              else
                -46739695596678
            else
              if i.val < 83 then
                -91416430542854
              else
                -32091850156934
          else
            if i.val < 86 then
              if i.val < 85 then
                -53317705780358
              else
                28525201053050
            else
              if i.val < 87 then
                -50534160823942
              else
                65970613825530
        else
          if i.val < 92 then
            if i.val < 90 then
              if i.val < 89 then
                -25201680030982
              else
                87769208522874
            else
              if i.val < 91 then
                56426015155450
              else
                152612081736826
          else
            if i.val < 94 then
              if i.val < 93 then
                124108566402682
              else
                225527762305402
            else
              if i.val < 95 then
                130079522690042
              else
                228487131939706
    else
      if i.val < 112 then
        if i.val < 104 then
          if i.val < 100 then
            if i.val < 98 then
              if i.val < 97 then
                134434333003258
              else
                201972036988794
            else
              if i.val < 99 then
                171697818603770
              else
                236447230929146
          else
            if i.val < 102 then
              if i.val < 101 then
                165328588975098
              else
                282645513790202
            else
              if i.val < 103 then
                80128194516858
              else
                225825037014906
        else
          if i.val < 108 then
            if i.val < 106 then
              if i.val < 105 then
                22386961766650
              else
                110467543489530
            else
              if i.val < 107 then
                70139091467770
              else
                80418103712634
          else
            if i.val < 110 then
              if i.val < 109 then
                135743898041722
              else
                126523354523258
            else
              if i.val < 111 then
                118196522898682
              else
                112770919161466
      else
        if i.val < 120 then
          if i.val < 116 then
            if i.val < 114 then
              if i.val < 113 then
                61338973327866
              else
                27614970833914
            else
              if i.val < 115 then
                39727842610682
              else
                -16694006967558
          else
            if i.val < 118 then
              if i.val < 117 then
                21250402202618
              else
                -11953438176262
            else
              if i.val < 119 then
                -34255484485382
              else
                -46357190216326
        else
          if i.val < 124 then
            if i.val < 122 then
              if i.val < 121 then
                -78995580740614
              else
                -90133738532102
            else
              if i.val < 123 then
                -103609515394950
              else
                -37304447331590
          else
            if i.val < 126 then
              if i.val < 125 then
                -206922269537030
              else
                49853041453306
            else
              if i.val < 127 then
                -399342982647814
              else
                -278099486214

def xZ : I → ℤ := fun i =>
  if i.val < 64 then
    if i.val < 32 then
      if i.val < 16 then
        if i.val < 8 then
          if i.val < 4 then
            if i.val < 2 then
              if i.val < 1 then
                -463150375523196
              else
                173639588100868
            else
              if i.val < 3 then
                -160664235972988
              else
                91941829332484
          else
            if i.val < 6 then
              if i.val < 5 then
                133592104161028
              else
                54108575312772
            else
              if i.val < 7 then
                146159178960260
              else
                34689381316228
        else
          if i.val < 12 then
            if i.val < 10 then
              if i.val < 9 then
                44428140612868
              else
                5498540566788
            else
              if i.val < 11 then
                47095384743300
              else
                -9049772926972
          else
            if i.val < 14 then
              if i.val < 13 then
                69742188796420
              else
                5361809197444
            else
              if i.val < 15 then
                -1344785395708
              else
                18716834808068
      else
        if i.val < 24 then
          if i.val < 20 then
            if i.val < 18 then
              if i.val < 17 then
                -49612955438844
              else
                19406451679620
            else
              if i.val < 19 then
                2157624875396
              else
                37008406682372
          else
            if i.val < 22 then
              if i.val < 21 then
                -6102282781692
              else
                75023104201860
            else
              if i.val < 23 then
                -153932080944508
              else
                92936251261444
        else
          if i.val < 28 then
            if i.val < 26 then
              if i.val < 25 then
                -236679365683708
              else
                78848793201412
            else
              if i.val < 27 then
                -117837455687676
              else
                69687233560452
          else
            if i.val < 30 then
              if i.val < 29 then
                14922981795332
              else
                79981717729540
            else
              if i.val < 31 then
                -20088977186556
              else
                81005273054596
    else
      if i.val < 48 then
        if i.val < 40 then
          if i.val < 36 then
            if i.val < 34 then
              if i.val < 33 then
                -101568849757692
              else
                66439155727108
            else
              if i.val < 35 then
                -70778633325052
              else
                66221180727556
          else
            if i.val < 38 then
              if i.val < 37 then
                -16821402294396
              else
                79838940485124
            else
              if i.val < 39 then
                -61569925956604
              else
                69344913102340
        else
          if i.val < 44 then
            if i.val < 42 then
              if i.val < 41 then
                -114955850683772
              else
                35098414715268
            else
              if i.val < 43 then
                -73082124872444
              else
                25742219587844
          else
            if i.val < 46 then
              if i.val < 45 then
                -27708889860476
              else
                54710253714564
            else
              if i.val < 47 then
                -68485932872828
              else
                76591989555588
      else
        if i.val < 56 then
          if i.val < 52 then
            if i.val < 50 then
              if i.val < 49 then
                -97848762647804
              else
                65375545797380
            else
              if i.val < 51 then
                -35257617851644
              else
                50057005854852
          else
            if i.val < 54 then
              if i.val < 53 then
                10484640466308
              else
                53491015434628
            else
              if i.val < 55 then
                -48603956425468
              else
                57868481251076
        else
          if i.val < 60 then
            if i.val < 58 then
              if i.val < 57 then
                -108290564202620
              else
                49970965204228
            else
              if i.val < 59 then
                -74556758920828
              else
                44879906822788
          else
            if i.val < 62 then
              if i.val < 61 then
                -30716939950844
              else
                48521376631044
            else
              if i.val < 63 then
                -54959702666748
              else
                46682425880580
  else
    if i.val < 96 then
      if i.val < 80 then
        if i.val < 72 then
          if i.val < 68 then
            if i.val < 66 then
              if i.val < 65 then
                -76906644604028
              else
                41216665631492
            else
              if i.val < 67 then
                -47473858597372
              else
                49238875457668
          else
            if i.val < 70 then
              if i.val < 69 then
                -43656035407612
              else
                62556778711812
            else
              if i.val < 71 then
                -88975952608380
              else
                57084424506372
        else
          if i.val < 76 then
            if i.val < 74 then
              if i.val < 73 then
                -83852322183036
              else
                42286217060484
            else
              if i.val < 75 then
                -14550841476732
              else
                49288871488644
          else
            if i.val < 78 then
              if i.val < 77 then
                -6825118027644
              else
                71444475510404
            else
              if i.val < 79 then
                -84301635680380
              else
                71386702930052
      else
        if i.val < 88 then
          if i.val < 84 then
            if i.val < 82 then
              if i.val < 81 then
                -111042193444988
              else
                46894865477380
            else
              if i.val < 83 then
                -51844569056252
              else
                34941047510916
          else
            if i.val < 86 then
              if i.val < 85 then
                -36873385160188
              else
                49366009367300
            else
              if i.val < 87 then
                -96382011850748
              else
                67206283100804
        else
          if i.val < 92 then
            if i.val < 90 then
              if i.val < 89 then
                -100116640270332
              else
                76116513337860
            else
              if i.val < 91 then
                -28637029020796
              else
                83665897420420
          else
            if i.val < 94 then
              if i.val < 93 then
                -21460601346428
              else
                83657551168388
            else
              if i.val < 95 then
                -90911347233276
              else
                66131219381124
    else
      if i.val < 112 then
        if i.val < 104 then
          if i.val < 100 then
            if i.val < 98 then
              if i.val < 97 then
                -88584806463100
              else
                53545676464260
            else
              if i.val < 99 then
                -17710406648572
              else
                71508895428356
          else
            if i.val < 102 then
              if i.val < 101 then
                -54270527594876
              else
                94078631146884
            else
              if i.val < 103 then
                -188488763741564
              else
                77973580235524
        else
          if i.val < 108 then
            if i.val < 106 then
              if i.val < 105 then
                -191177337841020
              else
                37978790677636
            else
              if i.val < 107 then
                -22669291536380
              else
                22280487827332
          else
            if i.val < 110 then
              if i.val < 109 then
                78962774404740
              else
                27470861536772
            else
              if i.val < 111 then
                13911153251460
              else
                12225310308100
      else
        if i.val < 120 then
          if i.val < 116 then
            if i.val < 114 then
              if i.val < 113 then
                -34970025144444
              else
                -17407262339964
            else
              if i.val < 115 then
                25533288225924
              else
                -17931297583100
          else
            if i.val < 118 then
              if i.val < 117 then
                51299862581636
              else
                6641249802500
            else
              if i.val < 119 then
                -8981873200252
              else
                17845246842500
        else
          if i.val < 124 then
            if i.val < 122 then
              if i.val < 121 then
                -17785193809660
              else
                33277542979332
            else
              if i.val < 123 then
                6697838437380
              else
                105409015636612
          else
            if i.val < 126 then
              if i.val < 125 then
                -143494081671804
              else
                206600426515204
            else
              if i.val < 127 then
                -420499983992444
              else
                238456382094340

def shiftZ (i : I) (a : I → ℤ) : I → ℤ := fun j => a (i + j)
def dotZ (a b : I → ℤ) : ℤ := ∑ k, a k * b k
def zmZ : I → ℤ := shiftZ (-1) zZ
def vmZ : I → ℤ := shiftZ (-1) vZ
def fIntercept (j : I) : ℤ := dotZ (zmZ - xZ) (xZ - shiftZ j xZ)
def fSlope (j : I) : ℤ := -dotZ vmZ (xZ - shiftZ j xZ)
def gIntercept (j : I) : ℤ := dotZ (xZ - zZ) (zZ - shiftZ j zZ)
def gSlope (j : I) : ℤ := dotZ vmZ (zZ - shiftZ j zZ)

def numerator : ℤ := 38847831300265103262189027
def denominator : ℤ := 20588352022933119368900773

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
theorem residual_squared : dotZ (xZ - zZ) (xZ - zZ) = 1638399999999268052811275665408 := by decide


end ADMMCycleData
