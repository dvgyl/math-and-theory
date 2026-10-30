import BinaryBasic

set_option autoImplicit false
namespace BinaryFuglede

def pointCode : Fin 64 → Fin 512 :=
  ![0, 11, 22, 29, 37, 46, 51, 56, 64, 71, 90, 93, 107, 108, 113, 118, 128, 142, 151, 153, 163, 173, 180, 186, 192, 205, 214, 219, 231, 234, 241, 252, 256, 263, 282, 285, 299, 300, 305, 310, 320, 331, 341, 350, 359, 364, 370, 377, 384, 399, 403, 412, 422, 425, 437, 442, 448, 459, 471, 476, 486, 493, 497, 506]

def freqCode : Fin 64 → Fin 512 :=
  ![0, 1, 2, 4, 8, 16, 32, 63, 64, 65, 66, 68, 72, 80, 96, 127, 128, 129, 130, 132, 136, 144, 160, 191, 192, 193, 194, 196, 200, 208, 224, 255, 256, 257, 258, 260, 264, 272, 288, 319, 320, 321, 322, 324, 328, 336, 352, 383, 384, 385, 386, 388, 392, 400, 416, 447, 448, 449, 450, 452, 456, 464, 480, 511]

def tileCode : Fin 8 → Fin 512 :=
  ![0, 1, 2, 4, 8, 16, 32, 63]

def allowedCode : Fin 28 → Fin 512 :=
  ![1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 31, 32, 33, 34, 36, 40, 47, 48, 55, 59, 61, 62, 63]

def point (i : Fin 64) : V := decodeFin (pointCode i)

def freq (i : Fin 64) : V := decodeFin (freqCode i)

def tileShift (i : Fin 8) : V := decodeFin (tileCode i)

def allowedShift (i : Fin 28) : V := decodeFin (allowedCode i)

def Eset : Set V := Set.range point
def Lset : Set V := Set.range freq
def Tset : Set V := Set.range tileShift
def Allowed : Set V := Set.range allowedShift

end BinaryFuglede
