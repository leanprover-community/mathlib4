
/-- Convert a character into a `UInt8`, by truncating (reducing modulo 256) if necessary. -/
def Char.toUInt8 (n : Char) : UInt8 := n.1.toUInt8

theorem Char.utf8Size_pos (c : Char) : 0 < c.utf8Size :=
  let this {c} {t e : UInt32} : [Decidable c] → 0 < t → 0 < e → 0 < ite c t e
  | Decidable.isTrue _, h, _ => h
  | Decidable.isFalse _, _, h => h
  this (by decide) $ this (by decide) $ this (by decide) (by decide)

theorem String.csize_pos : (c : Char) → 0 < String.csize c := Char.utf8Size_pos
