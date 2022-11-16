import Mathlib.Init.Algebra.Order



/-- Convert a character into a `UInt8`, by truncating (reducing modulo 256) if necessary. -/
def Char.toUInt8 (n : Char) : UInt8 := n.1.toUInt8

theorem Char.utf8Size_pos (c : Char) : 0 < c.utf8Size := by
  simp only [utf8Size]
  repeat (split; decide)
  decide

theorem String.csize_pos : (c : Char) → 0 < String.csize c := Char.utf8Size_pos

/-- Define a `LinearOrder` on `Char`-/
instance : LinearOrder Char where
  le := (·≤·) --Char.hasLe
  le_refl := fun a => @le_refl Nat _ _
  le_trans := fun a b c => @le_trans Nat _ _ _ _
  le_antisymm := fun a b h₁ h₂ => Char.eq_of_veq <| le_antisymm h₁ h₂
  lt := (·<·) --Char.hasLt
  lt_iff_le_not_le := fun a b => @lt_iff_le_not_le Nat _ _ _
  le_total := fun a b => @le_total Nat _ _ _
  decidable_le := by infer_instance --Char.decidableLe
  decidable_eq := by infer_instance --Char.decidableLeChar.decidableEq
  decidable_lt := by infer_instance --Char.decidableLeChar.decidableLt

theorem Char.ofNat_toNat {c : Char} (h : isValidCharNat c.toNat) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos h]
  cases c
  simp [Char.toNat]

#align char.of_nat_to_nat Char.ofNat_toNat
