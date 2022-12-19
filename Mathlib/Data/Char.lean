/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.char
! leanprover-community/mathlib commit c4658a649d216f57e99621708b09dcb3dcccbd23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.UInt
import Mathlib.Init.Algebra.Order

/-!
# More `Char` instances

This file provides a `LinearOrder` instance on `Char`. `Char` is the type of Unicode scalar values.
Provides an additional definition to truncate a `Char` to `UInt8` and a theorem on conversion to
`Nat`.
-/

/-- Convert a character into a `UInt8`, by truncating (reducing modulo 256) if necessary. -/
def Char.toUInt8 (n : Char) : UInt8 := n.1.toUInt8

theorem Char.utf8Size_pos (c : Char) : 0 < c.utf8Size := by
  simp only [utf8Size]
  repeat (split; decide)
  decide

theorem String.csize_pos : (c : Char) → 0 < String.csize c := Char.utf8Size_pos

/--
Provides a `LinearOrder` instance on `Char`. `Char` is the type of Unicode scalar values.
-/
instance : LinearOrder Char where
  le_refl := fun _ => @le_refl ℕ _ _
  le_trans := fun _ _ _  => @le_trans ℕ _ _ _ _
  le_antisymm := fun _ _ h₁ h₂ => Char.eq_of_val_eq <| UInt32.eq_of_val_eq <| Fin.ext <|
    @le_antisymm ℕ _ _ _ h₁ h₂
  lt_iff_le_not_le := fun _ _ => @lt_iff_le_not_le ℕ _ _ _
  le_total := fun _ _ => @le_total ℕ _ _ _
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  decidable_le := inferInstance

theorem Char.ofNat_toNat {c : Char} (h : isValidCharNat c.toNat) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos h]
  rfl
#align char.of_nat_to_nat Char.ofNat_toNat
