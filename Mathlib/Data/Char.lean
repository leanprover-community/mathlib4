/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.UInt
import Mathlib.Init.Algebra.Order

#align_import data.char from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

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
  -- ⊢ 0 < if c.val ≤ UInt32.ofNatCore 127 utf8Size.proof_1 then UInt32.ofNatCore 1 …
  repeat (split; decide)
  -- ⊢ 0 < UInt32.ofNatCore 4 utf8Size.proof_7
  decide
  -- 🎉 no goals

/--
Provides a `LinearOrder` instance on `Char`. `Char` is the type of Unicode scalar values.
-/
instance : LinearOrder Char where
  le_refl := fun _ => @le_refl ℕ _ _
  le_trans := fun _ _ _ => @le_trans ℕ _ _ _ _
  le_antisymm := fun _ _ h₁ h₂ => Char.eq_of_val_eq <| UInt32.eq_of_val_eq <| Fin.ext <|
    @le_antisymm ℕ _ _ _ h₁ h₂
  lt_iff_le_not_le := fun _ _ => @lt_iff_le_not_le ℕ _ _ _
  le_total := fun _ _ => @le_total ℕ _ _ _
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  decidableLE := inferInstance

theorem Char.ofNat_toNat {c : Char} (h : isValidCharNat c.toNat) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos h]
  -- ⊢ ofNatAux (toNat c) h = c
  rfl
  -- 🎉 no goals
#align char.of_nat_to_nat Char.ofNat_toNat
