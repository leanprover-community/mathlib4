/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Pi

/-!
# Characteristic of semirings of functions
-/

public section

section
variable {ι : Type*} {α : ι → Type*}

theorem CharZero.pi (i : ι) [Π i, AddMonoidWithOne (α i)] [CharZero (α i)] :
    CharZero (Π i, α i) where
  cast_injective _ _ h := Nat.cast_injective <| congrFun h i

/-- Strictly this only needs any one component to be char-zero, but this is awkward to express. -/
instance Pi.instCharZero [Nonempty ι] [Π i, AddMonoidWithOne (α i)] [∀ i, CharZero (α i)] :
    CharZero (Π i, α i) := by
  inhabit ι
  exact CharZero.pi default

end

section
variable {ι : Type*} {R : Type*} [Nonempty ι] [AddMonoidWithOne R]

instance Pi.instCharP (p : ℕ) [CharP R p] : CharP (ι → R) p where
  cast_eq_zero_iff x := by
    simp [← CharP.cast_eq_zero_iff R p x, funext_iff]

instance Pi.instExpChar : ∀ {p} [ExpChar R p], ExpChar (ι → R) p
  | _, @ExpChar.zero _ _ _ => .zero
  | _, @ExpChar.prime _ _ _ _ _ => .prime ‹_›

end
