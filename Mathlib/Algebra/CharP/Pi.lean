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
  cast_injective _ _ h := Nat.cast_injective congr($h i)

variable [Nonempty ι]

/-- Strictly this only needs any one component to be char-zero, but this is awkward to express. -/
instance Pi.instCharZero [Π i, AddMonoidWithOne (α i)] [∀ i, CharZero (α i)] :
    CharZero (Π i, α i) := by
  inhabit ι
  exact CharZero.pi default

instance Pi.instCharP [Π i, AddMonoidWithOne (α i)] (p : ℕ) [∀ i, CharP (α i) p] :
    CharP (Π i, α i) p where
  cast_eq_zero_iff x := by simp [funext_iff, CharP.cast_eq_zero_iff _ p x]

instance Pi.instExpChar [Π i, AddMonoidWithOne (α i)] (p : ℕ) [∀ i, ExpChar (α i) p] :
    ExpChar (Π i, α i) p := by
  inhabit ι
  obtain hp | rfl := expChar_is_prime_or_one (α default) p
  · simp only [expChar_prime_iff, hp] at *
    infer_instance
  · simp only [expChar_one_iff] at *
    infer_instance

end
