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

universe u v

section
variable {ι : Type*} {α : ι → Type*}

theorem CharZero.pi (i : ι) [Π i, AddMonoidWithOne (α i)] [CharZero (α i)] :
    CharZero (Π i, α i) where
  cast_injective _ _ h := Nat.cast_injective <| congrFun h i

/-- Strictly this only needs any one component to be char-zero, but this is awkward to express. -/
instance Pi.instCharZero [Nonempty ι] [Π i, AddMonoidWithOne (α i)] [Π i, CharZero (α i)] :
    CharZero (Π i, α i) := by
  inhabit ι
  exact CharZero.pi default

end

namespace CharP

instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiring R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  ⟨fun x =>
    let ⟨i⟩ := hi
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι → R) = 0 by rw [map_natCast, h],
          fun h ↦ by rw [← map_natCast (Pi.evalRingHom (fun _ : ι => R) i) x, h, map_zero]⟩⟩

-- diamonds
instance pi' (ι : Type u) [Nonempty ι] (R : Type v) [CommRing R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  CharP.pi ι R p

end CharP
