import Mathlib.Algebra.Group.Hom.Defs

/-!
# Transporting `CharZero` across injective `AddMonoidHom`s

This file exists in order to avoid adding extra imports to other files in this subdirectory.
-/

public section

theorem CharZero.of_addMonoidHom {M N : Type*} [AddCommMonoidWithOne M] [AddCommMonoidWithOne N]
    [CharZero M] (e : M →+ N) (he : e 1 = 1) (he' : Function.Injective e) : CharZero N where
  cast_injective n m h := by
    rwa [← map_natCast' _ he, ← map_natCast' _ he, he'.eq_iff, Nat.cast_inj] at h
