/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Nat.Cast.Basic

/-!
# Transporting `CharZero` accross injective `AddMonoidHom`s

This file exists in order to avoid adding extra imports to other files in this subdirectory.
-/

theorem CharZero.of_addMonoidHom {M N : Type*} [AddCommMonoidWithOne M] [AddCommMonoidWithOne N]
    [CharZero M] (e : M →+ N) (he : e 1 = 1) (he' : Function.Injective e) : CharZero N where
  cast_injective n m h := by
    rwa [← map_natCast' _ he, ← map_natCast' _ he, he'.eq_iff, Nat.cast_inj] at h
