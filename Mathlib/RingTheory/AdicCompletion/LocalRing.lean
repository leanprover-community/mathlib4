/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Basic Properties of Complete Local Ring

In this file we prove that a ring that is adic complete with respect to a maximal ideal
ia a local ring (complete local ring).

-/
set_option backward.defeqAttrib.useBackward true

public section

variable {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal]

theorem isLocalRing_of_isAdicComplete_maximal [IsAdicComplete m R] : IsLocalRing R :=
  IsLocalRing.of_unique_max_ideal ⟨m, ‹m.IsMaximal›, fun _ hJ ↦
    (‹m.IsMaximal›.eq_of_le hJ.ne_top <|
      (IsAdicComplete.le_jacobson_bot m).trans <| sInf_le ⟨bot_le, hJ⟩).symm⟩
