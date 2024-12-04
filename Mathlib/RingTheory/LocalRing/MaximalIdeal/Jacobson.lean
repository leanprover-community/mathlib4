/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Maximal ideals and Jacobson radicals of local rings

-/

variable {R : Type*} [CommRing R]

namespace IsLocalRing

variable [IsLocalRing R]

theorem maximalIdeal_le_jacobson (I : Ideal R) :
    IsLocalRing.maximalIdeal R ≤ I.jacobson :=
  le_sInf fun _ ⟨_, h⟩ => le_of_eq (IsLocalRing.eq_maximalIdeal h).symm

theorem jacobson_eq_maximalIdeal (I : Ideal R) (h : I ≠ ⊤) :
    I.jacobson = IsLocalRing.maximalIdeal R :=
  le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)

end IsLocalRing

@[deprecated (since := "2024-11-11")]
alias LocalRing.maximalIdeal_le_jacobson := IsLocalRing.maximalIdeal_le_jacobson

@[deprecated (since := "2024-11-11")]
alias LocalRing.jacobson_eq_maximalIdeal := IsLocalRing.jacobson_eq_maximalIdeal
