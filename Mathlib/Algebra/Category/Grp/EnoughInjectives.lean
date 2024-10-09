/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Grp.EpiMono

/-!

# Category of abelian groups has enough injectives

Given an abelian group `A`, then `i : A ⟶ ∏_{A⋆} ℚ ⧸ ℤ` defined by `i : a ↦ c ↦ c a` is an
injective presentation for `A`, hence category of abelian groups has enough injectives.

## Implementation notes

This file is split from `Mathlib.Algebra.Grp.Injective` is to prevent import loop.
This file's dependency imports `Mathlib.Algebra.Grp.Injective`.
-/

open CategoryTheory

universe u

namespace AddCommGrp

open CharacterModule

instance enoughInjectives : EnoughInjectives AddCommGrp.{u} where
  presentation A_ := Nonempty.intro
    { J := of <| (CharacterModule A_) → ULift.{u} (AddCircle (1 : ℚ))
      injective := injective_of_divisible _
      f := ⟨⟨fun a i ↦ ULift.up (i a), by aesop⟩, by aesop⟩
      mono := (AddCommGrp.mono_iff_injective _).mpr <| (injective_iff_map_eq_zero _).mpr
        fun a h0 ↦ eq_zero_of_character_apply (congr_arg ULift.down <| congr_fun h0 ·) }

end AddCommGrp


namespace CommGrp

instance enoughInjectives : EnoughInjectives CommGrp.{u} :=
  EnoughInjectives.of_equivalence commGroupAddCommGroupEquivalence.functor

end CommGrp
