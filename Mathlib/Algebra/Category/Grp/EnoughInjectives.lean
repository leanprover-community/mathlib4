/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Injective

/-!

# Category of abelian groups has enough injectives

Given an abelian group `A`, then `i : A ⟶ ∏_{A⋆} ℚ ⧸ ℤ` defined by `i : a ↦ c ↦ c a` is an
injective presentation for `A`, hence category of abelian groups has enough injectives.

## Main results

- `AddCommGrpCat.enoughInjectives` : the category of abelian groups (written additively) has
  enough injectives.
- `CommGrpCat.enoughInjectives` : the category of abelian groups (written multiplicatively) has
  enough injectives.

## Implementation notes

This file is split from `Mathlib/Algebra/Category/GrpCat/Injective.lean` to prevent import loops.
-/

open CategoryTheory

universe u

namespace AddCommGrpCat

open CharacterModule

instance enoughInjectives : EnoughInjectives AddCommGrpCat.{u} where
  presentation A_ := Nonempty.intro
    { J := of <| (CharacterModule A_) → ULift.{u} (AddCircle (1 : ℚ))
      injective := injective_of_divisible _
      f := ofHom ⟨⟨fun a i ↦ ULift.up (i a), by aesop⟩, by aesop⟩
      mono := (AddCommGrpCat.mono_iff_injective _).mpr <| (injective_iff_map_eq_zero _).mpr
        fun _ h0 ↦ eq_zero_of_character_apply (congr_arg ULift.down <| congr_fun h0 ·) }

end AddCommGrpCat


namespace CommGrpCat

instance enoughInjectives : EnoughInjectives CommGrpCat.{u} :=
  EnoughInjectives.of_equivalence commGroupAddCommGroupEquivalence.functor

end CommGrpCat
