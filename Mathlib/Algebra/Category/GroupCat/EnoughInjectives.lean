/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Module.CharacterModule

/-!

# Category of abelian groups has enough injectives

Given an abelian group `A`, then `i : A ⟶ ∏_{A⋆} ℚ ⧸ ℤ` defined by `i : a ↦ c ↦ c a` is an
injective presentation for `A`, hence category of abelian groups has enough injectives.

## Implementation notes

This file is splitted from `Mathlib.Algebra.GroupCat.Injective` is to prevent import loop.
This file's dependency imports `Mathlib.Algebra.GroupCat.Injective`.
-/

open CategoryTheory

universe u

namespace AddCommGroupCat

open CharacterModule

instance enoughInjectives : EnoughInjectives (AddCommGroupCat.{u}) where
  presentation A_ := Nonempty.intro
    { J := of <| (CharacterModule A_) → ULift.{u} (AddCircle (1 : ℚ))
      injective :=
        have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
        injective_of_divisible _
      f := ⟨⟨fun a i ↦ ULift.up <| i a, by aesop⟩, by aesop⟩
      mono := (AddCommGroupCat.mono_iff_injective _).mpr <|
      (injective_iff_map_eq_zero _).mpr fun a h0 ↦ by
        refine eq_zero_of_ofSpanSingleton_apply_self a ?_ -- <|
        let f : of (ℤ ∙ a) ⟶ of (ULift.{u} <| AddCircle (1 : ℚ)) :=
          ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap.toAddMonoidHom.comp <|
            ofSpanSingleton a)
        suffices H : f ⟨a, Submodule.mem_span_singleton_self a⟩ = 0
        · exact ULift.ext_iff _ _ |>.mp H
        let g : of (ℤ ∙ a) ⟶ A_ := AddSubgroupClass.subtype _
        have : Mono g := (mono_iff_injective _).mpr Subtype.val_injective
        erw [← DFunLike.congr_fun (Injective.comp_factorThru f g),
          show Injective.factorThru f g a = 0 from congr_fun h0
            ((ULift.moduleEquiv (R := ℤ)).toLinearMap.toAddMonoidHom.comp
              (Injective.factorThru f g))] }

end AddCommGroupCat


namespace CommGroupCat

instance enoughInjectives : EnoughInjectives CommGroupCat.{u} :=
  EnoughInjectives.of_equivalence commGroupAddCommGroupEquivalence.functor

end CommGroupCat
