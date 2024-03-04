/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Module.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat

#align_import algebra.category.Group.injective from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups and that the category of abelian groups has enough injective objects.

## Main results

- `AddCommGroupCat.injective_of_divisible` : a divisible group is also an injective object.
- `AddCommGroupCat.enoughInjectives` : the category of abelian groups (written additively) has
  enough injectives.
- `CommGroupCat.enoughInjectives` : the category of abelian group (written multiplicatively) has
  enough injectives.

## Implementation notes

The details of the proof that the category of abelian groups has enough injectives is hidden
inside the namespace `AddCommGroup.enough_injectives_aux_proofs`. These are not marked `private`,
but are not supposed to be used directly.

-/


open CategoryTheory

open Pointwise

universe u

variable (A : Type u) [AddCommGroup A]

set_option linter.uppercaseLean3 false

theorem Module.Baer.of_divisible [DivisibleBy A ℤ] : Module.Baer ℤ A := fun I g ↦ by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn ↦ ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton ℤ A (DivisibleBy.div gₘ m), fun n hn ↦ ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  rw [map_zsmul, LinearMap.toSpanSingleton_apply, DivisibleBy.div_cancel gₘ h0, ← map_zsmul g,
    SetLike.mk_smul_mk]

namespace AddCommGroupCat

theorem injective_as_module_iff : Injective (⟨A⟩ : ModuleCat ℤ) ↔
    Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  ((forget₂ (ModuleCat ℤ) AddCommGroupCat).asEquivalence.map_injective_iff ⟨A⟩).symm
#noalign AddCommGroup.injective_of_injective_as_module
#noalign AddCommGroup.injective_as_module_of_injective_as_Ab

instance injective_of_divisible [DivisibleBy A ℤ] :
    Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  (injective_as_module_iff A).mp <|
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible A).injective)
#align AddCommGroup.injective_of_divisible AddCommGroupCat.injective_of_divisible

instance injective_ratCircle : Injective <| of <| ULift.{u} <| AddCircle (1 : ℚ) :=
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  injective_of_divisible _

end AddCommGroupCat
