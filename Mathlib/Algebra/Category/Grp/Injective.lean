/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Instances.AddCircle

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups and that the category of abelian groups has enough injective objects.

## Main results

- `AddCommGrp.injective_of_divisible` : a divisible group is also an injective object.
- `AddCommGrp.enoughInjectives` : the category of abelian groups (written additively) has
  enough injectives.
- `CommGrp.enoughInjectives` : the category of abelian group (written multiplicatively) has
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

namespace AddCommGrp

theorem injective_as_module_iff : Injective (⟨A⟩ : ModuleCat ℤ) ↔
    Injective (⟨A,inferInstance⟩ : AddCommGrp) :=
  ((forget₂ (ModuleCat ℤ) AddCommGrp).asEquivalence.map_injective_iff ⟨A⟩).symm

instance injective_of_divisible [DivisibleBy A ℤ] :
    Injective (⟨A,inferInstance⟩ : AddCommGrp) :=
  (injective_as_module_iff A).mp <|
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible A).injective)

instance injective_ratCircle : Injective <| of <| ULift.{u} <| AddCircle (1 : ℚ) :=
  injective_of_divisible _

end AddCommGrp
