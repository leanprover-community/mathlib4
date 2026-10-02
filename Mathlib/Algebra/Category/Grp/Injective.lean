/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective objects in category of (additive) abelian
groups. The proof that the category of abelian groups has enough injective objects can be found
in `Mathlib/Algebra/Category/Grp/EnoughInjectives.lean`.

## Main results

- `AddCommGrpCat.injective_of_divisible` : a divisible group is also an injective object.

-/

public section

open CategoryTheory

universe u

variable (A : Type u) [AddCommGroup A]

namespace AddCommGrpCat

theorem injective_as_module_iff : Injective (ModuleCat.of ℤ A) ↔
    Injective (C := AddCommGrpCat) ↧A :=
  ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.map_injective_iff ↧A).symm

instance injective_of_divisible [DivisibleBy A ℤ] :
    Injective (C := AddCommGrpCat) ↧A :=
  (injective_as_module_iff A).mp <|
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible ℤ A).injective)

end AddCommGrpCat
