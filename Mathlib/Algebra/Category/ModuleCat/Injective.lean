/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.GroupCat.EnoughInjectives
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Logic.Equiv.TransferInstance

/-!
# Category of $R$-modules has enough injectives

we lift enough injectives of abelian groups to arbitrary $R$-modules by adjoint functors
`restrictScalars ⊣ coextendScalars`

## Implementation notes
This file is not part of `Algebra/Module/Injective.lean` to prevent import loop: enough-injectives
of abelian groups needs `Algebra/Module/Injective.lean` and this file needs enough-injectives of
abelian groups.
-/

open CategoryTheory

universe v u
variable (R : Type u) [Ring R]

instance : EnoughInjectives (ModuleCat.{v} ℤ) :=
  EnoughInjectives.of_equivalence (forget₂ (ModuleCat ℤ) AddCommGroupCat)

lemma ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R) :=
  EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap ℤ R))

open ModuleCat in
instance [UnivLE.{u,v}] : EnoughInjectives (ModuleCat.{v} R) :=
  letI := (equivShrink.{v} R).symm.ring
  letI := enoughInjectives.{v} (Shrink.{v} R)
  EnoughInjectives.of_equivalence (restrictScalars (equivShrink R).symm.ringEquiv.toRingHom)
