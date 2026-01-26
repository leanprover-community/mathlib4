import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Category of $R$-modules has enough injectives

We lift enough injectives of abelian groups to arbitrary $R$-modules by adjoint functors
`restrictScalars ⊣ coextendScalars`
-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [Ring R]

instance : EnoughInjectives (ModuleCat.{v} ℤ) :=
  EnoughInjectives.of_equivalence (forget₂ (ModuleCat ℤ) AddCommGrpCat)

lemma ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R) :=
  EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap ℤ R))

open ModuleCat in
instance [Small.{v} R] : EnoughInjectives (ModuleCat.{v} R) :=
  letI := enoughInjectives.{v} (Shrink.{v} R)
  EnoughInjectives.of_equivalence (restrictScalars (equivShrink R).symm.ringEquiv.toRingHom)
