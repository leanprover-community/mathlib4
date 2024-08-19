/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Pullback of sheaves

## Main definitions

* `CategoryTheory.Functor.sheafPullback`: the functor `Sheaf J A ⥤ Sheaf K A` obtained
as an extension of a functor `G : C ⥤ D` between the underlying categories.

* `CategoryTheory.Functor.sheafAdjunctionContinuous`: the adjunction
`G.sheafPullback A J K ⊣ G.sheafPushforwardContinuous A J K` when the functor
`G` is continuous. In case `G` is representably flat, the pullback functor
on sheaves commutes with finite limits: this is a morphism of sites in the
sense of SGA 4 IV 4.9.

-/


universe v₁ u₁

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type v₁} [SmallCategory C] {D : Type v₁} [SmallCategory D] (G : C ⥤ D)
variable (A : Type u₁) [Category.{v₁} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

-- Porting note: there was an explicit call to
-- CategoryTheory.Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u₁, v₁, v₁}
-- but it is not necessary (it was not either in mathlib)
instance [HasLimits A] : CreatesLimits (sheafToPresheaf J A) := inferInstance

-- The assumptions so that we have sheafification
variable [ConcreteCategory.{v₁} A] [PreservesLimits (forget A)] [HasColimits A] [HasLimits A]
variable [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]

attribute [local instance] reflectsLimitsOfReflectsIsomorphisms

instance {X : C} : IsCofiltered (J.Cover X) :=
  inferInstance

/-- The pullback functor `Sheaf J A ⥤ Sheaf K A` associated to a functor `G : C ⥤ D` in the
same direction as `G`. -/
@[simps!]
def Functor.sheafPullback : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ G.op.lan ⋙ presheafToSheaf K A

instance [RepresentablyFlat G] : PreservesFiniteLimits (G.sheafPullback A J K) := by
  have : PreservesFiniteLimits (G.op.lan ⋙ presheafToSheaf K A) :=
    compPreservesFiniteLimits _ _
  apply compPreservesFiniteLimits

/-- The pullback functor is left adjoint to the pushforward functor. -/
def Functor.sheafAdjunctionContinuous [Functor.IsContinuous.{v₁} G J K] :
    G.sheafPullback A J K ⊣ G.sheafPushforwardContinuous A J K :=
  ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end CategoryTheory
