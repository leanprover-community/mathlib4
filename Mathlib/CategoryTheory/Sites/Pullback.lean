/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.LeftExact

#align_import category_theory.sites.pushforward from "leanprover-community/mathlib"@"e2e38c005fc6f715502490da6cb0ec84df9ed228"

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


universe v₁ v₂ v₃ u₁ u₂ u₃ u

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (G : C ⥤ D) (A : Type u₃) [Category.{max u₂ v₂} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

-- porting note: there was an explicit call to
-- CategoryTheory.Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u₁, v₁, v₁}
-- but it is not necessary (it was not either in mathlib)
--instance [HasLimits A] : CreatesLimits (sheafToPresheaf J A) := inferInstance

-- The assumptions so that we have sheafification
--variable [ConcreteCategory.{v₁} A] [PreservesLimits (forget A)] [HasColimits A] [HasLimits A]

--variable [PreservesFilteredColimits (forget A)] [ReflectsIsomorphisms (forget A)]

attribute [local instance] reflectsLimitsOfReflectsIsomorphisms

instance {X : C} : IsCofiltered (J.Cover X) :=
  inferInstance

variable [∀ (X : Dᵒᵖ), HasColimitsOfShape (CostructuredArrow G.op X) A]
variable [ConcreteCategory A]
variable [PreservesLimits (forget A)]
variable [HasColimits A]
variable [HasLimits A]
variable [PreservesFilteredColimits (forget A)] [ReflectsIsomorphisms (forget A)]

/-- The pullback functor `Sheaf J A ⥤ Sheaf K A` associated to a functor `G : C ⥤ D` in the
same direction as `G`. -/
--@[simps!]
def Functor.sheafPullback : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ lan G.op ⋙ presheafToSheaf K A
#align category_theory.sites.pushforward CategoryTheory.Functor.sheafPullback

variable [PreservesFiniteLimits (lan G.op : (Cᵒᵖ⥤ A) ⥤ (Dᵒᵖ ⥤ A))]

--instance [RepresentablyFlat G] : PreservesFiniteLimits (G.sheafPullback A J K) := by
--  have : PreservesFiniteLimits (lan G.op ⋙ presheafToSheaf K A) :=
--    compPreservesFiniteLimits _ _
--  apply compPreservesFiniteLimits

/-- The pullback functor is left adjoint to the pushforward functor. -/
def Functor.sheafAdjunctionContinuous [Functor.IsContinuous.{max u₂ v₂} G J K] :
    G.sheafPullback A J K ⊣ G.sheafPushforwardContinuous A J K :=
  ((Lan.adjunction A G.op).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (sheafToPresheaf J A) (𝟭 _) (Iso.refl _) (Iso.refl _)
#align category_theory.sites.pullback_pushforward_adjunction CategoryTheory.Functor.sheafAdjunctionContinuous

end CategoryTheory

namespace CategoryTheory

variable {C D : Type (u + 1)} [LargeCategory C] [LargeCategory D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

instance (X : Dᵒᵖ) : HasColimitsOfShape (CostructuredArrow G.op X) (Type (u + 1)) := by
  sorry

example : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)) :=
  G.sheafPullback (Type (u + 1)) J K

end CategoryTheory

namespace CategoryTheory

variable {C : Type v₁} [SmallCategory C] {D : Type v₁} [SmallCategory D] (G : C ⥤ D)

variable (A : Type u₁) [Category.{v₁} A]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

-- porting note: there was an explicit call to
-- CategoryTheory.Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u₁, v₁, v₁}
-- but it is not necessary (it was not either in mathlib)
instance [HasLimits A] : CreatesLimits (sheafToPresheaf J A) := inferInstance

-- The assumptions so that we have sheafification
variable [ConcreteCategory.{v₁} A] [PreservesLimits (forget A)] [HasColimits A] [HasLimits A]

variable [PreservesFilteredColimits (forget A)] [ReflectsIsomorphisms (forget A)]


#check Functor.sheafPullback G A J K
/-- The pullback functor `Sheaf J A ⥤ Sheaf K A` associated to a functor `G : C ⥤ D` in the
same direction as `G`. -/
@[simps!]
def Functor.sheafPullback : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ lan G.op ⋙ presheafToSheaf K A
#align category_theory.sites.pushforward CategoryTheory.Functor.sheafPullback

instance [RepresentablyFlat G] : PreservesFiniteLimits (G.sheafPullback A J K) := by
  have : PreservesFiniteLimits (lan (Functor.op G) ⋙ presheafToSheaf K A) :=
    compPreservesFiniteLimits _ _
  apply compPreservesFiniteLimits

/-- The pullback functor is left adjoint to the pushforward functor. -/
def Functor.sheafAdjunctionContinuous [Functor.IsContinuous.{v₁} G J K] :
    G.sheafPullback A J K ⊣ G.sheafPushforwardContinuous A J K :=
  ((Lan.adjunction A G.op).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (sheafToPresheaf J A) (𝟭 _) (Iso.refl _) (Iso.refl _)
#align category_theory.sites.pullback_pushforward_adjunction CategoryTheory.Functor.sheafAdjunctionContinuous

end CategoryTheory
