/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

#align_import category_theory.limits.preserves.finite from "leanprover-community/mathlib"@"3974a774a707e2e06046a14c0eaef4654584fada"

/-!
# Preservation of finite (co)limits.

These functors are also known as left exact (flat) or right exact functors when the categories
involved are abelian, or more generally, finitely (co)complete.

## Related results
* `CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts` :
  see `CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`. Also provides
  the dual version.
* `CategoryTheory.Limits.preservesFiniteLimitsIffFlat` :
  see `CategoryTheory/Functor/Flat.lean`.

-/


open CategoryTheory

namespace CategoryTheory.Limits

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {J : Type w} [SmallCategory J] {K : J ⥤ C}

/-- A functor is said to preserve finite limits, if it preserves all limits of shape `J`,
where `J : Type` is a finite category.
-/
class PreservesFiniteLimits (F : C ⥤ D) where
  preservesFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by infer_instance
#align category_theory.limits.preserves_finite_limits CategoryTheory.Limits.PreservesFiniteLimits

attribute [instance] PreservesFiniteLimits.preservesFiniteLimits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
noncomputable instance (priority := 100) preservesLimitsOfShapeOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J F := by
  apply preservesLimitsOfShapeOfEquiv (FinCategory.equivAsType J)
#align category_theory.limits.preserves_limits_of_shape_of_preserves_finite_limits CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits

-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve limits of some arbitrary size, then we preserve all finite limits. -/
noncomputable def PreservesLimitsOfSize.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F where
  preservesFiniteLimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestLimitsOfPreservesLimits F
    exact preservesLimitsOfShapeOfEquiv (FinCategory.equivAsType J) F
#align category_theory.limits.preserves_limits.preserves_finite_limits_of_size CategoryTheory.Limits.PreservesLimitsOfSize.preservesFiniteLimits

-- Added as a specialization of the dangerous instance above, for limits indexed in Type 0.
noncomputable instance (priority := 120) PreservesLimitsOfSize0.preservesFiniteLimits
    (F : C ⥤ D) [PreservesLimitsOfSize.{0, 0} F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F
#align preserves_limits_of_size.zero.preserves_finite_limits CategoryTheory.Limits.PreservesLimitsOfSize0.preservesFiniteLimits

-- An alternative specialization of the dangerous instance for small limits.
noncomputable instance (priority := 120) PreservesLimits.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimits F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F
#align category_theory.limits.preserves_limits.preserves_finite_limits CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits

/-- We can always derive `PreservesFiniteLimits C` by showing that we are preserving limits at an
arbitrary universe. -/
def preservesFiniteLimitsOfPreservesFiniteLimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesLimitsOfShape J F) :
    PreservesFiniteLimits F where
      preservesFiniteLimits J (_ : SmallCategory J) _ := by
        letI : Category (ULiftHom (ULift J)) := ULiftHom.category
        haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm F
#align category_theory.limits.preserves_finite_limits_of_preserves_finite_limits_of_size CategoryTheory.Limits.preservesFiniteLimitsOfPreservesFiniteLimitsOfSize

/-- The composition of two left exact functors is left exact. -/
def compPreservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩
#align category_theory.limits.comp_preserves_finite_limits CategoryTheory.Limits.compPreservesFiniteLimits

/- Porting note: adding this class because quantified classes don't behave well
[#2764](https://github.com/leanprover-community/mathlib4/pull/2764) -/
/-- A functor `F` preserves finite products if it preserves all from `Discrete J`
for `Fintype J` -/
class PreservesFiniteProducts (F : C ⥤ D) where
  preserves : ∀ (J : Type) [Fintype J], PreservesLimitsOfShape (Discrete J) F

attribute [instance] PreservesFiniteProducts.preserves

instance compPreservesFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts F] [PreservesFiniteProducts G] :
    PreservesFiniteProducts (F ⋙ G) where
  preserves _ _ := inferInstance

noncomputable instance (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteProducts F where
  preserves _ _ := inferInstance

/--
A functor is said to reflect finite limits, if it reflects all limits of shape `J`,
where `J : Type` is a finite category.
-/
class ReflectsFiniteLimits (F : C ⥤ D) where
  reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F := by
    infer_instance

attribute [instance] ReflectsFiniteLimits.reflects

/- Similarly to preserving finite products, quantified classes don't behave well. -/
/--
A functor `F` preserves finite products if it reflects limits of shape `Discrete J` for finite `J`
-/
class ReflectsFiniteProducts (F : C ⥤ D) where
  reflects : ∀ (J : Type) [Fintype J], ReflectsLimitsOfShape (Discrete J) F

attribute [instance] ReflectsFiniteProducts.reflects

-- This is a dangerous instance as it has unbound universe variables.
/-- If we reflect limits of some arbitrary size, then we reflect all finite limits. -/
noncomputable def ReflectsLimitsOfSize.reflectsFiniteLimits
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w₂} F] : ReflectsFiniteLimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestLimitsOfReflectsLimits F
    exact reflectsLimitsOfShapeOfEquiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
noncomputable instance (priority := 120) (F : C ⥤ D) [ReflectsLimitsOfSize.{0, 0} F] :
    ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

-- An alternative specialization of the dangerous instance for small colimits.
noncomputable instance (priority := 120) (F : C ⥤ D)
    [ReflectsLimits F] : ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

/--
If `F ⋙ G` preserves finite limits and `G` reflects finite limits, then `F` preserves
finite limits.
-/
def preservesFiniteLimitsOfReflectsOfPreserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShapeOfReflectsOfPreserves F G

/--
If `F ⋙ G` preserves finite products and `G` reflects finite products, then `F` preserves
finite products.
-/
def preservesFiniteProductsOfReflectsOfPreserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts (F ⋙ G)] [ReflectsFiniteProducts G] : PreservesFiniteProducts F where
  preserves _ _ := preservesLimitsOfShapeOfReflectsOfPreserves F G

noncomputable instance reflectsFiniteLimitsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteLimits C] [PreservesFiniteLimits F] :
      ReflectsFiniteLimits F where
  reflects _ _ _ := reflectsLimitsOfShapeOfReflectsIsomorphisms

noncomputable instance reflectsFiniteProductsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteProducts C] [PreservesFiniteProducts F] :
      ReflectsFiniteProducts F where
  reflects _ _ := reflectsLimitsOfShapeOfReflectsIsomorphisms

instance compReflectsFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteProducts F] [ReflectsFiniteProducts G] :
    ReflectsFiniteProducts (F ⋙ G) where
  reflects _ _ := inferInstance

noncomputable instance (F : C ⥤ D) [ReflectsFiniteLimits F] : ReflectsFiniteProducts F where
  reflects _ _ := inferInstance

/-- A functor is said to preserve finite colimits, if it preserves all colimits of
shape `J`, where `J : Type` is a finite category.
-/
class PreservesFiniteColimits (F : C ⥤ D) where
  preservesFiniteColimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
      infer_instance
#align category_theory.limits.preserves_finite_colimits CategoryTheory.Limits.PreservesFiniteColimits

attribute [instance] PreservesFiniteColimits.preservesFiniteColimits

/--
Preserving finite colimits also implies preserving colimits over finite shapes in higher
universes, though through a noncomputable instance.
-/
noncomputable instance (priority := 100) preservesColimitsOfShapeOfPreservesFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J F := by
  apply preservesColimitsOfShapeOfEquiv (FinCategory.equivAsType J)
#align category_theory.limits.preserves_colimits_of_shape_of_preserves_finite_colimits CategoryTheory.Limits.preservesColimitsOfShapeOfPreservesFiniteColimits

-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve colimits of some arbitrary size, then we preserve all finite colimits. -/
noncomputable def PreservesColimitsOfSize.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F where
  preservesFiniteColimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestColimitsOfPreservesColimits F
    exact preservesColimitsOfShapeOfEquiv (FinCategory.equivAsType J) F
#align category_theory.limits.preserves_colimits_of_size.preserves_finite_colimits CategoryTheory.Limits.PreservesColimitsOfSize.preservesFiniteColimits

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
noncomputable instance (priority := 120) PreservesColimitsOfSize0.preservesFiniteColimits
    (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F
#align preserves_colimits_of_size.zero.preserves_finite_colimits CategoryTheory.Limits.PreservesColimitsOfSize0.preservesFiniteColimits

-- An alternative specialization of the dangerous instance for small colimits.
noncomputable instance (priority := 120) PreservesColimits.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimits F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F
#align category_theory.limits.preserves_colimits.preserves_finite_colimits CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits

/-- We can always derive `PreservesFiniteColimits C`
by showing that we are preserving colimits at an arbitrary universe. -/
def preservesFiniteColimitsOfPreservesFiniteColimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesColimitsOfShape J F) :
    PreservesFiniteColimits F where
      preservesFiniteColimits J (_ : SmallCategory J) _ := by
        letI : Category (ULiftHom (ULift J)) := ULiftHom.category
        haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesColimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm F
#align category_theory.limits.preserves_finite_colimits_of_preserves_finite_colimits_of_size CategoryTheory.Limits.preservesFiniteColimitsOfPreservesFiniteColimitsOfSize

/-- The composition of two right exact functors is right exact. -/
def compPreservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
    [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩
#align category_theory.limits.comp_preserves_finite_colimits CategoryTheory.Limits.compPreservesFiniteColimits

/- Porting note: adding this class because quantified classes don't behave well
[#2764](https://github.com/leanprover-community/mathlib4/pull/2764) -/
/-- A functor `F` preserves finite products if it preserves all from `Discrete J`
for `Fintype J` -/
class PreservesFiniteCoproducts (F : C ⥤ D) where
  preserves : ∀ (J : Type) [Fintype J], PreservesColimitsOfShape (Discrete J) F

attribute [instance] PreservesFiniteCoproducts.preserves

instance compPreservesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts F] [PreservesFiniteCoproducts G] :
    PreservesFiniteCoproducts (F ⋙ G) where
  preserves _ _ := inferInstance

noncomputable instance (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteCoproducts F where
  preserves _ _ := inferInstance

/--
A functor is said to reflect finite colimits, if it reflects all colimits of shape `J`,
where `J : Type` is a finite category.
-/
class ReflectsFiniteColimits (F : C ⥤ D) where
  reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsColimitsOfShape J F := by
    infer_instance

attribute [instance] ReflectsFiniteColimits.reflects

-- This is a dangerous instance as it has unbound universe variables.
/-- If we reflect colimits of some arbitrary size, then we reflect all finite colimits. -/
noncomputable def ReflectsColimitsOfSize.reflectsFiniteColimits
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w₂} F] : ReflectsFiniteColimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestColimitsOfReflectsColimits F
    exact reflectsColimitsOfShapeOfEquiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
noncomputable instance (priority := 120) (F : C ⥤ D) [ReflectsColimitsOfSize.{0, 0} F] :
    ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

-- An alternative specialization of the dangerous instance for small colimits.
noncomputable instance (priority := 120) (F : C ⥤ D)
    [ReflectsColimits F] : ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

/- Similarly to preserving finite coproducts, quantified classes don't behave well. -/
/--
A functor `F` preserves finite coproducts if it reflects colimits of shape `Discrete J` for
finite `J`
-/
class ReflectsFiniteCoproducts (F : C ⥤ D) where
  reflects : ∀ (J : Type) [Fintype J], ReflectsColimitsOfShape (Discrete J) F

attribute [instance] ReflectsFiniteCoproducts.reflects

/--
If `F ⋙ G` preserves finite colimits and `G` reflects finite colimits, then `F` preserves finite
colimits.
-/
def preservesFiniteColimitsOfReflectsOfPreserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteColimits (F ⋙ G)] [ReflectsFiniteColimits G] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShapeOfReflectsOfPreserves F G

/--
If `F ⋙ G` preserves finite coproducts and `G` reflects finite coproducts, then `F` preserves
finite coproducts.
-/
def preservesFiniteCoproductsOfReflectsOfPreserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts (F ⋙ G)] [ReflectsFiniteCoproducts G] :
    PreservesFiniteCoproducts F where
  preserves _ _ := preservesColimitsOfShapeOfReflectsOfPreserves F G

noncomputable instance reflectsFiniteColimitsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteColimits C] [PreservesFiniteColimits F] :
      ReflectsFiniteColimits F where
  reflects _ _ _ := reflectsColimitsOfShapeOfReflectsIsomorphisms

noncomputable instance reflectsFiniteCoproductsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteCoproducts C] [PreservesFiniteCoproducts F] :
      ReflectsFiniteCoproducts F where
  reflects _ _ := reflectsColimitsOfShapeOfReflectsIsomorphisms

instance compReflectsFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteCoproducts F] [ReflectsFiniteCoproducts G] :
    ReflectsFiniteCoproducts (F ⋙ G) where
  reflects _ _ := inferInstance

noncomputable instance (F : C ⥤ D) [ReflectsFiniteColimits F] : ReflectsFiniteCoproducts F where
  reflects _ _ := inferInstance

end CategoryTheory.Limits
