/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

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
universe u w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {J : Type w} [SmallCategory J] {K : J ⥤ C}

/-- A functor is said to preserve finite limits, if it preserves all limits of shape `J`,
where `J : Type` is a finite category.
-/
class PreservesFiniteLimits (F : C ⥤ D) : Prop where
  preservesFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by infer_instance

attribute [instance] PreservesFiniteLimits.preservesFiniteLimits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
instance (priority := 100) preservesLimitsOfShapeOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J F := by
  apply preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J)

-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve limits of some arbitrary size, then we preserve all finite limits. -/
lemma PreservesLimitsOfSize.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F where
  preservesFiniteLimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestLimits_of_preservesLimits F
    exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for limits indexed in Type 0.
instance (priority := 120) PreservesLimitsOfSize0.preservesFiniteLimits
    (F : C ⥤ D) [PreservesLimitsOfSize.{0, 0} F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F

-- An alternative specialization of the dangerous instance for small limits.
instance (priority := 120) PreservesLimits.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimits F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F

attribute [local instance] uliftCategory in
/-- We can always derive `PreservesFiniteLimits C` by showing that we are preserving limits at an
arbitrary universe. -/
lemma preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesLimitsOfShape J F) :
    PreservesFiniteLimits F where
      preservesFiniteLimits J (_ : SmallCategory J) _ := by
        haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/-- The composition of two left exact functors is left exact. -/
lemma comp_preservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Transfer preservation of finite limits along a natural isomorphism in the functor. -/
lemma preservesFiniteLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] :
    PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_natIso h

/-- A functor `F` preserves finite products if it preserves all from `Discrete J` for `Finite J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance. -/
class PreservesFiniteProducts (F : C ⥤ D) : Prop where
  preserves : ∀ n, PreservesLimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteProducts F] : PreservesLimitsOfShape (Discrete J) F := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := PreservesFiniteProducts.preserves (F := F) n
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

instance comp_preservesFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts F] [PreservesFiniteProducts G] :
    PreservesFiniteProducts (F ⋙ G) where
  preserves _ := inferInstance

instance (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteProducts F where
  preserves _ := inferInstance

/--
A functor is said to reflect finite limits, if it reflects all limits of shape `J`,
where `J : Type` is a finite category.
-/
class ReflectsFiniteLimits (F : C ⥤ D) : Prop where
  reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F := by
    infer_instance

attribute [instance] ReflectsFiniteLimits.reflects

/- Similarly to preserving finite products, quantified classes don't behave well. -/
/--
A functor `F` preserves finite products if it reflects limits of shape `Discrete J` for finite `J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
class ReflectsFiniteProducts (F : C ⥤ D) : Prop where
  reflects : ∀ n, ReflectsLimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) [ReflectsFiniteProducts F] (J : Type u) [Finite J] :
    ReflectsLimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := ReflectsFiniteProducts.reflects (F := F) n
  reflectsLimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

-- This is a dangerous instance as it has unbound universe variables.
/-- If we reflect limits of some arbitrary size, then we reflect all finite limits. -/
lemma ReflectsLimitsOfSize.reflectsFiniteLimits
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w₂} F] : ReflectsFiniteLimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestLimits_of_reflectsLimits F
    exact reflectsLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
instance (priority := 120) (F : C ⥤ D) [ReflectsLimitsOfSize.{0, 0} F] :
    ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

-- An alternative specialization of the dangerous instance for small colimits.
instance (priority := 120) (F : C ⥤ D)
    [ReflectsLimits F] : ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

/--
If `F ⋙ G` preserves finite limits and `G` reflects finite limits, then `F` preserves
finite limits.
-/
lemma preservesFiniteLimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_reflects_of_preserves F G

/--
If `F ⋙ G` preserves finite products and `G` reflects finite products, then `F` preserves
finite products.
-/
lemma preservesFiniteProducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts (F ⋙ G)] [ReflectsFiniteProducts G] : PreservesFiniteProducts F where
  preserves _ := preservesLimitsOfShape_of_reflects_of_preserves F G

instance reflectsFiniteLimits_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteLimits C] [PreservesFiniteLimits F] :
      ReflectsFiniteLimits F where
  reflects _ _ _ := reflectsLimitsOfShape_of_reflectsIsomorphisms

instance reflectsFiniteProducts_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteProducts C] [PreservesFiniteProducts F] :
      ReflectsFiniteProducts F where
  reflects _ := reflectsLimitsOfShape_of_reflectsIsomorphisms

instance comp_reflectsFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteProducts F] [ReflectsFiniteProducts G] :
    ReflectsFiniteProducts (F ⋙ G) where
  reflects _ := inferInstance

instance (F : C ⥤ D) [ReflectsFiniteLimits F] : ReflectsFiniteProducts F where
  reflects _ := inferInstance

/-- A functor is said to preserve finite colimits, if it preserves all colimits of
shape `J`, where `J : Type` is a finite category.
-/
class PreservesFiniteColimits (F : C ⥤ D) : Prop where
  preservesFiniteColimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
      infer_instance

attribute [instance] PreservesFiniteColimits.preservesFiniteColimits

/--
Preserving finite colimits also implies preserving colimits over finite shapes in higher
universes.
-/
instance (priority := 100) preservesColimitsOfShapeOfPreservesFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J F := by
  apply preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J)

-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve colimits of some arbitrary size, then we preserve all finite colimits. -/
lemma PreservesColimitsOfSize.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F where
  preservesFiniteColimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestColimits_of_preservesColimits F
    exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
instance (priority := 120) PreservesColimitsOfSize0.preservesFiniteColimits
    (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F

-- An alternative specialization of the dangerous instance for small colimits.
instance (priority := 120) PreservesColimits.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimits F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F

attribute [local instance] uliftCategory in
/-- We can always derive `PreservesFiniteColimits C`
by showing that we are preserving colimits at an arbitrary universe. -/
lemma preservesFiniteColimits_of_preservesFiniteColimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesColimitsOfShape J F) :
    PreservesFiniteColimits F where
      preservesFiniteColimits J (_ : SmallCategory J) _ := by
        letI : Category (ULiftHom (ULift J)) := ULiftHom.category
        haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/-- The composition of two right exact functors is right exact. -/
lemma comp_preservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
    [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Transfer preservation of finite colimits along a natural isomorphism in the functor. -/
lemma preservesFiniteColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] :
    PreservesFiniteColimits G where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_natIso h

/-- A functor `F` preserves finite products if it preserves all from `Discrete J` for `Fintype J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance. -/
class PreservesFiniteCoproducts (F : C ⥤ D) : Prop where
  /-- preservation of colimits indexed by `Discrete (Fin n)`. -/
  preserves : ∀ n, PreservesColimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteCoproducts F] : PreservesColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := PreservesFiniteCoproducts.preserves (F := F) n
  preservesColimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

instance comp_preservesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts F] [PreservesFiniteCoproducts G] :
    PreservesFiniteCoproducts (F ⋙ G) where
  preserves _ := inferInstance

instance (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteCoproducts F where
  preserves _ := inferInstance

/--
A functor is said to reflect finite colimits, if it reflects all colimits of shape `J`,
where `J : Type` is a finite category.
-/
class ReflectsFiniteColimits (F : C ⥤ D) : Prop where
  [reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsColimitsOfShape J F]

attribute [instance] ReflectsFiniteColimits.reflects

-- This is a dangerous instance as it has unbound universe variables.
/-- If we reflect colimits of some arbitrary size, then we reflect all finite colimits. -/
lemma ReflectsColimitsOfSize.reflectsFiniteColimits
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w₂} F] : ReflectsFiniteColimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestColimits_of_reflectsColimits F
    exact reflectsColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
instance (priority := 120) (F : C ⥤ D) [ReflectsColimitsOfSize.{0, 0} F] :
    ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

-- An alternative specialization of the dangerous instance for small colimits.
instance (priority := 120) (F : C ⥤ D)
    [ReflectsColimits F] : ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

/- Similarly to preserving finite coproducts, quantified classes don't behave well. -/
/--
A functor `F` preserves finite coproducts if it reflects colimits of shape `Discrete J`
for finite `J`.

We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
class ReflectsFiniteCoproducts (F : C ⥤ D) : Prop where
  reflects : ∀ n, ReflectsColimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) [ReflectsFiniteCoproducts F] (J : Type u) [Finite J] :
    ReflectsColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := ReflectsFiniteCoproducts.reflects (F := F) n
  reflectsColimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

/--
If `F ⋙ G` preserves finite colimits and `G` reflects finite colimits, then `F` preserves finite
colimits.
-/
lemma preservesFiniteColimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteColimits (F ⋙ G)] [ReflectsFiniteColimits G] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_reflects_of_preserves F G

/--
If `F ⋙ G` preserves finite coproducts and `G` reflects finite coproducts, then `F` preserves
finite coproducts.
-/
lemma preservesFiniteCoproducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts (F ⋙ G)] [ReflectsFiniteCoproducts G] :
    PreservesFiniteCoproducts F where
  preserves _ := preservesColimitsOfShape_of_reflects_of_preserves F G

instance reflectsFiniteColimitsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteColimits C] [PreservesFiniteColimits F] :
      ReflectsFiniteColimits F where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

instance reflectsFiniteCoproductsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteCoproducts C] [PreservesFiniteCoproducts F] :
      ReflectsFiniteCoproducts F where
  reflects _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

instance comp_reflectsFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteCoproducts F] [ReflectsFiniteCoproducts G] :
    ReflectsFiniteCoproducts (F ⋙ G) where
  reflects _ := inferInstance

instance (F : C ⥤ D) [ReflectsFiniteColimits F] : ReflectsFiniteCoproducts F where
  reflects _ := inferInstance

end CategoryTheory.Limits
