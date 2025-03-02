/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Transferring "abelian-ness" across a functor

If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

A particular example is the transfer of `Abelian` instances from a category `C` to `ShrinkHoms C`;
see `ShrinkHoms.abelian`. In this case, we also transfer the `Preadditive` structure.

See <https://stacks.math.columbia.edu/tag/03A3>

## Notes
The hypotheses, following the statement from the Stacks project,
may appear surprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `Reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/


noncomputable section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D)
variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]

/-- No point making this an instance, as it requires `i`. -/
theorem hasKernels [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C) : HasKernels C :=
  { has_limit := fun f => by
      have := NatIso.naturality_1 i f
      simp? at this says
        simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, Functor.id_map] at this
      rw [← this]
      haveI : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }

/-- No point making this an instance, as it requires `i` and `adj`. -/
theorem hasCokernels (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F) : HasCokernels C :=
  { has_colimit := fun f => by
      have : PreservesColimits G := adj.leftAdjoint_preservesColimits
      have := NatIso.naturality_1 i f
      simp? at this says
        simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, Functor.id_map] at this
      rw [← this]
      haveI : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }

end AbelianOfAdjunction

open AbelianOfAdjunction

/-- If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (with `G` preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian. -/
@[stacks 03A3]
def abelianOfAdjunction {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
    (adj : G ⊣ F) : Abelian C := by
  haveI := hasKernels F G i
  haveI := hasCokernels F G i adj
  have : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    let arrowIso : Arrow.mk (G.map (F.map f)) ≅ Arrow.mk f :=
      ((Functor.mapArrowFunctor _ _).mapIso i).app (Arrow.mk f)
    have : PreservesColimits G := adj.leftAdjoint_preservesColimits
    let iso : Arrow.mk (G.map (Abelian.coimageImageComparison (F.map f))) ≅
        Arrow.mk (Abelian.coimageImageComparison f) :=
      Abelian.PreservesCoimageImageComparison.iso G (F.map f) ≪≫
        Abelian.coimageImageComparisonFunctor.mapIso arrowIso
    rw [Arrow.isIso_iff_isIso_of_isIso iso.inv]
    infer_instance
  apply Abelian.ofCoimageImageComparisonIsIso

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    [F.IsEquivalence] : Abelian C :=
  abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction

namespace ShrinkHoms

universe w

variable {C : Type*} [Category C] [LocallySmall.{w} C]

section Preadditive

variable [Preadditive C]

variable (C)

instance preadditive : Preadditive.{w} (ShrinkHoms C) :=
  .ofFullyFaithful (equivalence C).fullyFaithfulInverse

instance : (inverse C).Additive :=
  (equivalence C).symm.fullyFaithfulFunctor.additive_ofFullyFaithful

instance : (functor C).Additive :=
  (equivalence C).symm.additive_inverse_of_FullyFaithful

instance hasLimitsOfShape (J : Type*) [Category J]
    [HasLimitsOfShape J C] : HasLimitsOfShape.{_, _, w} J (ShrinkHoms C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (inverse C)

instance hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteLimits.{w} (ShrinkHoms C) := ⟨fun _ => inferInstance⟩

end Preadditive

variable (C) in
noncomputable instance abelian [Abelian C] :
    Abelian.{w} (ShrinkHoms C) := abelianOfEquivalence (inverse C)

end ShrinkHoms


namespace AsSmall

universe w v u

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

variable (C)

instance preadditive : Preadditive (AsSmall.{w} C) :=
  .ofFullyFaithful equiv.fullyFaithfulInverse

instance : (down (C := C)).Additive :=
  equiv.symm.fullyFaithfulFunctor.additive_ofFullyFaithful

instance : (up (C := C)).Additive :=
  equiv.symm.additive_inverse_of_FullyFaithful

instance hasLimitsOfShape (J : Type*) [Category J]
    [HasLimitsOfShape J C] : HasLimitsOfShape.{_, _, max u v w} J (AsSmall.{w} C) :=
  Adjunction.hasLimitsOfShape_of_equivalence equiv.inverse

instance hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteLimits (AsSmall.{w} C) := ⟨fun _ => inferInstance⟩

end Preadditive

variable (C) in
noncomputable instance abelian [Abelian C] :
    Abelian (AsSmall.{w} C) := abelianOfEquivalence equiv.inverse

end AsSmall

end CategoryTheory
