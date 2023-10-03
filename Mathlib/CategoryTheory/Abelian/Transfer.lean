/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Injective

#align_import category_theory.abelian.transfer from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Transferring properties across a functor

## abelian-ness
If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>

### Notes
The hypotheses, following the statement from the Stacks project,
may appear surprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `Reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)

## enough-injectives
If `C, D` are abelian categories with adjoint functors `L ⊣ R` where `L` is a faithful exact
functor from `C` to `D`, then `D` having enough injectives implies that `C` has enough injectives.

### Notes

In `EnoughInjectives.of_equivalence`, if we require `C` and `D` to have morphisms at the same
universe level, then it suffices to assume only `abelian C`, since `abelian D` would be implied by
`abelian_of_adjunction`. Maybe "transferring abelian-ness" should have a more relaxed universe
level?

-/


noncomputable section

namespace CategoryTheory

open Limits

universe v v₁ v₂ u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v} C] [Preadditive C]

variable {D : Type u₂} [Category.{v} D] [Abelian D]

variable (F : C ⥤ D)

variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]

variable (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)

/-- No point making this an instance, as it requires `i`. -/
theorem hasKernels [PreservesFiniteLimits G] : HasKernels C :=
  { has_limit := fun f => by
      have := NatIso.naturality_1 i f
      simp at this
      rw [← this]
      haveI : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }
#align category_theory.abelian_of_adjunction.has_kernels CategoryTheory.AbelianOfAdjunction.hasKernels

/-- No point making this an instance, as it requires `i` and `adj`. -/
theorem hasCokernels : HasCokernels C :=
  { has_colimit := fun f => by
      have : PreservesColimits G := adj.leftAdjointPreservesColimits
      have := NatIso.naturality_1 i f
      simp at this
      rw [← this]
      haveI : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }
#align category_theory.abelian_of_adjunction.has_cokernels CategoryTheory.AbelianOfAdjunction.hasCokernels

variable [Limits.HasCokernels C]

/-- Auxiliary construction for `coimageIsoImage` -/
def cokernelIso {X Y : C} (f : X ⟶ Y) : G.obj (cokernel (F.map f)) ≅ cokernel f := by
  -- We have to write an explicit `PreservesColimits` type here,
  -- as `leftAdjointPreservesColimits` has universe variables.
  have : PreservesColimits G := adj.leftAdjointPreservesColimits
  -- porting note: the next `have` has been added, otherwise some instance were not found
  have : ∀ (X' Y' : C) (f' : X' ⟶ Y'), HasCokernel f' := inferInstance
  calc
    G.obj (cokernel (F.map f)) ≅ cokernel (G.map (F.map f)) :=
      (asIso (cokernelComparison _ G)).symm
    _ ≅ cokernel (i.hom.app X ≫ f ≫ i.inv.app Y) := cokernelIsoOfEq (NatIso.naturality_2 i f).symm
    _ ≅ cokernel (f ≫ i.inv.app Y) := cokernelEpiComp (i.hom.app X) (f ≫ i.inv.app Y)
    _ ≅ cokernel f := cokernelCompIsIso f (i.inv.app Y)
#align category_theory.abelian_of_adjunction.cokernel_iso CategoryTheory.AbelianOfAdjunction.cokernelIso

variable [Limits.HasKernels C] [PreservesFiniteLimits G]

/-- Auxiliary construction for `coimageIsoImage` -/
def coimageIsoImageAux {X Y : C} (f : X ⟶ Y) :
    kernel (G.map (cokernel.π (F.map f))) ≅ kernel (cokernel.π f) := by
  have : PreservesColimits G := adj.leftAdjointPreservesColimits
  -- porting note: the next `have` has been added, otherwise some instance were not found
  have : ∀ (X' Y' : C) (f' : X' ⟶ Y'), HasCokernel f' := inferInstance
  calc
    kernel (G.map (cokernel.π (F.map f))) ≅
        kernel (cokernel.π (G.map (F.map f)) ≫ cokernelComparison (F.map f) G) :=
      kernelIsoOfEq (π_comp_cokernelComparison _ _).symm
    _ ≅ kernel (cokernel.π (G.map (F.map f))) := (kernelCompMono _ _)
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernelIsoOfEq _).hom) :=
      (kernelIsoOfEq (π_comp_cokernelIsoOfEq_hom (NatIso.naturality_2 i f)).symm)
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _)) := (kernelCompMono _ _)
    _ ≅ kernel (cokernel.π (f ≫ i.inv.app Y) ≫ (cokernelEpiComp (i.hom.app X) _).inv) :=
      (kernelIsoOfEq (by simp only [cokernel.π_desc, cokernelEpiComp_inv]))
    _ ≅ kernel (cokernel.π (f ≫ _)) := (kernelCompMono _ _)
    _ ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernelCompIsIso f (i.inv.app Y)).inv) :=
      (kernelIsoOfEq
        (by simp only [cokernel.π_desc, cokernelCompIsIso_inv, Iso.hom_inv_id_app_assoc,
          NatIso.inv_inv_app]))
    _ ≅ kernel (cokernel.π f ≫ _) := (kernelIsIsoComp _ _)
    _ ≅ kernel (cokernel.π f) := kernelCompMono _ _
#align category_theory.abelian_of_adjunction.coimage_iso_image_aux CategoryTheory.AbelianOfAdjunction.coimageIsoImageAux

variable [Functor.PreservesZeroMorphisms F]

/-- Auxiliary definition: the abelian coimage and abelian image agree.
We still need to check that this agrees with the canonical morphism.
-/
def coimageIsoImage {X Y : C} (f : X ⟶ Y) : Abelian.coimage f ≅ Abelian.image f := by
  have : PreservesLimits F := adj.rightAdjointPreservesLimits
  -- porting note: the next `have` has been added, otherwise some instance were not found
  haveI : ∀ (X' Y' : D) (f' : X' ⟶ Y'), HasCokernel f' := inferInstance
  calc
    Abelian.coimage f ≅ cokernel (kernel.ι f) := Iso.refl _
    _ ≅ G.obj (cokernel (F.map (kernel.ι f))) := (cokernelIso _ _ i adj _).symm
    _ ≅ G.obj (cokernel (kernelComparison f F ≫ kernel.ι (F.map f))) :=
      (G.mapIso (cokernelIsoOfEq (by simp)))
    _ ≅ G.obj (cokernel (kernel.ι (F.map f))) := (G.mapIso (cokernelEpiComp _ _))
    _ ≅ G.obj (Abelian.coimage (F.map f)) := (Iso.refl _)
    _ ≅ G.obj (Abelian.image (F.map f)) := (G.mapIso (Abelian.coimageIsoImage _))
    _ ≅ G.obj (kernel (cokernel.π (F.map f))) := (Iso.refl _)
    _ ≅ kernel (G.map (cokernel.π (F.map f))) := (PreservesKernel.iso _ _)
    _ ≅ kernel (cokernel.π f) := (coimageIsoImageAux F G i adj f)
    _ ≅ Abelian.image f := Iso.refl _
#align category_theory.abelian_of_adjunction.coimage_iso_image CategoryTheory.AbelianOfAdjunction.coimageIsoImage

-- The account of this proof in the Stacks project omits this calculation.
@[nolint unusedHavesSuffices]
theorem coimageIsoImage_hom {X Y : C} (f : X ⟶ Y) :
    (coimageIsoImage F G i adj f).hom = Abelian.coimageImageComparison f := by
  -- porting note: the next `have` have been added, otherwise some instance were not found
  have : ∀ (X' Y' : C) (f' : X' ⟶ Y'), HasCokernel f' := inferInstance
  have : ∀ (X' Y' : C) (f' : X' ⟶ Y'), HasKernel f' := inferInstance
  have : ∀ (X' Y' : D) (f' : X' ⟶ Y'), HasCokernel f' := inferInstance
  have : ∀ (X' Y' : D) (f' : X' ⟶ Y'), HasKernel f' := inferInstance
  dsimp only [coimageIsoImage, Iso.instTransIso_trans, Iso.refl, Iso.trans, Iso.symm,
    Functor.mapIso, cokernelEpiComp, cokernelIso, cokernelCompIsIso_inv,
    asIso, coimageIsoImageAux, kernelCompMono]
  simpa only [← cancel_mono (Abelian.image.ι f), ← cancel_epi (Abelian.coimage.π f),
    Category.assoc, Category.id_comp, cokernel.π_desc_assoc,
    π_comp_cokernelIsoOfEq_inv_assoc, PreservesKernel.iso_hom,
    π_comp_cokernelComparison_assoc, ← G.map_comp_assoc, kernel.lift_ι,
    Abelian.coimage_image_factorisation, lift_comp_kernelIsoOfEq_hom_assoc,
    kernelIsIsoComp_hom, kernel.lift_ι_assoc, kernelIsoOfEq_hom_comp_ι_assoc,
    kernelComparison_comp_ι_assoc, π_comp_cokernelIsoOfEq_hom_assoc,
    asIso_hom, NatIso.inv_inv_app] using NatIso.naturality_1 i f
#align category_theory.abelian_of_adjunction.coimage_iso_image_hom CategoryTheory.AbelianOfAdjunction.coimageIsoImage_hom

end AbelianOfAdjunction

open AbelianOfAdjunction

/-- If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>
-/
def abelianOfAdjunction {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
    (adj : G ⊣ F) : Abelian C := by
  haveI := hasKernels F G i
  haveI := hasCokernels F G i adj
  have : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    rw [← coimageIsoImage_hom F G i adj f]
    infer_instance
  apply Abelian.ofCoimageImageComparisonIsIso
#align category_theory.abelian_of_adjunction CategoryTheory.abelianOfAdjunction

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    [IsEquivalence F] : Abelian C :=
  abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction
#align category_theory.abelian_of_equivalence CategoryTheory.abelianOfEquivalence

namespace transfer_enough_injectives

variable {𝒜: Type u₁} {ℬ : Type u₂} [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
variable (L : 𝒜 ⥤ ℬ) (R : ℬ ⥤ 𝒜)

/--
Give a pair of functors
```
  --- L -->
𝒜          ℬ,
  <-- R ---
```
for `A : 𝒜`, pick an injective presentation `L A ⟶ J` which always exists by enough
injectives of `ℬ`. we pullback `J` across `R`.
-/
def adjointObjectOfInjectivePresentation {A : 𝒜}
    (a : InjectivePresentation <| L.obj A) :=
  R.obj <| a.J

variable {L R}
variable (adj : L ⊣ R)

/-
If `g : X → R(J)` and `f : X → Y` is mono in `𝓐`, then there is an morphism `L(Y) → J`
See the diagram below:
```
𝓐                             𝓑
A ---> R(J)                 L(A) -----> J <--------
      /                                /          |
     /                                /           |
    /  g                           by adjunction  |
   /                                /             |
  /                                /         by injectivity
X                              L(X)               |
|                               |L.map f          |
v                               v                 |
Y                              L(Y) ---------------
```
-/

/--
Let `L(A) ⟶ J` be an injective presentation.
If `g : X → R(J)` and `f : X → Y` is mono in `𝓐`, then there is an morphism `L(Y) → J`:
* Since `L` preserves finite limits, `L(f)` is mono
* If `L ⊣ R`, then `g` gives a `L(X) ⟶ J`
* we then factor `X ⟶ R(J)` into `L(f)` and `L(Y) ⟶ J`
-/
def toInjectiveObject [PreservesFiniteLimits L] {A X Y : 𝒜} (a : InjectivePresentation <| L.obj A)
    (g : X ⟶ adjointObjectOfInjectivePresentation L R a) (f : X ⟶ Y) [Mono f] :
    L.obj Y ⟶ a.J :=
  let i1 := a.injective.factors
  (i1 ((adj.homEquiv X <| a.J).symm g) (L.map f)).choose

lemma toInjectiveObject_spec [PreservesFiniteLimits L] {A X Y : 𝒜}
    (a : InjectivePresentation <| L.obj A)
    (g : X ⟶ adjointObjectOfInjectivePresentation L R a) (f : X ⟶ Y) [Mono f] :
    L.map f ≫ toInjectiveObject adj a g f =
    (adj.homEquiv X <| a.J).symm g :=
  let i1 := a.injective.factors
  (i1 ((adj.homEquiv X <| a.J).symm g) (L.map f)).choose_spec

/--
Let `L(A) ⟶ J` be an injective presentation.
If `g : X → R(J)` and `f : X → Y` is mono in `𝓐`, then there is an morphism `L(Y) → J` as in
`toInjectiveUnder`, then we obtain a map `Y ⟶ R(J)` via adjunction
-/
def adjointToInjective [PreservesFiniteLimits L] {A X Y : 𝒜}
    (a : InjectivePresentation <| L.obj A)
    (g : X ⟶ adjointObjectOfInjectivePresentation L R a) (f : X ⟶ Y) [Mono f] :
    Y ⟶ adjointObjectOfInjectivePresentation L R a :=
  adj.homEquiv _ _ <| toInjectiveObject adj a g f

lemma adjointToInjective_spec [PreservesFiniteLimits L] {A X Y : 𝒜}
    (a : InjectivePresentation <| L.obj A)
    (g : X ⟶ adjointObjectOfInjectivePresentation L R a) (f : X ⟶ Y) [Mono f] :
    f ≫ adjointToInjective adj a g f = g := by
  have := toInjectiveObject_spec adj a g f
  rw [← adj.homEquiv_apply_eq] at this
  rw [← this]
  simp only [adjointToInjective, toInjectiveObject, Adjunction.homEquiv_counit, Functor.id_obj,
    Adjunction.homEquiv_unit, Functor.comp_obj, Functor.map_comp, Adjunction.unit_naturality_assoc,
    Category.assoc, Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  generalize_proofs h1 h2
  congr 4
  ext
  rw [h1.choose_spec]

lemma injective_adjointObjectOfInjectivePresentation_of_adj [PreservesFiniteLimits L] {A : 𝒜}
    (a : InjectivePresentation <| L.obj A) :
    Injective (adjointObjectOfInjectivePresentation L R a) where
  factors _ _ _ := ⟨_, adjointToInjective_spec adj a _ _⟩

variable (L R)
/--
Let `L(A) ⟶ J` be an injective presentation of `L(A)`, then `A ⟶ R(J)` is an injective
presentation of `A`
-/
def under {A : 𝒜} (a : InjectivePresentation <| L.obj A) : 𝒜 :=
  adjointObjectOfInjectivePresentation L R a

variable {L R}
/--
Let `L(A) ⟶ J` be an injective presentation of `L(A)`, then `A ⟶ R(J)` is an injective
presentation of `A`
-/
def toUnder {A : 𝒜} (a : InjectivePresentation <| L.obj A) :
    A ⟶ under L R a := adj.homEquiv _ _ <| a.f

lemma mono_toUnder [Abelian 𝒜] [Abelian ℬ] [PreservesFiniteLimits L] [Faithful L]
    {A : 𝒜} (a : InjectivePresentation <| L.obj A) : Mono (toUnder adj a) := by
  have eq1 : L.map (toUnder adj a) ≫ (adj.counit.app _) = a.f
  ·  simp [toUnder]
  have m1 : Mono (L.map (toUnder adj a) ≫ (adj.counit.app _))
  · rw [eq1]
    exact a.mono
  have m2 : Mono (L.map (toUnder adj a))
  · exact mono_of_mono _ (adj.counit.app a.J)
  have eq2 : L.map (kernel.ι (toUnder adj a)) =
    (PreservesKernel.iso L (toUnder adj a)).hom ≫ kernel.ι (L.map (toUnder adj a))
  · simp
  have eq3 : kernel.ι (toUnder adj a) = 0
  · refine L.zero_of_map_zero _ ?_
    rw [Abelian.mono_iff_kernel_ι_eq_zero] at m2
    rw [eq2, m2, comp_zero]
  rw [Abelian.mono_iff_kernel_ι_eq_zero, eq3]

end transfer_enough_injectives

open transfer_enough_injectives in
/--
[Lemma 3.8](https://ncatlab.org/nlab/show/injective+object#preservation_of_injective_objects)
-/
lemma EnoughInjectives.of_adjunction {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [Faithful L] [PreservesFiniteLimits L]
    [EnoughInjectives D] : EnoughInjectives C where
  presentation _ :=
    ⟨⟨_, injective_adjointObjectOfInjectivePresentation_of_adj adj
      (EnoughInjectives.presentation _).some, _, mono_toUnder adj _⟩⟩

/-- An equivalence of categories transfers enough injectives. -/
lemma EnoughInjectives.of_equivalence {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (e : C ⥤ D) [IsEquivalence e] [EnoughInjectives D] : EnoughInjectives C :=
EnoughInjectives.of_adjunction (adj := e.asEquivalence.toAdjunction)

end CategoryTheory
