/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Morphisms of finite presentation

A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation.

A morphism of schemes is of finite presentation if it is both locally of finite presentation and
quasi-compact.

We show that these properties are local, and are stable under compositions.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation.
-/
@[mk_iff]
class IsLocallyOfFinitePresentation (f : X ⟶ Y) : Prop where
  finitePresentation_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ (Opens.map f.1.base).obj U.1),
      (Scheme.Hom.appLe f e).FinitePresentation

namespace IsLocallyOfFinitePresentation

lemma finitePresentation_of_affine_subset' [IsLocallyOfFinitePresentation f]
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ (Opens.map f.1.base).obj U.1) :
    (Scheme.Hom.appLe f e).FinitePresentation :=
  ‹IsLocallyOfFinitePresentation f›.finitePresentation_of_affine_subset U V e

lemma isLocallyOfFinitePresentation_eq :
    @IsLocallyOfFinitePresentation = affineLocally @RingHom.FinitePresentation := by
  ext X Y f
  rw [isLocallyOfFinitePresentation_iff, affineLocally_iff_affineOpens_le]
  exact RingHom.finitePresentation_respectsIso

instance (priority := 900) of_isOpenImmersion [IsOpenImmersion f] :
    IsLocallyOfFinitePresentation f :=
  isLocallyOfFinitePresentation_eq.symm ▸
    RingHom.finitePresentation_is_local.affineLocally_of_isOpenImmersion f

instance (priority := 900) [IsLocallyOfFinitePresentation f] : LocallyOfFiniteType f :=
  ⟨fun U V e ↦
    RingHom.FiniteType.of_finitePresentation (finitePresentation_of_affine_subset' f U V e)⟩

instance stableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsLocallyOfFinitePresentation :=
  isLocallyOfFinitePresentation_eq.symm ▸
    RingHom.finitePresentation_is_local.affineLocally_isStableUnderComposition

instance comp {Z : Scheme} (g : Y ⟶ Z)
    [hf : IsLocallyOfFinitePresentation f] [hg : IsLocallyOfFinitePresentation g] :
    IsLocallyOfFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

lemma affine_openCover_iff
    (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} ((𝒰.pullbackCover f).obj i)) [∀ i j, IsAffine ((𝒰' i).obj j)] :
    IsLocallyOfFinitePresentation f ↔
      ∀ i j, (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op).FinitePresentation :=
  isLocallyOfFinitePresentation_eq.symm ▸
    RingHom.finitePresentation_is_local.affine_openCover_iff f 𝒰 𝒰'

lemma source_openCover_iff
    (𝒰 : Scheme.OpenCover.{u} X) : IsLocallyOfFinitePresentation f ↔
      ∀ i, IsLocallyOfFinitePresentation (𝒰.map i ≫ f) :=
  isLocallyOfFinitePresentation_eq.symm ▸
    RingHom.finitePresentation_is_local.source_openCover_iff f 𝒰

lemma openCover_iff (𝒰 : Scheme.OpenCover.{u} Y) :
    IsLocallyOfFinitePresentation f ↔
      ∀ i, IsLocallyOfFinitePresentation (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  isLocallyOfFinitePresentation_eq.symm ▸
    RingHom.finitePresentation_is_local.is_local_affineLocally.openCover_iff f 𝒰

lemma respectsIso :
    MorphismProperty.RespectsIso @IsLocallyOfFinitePresentation :=
  isLocallyOfFinitePresentation_eq.symm ▸
    targetAffineLocally_respectsIso
      (sourceAffineLocally_respectsIso RingHom.finitePresentation_respectsIso)

end IsLocallyOfFinitePresentation

end AlgebraicGeometry
