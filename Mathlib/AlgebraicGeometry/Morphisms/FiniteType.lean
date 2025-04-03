/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteType_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).FiniteType

theorem locallyOfFiniteType_eq : @LocallyOfFiniteType = affineLocally @RingHom.FiniteType := by
  ext X Y f
  rw [locallyOfFiniteType_iff, affineLocally_iff_affineOpens_le]
  exact RingHom.finiteType_respectsIso

instance (priority := 900) locallyOfFiniteType_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.affineLocally_of_isOpenImmersion f

instance locallyOfFiniteType_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @LocallyOfFiniteType :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.affineLocally_isStableUnderComposition

instance locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

theorem locallyOfFiniteType_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f := by
  revert hf
  rw [locallyOfFiniteType_eq]
  apply RingHom.finiteType_is_local.affineLocally_of_comp
  introv H
  exact RingHom.FiniteType.of_comp_finiteType H

theorem LocallyOfFiniteType.affine_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} ((𝒰.pullbackCover f).obj i)) [∀ i j, IsAffine ((𝒰' i).obj j)] :
    LocallyOfFiniteType f ↔
    ∀ i j, (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd _ _).op).FiniteType :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.affine_openCover_iff f 𝒰 𝒰'

theorem LocallyOfFiniteType.source_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.OpenCover.{u} X) : LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (𝒰.map i ≫ f) :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.source_openCover_iff f 𝒰

instance locallyOfFiniteType_isLocalAtTarget : IsLocalAtTarget @LocallyOfFiniteType := by
  have := RingHom.finiteType_is_local.hasAffinePropertyAffineLocally
  rw [← locallyOfFiniteType_eq] at this
  infer_instance

end AlgebraicGeometry
