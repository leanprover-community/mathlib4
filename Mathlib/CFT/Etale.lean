/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CFT.Smooth
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions and base change.

-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class Etale (f : X ⟶ Y) : Prop where
  etale_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).hom.Etale

instance : HasRingHomProperty @Etale RingHom.Etale where
  isLocal_ringHomProperty := RingHom.Etale.propertyIsLocal
  eq_affineLocally' := by ext X Y f; rw [etale_iff, affineLocally_iff_affineOpens_le]

instance (priority := 900) [IsOpenImmersion f] :  Etale f :=
  HasRingHomProperty.of_isOpenImmersion fun _ _ ↦ .of_bijective Function.bijective_id

instance (priority := 900) [Etale f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally @Etale] at ‹Etale f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
  refine affineLocally_le (fun hf ↦ ?_) f ‹_›
  exact hf.2

instance (priority := 900) [Etale f] : Smooth f := by
  rw [HasRingHomProperty.eq_affineLocally @Etale] at ‹Etale f›
  rw [HasRingHomProperty.eq_affineLocally @Smooth]
  exact affineLocally_le (fun h ↦ ((RingHom.etale_iff_formallyUnramified_and_smooth _).mp h).2)
    f ‹_›

instance : MorphismProperty.IsStableUnderComposition @Etale :=
  HasRingHomProperty.stableUnderComposition RingHom.Etale.stableUnderComposition

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] : Etale (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹_› ‹_›

instance : MorphismProperty.IsMultiplicative @Etale where
  id_mem _ := inferInstance

open scoped TensorProduct in
instance : MorphismProperty.IsStableUnderBaseChange @Etale :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Etale.isStableUnderBaseChange

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale g] :
    Etale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale f] :
    Etale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [Etale f] : Etale (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Etale f] :
    Etale (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

end AlgebraicGeometry
