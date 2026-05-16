/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Flat

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
class Smooth (f : X ⟶ Y) : Prop where
  smooth_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).hom.Smooth

instance : HasRingHomProperty @Smooth RingHom.Smooth where
  isLocal_ringHomProperty := RingHom.Smooth.propertyIsLocal
  eq_affineLocally' := by ext X Y f; rw [smooth_iff, affineLocally_iff_affineOpens_le]

instance {R : Type*} [CommRing R] : Algebra.Smooth R R where -- move me

instance (priority := 900) [IsOpenImmersion f] :  Smooth f :=
  HasRingHomProperty.of_isOpenImmersion fun R _ ↦
    RingHom.smooth_algebraMap.mpr (inferInstanceAs (Algebra.Smooth R R))

instance (priority := 900) [Smooth f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally @Smooth] at ‹Smooth f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
  refine affineLocally_le (fun hf ↦ ?_) f ‹_›
  exact hf.2

lemma _root_.RingHom.Smooth.flat {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (H : f.Smooth) : f.Flat := by
  algebraize [f]; exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance (priority := 900) [Smooth f] : Flat f := by
  rw [HasRingHomProperty.eq_affineLocally @Smooth] at ‹Smooth f›
  rw [HasRingHomProperty.eq_affineLocally @Flat]
  exact affineLocally_le RingHom.Smooth.flat f ‹_›

instance : MorphismProperty.IsStableUnderComposition @Smooth :=
  HasRingHomProperty.stableUnderComposition fun _ _ _ _ _ _ _ _ ↦ RingHom.Smooth.comp

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Smooth g] : Smooth (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹_› ‹_›

instance : MorphismProperty.IsMultiplicative @Smooth where
  id_mem _ := inferInstance

open scoped TensorProduct in
instance smooth_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @Smooth :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Smooth.isStableUnderBaseChange

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth g] :
    Smooth (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth f] :
    Smooth (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [Smooth f] : Smooth (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Smooth f] :
    Smooth (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

end AlgebraicGeometry
