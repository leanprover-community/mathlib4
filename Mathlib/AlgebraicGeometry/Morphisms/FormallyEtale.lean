/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Formally etale morphisms

A morphism of schemes `f : X ⟶ Y` is formally etale if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally etale.

We show that these properties are local, and are stable under compositions and base change.

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

open AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is formally etale if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally etale. -/
@[mk_iff]
class FormallyEtale (f : X ⟶ Y) : Prop where
  formallyEtale_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FormallyEtale

alias Scheme.Hom.formallyEtale_appLE := FormallyEtale.formallyEtale_appLE

namespace FormallyEtale

instance : HasRingHomProperty @FormallyEtale RingHom.FormallyEtale where
  isLocal_ringHomProperty := RingHom.FormallyEtale.propertyIsLocal
  eq_affineLocally' := by ext X Y f; rw [formallyEtale_iff, affineLocally_iff_forall_isAffineOpen]

instance : MorphismProperty.IsStableUnderComposition @FormallyEtale :=
  HasRingHomProperty.stableUnderComposition RingHom.FormallyEtale.stableUnderComposition

instance (priority := 900) [IsOpenImmersion f] : FormallyEtale f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.FormallyEtale.holdsForLocalization.holdsForLocalizationAway.containsIdentities

theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallyEtale (f ≫ g)] [FormallyUnramified g] : FormallyEtale f :=
  HasRingHomProperty.of_comp' (fun {R S T _ _ _} f g H H' ↦ by
    algebraize [f, g, g.comp f]
    exact Algebra.FormallyEtale.of_restrictScalars (R := R)) ‹_› ‹FormallyUnramified g›

instance : MorphismProperty.IsMultiplicative @FormallyEtale where
  id_mem _ := inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @FormallyEtale :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.FormallyEtale.isStableUnderBaseChange

instance (priority := low) [FormallyEtale f] : FormallyUnramified f := by
  rw [HasRingHomProperty.eq_affineLocally @FormallyEtale] at ‹_›
  rw [HasRingHomProperty.eq_affineLocally @FormallyUnramified]
  exact affineLocally_le RingHom.FormallyEtale.formallyUnramified f ‹_›

end FormallyEtale

end AlgebraicGeometry
