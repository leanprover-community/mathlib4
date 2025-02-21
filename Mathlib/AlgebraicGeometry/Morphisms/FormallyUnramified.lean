/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.RingHom.Unramified

/-!
# Formally unramified morphisms

A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

We show that these properties are local, and are stable under compositions and base change.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified. -/
@[mk_iff]
class FormallyUnramified (f : X ⟶ Y) : Prop where
  formallyUnramified_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).hom.FormallyUnramified

namespace FormallyUnramified

instance : HasRingHomProperty @FormallyUnramified RingHom.FormallyUnramified where
  isLocal_ringHomProperty := RingHom.FormallyUnramified.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [formallyUnramified_iff, affineLocally_iff_affineOpens_le]

instance : MorphismProperty.IsStableUnderComposition @FormallyUnramified :=
  HasRingHomProperty.stableUnderComposition RingHom.FormallyUnramified.stableUnderComposition

/-- `f : X ⟶ S` is formally unramified if `X ⟶ X ×ₛ X` is an open immersion.
In particular, monomorphisms (e.g. immersions) are formally unramified.
The converse is true if `f` is locally of finite type. -/
instance (priority := 900) [IsOpenImmersion (pullback.diagonal f)] : FormallyUnramified f := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (pullback.snd f (Y.affineCover.map i))) :=
      MorphismProperty.pullback_snd (P := .diagonal @IsOpenImmersion) _ _ ‹_›
    exact this (pullback.snd _ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · rw [IsLocalAtSource.iff_of_openCover (P := @FormallyUnramified) X.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (X.affineCover.map i ≫ f)) :=
      MorphismProperty.comp_mem (.diagonal @IsOpenImmersion) _ _
        (inferInstanceAs (IsOpenImmersion _)) ‹_›
    exact this (_ ≫ _) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  algebraize [φ.hom]
  let F := (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
  have hF : Function.Surjective F := fun x ↦ ⟨.mk _ _ _ x 1, by simp [F]⟩
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom F)) := by
    rwa [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _
      (pullbackSpecIso R S S).inv, ← AlgebraicGeometry.diagonal_Spec_map R S]
  obtain ⟨e, he, he'⟩ := (isOpenImmersion_SpecMap_iff_of_surjective _ hF).mp this
  refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton.mp (he'.le hx)
  refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
  rw [pow_two, Subtype.coe_mk, ← he, mul_assoc]
  exact Ideal.mul_mem_mul (he'.ge (Ideal.mem_span_singleton_self e)) hx

theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallyUnramified (f ≫ g)] : FormallyUnramified f :=
  HasRingHomProperty.of_comp (fun {R S T _ _ _} f g H ↦ by
    algebraize [f, g, g.comp f]
    exact Algebra.FormallyUnramified.of_comp R S T) ‹_›

instance : MorphismProperty.IsMultiplicative @FormallyUnramified where
  id_mem _ := inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @FormallyUnramified :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.FormallyUnramified.isStableUnderBaseChange

end FormallyUnramified

end AlgebraicGeometry
