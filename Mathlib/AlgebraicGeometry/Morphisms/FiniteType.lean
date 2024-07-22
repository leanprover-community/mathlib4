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

We show that these properties are local, and are stable under compositions and base change.

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

instance : HasRingHomProperty @LocallyOfFiniteType RingHom.FiniteType where
  isLocal_ringHomProperty := RingHom.finiteType_is_local
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFiniteType_iff, affineLocally_iff_affineOpens_le]

instance (priority := 900) locallyOfFiniteType_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  HasRingHomProperty.of_isOpenImmersion

instance locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

theorem locallyOfFiniteType_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f :=
  HasRingHomProperty.of_comp (fun f g ↦ RingHom.FiniteType.of_comp_finiteType) ‹_›

open scoped TensorProduct in
lemma locallyOfFiniteType_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @LocallyOfFiniteType := by
  apply HasRingHomProperty.stableUnderBaseChange
  apply RingHom.StableUnderBaseChange.mk _ RingHom.finiteType_is_local.respectsIso
  intros R S T _ _ _ _ _ H
  have H : Algebra.FiniteType R T := by
    delta RingHom.FiniteType at H; convert H; exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  suffices Algebra.FiniteType S (S ⊗[R] T) by
    delta RingHom.FiniteType; convert this; exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  obtain ⟨ι, _, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp H
  let g := (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] T)
    (Algebra.TensorProduct.includeRight.comp f))
  have hg : Function.Surjective g := by
    show Function.Surjective (g.toLinearMap.restrictScalars R)
    convert f.toLinearMap.lTensor_surjective S hf using 2
    ext; simp [g]
  exact ((Algebra.FiniteType.mvPolynomial _ _).equiv
    (MvPolynomial.algebraTensorAlgEquiv R (σ := ι) S).symm).of_surjective _ hg

end AlgebraicGeometry
