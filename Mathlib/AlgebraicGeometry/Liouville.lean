/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-
# Liouville's theorem

In this file, we show that the global sections of a variety (integral scheme universally-closed
and of finite type over `Spec K`) forms a finite field extension of the base field.

-/

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

variable (K : Type u) {X Y : Scheme.{u}} [Field K]

/-- If `f : X ⟶ Y` is universally closed and `Y` is affine,
then the map on global sections is integral. -/
theorem isIntegral_appTop_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f] [IsAffine Y] :
    f.appTop.hom.IsIntegral := by
  have : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  have : f = X.toSpecΓ ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have : Surjective X.toSpecΓ := by
    constructor
    apply surjective_of_isClosed_range_of_injective
    · exact X.toSpecΓ.isClosedMap.isClosed_range
    · simp only [Scheme.toSpecΓ_appTop]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, ⊤)).hom).1
  rw [← IsIntegralHom.SpecMap_iff, IsIntegralHom.iff_universallyClosed_and_isAffineHom]
  exact ⟨.of_comp_surjective X.toSpecΓ _, inferInstance⟩

/-- If `X` is an integral scheme that is universally closed over `Spec K`,
then `Γ(X, ⊤)` is a field. -/
theorem isField_of_universallyClosed (f : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed f] :
    IsField Γ(X, ⊤) := by
  let F := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

/-- If `X` is an integral scheme that is universally closed and of finite type over `Spec K`,
then `Γ(X, ⊤)` is a finite field extension over `K`. -/
theorem finite_appTop_of_universallyClosed (f : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed f] [LocallyOfFiniteType f] :
    f.appTop.hom.Finite := by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  letI := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    _ (Field.toIsField K)).toField
  letI := (isField_of_universallyClosed K f).toField
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (A := Γ(X, U))
    (g := (X.presheaf.map (homOfLE le_top).op).hom)
  exact LocallyOfFiniteType.finiteType_of_affine_subset ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)

end AlgebraicGeometry
