/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Fangming Li
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Stalks of a Scheme

Given a scheme `X` and a point `x : X`, `AlgebraicGeometry.Scheme.fromSpecStalk X x` is the
canonical scheme morphism from `Spec(O_x)` to `X`. This is helpful for constructing the canonical
map from the spectrum of the residue field of a point to the original scheme.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

/--
A morphism from `Spec(O_x)` to `X`, which is defined with the help of an affine open
neighborhood `U` of `x`.
-/
noncomputable def IsAffineOpen.fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

/--
The morphism from `Spec(O_x)` to `X` given by `IsAffineOpen.fromSpec` does not depend on the affine
open neighborhood of `x` we choose.
-/
theorem IsAffineOpen.fromSpecStalk_eq {X : Scheme} (x : X) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X) (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op]
    erw [← Scheme.Spec_map (X.presheaf.map _).op, ← Scheme.Spec_map (X.presheaf.germ _ x h₂).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res, Scheme.Spec_map,
      Quiver.Hom.unop_op]
  · delta fromSpecStalk
    rw [← hV.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_right).op]
    erw [← Scheme.Spec_map (X.presheaf.map _).op, ← Scheme.Spec_map (X.presheaf.germ _ x h₂).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res, Scheme.Spec_map,
      Quiver.Hom.unop_op]

/--
If `x` is a point of `X`, this is the canonical morphism from `Spec(O_x)` to `X`.
-/
noncomputable def Scheme.fromSpecStalk (X : Scheme) (x : X) :
    Scheme.Spec.obj (op (X.presheaf.stalk x)) ⟶ X :=
  (isAffineOpen_opensRange (X.affineOpenCover.map x)).fromSpecStalk (X.affineOpenCover.covers x)

@[simp]
theorem IsAffineOpen.fromSpecStalk_eq_fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x := fromSpecStalk_eq ..

instance IsAffineOpen.fromSpecStalk_isPreimmersion {X : Scheme.{u}} {U : Opens X}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) : IsPreimmersion (hU.fromSpecStalk hx) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  haveI : IsPreimmersion (Spec.map (X.presheaf.germ U x hx)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    IsPreimmersion.of_isLocalization (R := Γ(X, U)) (S := X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  apply IsPreimmersion.comp

instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecStalk x) :=
  IsAffineOpen.fromSpecStalk_isPreimmersion _ _ _

end AlgebraicGeometry
