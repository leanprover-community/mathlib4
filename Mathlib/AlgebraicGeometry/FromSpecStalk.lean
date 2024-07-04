/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Fangming Li
-/
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The Canonical Map from the Spectrum of a Stalk to the Original Scheme

In this file, we define:
Given a scheme `X` and a point `x : X.carrier`, `AlgebraicGeometry.Scheme.FromSpecStalk X x` is the
canonical scheme morphism from Spec(O_`x`) to `X`.

This is helpful for constructing the canonical map from the spectrum of the residue field of a point
to the original scheme.
-/

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

@[reassoc]
lemma Scheme.isoSpec_inv_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map (f.app ⊤) ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.eq_inv_comp, isoSpec, asIso_hom, ← ΓSpec.adjunction_unit_naturality_assoc, isoSpec,
    asIso_inv, IsIso.hom_inv_id, Category.comp_id]

@[reassoc]
lemma Scheme.isoSpec_hom_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.hom ≫ Spec.map (f.app ⊤) = f ≫ Y.isoSpec.hom := by
  simp only [isoSpec, asIso_hom, ΓSpec.adjunction_unit_naturality]

@[reassoc]
lemma IsAffineOpen.map_fromSpec {X : Scheme} {U V : TopologicalSpace.Opens X.carrier}
    (h : op U ⟶ op V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Spec.map (X.presheaf.map h) ≫ hU.fromSpec = hV.fromSpec := by
  have : IsAffine (X.restrictFunctor.obj U).left := hU
  haveI : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec, ← X.restrictFunctor_map_ofRestrict h.unop, ← Scheme.isoSpec_inv_naturality_assoc,
      ← Spec.map_comp_assoc, Scheme.restrictFunctor_map_app, ← Functor.map_comp]
  rw [fromSpec, ← Spec.map_comp_assoc, ← Functor.map_comp]
  congr 1

/--
A morphism from Spec(O_`x`) to `X`, which is defined with the help of an affine open
neighborhood `U` of `x`.
`IsAffineOpen.FromSpec hU hxU = (Scheme.Spec.map (X.presheaf.germ ⟨x, hxU⟩).op) ≫ hU.fromSpec`.
-/
noncomputable def IsAffineOpen.FromSpecStalk {X : Scheme} {U : TopologicalSpace.Opens X.carrier}
    (hU : IsAffineOpen U) {x : X.carrier} (hxU : x ∈ U) :
    Scheme.Spec.obj (op (X.stalk x)) ⟶ X :=
  (Scheme.Spec.map (X.presheaf.germ ⟨x, hxU⟩).op) ≫ hU.fromSpec

/--
The morphism from Spec(O_`x`) to `X` given by `IsAffineOpen.FromSpec` does not depend on the affine
open neighborhood of `x` we choose.
-/
lemma IsAffineOpen.fromSpecStalk_eq {X : Scheme} (x : X.carrier)
    {U V : TopologicalSpace.Opens X.carrier} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.FromSpecStalk hxU = hV.FromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X) (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity FromSpecStalk h₁ h₂
  · delta FromSpecStalk
    rw [← hU.map_fromSpec (homOfLE $ h₃.trans inf_le_left).op h₁]
    erw [← Scheme.Spec_map (X.presheaf.map _).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res]
  · delta FromSpecStalk
    rw [← hV.map_fromSpec (homOfLE $ h₃.trans inf_le_right).op h₁]
    erw [← Scheme.Spec_map (X.presheaf.map _).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res]

/--
The canonical scheme morphism from Spec(O_`x`) to `X`.
`Scheme.FromSpecStalk X x` is defined as:
`(isAffineOpen_opensRange (X.affineOpenCover.map x)).FromSpecStalk (X.affineOpenCover.covers x)`
-/
noncomputable def Scheme.FromSpecStalk (X : Scheme) (x : X.carrier) :
    Scheme.Spec.obj (op (X.stalk x)) ⟶ X :=
  (isAffineOpen_opensRange (X.affineOpenCover.map x)).FromSpecStalk (X.affineOpenCover.covers x)

end AlgebraicGeometry
