/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso

/-!
# The Residue Field of a Point in a Locally Ringed Space and the Canonical Morphism

In this file, we have defined the residue field of a point in a locally ringed space. Also, given a
scheme `X` and a point `x : X`, we have constructed the canonical morphism from the spectrum of the
residue field of `x` to `X`.
-/

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/--
Given a locally ringed space `X` and a point `x : X.toTopCat`, the residue field of `x` is the
residue field of the stalk at `x`.
-/
noncomputable def ResidueField {X : LocallyRingedSpace} (x : X) : CommRingCat where
  α := LocalRing.ResidueField (stalk X x)
  str := LocalRing.ResidueFieldCommRing (X.stalk x)

lemma ResidueField.isField {X : LocallyRingedSpace} (x : X) :
    IsField (X.ResidueField x) :=
  Semifield.toIsField (LocalRing.ResidueField (X.stalk x))

noncomputable instance {X : LocallyRingedSpace} (x : X) : Field (X.ResidueField x) :=
  LocalRing.ResidueField.field (X.stalk x)

end LocallyRingedSpace

namespace Scheme

/--
The canonical morphism from the spectrum of the stalk at `x` to `X`.
-/
noncomputable def HomFromStalkSpec {X : Scheme} (x : X) :
    (Scheme.Spec.obj (Opposite.op (X.stalk x))) ⟶ X :=
-- Because `X` is a scheme, `x` has an affine open neighbourhood `U`.
  let U := (X.local_affine x).choose
-- The ring `R` such that `U` is isomorphic to Spec(`R`).
  let R := (X.local_affine x).choose_spec.choose
-- The isomorphism from `U` to Spec(`R`).
  let iUR := Classical.choice (X.local_affine x).choose_spec.choose_spec
-- Because `U` is isomorphic to Spec(`R`) and the global section of Spec(`R`) is `R` itself, `R`
-- is isomorphic to the section over `U`. In particular, we have a map from `R` to the the section
-- over `U`.
  let hRU := CategoryTheory.CategoryStruct.comp (StructureSheaf.toOpen R ⊤)
        (CategoryTheory.CategoryStruct.comp (iUR.hom.val.c.1 (Opposite.op ⊤))
          (CategoryTheory.eqToHom (by simp only [LocallyRingedSpace.restrict_carrier,
            TopCat.Presheaf.pushforwardObj_obj, CategoryTheory.Functor.op_obj,
            TopologicalSpace.Opens.map_top, LocallyRingedSpace.restrict_presheaf_obj,
            TopologicalSpace.Opens.openEmbedding_obj_top])))
-- We regard `x` as an element of `U`.
  let x' : U.1 := ⟨x, U.2⟩
-- The homomorphism from the section over `U` to the stalk at `x`.
  let hUs := TopCat.Presheaf.germ X.presheaf x'
-- According to the above setting, the composition of `hRU` and `hUs` is a map from `R` to the
-- stalk of `x`. Due to the contravariance of the spectrum functor, we get a morphism from the
-- spectrum of the stalk at `x` to Spec(`R`).
  let hxR := Spec.locallyRingedSpaceMap (CategoryTheory.CategoryStruct.comp hRU hUs)
-- The locally ringed space morphism induced by the open embedding from `U` to `X`.
  let hUX := X.ofRestrict (TopologicalSpace.OpenNhds.openEmbedding U)
-- The final morphism we use is the composition of `hxR`, `iUR.inv` and `hUX`.
  let this := CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp hxR iUR.inv)
    hUX
  this

end Scheme

open CategoryTheory

@[reassoc]
lemma isoSpec_inv_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map (f.app ⊤) ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.eq_inv_comp, Scheme.isoSpec, asIso_hom, ← ΓSpec.adjunction_unit_naturality_assoc,
    Scheme.isoSpec, asIso_inv, IsIso.hom_inv_id, Category.comp_id]

@[reassoc]
lemma IsAffineOpen.map_fromSpec {X : Scheme} {U V : TopologicalSpace.Opens X.carrier}
    (h : Opposite.op U ⟶ Opposite.op V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Spec.map (X.presheaf.map h) ≫ hU.fromSpec = hV.fromSpec := by
  have : IsAffine (X.restrictFunctor.obj U).left := hU
  have : IsAffine _ := hV
  conv_rhs =>
    rw [IsAffineOpen.fromSpec, ← X.restrictFunctor_map_ofRestrict h.unop,
      ← isoSpec_inv_naturality_assoc, ← Spec.map_comp_assoc,
      Scheme.restrictFunctor_map_app, ← Functor.map_comp]
  rw [IsAffineOpen.fromSpec, ← Spec.map_comp_assoc, ← Functor.map_comp]
  congr 1

noncomputable def FromSpecStalk {X : Scheme} {U : TopologicalSpace.Opens X.carrier}
    (hU : IsAffineOpen U) {x : X.carrier} (hxU : x ∈ U) :
    Scheme.Spec.obj (Opposite.op $ X.stalk x) ⟶ X :=
  CategoryTheory.CategoryStruct.comp (Scheme.Spec.map (X.presheaf.germ ⟨x, hxU⟩).op) hU.fromSpec

lemma fromSpecStalk_eq {X : Scheme} (x : X.carrier) {U V : TopologicalSpace.Opens X.carrier}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hxU : x ∈ U) (hxV : x ∈ V) :
    FromSpecStalk hU hxU = FromSpecStalk hV hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X) (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity FromSpecStalk h₁ h₂; delta FromSpecStalk
  · rw [← hU.map_fromSpec (homOfLE $ h₃.trans inf_le_left).op h₁]
    have : Spec.map (X.presheaf.map (homOfLE (LE.le.trans h₃ inf_le_left)).op) =
        Scheme.Spec.map (X.presheaf.map (homOfLE (LE.le.trans h₃ inf_le_left)).op).op := by
      simp only [Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [this]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res]
  · delta FromSpecStalk
    rw [← hV.map_fromSpec (homOfLE $ h₃.trans inf_le_right).op h₁]
    have : Spec.map (X.presheaf.map (homOfLE (LE.le.trans h₃ inf_le_right)).op) =
        Scheme.Spec.map (X.presheaf.map (homOfLE (LE.le.trans h₃ inf_le_right)).op).op := by
      simp only [Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [this, ← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res]

end AlgebraicGeometry
