/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
/-!

# Birational maps between schemes

A `BirationalMap` between irreducible schemes is a pair of dominant rational
maps that are mutually inverse. For schemes over a base `S`, the predicate
`BirationalMap.IsOver` says that a birational map is defined over `S`.

## Main results

- The birational automorphisms of a scheme `X` form a group, see the group instance on
  `BirationalMap X X`. Those defined over a base scheme `S` form a subgroup, see
  `birationalAutOver`.
- A partial isomorphism gives rise to a birational map, see `PartialIso.toBirationalMap`
  (stacks 0BAA 'if' part).

## Future work

- Show the 'only if' part of stacks 0BAA: A birational map yields a partial isomorphism.
- Show that over a field `S = Spec K`, birational maps over `Spec K` between `X` and `Y`
  correspond to algebra isomorphisms between their function fields.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A birational map between irreducible schemes `X` and `Y`. Consists of a pair of dominant
mutually inverse rational maps `hom : X ⤏ Y` and `inv : Y ⤏ X`. -/
structure BirationalMap (X Y : Scheme.{u}) [IrreducibleSpace X] [IrreducibleSpace Y] where
  /-- The forward rational map of a birational map. -/
  hom : X ⤏ Y
  [isDominant_hom : hom.IsDominant]
  /-- The inverse rational map of a birational map. -/
  inv : Y ⤏ X
  [isDominant_inv : inv.IsDominant]
  hom_comp_inv_id : hom.comp inv = .id X := by grind
  inv_comp_hom_id : inv.comp hom = .id Y := by grind

attribute [instance] BirationalMap.isDominant_hom BirationalMap.isDominant_inv

attribute [simp, grind =] BirationalMap.hom_comp_inv_id BirationalMap.inv_comp_hom_id

namespace BirationalMap

variable {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

@[ext, grind ext]
lemma ext (f g : X.BirationalMap Y) (e : f.hom = g.hom) : f = g := by
  suffices f.inv = g.inv by grind [BirationalMap]
  calc
    f.inv = f.inv.comp (g.hom.comp g.inv) := by grind
    _     = g.inv := by grind

variable (X) in
/-- The identity birational map on `X`. -/
@[simps, refl]
def refl : X.BirationalMap X where
  hom := RationalMap.id X
  inv := RationalMap.id X

/-- The inverse of a birational map. -/
@[simps, symm]
def symm (f : X.BirationalMap Y) : Y.BirationalMap X where
  hom := f.inv
  inv := f.hom

/-- The composition of two birational maps. -/
@[simps, trans]
noncomputable def trans (f : X.BirationalMap Y) (g : Y.BirationalMap Z) :
    BirationalMap X Z where
  hom := f.hom.comp g.hom
  inv := g.inv.comp f.inv

@[simp]
theorem refl_trans (f : X.BirationalMap Y) : (refl X).trans f = f := by
  ext; simp

@[simp]
theorem trans_refl (f : X.BirationalMap Y) : f.trans (refl Y) = f := by
  ext; simp

@[simp, grind _=_]
theorem trans_symm (f : X.BirationalMap Y) (g : Y.BirationalMap Z) :
    (f.trans g).symm = g.symm.trans f.symm := by
  ext; simp

@[simp]
theorem symm_trans_self_id (f : X.BirationalMap Y) : f.symm.trans f = refl Y := by
  ext; simp

@[simp]
theorem self_trans_symm_id (f : X.BirationalMap Y) : f.trans f.symm = refl X := by
  ext; simp

@[simp, grind _=_]
theorem trans_assoc {W : Scheme.{u}} [IrreducibleSpace W]
    (f : X.BirationalMap Y) (g : Y.BirationalMap Z) (h : Z.BirationalMap W) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext; simp only [BirationalMap.trans_hom, f.hom.comp_assoc]

noncomputable instance : Group (X.BirationalMap X) where
  one := refl X
  inv := symm
  mul := trans
  mul_assoc := trans_assoc
  one_mul := refl_trans
  mul_one := trans_refl
  inv_mul_cancel := symm_trans_self_id

/-- A birational map between irreducible schemes `X` and `Y` over a base scheme `S`: a
`BirationalMap` whose underlying forward rational map is an `S`-map.
The inverse is then automatically an `S`-map too, see `BirationalMapOver.isOver_inv`. -/
abbrev IsOver (S : Scheme.{u}) [X.Over S] [Y.Over S] (f : X.BirationalMap Y) : Prop :=
  f.hom.IsOver S

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (f : BirationalMap X Y) [hf : f.IsOver S] :
    f.inv.IsOver S := by
  simp [RationalMap.isOver_iff, ← RationalMap.isOver_iff.mp hf, ← RationalMap.comp_toRationalMap,
    ← RationalMap.comp_assoc]

end BirationalMap

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- The subgroup of the group of birational self-maps of `X` consisting of those maps
that are defined over the base scheme `S`. -/
def birationalAutOver (S : Scheme.{u}) [X.Over S] : Subgroup (X.BirationalMap X) where
  carrier := { f | f.IsOver S }
  one_mem' := inferInstanceAs ((RationalMap.id X).IsOver S)
  mul_mem' {f g} (_ : f.IsOver S) (_ : g.IsOver S) := inferInstanceAs ((f.hom.comp g.hom).IsOver S)
  inv_mem' {f} (_ : f.IsOver S) := inferInstanceAs (f.inv.IsOver S)

set_option backward.isDefEq.respectTransparency.types false in
lemma PartialIso.toPartialMap_comp_symm (f : X.PartialIso Y) :
    f.toPartialMap.comp f.symm.toPartialMap =
      (PartialMap.id X).restrict f.source f.dense_source le_top := by
  ext1
  · -- This change seems hard to remove
    change f.source.ι ''ᵁ f.iso.hom ⁻¹ᵁ f.target.ι ⁻¹ᵁ f.target = f.source
    rw [Opens.ι_preimage_self, Hom.preimage_top, Opens.ι_image_top]
  · -- This change seems hard to remove
    change (f.source.ι.isoImage (f.iso.hom ⁻¹ᵁ f.target.ι ⁻¹ᵁ f.target)).inv ≫
      (f.iso.hom ≫ f.target.ι) ∣_ f.target ≫ f.iso.inv ≫ f.source.ι = _
    simp_rw [morphismRestrict_comp, Opens.morphismRestrict_ι, homOfLE_ι,
      morphismRestrict_ι, Category.assoc, Iso.hom_inv_id_assoc, Hom.isoImage_inv_ι, isoOfEq_hom,
      PartialMap.restrict_hom, PartialMap.id_domain, PartialMap.id_hom, topIso_hom, homOfLE_ι]
    exact (X.homOfLE_ι _).symm

set_option backward.isDefEq.respectTransparency.types false in
lemma PartialIso.symm_toPartialMap_comp (f : X.PartialIso Y) :
    f.symm.toPartialMap.comp f.toPartialMap =
      (PartialMap.id Y).restrict f.target f.dense_target le_top := by
  ext1
  · -- This change seems hard to remove
    change f.target.ι ''ᵁ f.iso.inv ⁻¹ᵁ f.source.ι ⁻¹ᵁ f.source = f.target
    rw [Opens.ι_preimage_self, Hom.preimage_top, Opens.ι_image_top]
  · -- This change seems hard to remove
    change (f.target.ι.isoImage (f.iso.inv ⁻¹ᵁ f.source.ι ⁻¹ᵁ f.source)).inv ≫
      (f.iso.inv ≫ f.source.ι) ∣_ f.source ≫ f.iso.hom ≫ f.target.ι = _
    simp_rw [morphismRestrict_comp, Opens.morphismRestrict_ι, homOfLE_ι,
      morphismRestrict_ι, Category.assoc, Iso.inv_hom_id_assoc, Hom.isoImage_inv_ι, isoOfEq_hom,
      PartialMap.restrict_hom, PartialMap.id_domain, PartialMap.id_hom, topIso_hom, homOfLE_ι]
    exact (Y.homOfLE_ι _).symm

/-- A partial isomorphism gives rise to a birational map. -/
@[simps, stacks 0BAA "(1) 'if' part"]
def PartialIso.toBirationalMap (f : X.PartialIso Y) : X.BirationalMap Y where
  hom := f.toRationalMap
  inv := f.symm.toRationalMap
  hom_comp_inv_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff,
      PartialIso.toPartialMap_comp_symm]
    apply PartialMap.restrict_equiv
  inv_comp_hom_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff,
      PartialIso.symm_toPartialMap_comp]
    apply PartialMap.restrict_equiv

@[stacks 0BAA "(2) 'if' part"]
lemma PartialIso.isOver_toBirationalMap (S : Scheme.{u}) [X.Over S] [Y.Over S] (f : X.PartialIso Y)
    (hf : f.IsOver (X ↘ S) (Y ↘ S)) : f.toBirationalMap.IsOver S :=
  have : PartialMap.IsOver S f.toPartialMap := ⟨hf⟩
  inferInstanceAs (RationalMap.IsOver S f.toRationalMap)

end AlgebraicGeometry.Scheme
