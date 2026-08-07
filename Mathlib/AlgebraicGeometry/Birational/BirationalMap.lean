/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

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
  (Stacks 0BAA 'if' part).

## Future work

- Show the 'only if' part of Stacks 0BAA: A birational map yields a partial isomorphism.
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
theorem symm_trans_self (f : X.BirationalMap Y) : f.symm.trans f = refl Y := by
  ext; simp

@[simp]
theorem self_trans_symm (f : X.BirationalMap Y) : f.trans f.symm = refl X := by
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
  inv_mul_cancel := symm_trans_self

/-- A birational map between irreducible schemes `X` and `Y` over a base scheme `S`, via structure
maps `sX : X ⟶ S` and `sY : Y ⟶ S`: a `BirationalMap` whose underlying forward rational map is an
`S`-map. The inverse is then automatically an `S`-map too, see the `f.inv.IsOver sY sX` instance. -/
abbrev IsOver {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (f : X.BirationalMap Y) : Prop :=
  f.hom.IsOver sX sY

instance {S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} (f : BirationalMap X Y) [hf : f.IsOver sX sY] :
    f.inv.IsOver sY sX := by
  simp [RationalMap.isOver_iff, ← RationalMap.isOver_iff.mp hf, ← RationalMap.comp_toRationalMap,
    ← RationalMap.comp_assoc]

end BirationalMap

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- The subgroup of the group of birational self-maps of `X` consisting of those maps
that are defined over the base scheme `S`, via a structure map `sX : X ⟶ S`. -/
def birationalAutOver {S : Scheme.{u}} (sX : X ⟶ S) : Subgroup (X.BirationalMap X) where
  carrier := { f | f.IsOver sX sX }
  one_mem' := RationalMap.isOver_iff.mpr (RationalMap.id_compHom sX)
  mul_mem' {f g} (hf : f.IsOver sX sX) (hg : g.IsOver sX sX) := RationalMap.isOver_comp _ hf _ hg
  inv_mem' {f} (_ : f.IsOver sX sX) := inferInstanceAs (f.inv.IsOver sX sX)

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
lemma PartialIso.isOver_toBirationalMap {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (f : X.PartialIso Y) (hf : f.IsOver sX sY) : f.toBirationalMap.IsOver sX sY :=
  have : f.toPartialMap.IsOver sX sY := ⟨(Category.assoc _ _ _).trans hf⟩
  inferInstanceAs (f.toRationalMap.IsOver sX sY)

end AlgebraicGeometry.Scheme
