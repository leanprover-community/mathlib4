/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryAut
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryDegree
public import Mathlib.NumberTheory.CFT.ClassFormation.GrothendieckTopology
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Class formations

-/

-- depends on: #42397, #42396, #42320, #42568

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open PreGaloisCategory GaloisCategory

-- The assumption `[EssentiallySmall.{v} C]` may be required in some places

variable (C) in
/-- A formation for a Galois category `C` is a sheaf of abelian groups
on the category of connected objects in `C` (equipped with the regular topology). -/
structure Formation [GaloisCategory C] where
  /-- the underlying sheaf on the category of connected objects on the Galois category -/
  sheaf : Sheaf (isConnectedTopology C) Ab.{v}

namespace Formation

variable [GaloisCategory C] (Φ : Formation C)

lemma isSheaf_forget : Presieve.IsSheaf (isConnectedTopology C) (Φ.sheaf.obj ⋙ forget _) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) Φ.sheaf.property

section

variable {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
  [PreGaloisCategory.IsConnected Y]

/-- If `Φ` is a formation and `f : Y ⟶ X` is a Galois cover, this is the induced
representation of the group of automorphisms of `Over.mk f`. -/
@[implicit_reducible, nolint unusedArguments]
def representation [IsGaloisCover f] :
    Representation (ULift.{v} ℤ) (Aut (Over.mk f)) (Φ.sheaf.obj.obj (op (isConnectedMk Y))) where
  toFun g :=
    { toFun := (Φ.sheaf.obj.map (ObjectProperty.homMk g.inv.left).op).hom.toFun
      map_add' := by simp
      map_smul' := by simp }
  map_one' := by
    ext : 1
    dsimp [Aut.one_def]
    rw [ObjectProperty.homMk_id]
    simp
  map_mul' g h := by
    ext : 1
    dsimp
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

variable [IsGaloisCover f]

@[simp]
lemma representation_apply (σ : Aut (Over.mk f)) (x : Φ.sheaf.obj.obj (op (isConnectedMk Y))) :
    Φ.representation f σ x =
      Φ.sheaf.obj.map (ObjectProperty.homMk σ.inv.left).op x := rfl

/-- If `Φ` is a formation and `f : Y ⟶ X` is a Galois cover, this is the induced
representation of the group of automorphisms of `Over.mk f`, as an object
in `Rep`. -/
abbrev rep : Rep.{v} (ULift.{v} ℤ) (Aut (Over.mk f)) := Rep.of (Φ.representation f)

/-- The cohomology of a Galois cover for a formation. -/
noncomputable abbrev H (n : ℕ) : Ab.{v} :=
  (forget₂ _ _).obj (groupCohomology (Φ.rep f) n)

end

section

variable {Y X' X : C}
  [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X']
  [PreGaloisCategory.IsConnected X]
  (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
  [IsGaloisCover fg] [IsGaloisCover f]

/-- Auxiliary definition for `resRep`. -/
abbrev resIntertwiningMap (fac : f ≫ g = fg := by cat_disch) :
  Representation.IntertwiningMap ((Φ.rep fg).ρ.comp (Aut.overMap f g fg))
    (Φ.representation f) where
  toLinearMap := .id
  isIntertwining' _ := rfl

/-- If `Φ` is a formation, and `f ≫ g = fg` where `fg` and `f` are Galois covers,
then this is the morphism from the restriction of `Φ.rep fg` to `Φ.rep f`. -/
abbrev resRep (fac : f ≫ g = fg := by cat_disch) :
    Rep.res (Aut.overMap f g fg) (Φ.rep fg) ⟶ Φ.rep f :=
  Rep.ofHom (Φ.resIntertwiningMap f g fg)

/-- The restriction morphisms on the cohomology of a formation. -/
noncomputable def restriction {Y X' X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X']
    [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
    [IsGaloisCover fg] [IsGaloisCover f] (n : ℕ)
    (fac : f ≫ g = fg := by cat_disch) :
    Φ.H fg n ⟶ Φ.H f n :=
  (forget₂ _ _).map (groupCohomology.map (Aut.overMap f g fg) (Φ.resRep f g fg) n)

end

section

variable {Y' Y X : C}
  [PreGaloisCategory.IsConnected Y'] [PreGaloisCategory.IsConnected Y]
  [PreGaloisCategory.IsConnected X]
  (f : Y' ⟶ Y) (g : Y ⟶ X) (fg : Y' ⟶ X)
  [IsGaloisCover g] [IsGaloisCover fg]

/-- Auxiliary definition for `infRep`. -/
abbrev infIntertwiningMap (fac : f ≫ g = fg := by cat_disch) :
  Representation.IntertwiningMap ((Φ.rep g).ρ.comp
    (autMapOfIsGaloisCover f g fg)) (Φ.representation fg) where
  toLinearMap :=
    { toFun x := (Φ.sheaf.obj.map (isConnectedHomMk f).op) x
      map_add' := by simp
      map_smul' := by simp }
  isIntertwining' g := by
    ext x
    dsimp [representation]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 4
    ext : 1
    simp

/-- If `Φ` is a formation, and `f ≫ g = fg` where `fg` and `g` are Galois covers,
then this is the morphism from the restriction of `Φ.rep fg` to `Φ.rep f`. -/
noncomputable abbrev infRep (fac : f ≫ g = fg := by cat_disch) :
    Rep.res (autMapOfIsGaloisCover f g fg) (Φ.rep g) ⟶ Φ.rep fg :=
  Rep.ofHom (Φ.infIntertwiningMap f g fg)

/-- The inflation morphisms on the cohomology of a formation. -/
noncomputable def inflation (n : ℕ)
    (fac : f ≫ g = fg := by cat_disch) :
    Φ.H g n ⟶ Φ.H fg n :=
  (forget₂ _ _).map (groupCohomology.map (autMapOfIsGaloisCover f g fg) (Φ.infRep f g fg) n)

end

/-def corestriction {Y X' X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X']
    [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
    [IsGaloisCover fg] [IsGaloisCover f] (n : ℕ)
    (fac : f ≫ g = fg := by cat_disch) :
    Φ.H f n ⟶ Φ.H fg n := by
  sorry-/

end Formation

section

variable [GaloisCategory C]

variable (C) in
/-- A field formation is a formation which which the cohomology is trivial
in degree `1`. -/
structure FieldFormation extends Formation C where
  isZero_H_one {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] :
      IsZero (toFormation.H f 1)

/-! The definition below is suggested by Serre in _Corps locaux_ p. 176
(this is chosen in order to involve only group cohomology of finite
groups rather than any "colimit" of these groups, which could also
be interpreted here as the cohomology for the Grothendieck
topology `isConnectedTopology C`). With these axioms, when taking a
suitable colimit, we should get a subgroup of `ℚ / ℤ` which may
not be the whole `ℚ / ℤ`. If we want that the invariant is an isomorphism
with `ℚ / ℤ`, an extra condition on `C` should be added. -/

variable (C) in
/-- A class formation is a field formation for which the cohomology
in degree `2` of a Galois cover `f : Y ⟶ X` identifies to `ℤ / dℤ` where
`d` is the degree of `f`, and the isomorphisms should satisfy compatibilities
with inflation and restriction maps. In this implementation,
the isomorphisms are given by the data of the fundamental class in `H f 2`. -/
structure ClassFormation extends FieldFormation C where
  /-- The fundamental class attached to a Galois cover -/
  u {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] : toFormation.H f 2
  addOrderOf_u {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] :
    addOrderOf (u f) = degMap f
  zmultiples_u {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] :
    AddSubgroup.zmultiples (u f) = ⊤
  inflation_u {Y' Y X : C} [PreGaloisCategory.IsConnected Y']
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y' ⟶ Y) (g : Y ⟶ X) (fg : Y' ⟶ X)
    [IsGaloisCover g] [IsGaloisCover fg]
    (fac : f ≫ g = fg := by cat_disch) :
    (toFormation.inflation f g fg 2) (u g) = degMap f • u fg
  restriction_u {Y X' X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X'] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
    [IsGaloisCover f] [IsGaloisCover fg]
    (fac : f ≫ g = fg := by cat_disch) :
    (toFormation.restriction f g fg 2) (u fg) = u f

end

end CategoryTheory
