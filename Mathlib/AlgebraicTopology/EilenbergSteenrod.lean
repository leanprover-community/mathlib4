/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopPair

/-!
# Eilenberg-Steenrod homology theories

In this file we introduce the Eilenberg-Steenrod axioms for homology theories.

The data for a homology theory is bundled in a structure `HomologyPretheory` consisting of functors
`Hₚ i : TopPair ⥤ C` and `H i : TopCat ⥤ C` which represent the `i`th relative and regular homology,
respectively, (indexed by a `ComplexShape`) and a proof that they agree on `TopCat`. They also
require boundary morphisms `δ i j :  Hₚ i ⟶ proj₂ ⋙ H j` for the long exact sequence of
topological pairs. These are nonzero only if `c.Rel i j`.

We introduce a typeclass `IsHomotopyInvariant` for the first axiom.
-/

@[expose] public section

open CategoryTheory TopPair ObjectProperty

universe u

namespace TopPair

/-- A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
@[ext]
structure HomologyPretheory
    (C : Type*) [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  /-- The relative homology functor of a `HomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u} ⥤ C
  /-- The regular homology functor of a `HomologyPretheory`. -/
  H (i : ι) : TopCat.{u} ⥤ C
  /-- `Hₚ` and `H` agree on `TopCat` -/
  iso (i : ι) : H i ≅ incl ⋙ Hₚ i
  /-- The boundary natural transformation of a `HomologyPretheory`. -/
  δ (i j : ι) : Hₚ i ⟶ proj₂ ⋙ H j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace HomologyPretheory

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- A morphism in the category `HomologyPretheory`. -/
@[ext]
structure Hom (HP HP' : HomologyPretheory.{u} C c) where
  /-- The natural transformation of relative homology functors in a morphism of
  `HomologyPretheory`s. -/
  homₚ (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i
  /-- The natural transformation of homology functors in a morphism of
  `HomologyPretheory`s. -/
  hom (i : ι) : HP.H i ⟶ HP'.H i := (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv
  /-- `homₚ` and `hom` need to be compatible with `HomologyPretheory.iso`. -/
  iso_comm (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom := by cat_disch
  /-- `homₚ` needs to be compatible with the boundary maps. -/
  w (i j : ι) : HP.δ i j ≫ proj₂.whiskerLeft (hom j) = homₚ i ≫ HP'.δ i j := by cat_disch

attribute [reassoc (attr := simp)] Hom.iso_comm
attribute [reassoc (attr := local simp)] Hom.w

@[simps]
instance : Category (HomologyPretheory.{u} C c) where
  Hom := HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

variable {HP HP' : HomologyPretheory.{u} C c}

@[reassoc]
lemma Hom.iso_comm_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    dsimp% (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) =
    (f.hom i).app X ≫ (HP'.iso i).hom.app X :=
  congr($(f.iso_comm _).app _)

@[reassoc]
lemma Hom.w_app (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u}) :
    dsimp% (HP.δ i j).app X ≫ (f.hom j).app X.left = (f.homₚ i).app X ≫ (HP'.δ i j).app X :=
  congr($(f.w _ _).app _)

@[reassoc]
lemma iso_homₚ_inv_hom (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = f.hom i := by simp

@[reassoc (attr := simp)]
lemma iso_homₚ_inv_hom_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    dsimp% (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) ≫ (HP'.iso i).inv.app X =
    (f.hom i).app X := congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).inv ≫ f.hom i ≫ (HP'.iso i).hom = incl.whiskerLeft (f.homₚ i) :=
  ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    dsimp% (HP.iso i).inv.app X ≫ (f.hom i).app X ≫ (HP'.iso i).hom.app X =
    (f.homₚ i).app (ofTopCat X) := congr($(inv_hom_iso_homₚ _ _).app _)

/-- The forgetful functor that sends a `HomologyPretheory` to it's relative homology functor `Hₚ`.
-/
@[simps]
protected def forgetₚ (i : ι) : HomologyPretheory.{u} C c ⥤ TopPair.{u} ⥤ C where
  obj HP := HP.Hₚ i
  map f := f.homₚ i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.homₚ i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.forgetₚ i).map f))

/-- The forgetful functor that sends a `HomologyPretheory` to it's homology functor `H`. -/
@[simps]
protected def forget (i : ι) : HomologyPretheory.{u} C c ⥤ TopCat.{u} ⥤ C where
  obj HP := HP.H i
  map f := f.hom i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.hom i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.forget i).map f))

variable (HP HP' : HomologyPretheory.{u} C c)

/-- A `HomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes homotopic maps to
the same map in homology -/
class IsHomotopyInvariant (HP : HomologyPretheory.{u} C c) where
  map_eq_of_homotopy (HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι) :
    (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

export IsHomotopyInvariant (map_eq_of_homotopy)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsHomotopyInvariant` as `ObjectProperty`. -/
abbrev isHomotopyInvariant : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsHomotopyInvariant

instance : IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c) where
  of_iso e _ := ⟨fun F _ ↦ by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

end HomologyPretheory

end TopPair
