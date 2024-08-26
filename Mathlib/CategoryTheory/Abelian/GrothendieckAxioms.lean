/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isaac Hernando, Coleton Kotch, Adam Topaz
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
/-!
# Grothendieck Axioms

This file defines some of the Grothendieck Axioms for abelian categories, and proves
basic facts about them.

## Definitions

1. `AB4` -- an abelian category satisfies `AB4` provided that coproducts are exact.
2. `AB5` -- an abelian category satisfies `AB5` provided that filtered colimits are exact.

## Results

- `AB5` implies `AB4`

## Implementation Details

For `AB4` and `AB5`, we only assume left exactness as right exactness is automatic.

## Projects

- Add additional axioms.

-/

namespace CategoryTheory

open Limits Classical

universe v v' u u'

variable (C : Type u) [Category.{v} C]

--Right exactness for arbitrary shapes.
noncomputable
example (J : Type u') [Category.{v'} J] [HasColimitsOfShape J C] :
    PreservesFiniteColimits (colim (J := J) (C := C)) :=
  inferInstance

/--
A category `C` which has coproducts is said to have `AB4` provided that
coproducts are exact.
-/
class AB4 [HasCoproducts C] where
  preservesFiniteLimits (α : Type v) :
    PreservesFiniteLimits (colim (J := Discrete α) (C := C))

instance [HasCoproducts C] [AB4 C] (α : Type v) :
    PreservesFiniteLimits (colim (J := Discrete α) (C := C)) :=
  AB4.preservesFiniteLimits _

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
class AB5 [HasFilteredColimits C] where
  preservesFiniteLimits (J : Type v) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim (J := J) (C := C))

instance [HasFilteredColimits C] [AB5 C]
    (J : Type v) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim (J := J) (C := C)) :=
  AB5.preservesFiniteLimits _

variable {C}
variable {α : Type v} (X Y : α → C) [HasCoproduct X] [HasCoproduct Y]
variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/--
This is the functor `Finset α ⥤ C` which, on objects, sends a finite set `S` to
`⨁ fun s : S => X s`. We will show below that the colimit of this functor is
isomorphic to `∐ X`.
-/
@[simps]
noncomputable
def finsetBiproductDiagram : Finset α ⥤ C where
  obj S := ⨁ fun s : S => X s
  map {S T} i := biproduct.desc fun b => biproduct.ι (fun t : T => X t) ⟨b, i.le b.prop⟩

/--
IMPLEMENTATION: This is the cocone over `finsetBiproductDiagram` whose cocone point is `∐ X`.
We will show that this is a colimit cocone below.
-/
@[simps]
noncomputable
def finsetBiproductCocone : Cocone (finsetBiproductDiagram X) where
  pt := ∐ X
  ι := { app := fun _ => biproduct.desc fun _ => Sigma.ι _ _ }

/--
The cocone `finsetBiproductDiagram X` is indeed a colimit.
This is used to show that `∐ X` is isomorphic to the colimit of `finsetBiproductDiagram X`.
-/
@[simps]
noncomputable
def isColimitFinsetBiproductCocone : IsColimit (finsetBiproductCocone X) where
  desc S := Sigma.desc
    fun a => biproduct.ι (fun (b : ({a} : Finset α)) => X b) ⟨a, by simp⟩ ≫ S.ι.app {a}
  fac S A := by
    dsimp
    ext ⟨a,ha⟩
    let e : ({a} : Finset α) ⟶ A := homOfLE <| by simpa
    simp [← S.w e]
  uniq S m hm := by
    dsimp
    ext a
    simp [← hm {a}]

/--
The isomorphism between `∐ X` and `finsetBiproductDiagram X`.
-/
noncomputable
def coproductIsoColimitFinsetBiproductDiagram [HasColimitsOfShape (Finset α) C] :
    ∐ X ≅ colimit (finsetBiproductDiagram X) :=
  isColimitFinsetBiproductCocone X |>.coconePointUniqueUpToIso <| colimit.isColimit _

@[reassoc (attr := simp)]
lemma ι_coproductIsoColimitFinsetBiproductDiagram_hom [HasColimitsOfShape (Finset α) C] (a) :
    Sigma.ι X a ≫ (coproductIsoColimitFinsetBiproductDiagram X).hom =
    biproduct.ι (fun (b : ({a} : Finset α)) => X b) ⟨a, by simp⟩ ≫
    colimit.ι (finsetBiproductDiagram X) {a} := by
  dsimp [coproductIsoColimitFinsetBiproductDiagram, IsColimit.coconePointUniqueUpToIso]
  simp

/--
IMPLEMENTATION: Functoriality of `finsetBiproductDiagram`.
-/
@[simps]
noncomputable
def finsetBiproductNatTrans (η : X ⟶ Y) :
    finsetBiproductDiagram X ⟶ finsetBiproductDiagram Y where
  app A := biproduct.map (η ·)
  naturality {X Y} f := by
    dsimp
    ext i j
    simp only [Category.assoc, biproduct.map_π, biproduct.ι_desc_assoc,
      ne_eq, biproduct.ι_π_assoc, biproduct.map_desc, biproduct.ι_π]
    split_ifs with h
    · subst h
      simp
    · simp

variable (α C)

/--
`finsetBiproductDiagram` as a functor.
-/
@[simps]
noncomputable
def discreteDiagramToFinsetBiproductDiagram : (Discrete α ⥤ C) ⥤ (Finset α ⥤ C) where
  obj F := finsetBiproductDiagram fun a => F.obj ⟨a⟩
  map η := finsetBiproductNatTrans _ _ (η.app ⟨·⟩)

/--
The coproduct functor indexed by `α` is isomorphic to the composition of
`discreteDiagramToFinsetBiproductDiagram` and the colimit functor.
-/
@[simps!]
noncomputable
def coproductFunctorIso [HasCoproducts C] [HasColimitsOfShape (Finset α) C] :
    (colim (J := Discrete α) (C := C)) ≅ discreteDiagramToFinsetBiproductDiagram C α ⋙ colim :=
  NatIso.ofComponents
    (fun F =>
      HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F)) ≪≫
      coproductIsoColimitFinsetBiproductDiagram (F.obj ⟨·⟩)) <| by
        intro x y f
        dsimp
        ext ⟨⟩
        simp [Function.comp]

/--
IMPLEMENTATION: A single component of `discreteDiagramToFinsetBiproductDiagram`.
-/
@[simps]
noncomputable
def discreteDiagramToBiproduct (A : Finset α) :
    (Discrete α ⥤ C) ⥤ C where
  obj F := ⨁ fun a : A => F.obj ⟨a⟩
  map η := biproduct.map fun _ => η.app _

noncomputable
instance (A : Finset α)
    (J : Type u') [Category.{v'} J] [HasLimitsOfShape J C] (K : J ⥤ Discrete α ⥤ C) :
    PreservesLimit K (discreteDiagramToBiproduct C α A) where
  preserves {S} hS := {
    lift := fun E => biproduct.lift fun ⟨a,ha⟩ =>
      let K' := K ⋙ (evaluation _ _).obj ⟨a⟩
      let S' : Cone K' := Functor.mapCone _ S
      let hS' : IsLimit S' := isLimitOfPreserves _ hS
      hS'.lift ⟨_, fun j => E.π.app _ ≫
        biproduct.π (fun a : A => (K.obj j).obj ⟨a⟩) ⟨a, ha⟩, by
          intro i j f
          simp only [Functor.const_obj_obj, Functor.comp_obj, evaluation_obj_obj,
            Functor.const_obj_map, discreteDiagramToBiproduct_obj, ← E.w f, Functor.comp_map,
            discreteDiagramToBiproduct_map, Category.assoc, biproduct.map_π, Category.id_comp,
            evaluation_obj_map, K']⟩
    fac := by
      intro E j
      dsimp
      ext ⟨a, ha⟩
      let K' := K ⋙ (evaluation _ _).obj ⟨a⟩
      let S' : Cone K' := Functor.mapCone _ S
      let hS' : IsLimit S' := isLimitOfPreserves _ hS
      simp only [biproduct.lift_map, biproduct.lift_π]
      apply hS'.fac
    uniq := by
      intro E m hm
      dsimp
      ext ⟨a,ha⟩
      let K' := K ⋙ (evaluation _ _).obj ⟨a⟩
      let S' : Cone K' := Functor.mapCone _ S
      let hS' : IsLimit S' := isLimitOfPreserves _ hS
      simp only [biproduct.lift_π]
      apply hS'.hom_ext
      intro j
      rw [hS'.fac]
      simp only [Functor.comp_obj, evaluation_obj_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
        evaluation_obj_map, Category.assoc, ← (hm j), discreteDiagramToBiproduct_obj,
        discreteDiagramToBiproduct_map, biproduct.map_π, K', S']
  }

noncomputable
instance (J : Type u') [Category.{v'} J] [HasLimitsOfShape J C] (K : J ⥤ Discrete α ⥤ C) :
    PreservesLimit K ((discreteDiagramToFinsetBiproductDiagram C α)) := by
  apply Limits.preservesLimitOfEvaluation
  intro A
  change PreservesLimit K (discreteDiagramToBiproduct _ _ A)
  infer_instance

noncomputable
instance [HasLimits C] : PreservesLimits (discreteDiagramToFinsetBiproductDiagram C α) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }

noncomputable
instance [HasFiniteLimits C] :
    PreservesFiniteLimits (discreteDiagramToFinsetBiproductDiagram C α) where
  preservesFiniteLimits _ _ _ := ⟨@fun _ => inferInstance⟩

noncomputable
instance [HasCoproducts C] [HasFilteredColimits C] [HasFiniteLimits C] [AB5 C] : AB4 C where
  preservesFiniteLimits _ :=
    ⟨fun _ => ⟨@fun _ => preservesLimitOfNatIso _ (coproductFunctorIso _ _).symm⟩⟩

end CategoryTheory
