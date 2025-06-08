/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Uni Marx
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.Data.Rel

/-!
# Basics on the category of relations

We define the category of types `CategoryTheory.RelCat` with binary relations as morphisms.
Associating each function with the relation defined by its graph yields a faithful and
essentially surjective functor `graphFunctor` that also characterizes all isomorphisms
(see `rel_iso_iff`).

By flipping the arguments to a relation, we construct an equivalence `opEquivalence` between
`RelCat` and its opposite.
-/

open Rel

attribute [local simp] Rel.comp Rel.inv flip

namespace CategoryTheory

universe u

/-- A type synonym for `Type u`, which carries the category instance for which
    morphisms are binary relations. -/
def RelCat :=
  Type u

namespace RelCat
variable {X Y Z : RelCat.{u}}

instance inhabited : Inhabited RelCat := by unfold RelCat; infer_instance

/-- The morphisms in the relation category are relations. -/
structure Hom (X Y : RelCat.{u}) : Type u where
  /-- Build a morphism `X ⟶ Y` for `X Y : RelCat` from a relation between `X` and `Y`. -/
  ofRel ::
  /-- The underlying relation between `X` and `Y` of a morphism `X ⟶ Y` for `X Y : RelCat`. -/
  rel : Rel X Y

/-- The category of types with binary relations as morphisms. -/
instance instLargeCategory : LargeCategory RelCat where
  Hom := Hom
  id _ := .ofRel (· = ·)
  comp f g := .ofRel <| f.rel.comp g.rel

namespace Hom

@[ext] lemma ext (f g : X ⟶ Y) (h : f.rel = g.rel) : f = g := by
  obtain ⟨R⟩ := f; obtain ⟨S⟩ := g; congr

@[simp] protected theorem rel_id (X : RelCat.{u}) : rel (𝟙 X) = (· = ·) := rfl

@[simp] protected theorem rel_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).rel = f.rel.comp g.rel := rfl

theorem rel_id_apply₂ (X : RelCat) (x y : X) : rel (𝟙 X) x y ↔ x = y := .rfl

theorem rel_comp_apply₂ (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (f ≫ g).rel x z ↔ ∃ y, f.rel x y ∧ g.rel y z := .rfl

end Hom

/-- The essentially surjective faithful embedding
from the category of types and functions into the category of types and relations. -/
def graphFunctor : Type u ⥤ RelCat.{u} where
  obj X := X
  map f := .ofRel f.graph
  map_comp := by aesop (add simp [Rel.comp])

@[simp] theorem graphFunctor_map {X Y : Type u} (f : X ⟶ Y) (x : X) (y : Y) :
    (graphFunctor.map f).rel x y ↔ f x = y := .rfl

instance graphFunctor_faithful : graphFunctor.Faithful where
  map_injective h := Function.graph_injective congr(($h).rel)

instance graphFunctor_essSurj : graphFunctor.EssSurj :=
    graphFunctor.essSurj_of_surj Function.surjective_id

/-- A relation is an isomorphism in `RelCat` iff it is the image of an isomorphism in
`Type u`. -/
theorem rel_iso_iff {X Y : RelCat} (r : X ⟶ Y) :
    IsIso (C := RelCat) r ↔ ∃ f : Iso (C := Type u) X Y, graphFunctor.map f.hom = r := by
  constructor
  · intro h
    have h1 := congr_fun₂ congr(($h.hom_inv_id).rel)
    have h2 := congr_fun₂ congr(($h.inv_hom_id).rel)
    simp only [RelCat.Hom.rel_comp_apply₂, RelCat.Hom.rel_id_apply₂, eq_iff_iff] at h1 h2
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun a => (h1 a a).mpr rfl)
    obtain ⟨g, hg⟩ := Classical.axiomOfChoice (fun a => (h2 a a).mpr rfl)
    suffices hif : IsIso (C := Type u) f by
      use asIso f
      ext x y
      simp only [asIso_hom, graphFunctor_map]
      constructor
      · rintro rfl
        exact (hf x).1
      · intro hr
        specialize h2 (f x) y
        rw [← h2]
        use x, (hf x).2, hr
    use g
    constructor
    · ext x
      apply (h1 _ _).mp
      use f x, (hg _).2, (hf _).2
    · ext y
      apply (h2 _ _).mp
      use g y, (hf (g y)).2, (hg y).2
  · rintro ⟨f, rfl⟩
    apply graphFunctor.map_isIso

section Opposite
open Opposite

/-- The argument-swap isomorphism from `RelCat` to its opposite. -/
def opFunctor : RelCat ⥤ RelCatᵒᵖ where
  obj X := op X
  map {_ _} r := .op <| .ofRel r.rel.inv
  map_id X := by
    congr
    simp only [unop_op, RelCat.Hom.rel_id]
    ext x y
    exact Eq.comm
  map_comp {X Y Z} f g := by
    unfold Category.opposite
    congr
    ext x y
    apply exists_congr
    exact fun a => And.comm

/-- The other direction of `opFunctor`. -/
def unopFunctor : RelCatᵒᵖ ⥤ RelCat where
  obj X := unop X
  map {_ _} r := .ofRel r.unop.rel.inv

@[simp] theorem opFunctor_comp_unopFunctor_eq :
    Functor.comp opFunctor unopFunctor = Functor.id _ := rfl

@[simp] theorem unopFunctor_comp_opFunctor_eq :
    Functor.comp unopFunctor opFunctor = Functor.id _ := rfl

/-- `RelCat` is self-dual: The map that swaps the argument order of a
    relation induces an equivalence between `RelCat` and its opposite. -/
@[simps]
def opEquivalence : Equivalence RelCat RelCatᵒᵖ where
  functor := opFunctor
  inverse := unopFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance : opFunctor.IsEquivalence := by
  change opEquivalence.functor.IsEquivalence
  infer_instance

instance : unopFunctor.IsEquivalence := by
  change opEquivalence.inverse.IsEquivalence
  infer_instance

end Opposite

end RelCat

end CategoryTheory
