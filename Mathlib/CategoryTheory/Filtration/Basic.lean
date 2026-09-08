/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simone M. Chiarello, Matteo Cipollina
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Filtrations

In this file, a filtration on `X` indexed by a category `I` is defined as a functor
`I ⥤ MonoOver X`.

We also define the category of filtered objects and strict morphisms, characterized by
pullback squares at each filtration level.

## Implementation notes

We model a filtration as a functor to `MonoOver X`, so that the filtration steps and their
inclusions into `X` are bundled together and functorial in the index category.

## References

* [P. Deligne, *Théorie de Hodge : II*][deligne_hodge2]
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A filtration on `X` indexed by `I`, as a functor `I ⥤ MonoOver X`. -/
structure Filtration (X : C) (I : Type*) [Category I] where
  /-- The underlying functor `I ⥤ MonoOver X`. -/
  toMonoOver : I ⥤ MonoOver X

namespace Filtration

variable {X : C} {I : Type*} [Category I]

/-- The underlying diagram in `C` obtained by forgetting `MonoOver`. -/
@[simps! -isSimp]
abbrev diagram (F : Filtration X I) : I ⥤ C :=
  F.toMonoOver ⋙ MonoOver.forget _ ⋙ Over.forget _

/-- The object at index `i` (domain of the mono into `X`). -/
abbrev obj (F : Filtration X I) (i : I) : C :=
  F.diagram.obj i

/-- The natural transformation from the filtration diagram to the constant underlying object. -/
@[implicit_reducible, simps -isSimp]
def ι (F : Filtration X I) : F.diagram ⟶ (Functor.const _).obj X where
  app i := (F.toMonoOver.obj i).obj.hom

instance (F : Filtration X I) (i : I) : Mono (F.ι.app i) := by
  dsimp [ι_app]
  infer_instance

end Filtration

/-- A filtered object: an object equipped with a filtration. -/
structure FilteredObject (C : Type u) [Category.{v} C] (I : Type*) [Category I] where
  /-- The underlying object. -/
  X : C
  /-- The filtration on `X`. -/
  filtration : Filtration X I

namespace FilteredObject

variable {I : Type*} [Category I]

/-- The filtration diagram in `C`. -/
abbrev filtrationDiagram (F : FilteredObject C I) : I ⥤ C :=
  F.filtration.diagram

/-- Morphisms of filtered objects: a morphism on objects and a compatible natural transformation
between the filtration diagrams. -/
@[ext]
structure Hom (F G : FilteredObject C I) where
  /-- The underlying morphism on objects. -/
  hom : F.X ⟶ G.X
  /-- The levelwise maps between filtration steps, natural in the index. -/
  natTrans : F.filtration.diagram ⟶ G.filtration.diagram
  /-- Commutativity with the structure maps into the underlying objects. -/
  comm (i : I) : natTrans.app i ≫ G.filtration.ι.app i = F.filtration.ι.app i ≫ hom := by
    cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The category structure on filtered objects. -/
@[simps! id_hom id_natTrans comp_hom comp_natTrans]
instance : Category (FilteredObject C I) where
  Hom := Hom
  id _ := .mk (𝟙 _) (𝟙 _)
  comp f g := .mk (f.hom ≫ g.hom) (f.natTrans ≫ g.natTrans)

@[ext]
lemma hom_ext {F G : FilteredObject C I} {f g : F ⟶ G} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h (by
    ext i
    simp [← cancel_mono (G.filtration.ι.app i), h])

/-- Constructor for morphisms of filtered objects. -/
@[implicit_reducible, simps]
def homMk {F G : FilteredObject C I}
    (hom : F.X ⟶ G.X)
    (app : ∀ (i : I), F.filtration.obj i ⟶ G.filtration.obj i)
    (comm : ∀ (i : I), app i ≫ G.filtration.ι.app i =
      F.filtration.ι.app i ≫ hom := by cat_disch) :
    F ⟶ G where
  hom := hom
  natTrans.app := app
  natTrans.naturality i j f := by
    rw [← cancel_mono (G.filtration.ι.app j)]
    simp [comm, dsimp% G.filtration.ι.naturality f,
      dsimp% F.filtration.ι.naturality_assoc f]
  comm := comm

/-- Constructor for isomorphisms of filtered objects. -/
@[implicit_reducible, simps]
def isoMk {F G : FilteredObject C I}
    (iso : F.X ≅ G.X)
    (app : ∀ (i : I), F.filtration.obj i ≅ G.filtration.obj i)
    (comm : ∀ (i : I), (app i).hom ≫ G.filtration.ι.app i =
      F.filtration.ι.app i ≫ iso.hom := by cat_disch) :
    F ≅ G where
  hom := homMk iso.hom (fun i ↦ (app i).hom) comm
  inv := homMk iso.inv (fun i ↦ (app i).inv) (fun i ↦ by
    rw [← cancel_mono iso.hom, Category.assoc, ← comm]
    simp)

/-- Strictness of a filtered morphism: each compatibility square is a pullback. -/
class IsStrictHom {F G : FilteredObject C I} (f : F ⟶ G) : Prop where
  /-- The square at each filtration step is a pullback square. -/
  isPullback (f) (i : I) :
    IsPullback (f.natTrans.app i) (F.filtration.ι.app i) (G.filtration.ι.app i) f.hom

instance (F : FilteredObject C I) : IsStrictHom (𝟙 F) where
  isPullback _ := IsPullback.of_id_fst

instance {F G H : FilteredObject C I} (f : F ⟶ G) (g : G ⟶ H)
    [IsStrictHom f] [IsStrictHom g] : IsStrictHom (f ≫ g) where
  isPullback i :=
    (IsStrictHom.isPullback f i).paste_horiz (IsStrictHom.isPullback g i)

variable (C I) in
/-- The morphism property of strict morphisms of filtered objects. -/
abbrev isStrictHom : MorphismProperty (FilteredObject C I) :=
  fun _ _ f ↦ IsStrictHom f

instance : (isStrictHom C I).IsMultiplicative where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

/-- The forgetful functor `FilteredObject C I ⥤ C`. -/
@[implicit_reducible, simps]
def forget : FilteredObject C I ⥤ C where
  obj A := A.X
  map f := f.hom

end FilteredObject

end CategoryTheory
