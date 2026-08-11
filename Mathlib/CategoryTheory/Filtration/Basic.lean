/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simone Melchiorre Chiarello, Matteo Cipollina
-/

module

public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Filtrations

In this file, a filtration on `X` indexed by a category `ι` is defined as a functor
`ι ⥤ MonoOver X`.

We also define the category of filtered objects, strict morphisms (pullback squares at each level),
and graded pieces (as cokernels) bundled as a functor out of `ComposableArrows ι 1`.

## Implementation notes

We model a filtration as a functor to `MonoOver X` so that it is functorial in the index category.
This also makes it easy to compare with other constructions indexed by morphisms in `ι`, via
`ComposableArrows ι 1`.

## References

* [P. Deligne, *Théorie de Hodge : II*][deligne_hodge2]
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- A filtration on `X` indexed by `ι`, as a functor `ι ⥤ MonoOver X`. -/
@[ext]
structure Filtration (X : C) (ι : Type*) [Category ι] where
  /-- The underlying functor `ι ⥤ MonoOver X`. -/
  toMonoOver : ι ⥤ MonoOver X

namespace Filtration

variable {X : C} {ι : Type*} [Category ι]

/-- The object at index `i` (domain of the mono into `X`). -/
abbrev obj (F : Filtration X ι) (i : ι) : C :=
  (F.toMonoOver.obj i).obj.left

/-- The underlying diagram in `C` obtained by forgetting `MonoOver`. -/
abbrev diagram (F : Filtration X ι) : ι ⥤ C :=
  { obj := fun i ↦ F.obj i
    map := fun f ↦ (F.toMonoOver.map f).hom.left
    map_id := by simp
    map_comp := by simp }

@[simp]
lemma diagram_obj (F : Filtration X ι) (i : ι) :
    F.diagram.obj i = (F.toMonoOver.obj i).obj.left := rfl

@[simp]
lemma diagram_map (F : Filtration X ι) {i j : ι} (f : i ⟶ j) :
    F.diagram.map f = (F.toMonoOver.map f).hom.left := rfl

/-- The structure map (a monomorphism) `F.obj i ⟶ X`. -/
abbrev inj (F : Filtration X ι) (i : ι) : F.obj i ⟶ X :=
  (F.toMonoOver.obj i).obj.hom

@[simp]
lemma inj_eq (F : Filtration X ι) (i : ι) :
    F.inj i = (F.toMonoOver.obj i).obj.hom := rfl

end Filtration

/-- A filtered object: an object equipped with a filtration. -/
@[ext]
structure FilteredObject (C : Type u) [Category.{v} C] (ι : Type*) [Category ι] where
  /-- The underlying object. -/
  X : C
  /-- The filtration on `X`. -/
  filtration : Filtration X ι

namespace FilteredObject

instance (ι : Type*) [Category ι] : CoeOut (FilteredObject C ι) C where
  coe A := A.X

variable {ι : Type*} [Category ι]

/-- The filtration diagram in `C`. -/
abbrev filtrationDiagram (F : FilteredObject C ι) : ι ⥤ C :=
  F.filtration.diagram

/-- Morphisms of filtered objects: a morphism on objects and a compatible natural transformation
between the filtration diagrams. -/
@[ext]
structure Hom (F G : FilteredObject C ι) where
  /-- The underlying morphism on objects. -/
  hom : F.X ⟶ G.X
  /-- The levelwise maps between filtration steps, natural in the index. -/
  natTrans : F.filtration.diagram ⟶ G.filtration.diagram
  /-- Commutativity with injections into the underlying objects. -/
  comm (i : ι) : natTrans.app i ≫ G.filtration.inj i = F.filtration.inj i ≫ hom := by
    cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The category structure on filtered objects. -/
@[simps! id_hom id_natTrans comp_hom comp_natTrans]
instance : Category (FilteredObject C ι) where
  Hom F G := Hom F G
  id F :=
    { hom := 𝟙 _
      natTrans := 𝟙 _
      comm := by
        intro i
        simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      natTrans := f.natTrans ≫ g.natTrans
      comm := by
        intro i
        dsimp only [Filtration.diagram, Filtration.inj, Filtration.obj]
        rw [NatTrans.comp_app]
        rw [Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc] }
  id_comp f := by
    apply Hom.ext <;> simp
  comp_id f := by
    apply Hom.ext <;> simp
  assoc f g h := by
    apply Hom.ext <;> simp [Category.assoc]

@[simp]
lemma hom_id (F : FilteredObject C ι) : (𝟙 F : F ⟶ F).hom = 𝟙 _ := rfl

@[simp]
lemma hom_comp {F G H : FilteredObject C ι} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
lemma natTrans_id (F : FilteredObject C ι) : (𝟙 F : F ⟶ F).natTrans = 𝟙 _ := rfl

@[simp]
lemma natTrans_comp {F G H : FilteredObject C ι} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).natTrans = f.natTrans ≫ g.natTrans := rfl

/-- Strictness of a filtered morphism: each compatibility square is a pullback. -/
class IsStrictHom {F G : FilteredObject C ι} (f : F ⟶ G) : Prop where
  /-- The square at each filtration step is a pullback square. -/
  isPullback (i : ι) :
    IsPullback (f.natTrans.app i) (F.filtration.inj i) (G.filtration.inj i) f.hom

instance (F : FilteredObject C ι) : IsStrictHom (𝟙 F) where
  isPullback _ := IsPullback.of_id_fst

instance {F G H : FilteredObject C ι} (f : F ⟶ G) (g : G ⟶ H)
    [IsStrictHom f] [IsStrictHom g] : IsStrictHom (f ≫ g) where
  isPullback i :=
    IsPullback.paste_horiz (IsStrictHom.isPullback (f := f) i)
      (IsStrictHom.isPullback (f := g) i)

/-- The forgetful functor `FilteredObject C ι ⥤ C`. -/
@[simps]
def forget : FilteredObject C ι ⥤ C where
  obj A := A.X
  map f := f.hom
  map_id := by intro A; rfl
  map_comp := by intro A B D f g; rfl

end FilteredObject

namespace FilteredObject

section Compatibility

variable {ι : Type*} [Category ι]
variable (F G : FilteredObject C ι)

/-!
### Compatibility as existence of a natural transformation
-/

/-- Existence of a filtered morphism with underlying map `f`. -/
def CompatibleWith (f : F.X ⟶ G.X) : Prop :=
  ∃ α : F.filtration.diagram ⟶ G.filtration.diagram,
    ∀ i : ι, α.app i ≫ G.filtration.inj i = F.filtration.inj i ≫ f

lemma compatibleWith_iff_exists_hom (f : F.X ⟶ G.X) :
    CompatibleWith (C := C) (F := F) (G := G) f ↔ ∃ φ : F ⟶ G, φ.hom = f := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨{ hom := f
              natTrans := α
              comm := ?_ }, rfl⟩
    intro i
    simpa using (hα i)
  · rintro ⟨φ, rfl⟩
    refine ⟨φ.natTrans, ?_⟩
    intro i
    simp

end Compatibility

end FilteredObject

namespace Filtration

open Opposite

/-- A decreasing `ℤ`-filtration on `X` is a filtration indexed by `ℤᵒᵖ`. -/
abbrev DecFiltration (X : C) : Type _ := Filtration X (ℤᵒᵖ)

namespace DecFiltration

variable {X : C}

/-- The translation functor `ℤᵒᵖ ⥤ ℤᵒᵖ` sending `n` to `n + k`. -/
noncomputable def shiftFunctor (k : ℤ) : (ℤᵒᵖ) ⥤ (ℤᵒᵖ) where
  obj n := Opposite.op (k + Opposite.unop n)
  map {i j} f := by
    have hij : Opposite.unop j ≤ Opposite.unop i := by
      simpa using (show Opposite.unop j ≤ Opposite.unop i from leOfHom f.unop)
    simpa [add_comm, add_left_comm, add_assoc] using (homOfLE (add_le_add_left hij k)).op
  map_id := by
    intro i
    apply Subsingleton.elim
  map_comp := by
    intro i j l f g
    apply Subsingleton.elim

/-- `shiftFunctor` on objects. -/
@[simp]
lemma shiftFunctor_obj (k : ℤ) (n : ℤᵒᵖ) :
    (shiftFunctor k).obj n = Opposite.op (k + Opposite.unop n) := rfl

/-- Shift a decreasing `ℤ`-filtration. -/
noncomputable def shift (F : DecFiltration (C := C) X) (k : ℤ) : DecFiltration (C := C) X where
  toMonoOver := shiftFunctor k ⋙ F.toMonoOver

/-- The canonical inclusion map `F^{n+1} ⟶ F^n` between successive steps. -/
noncomputable def succHom (F : DecFiltration (C := C) X) (n : ℤ) :
    (F.obj (Opposite.op (n + 1))) ⟶ (F.obj (Opposite.op n)) := by
  exact
    (F.toMonoOver.map
        ((homOfLE (show n ≤ n + 1 from
            le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))).op)).hom.left

@[simp, reassoc]
lemma succHom_comp_inj (F : DecFiltration (C := C) X) (n : ℤ) :
    succHom (C := C) (X := X) F n ≫ F.inj (Opposite.op n) =
      F.inj (Opposite.op (n + 1)) := by
  simp [succHom, Filtration.inj]

section GradedZ

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The graded piece `Gr^n(X) := F^n / F^{n+1}`, defined as a cokernel.
See [deligne_hodge2, §1.1.7]. -/
noncomputable def gr (F : DecFiltration (C := C) X) (n : ℤ) : C :=
  cokernel (succHom (C := C) (X := X) F n)

/-- The canonical projection `F^n ⟶ Gr^n` (the cokernel map). -/
noncomputable def grπ (F : DecFiltration (C := C) X) (n : ℤ) :
    (F.obj (Opposite.op n)) ⟶ F.gr (C := C) (X := X) n :=
  cokernel.π (succHom (C := C) (X := X) F n)

@[simp, reassoc]
lemma succHom_grπ (F : DecFiltration (C := C) X) (n : ℤ) :
    succHom (C := C) (X := X) F n ≫ F.grπ (C := C) (X := X) n = 0 := by
  exact cokernel.condition _

end GradedZ

end DecFiltration

section Graded

variable {ι : Type*} [Category ι] {X : C}
variable [HasZeroMorphisms C] [HasCokernels C]

/-- The map in `C` associated to `S : ComposableArrows ι 1`. -/
noncomputable def grMap (F : Filtration X ι) (S : ComposableArrows ι 1) :
    F.obj S.left ⟶ F.obj S.right :=
  (F.toMonoOver.map S.hom).hom.left

/-- The graded piece attached to `S : ComposableArrows ι 1`. -/
noncomputable def gr (F : Filtration X ι) (S : ComposableArrows ι 1) : C :=
  cokernel (grMap (C := C) F S)

/-- The canonical projection `F.obj S.right ⟶ F.gr S`. -/
noncomputable def grπ (F : Filtration X ι) (S : ComposableArrows ι 1) :
    F.obj S.right ⟶ F.gr (C := C) (X := X) S :=
  cokernel.π (grMap (C := C) F S)

@[simp, reassoc]
lemma grMap_grπ (F : Filtration X ι) (S : ComposableArrows ι 1) :
    grMap (C := C) F S ≫ grπ (C := C) F S = 0 := by
  exact cokernel.condition _

/-- The graded pieces of a filtration, as a functor `ComposableArrows ι 1 ⥤ C`. -/
noncomputable def grFunctor (F : Filtration X ι) : ComposableArrows ι 1 ⥤ C where
  obj S := F.gr (C := C) (X := X) S
  map {S T} φ := by
    classical
    let l : S.left ⟶ T.left := φ.app 0
    let r : S.right ⟶ T.right := φ.app 1
    refine cokernel.map (grMap (C := C) F S) (grMap (C := C) F T)
      ((F.toMonoOver.map l).hom.left) ((F.toMonoOver.map r).hom.left) ?_
    have hι : S.hom ≫ r = l ≫ T.hom := by
      simp [CategoryTheory.ComposableArrows.hom, l, r]
    change (F.toMonoOver.map S.hom).hom.left ≫ (F.toMonoOver.map r).hom.left =
      (F.toMonoOver.map l).hom.left ≫ (F.toMonoOver.map T.hom).hom.left
    simpa [Functor.map_comp, Category.assoc] using
      congrArg (fun k => (F.toMonoOver.map k).hom.left) hι
  map_id := by
    intro S
    apply coequalizer.hom_ext
    have hid : (F.toMonoOver.map (𝟙 (S.obj 1))).hom.left = 𝟙 _ := by
      simp
    simp only [coequalizer_as_cokernel, Nat.reduceAdd, Fin.isValue, NatTrans.id_app,
      cokernel.π_desc]
    rw [hid]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  map_comp := by
    intro S T U φ ψ
    apply coequalizer.hom_ext
    dsimp only [gr, grπ]
    rw (occs := .pos [1]) [cokernel.π_desc]
    change (F.toMonoOver.map ((φ ≫ ψ).app 1)).hom.left ≫
      cokernel.π (grMap (C := C) F U) = _
    rw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc]
    rw [NatTrans.comp_app, F.toMonoOver.map_comp]
    simp [Category.assoc]

@[simp]
lemma grFunctor_obj (F : Filtration X ι) (S : ComposableArrows ι 1) :
    (grFunctor (C := C) (X := X) F).obj S = F.gr (C := C) (X := X) S := rfl

@[simp, reassoc]
lemma grπ_grFunctor_map (F : Filtration X ι) {S T : ComposableArrows ι 1} (φ : S ⟶ T) :
    grπ (C := C) (X := X) F S ≫ (grFunctor (C := C) (X := X) F).map φ =
      (F.toMonoOver.map (φ.app 1)).hom.left ≫ grπ (C := C) (X := X) F T := by
  exact cokernel.π_desc _ _ _

end Graded

end Filtration

end CategoryTheory
