/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
## Filtrations

A filtration on `X` indexed by `ι` is a functor `ι ⥤ MonoOver X`.

We also define the category of filtered objects and, for decreasing `ℤ`-filtrations (`ℤᵒᵖ`),
basic operations (boundedness, shift, graded pieces).
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

/-- The underlying diagram in `C` obtained by forgetting `MonoOver`. -/
abbrev diagram (F : Filtration X ι) : ι ⥤ C :=
  F.toMonoOver ⋙ MonoOver.forget _ ⋙ Over.forget _

@[simp]
lemma diagram_obj (F : Filtration X ι) (i : ι) :
    F.diagram.obj i = (F.toMonoOver.obj i).obj.left := rfl

@[simp]
lemma diagram_map (F : Filtration X ι) {i j : ι} (f : i ⟶ j) :
    F.diagram.map f = (F.toMonoOver.map f).hom.left := rfl

/-- The object at index `i` (domain of the mono into `X`). -/
abbrev obj (F : Filtration X ι) (i : ι) : C :=
  (F.toMonoOver.obj i).obj.left

/-- The structure map (a monomorphism) `F.obj i ⟶ X`. -/
abbrev inj (F : Filtration X ι) (i : ι) : F.obj i ⟶ X :=
  (F.toMonoOver.obj i).obj.hom

@[simp]
lemma inj_eq (F : Filtration X ι) (i : ι) :
    F.inj i = (F.toMonoOver.obj i).obj.hom := rfl

/-- The `i`-th filtration step as a subobject of `X`. -/
noncomputable def subobject (F : Filtration X ι) (i : ι) : Subobject X :=
  Subobject.mk (F.inj i)

@[simp, reassoc]
lemma subobject_arrow_eq (F : Filtration X ι) (i : ι) :
    (Subobject.mk (F.toMonoOver.obj i).obj.hom).arrow = (F.subobject i).arrow := by
  rfl

/-- A morphism in the index category induces an inclusion of steps. -/
lemma subobject_le_of_hom (F : Filtration X ι) {i j : ι} (f : i ⟶ j) :
    F.subobject i ≤ F.subobject j := by
  classical
  refine Subobject.mk_le_mk_of_comm ((F.toMonoOver.map f).hom.left) ?_
  simp [Filtration.inj]

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
@[simps id_hom id_natTrans comp_hom comp_natTrans]
instance : Category (FilteredObject C ι) where
  Hom F G := Hom F G
  id F :=
    { hom := 𝟙 _
      natTrans := 𝟙 _ }
  comp f g :=
    { hom := f.hom ≫ g.hom
      natTrans := f.natTrans ≫ g.natTrans }

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

section Images

variable [HasImages C]

/-- The image of a subobject under a morphism. -/
noncomputable def imageSubobject {A B : C} (f : A ⟶ B) (S : Subobject A) : Subobject B :=
  Subobject.mk (image.ι (S.arrow ≫ f))

lemma imageSubobject_mono {A B : C} (f : A ⟶ B) :
    Monotone (imageSubobject (C := C) f) := by
  intro S T hle
  dsimp [imageSubobject]
  refine Subobject.mk_le_mk_of_comm (image.lift
    { I := image (T.arrow ≫ f)
      m := image.ι (T.arrow ≫ f)
      e := S.ofLE T hle ≫ factorThruImage (T.arrow ≫ f)
      fac := by
        rw [Category.assoc, image.fac, ← Category.assoc, Subobject.ofLE_arrow] }) ?_
  exact image.lift_fac _

/-- A basic functoriality inequality for `imageSubobject`. -/
lemma imageSubobject_comp_le {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (S : Subobject A) :
    imageSubobject (C := C) (f ≫ g) S ≤
      imageSubobject (C := C) g (imageSubobject (C := C) f S) := by
  dsimp only [imageSubobject]
  let T := Subobject.mk (image.ι (S.arrow ≫ f))
  let sfg := S.arrow ≫ f ≫ g
  let sf := S.arrow ≫ f
  let Tg := T.arrow ≫ g
  have key : (Subobject.underlyingIso (image.ι sf)).inv ≫ T.arrow = image.ι sf :=
    Subobject.underlyingIso_arrow _
  have fac_eq :
      (factorThruImage sf ≫ (Subobject.underlyingIso (image.ι sf)).inv ≫ factorThruImage Tg) ≫
          image.ι Tg =
        sfg := by
    rw [Category.assoc, Category.assoc, image.fac]
    rw [← Category.assoc (Subobject.underlyingIso _).inv, key]
    rw [← Category.assoc, image.fac]
    aesop
  let MF : MonoFactorisation sfg :=
    { I := image Tg
      m := image.ι Tg
      e := factorThruImage sf ≫ (Subobject.underlyingIso (image.ι sf)).inv ≫ factorThruImage Tg
      fac := fac_eq }
  refine Subobject.mk_le_of_comm
    (image.lift MF ≫ (Subobject.underlyingIso (image.ι Tg)).inv) ?_
  rw [Category.assoc, Subobject.underlyingIso_arrow, image.lift_fac]

end Images

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

section DeligneCompatibility

variable [HasImages C]
variable {ι : Type*} [Category ι]
variable {F G : FilteredObject C ι}

/-!
### Deligne-style filtration preservation (via images)
-/

/-- Deligne-style filtration preservation for a morphism `f : F.X ⟶ G.X`. -/
def PreservesFiltration (f : F.X ⟶ G.X) : Prop :=
  ∀ i : ι,
    imageSubobject (C := C) f (F.filtration.subobject i) ≤ G.filtration.subobject i

/-- A morphism of filtered objects induces Deligne-style filtration preservation. -/
lemma Hom.preservesFiltration (f : F ⟶ G) :
    PreservesFiltration (C := C) (F := F) (G := G) f.hom := by
  intro i
  classical
  -- Let `S` be the `i`-th filtration subobject of `F.X`.
  set S : Subobject F.X := F.filtration.subobject i
  dsimp [PreservesFiltration, imageSubobject]
  have hS : S.arrow = (Subobject.underlyingIso (F.filtration.inj i)).hom ≫ F.filtration.inj i := by
    simp [S, Filtration.subobject]
  let MF : MonoFactorisation (S.arrow ≫ f.hom) :=
    { I := G.filtration.obj i
      m := G.filtration.inj i
      e := (Subobject.underlyingIso (F.filtration.inj i)).hom ≫ f.natTrans.app i
      fac := by
        simp [hS, Category.assoc, f.comm i] }
  refine Subobject.mk_le_mk_of_comm (image.lift MF) ?_
  exact image.lift_fac MF

end DeligneCompatibility

end FilteredObject

/-
## `ℤ`-indexed specializations

We work with decreasing `ℤ`-filtrations encoded as `Filtration X ℤᵒᵖ`.
-/

namespace Filtration

open Opposite

/-- A decreasing `ℤ`-filtration on `X` is a filtration indexed by `ℤᵒᵖ`. -/
abbrev DecFiltration (X : C) : Type _ := Filtration X (ℤᵒᵖ)

namespace DecFiltration

variable {X : C}

/-- The `n`-th step as a subobject of `X`. -/
noncomputable abbrev step (F : DecFiltration (C := C) X) (n : ℤ) : Subobject X :=
  F.subobject (Opposite.op n)

@[simp]
lemma step_def (F : DecFiltration (C := C) X) (n : ℤ) :
    F.step n = F.subobject (Opposite.op n) := rfl

section Finite

variable [HasZeroObject C] [HasZeroMorphisms C]

/-- Finiteness/boundedness of a decreasing `ℤ`-filtration (Deligne 1.1.4). -/
def IsFinite (F : DecFiltration (C := C) X) : Prop :=
  ∃ a b : ℤ,
    (∀ n : ℤ, n ≤ a → F.step n = ⊤) ∧ (∀ n : ℤ, b ≤ n → F.step n = ⊥)

end Finite

section OfSubobject

/-- Build a decreasing `ℤ`-filtration from an antitone function `ℤ → Subobject X`. -/
noncomputable def ofAntitone (F : ℤ → Subobject X) (hF : Antitone F) :
    DecFiltration (C := C) X :=
by
  classical
  -- We define the functor on the thin category `ℤᵒᵖ`.
  refine { toMonoOver := ?_ }
  refine
    { obj := fun n => MonoOver.mk (X := X) (F (Opposite.unop n)).arrow
      map := fun {i j} f => by
        have hij : Opposite.unop j ≤ Opposite.unop i := by
          simpa using (show Opposite.unop j ≤ Opposite.unop i from leOfHom f.unop)
        have hle : F (Opposite.unop i) ≤ F (Opposite.unop j) := hF hij
        refine MonoOver.homMk ((F (Opposite.unop i)).ofLE (F (Opposite.unop j)) hle) ?_
        simp [MonoOver.mk, MonoOver.arrow, Subobject.ofLE_arrow]
      map_id := by
        intro i
        apply Subsingleton.elim
      map_comp := by
        intro i j k f g
        apply Subsingleton.elim }

@[simp]
lemma ofAntitone_step (F : ℤ → Subobject X) (hF : Antitone F) (n : ℤ) :
    (ofAntitone (C := C) (X := X) F hF).step n = F n := by
  classical
  simp [ofAntitone, DecFiltration.step, Filtration.subobject, Filtration.inj, Subobject.mk_arrow]

end OfSubobject

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

/-- Shift a decreasing `ℤ`-filtration: `(F.shift k).step n = F.step (n + k)`. -/
noncomputable def shift (F : DecFiltration (C := C) X) (k : ℤ) : DecFiltration (C := C) X where
  toMonoOver := shiftFunctor k ⋙ F.toMonoOver

@[simp]
lemma shift_step (F : DecFiltration (C := C) X) (k n : ℤ) :
    (F.shift k).step n = F.step (n + k) := by
  -- By definition, shifting uses `k + n`; rewrite using commutativity of `ℤ`.
  simpa [add_comm] using (show (F.shift k).step n = F.step (k + n) from rfl)

lemma step_le_step_of_le (F : DecFiltration (C := C) X) {n m : ℤ} (h : n ≤ m) :
    F.step m ≤ F.step n := by
  -- A morphism `op m ⟶ op n` in `ℤᵒᵖ` is the opposite of a morphism `n ⟶ m` in `ℤ`.
  simpa [DecFiltration.step] using F.subobject_le_of_hom ((homOfLE h).op)

/-- The steps of a decreasing `ℤ`-filtration form an antitone function. -/
lemma step_antitone (F : DecFiltration (C := C) X) : Antitone F.step := by
  intro n m h
  exact step_le_step_of_le (C := C) (X := X) F h

/-- The canonical inclusion map `F^{n+1} ⟶ F^n` between successive steps. -/
noncomputable def succHom (F : DecFiltration (C := C) X) (n : ℤ) :
    (F.obj (Opposite.op (n + 1))) ⟶ (F.obj (Opposite.op n)) := by
  classical
  -- A morphism `op (n+1) ⟶ op n` in `ℤᵒᵖ` is the opposite of a morphism `n ⟶ n+1` in `ℤ`.
  exact
    (F.toMonoOver.map
        ((homOfLE (show n ≤ n + 1 from
            le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))).op)).hom.left

@[simp, reassoc]
lemma succHom_comp_inj (F : DecFiltration (C := C) X) (n : ℤ) :
    succHom (C := C) (X := X) F n ≫ F.inj (Opposite.op n) =
      F.inj (Opposite.op (n + 1)) := by
  classical
  -- This is the commutativity in `MonoOver X` for the arrow `op (n+1) ⟶ op n`.
  have h :=
    (MonoOver.w (k := F.toMonoOver.map
      ((homOfLE (show n ≤ n + 1 from
        le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))).op)))
  simp [succHom, Filtration.inj]

section Graded

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The graded piece `Gr^n(X) := F^n / F^{n+1}` (Deligne 1.1.7), defined as a cokernel. -/
noncomputable def gr (F : DecFiltration (C := C) X) (n : ℤ) : C :=
  cokernel (succHom (C := C) (X := X) F n)

/-- The canonical projection `F^n ⟶ Gr^n` (the cokernel map). -/
noncomputable def grπ (F : DecFiltration (C := C) X) (n : ℤ) :
    (F.obj (Opposite.op n)) ⟶ F.gr n :=
  cokernel.π (succHom (C := C) (X := X) F n)

@[simp, reassoc]
lemma succHom_grπ (F : DecFiltration (C := C) X) (n : ℤ) :
    succHom (C := C) (X := X) F n ≫ F.grπ n = 0 := by
  simp [DecFiltration.grπ]

end Graded

end DecFiltration

end Filtration

end CategoryTheory
