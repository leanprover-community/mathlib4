/-
Copyright (c) 2026 Matteo Cipollina,Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!

## Filtered objects in an abelian category (Deligne, *Théorie de Hodge II*, §1.1).

This file provides:
* Decreasing ℤ-indexed filtrations on objects of an abelian category.
* Finiteness (boundedness) of filtrations.
* Shifted filtrations.
* Induced filtrations on subobjects.
* Quotient filtrations on cokernels of monomorphisms.
* Associated graded pieces `Gr`.
* The category of filtered objects and its forgetful functor.

The definitions follow Deligne (1.1.2), (1.1.4), (1.1.5), (1.1.7), (1.1.8).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- A decreasing (i.e. antitone) ℤ-indexed filtration on an object `A`.

This matches Deligne (1.1.2) ("filtration décroissante") where the condition is
`m ≤ n ⇒ F n ≤ F m`.
-/
structure DecFiltration (A : C) where
  /-- The `n`-th step `F n` of the filtration, as a subobject of `A`. -/
  F : ℤ → Subobject A
  /-- The filtration is decreasing: `n ≤ m ⇒ F m ≤ F n`. -/
  antitone' : Antitone F

attribute [simp] DecFiltration.antitone'

namespace DecFiltration

variable {A : C}

/-- Coercion from a filtration to its underlying function `ℤ → Subobject A`. -/
instance : CoeFun (DecFiltration A) (fun _ => ℤ → Subobject A) where
  coe F := F.F

lemma antitone (F : DecFiltration A) : Antitone (F : ℤ → Subobject A) :=
  F.antitone'

/-- A filtration is *finite* if it is bounded above by `⊤` and bounded below by `⊥`.

This is Deligne (1.1.4).
-/
def IsFinite [Abelian C] (F : DecFiltration A) : Prop :=
  ∃ a b : ℤ, (∀ n : ℤ, n ≤ a → F n = ⊤) ∧ (∀ n : ℤ, b ≤ n → F n = ⊥)

/-- Shift a decreasing filtration by an integer `k`:
`(F.shift k) n = F (n + k)`.

This corresponds to Deligne's shifted filtrations (1.1.2).
-/
def shift (F : DecFiltration A) (k : ℤ) : DecFiltration A where
  F n := F (n + k)
  antitone' := by
    intro m n h
    exact F.antitone (by omega)

@[simp] lemma shift_apply (F : DecFiltration A) (k n : ℤ) : F.shift k n = F (n + k) := rfl

/-- The associated graded piece `Gr^n(A) = F^n(A) / F^{n+1}(A)`.

This is Deligne (1.1.7) (with ℤ-indexing).

We define it as the cokernel of the canonical monomorphism `F(n+1) → F(n)` induced
by the inequality `F(n+1) ≤ F(n)`.
-/
noncomputable def gr [Abelian C] (F : DecFiltration A) (n : ℤ) : C :=
  let le' : F (n + 1) ≤ F n := F.antitone (by omega)
  cokernel ((F (n + 1)).ofLE (F n) le')

/-- The canonical inclusion `F^{n+1}(A) ⟶ F^n(A)`. -/
noncomputable def grι (F : DecFiltration A) (n : ℤ) :
    (F (n + 1) : C) ⟶ (F n : C) :=
  (F (n + 1)).ofLE (F n) (F.antitone (by omega))

/-- The canonical projection `F^n(A) ⟶ Gr_F^n(A) = F^n(A)/F^{n+1}(A)`. -/
noncomputable def grπ [Abelian C] (F : DecFiltration A) (n : ℤ) : (F n : C) ⟶ F.gr n := by
  classical
  simpa [DecFiltration.gr, grι] using cokernel.π (grι (A := A) F n)

@[simp, reassoc] lemma grι_grπ [Abelian C] (F : DecFiltration A) (n : ℤ) :
    grι (A := A) F n ≫ grπ (A := A) F n = 0 := by
  classical
  simp [grι, grπ, DecFiltration.gr]

/-- A map out of `Gr_F^n(A)` induced by a map out of `F^n(A)` killing `F^{n+1}(A)`. -/
noncomputable def grDesc [Abelian C] (F : DecFiltration A) (n : ℤ) {X : C}
    (f : (F n : C) ⟶ X)
    (hf : grι (A := A) F n ≫ f = 0) : F.gr n ⟶ X := by
  classical
  simpa [DecFiltration.gr, grι] using cokernel.desc (grι (A := A) F n) f hf

@[simp, reassoc] lemma grπ_grDesc [Abelian C] (F : DecFiltration A) (n : ℤ) {X : C}
    (f : (F n : C) ⟶ X) (hf : grι (A := A) F n ≫ f = 0) :
    grπ (A := A) F n ≫ grDesc (A := A) F n f hf = f := by
  classical
  simp [grDesc, grπ]

/-- The induced filtration on a subobject `X ⊆ A`.

Deligne (1.1.8) says the induced filtration is characterized by strictness of the
inclusion; categorically it is computed as pullback along the monomorphism `X → A`.
-/
noncomputable def induced [Abelian C] (F : DecFiltration A) (X : Subobject A) :
    DecFiltration (X : C) where
  F n := (Subobject.pullback X.arrow).obj (F n)
  antitone' := by
    intro m n h
    exact (Subobject.pullback X.arrow).monotone (F.antitone h)

@[simp] lemma induced_apply [Abelian C] (F : DecFiltration A) (X : Subobject A) (n : ℤ) :
    F.induced X n = (Subobject.pullback X.arrow).obj (F n) := rfl

/-- The quotient object `A/X` for a subobject `X ⊆ A` in an abelian category.

We define it as the cokernel of the monomorphism `X → A`.
-/
noncomputable def quotientObj [Abelian C] (X : Subobject A) : C :=
  cokernel X.arrow

/-- The quotient map `A → A/X`. -/
noncomputable def quotientπ [Abelian C] (X : Subobject A) : A ⟶ quotientObj X :=
  cokernel.π X.arrow

/-- The quotient filtration on `A/X`.

Deligne (1.1.8) defines the quotient filtration as the unique filtration making the
projection strict; abstractly it is given by mapping each step along the quotient map.
-/
noncomputable def quotient [Abelian C] (F : DecFiltration A) (X : Subobject A) :
    DecFiltration (quotientObj X) where
  F n := Subobject.mk (image.ι ((F n).arrow ≫ quotientπ X))
  antitone' := by
    intro m n h
    have hle : F n ≤ F m := F.antitone h
    refine Subobject.mk_le_mk_of_comm (image.lift
      { I := image ((F m).arrow ≫ quotientπ X)
        m := image.ι ((F m).arrow ≫ quotientπ X)
        e := (F n).ofLE (F m) hle ≫ factorThruImage ((F m).arrow ≫ quotientπ X)
        fac := by rw [Category.assoc, image.fac, ← Category.assoc, Subobject.ofLE_arrow] }) ?_
    exact image.lift_fac _

@[simp] lemma quotient_apply [Abelian C] (F : DecFiltration A)
    (X : Subobject A) (n : ℤ) :
    F.quotient X n = Subobject.mk (image.ι ((F n).arrow ≫ quotientπ X)) := rfl

end DecFiltration

/-- A filtered object of a category: an object equipped with a decreasing ℤ-filtration.

This is Deligne's "objet filtré" (1.1.2).
-/
structure FilteredObject (C : Type u) [Category.{v} C] where
  /-- The underlying object. -/
  obj : C
  /-- The decreasing filtration on `obj`. -/
  F : DecFiltration obj

namespace FilteredObject

instance : Coe (FilteredObject C) C where
  coe X := X.obj

/-- The image of a subobject under a morphism, defined via image factorization.

For `S : Subobject A` and `f : A ⟶ B`, this is the subobject of `B` given by
the image of the composite `S.arrow ≫ f`.
-/
noncomputable def imageSubobject [Abelian C] {A B : C} (f : A ⟶ B) (S : Subobject A) :
    Subobject B :=
  Subobject.mk (image.ι (S.arrow ≫ f))

lemma imageSubobject_mono [Abelian C] {A B : C} (f : A ⟶ B) :
    Monotone (imageSubobject f : Subobject A → Subobject B) := by
  intro S T hle
  dsimp [imageSubobject]
  refine Subobject.mk_le_mk_of_comm (image.lift
    { I := image (T.arrow ≫ f)
      m := image.ι (T.arrow ≫ f)
      e := S.ofLE T hle ≫ factorThruImage (T.arrow ≫ f)
      fac := by rw [Category.assoc, image.fac, ← Category.assoc, Subobject.ofLE_arrow] }) ?_
  exact image.lift_fac _

/-- Morphisms of filtered objects (Deligne (1.1.5)).

A morphism `f : (A,F) → (B,G)` is a morphism `A → B` such that for all `n` the image of
`F n` lands inside `G n`.
-/
structure Hom [Abelian C] (A B : FilteredObject C) where
  /-- Underlying morphism in `C`. -/
  hom : (A : C) ⟶ (B : C)
  /-- Filtration-compatibility: `f(F^n A) ⊆ F^n B`. -/
  compat : ∀ n : ℤ, imageSubobject hom (A.F n) ≤ B.F n

attribute [simp] Hom.compat

@[ext] lemma Hom.ext [Abelian C] {A B : FilteredObject C} (f g : Hom A B)
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; simp_all

/-- Identity morphism of a filtered object. -/
noncomputable def id [Abelian C] (A : FilteredObject C) : Hom A A where
  hom := 𝟙 A.obj
  compat := by
    intro n
    dsimp only [imageSubobject]
    have hf : (A.F n).arrow ≫ 𝟙 A.obj = (A.F n).arrow := Category.comp_id _
    haveI hmono : Mono ((A.F n).arrow ≫ 𝟙 A.obj) := by rw [hf]; infer_instance
    haveI : Mono (factorThruImage ((A.F n).arrow ≫ 𝟙 A.obj)) :=
      mono_of_mono_fac (image.fac _)
    haveI : IsIso (factorThruImage ((A.F n).arrow ≫ 𝟙 A.obj)) :=
      isIso_of_mono_of_epi _
    apply Subobject.mk_le_of_comm (inv (factorThruImage ((A.F n).arrow ≫ 𝟙 A.obj)))
    rw [IsIso.inv_comp_eq, image.fac, hf]

/-- Key lemma: imageSubobject (f ≫ g) S ≤ imageSubobject g (imageSubobject f S). -/
lemma imageSubobject_comp_le [Abelian C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (S : Subobject A) :
    imageSubobject (f ≫ g) S ≤ imageSubobject g (imageSubobject f S) := by
  dsimp only [imageSubobject]
  let T := Subobject.mk (image.ι (S.arrow ≫ f))
  let sfg := S.arrow ≫ f ≫ g
  let sf := S.arrow ≫ f
  let Tg := T.arrow ≫ g
  have key : (Subobject.underlyingIso (image.ι sf)).inv ≫ T.arrow = image.ι sf :=
    Subobject.underlyingIso_arrow _
  have fac_eq : (factorThruImage sf ≫ (Subobject.underlyingIso (image.ι sf)).inv ≫
      factorThruImage Tg) ≫ image.ι Tg = sfg := by
    rw [Category.assoc, Category.assoc, image.fac]
    rw [← Category.assoc (Subobject.underlyingIso _).inv, key]
    rw [← Category.assoc, image.fac]
    aesop
  let MF : MonoFactorisation sfg := {
    I := image Tg
    m := image.ι Tg
    e := factorThruImage sf ≫ (Subobject.underlyingIso (image.ι sf)).inv ≫ factorThruImage Tg
    fac := fac_eq
  }
  refine Subobject.mk_le_of_comm
    (image.lift MF ≫ (Subobject.underlyingIso (image.ι Tg)).inv) ?_
  rw [Category.assoc, Subobject.underlyingIso_arrow, image.lift_fac]

/-- Composition of morphisms of filtered objects. -/
noncomputable def comp [Abelian C] {A B D : FilteredObject C} (f : Hom A B) (g : Hom B D) :
    Hom A D where
  hom := f.hom ≫ g.hom
  compat := by
    intro n
    calc imageSubobject (f.hom ≫ g.hom) (A.F n)
        ≤ imageSubobject g.hom (imageSubobject f.hom (A.F n)) := imageSubobject_comp_le _ _ _
      _ ≤ imageSubobject g.hom (B.F n) := imageSubobject_mono g.hom (f.compat n)
      _ ≤ D.F n := g.compat n

noncomputable instance [Abelian C] : Category (FilteredObject C) where
  Hom A B := Hom A B
  id A := id A
  comp f g := comp f g
  id_comp := by intro A B f; ext; simp only [FilteredObject.id, FilteredObject.comp,
    Category.id_comp]
  comp_id := by intro A B f; ext; simp only [FilteredObject.id, FilteredObject.comp,
    Category.comp_id]
  assoc := by intro A B D E f g h; ext; simp only [FilteredObject.comp, Category.assoc]

lemma hom_id [Abelian C] (A : FilteredObject C) : (𝟙 A : A ⟶ A).hom = 𝟙 A.obj := rfl

@[simp] lemma hom_comp [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The forgetful functor `FilteredObject C ⥤ C`. -/
@[simps] noncomputable def forget [Abelian C] : FilteredObject C ⥤ C where
  obj A := A.obj
  map f := f.hom
  map_id := by intro A; rfl
  map_comp := by intro A B D f g; rfl

end FilteredObject

end CategoryTheory
