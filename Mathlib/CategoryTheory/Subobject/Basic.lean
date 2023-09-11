/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison

! This file was ported from Lean 3 source module category_theory.subobject.basic
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Subobject.MonoOver
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Elementwise

/-!
# Subobjects

We define `Subobject X` as the quotient (by isomorphisms) of
`MonoOver X := {f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.

There is a coercion from `Subobject X` back to the ambient category `C`
(using choice to pick a representative), and for `P : Subobject X`,
`P.arrow : (P : C) ⟶ X` is the inclusion morphism.

We provide
* `def pullback [HasPpullbacks C] (f : X ⟶ Y) : Subobject Y ⥤ Subobject X`
* `def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y`
* `def «exists_» [HasImages C] (f : X ⟶ Y) : Subobject X ⥤ Subobject Y`
and prove their basic properties and relationships.
These are all easy consequences of the earlier development
of the corresponding functors for `MonoOver`.

The subobjects of `X` form a preorder making them into a category. We have `X ≤ Y` if and only if
`X.arrow` factors through `Y.arrow`: see `ofLE`/`ofLEMk`/`ofMkLE`/`ofMkLEMk` and
`le_of_comm`. Similarly, to show that two subobjects are equal, we can supply an isomorphism between
the underlying objects that commutes with the arrows (`eq_of_comm`).

See also

* `CategoryTheory.Subobject.factorThru` :
  an API describing factorization of morphisms through subobjects.
* `CategoryTheory.Subobject.lattice` :
  the lattice structures on subobjects.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.

### Implementation note

Currently we describe `pullback`, `map`, etc., as functors.
It may be better to just say that they are monotone functions,
and even avoid using categorical language entirely when describing `Subobject X`.
(It's worth keeping this in mind in future use; it should be a relatively easy change here
if it looks preferable.)

### Relation to pseudoelements

There is a separate development of pseudoelements in `CategoryTheory.Abelian.Pseudoelements`,
as a quotient (but not by isomorphism) of `Over X`.

When a morphism `f` has an image, the image represents the same pseudoelement.
In a category with images `Pseudoelements X` could be constructed as a quotient of `MonoOver X`.
In fact, in an abelian category (I'm not sure in what generality beyond that),
`Pseudoelements X` agrees with `Subobject X`, but we haven't developed this in mathlib yet.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

/-!
We now construct the subobject lattice for `X : C`,
as the quotient by isomorphisms of `mono_over X`.

Since `MonoOver X` is a thin category, we use `ThinSkeleton` to take the quotient.

Essentially all the structure defined above on `MonoOver X` descends to `Subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/


/-- The category of subobjects of `X : C`, defined as isomorphism classes of monomorphisms into `X`.
-/
def Subobject (X : C) :=
  ThinSkeleton (MonoOver X)
#align category_theory.subobject CategoryTheory.Subobject

instance (X : C) : PartialOrder (Subobject X) := by
  dsimp only [Subobject]
  infer_instance

namespace Subobject

-- porting note: made it a def rather than an abbreviation
-- because Lean would make it too transparent
/-- Convenience constructor for a subobject. -/
def mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X :=
  (toThinSkeleton _).obj (MonoOver.mk' f)
#align category_theory.subobject.mk CategoryTheory.Subobject.mk

section

attribute [local ext] CategoryTheory.Comma

protected theorem ind {X : C} (p : Subobject X → Prop)
    (h : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], p (Subobject.mk f)) (P : Subobject X) : p P := by
  apply Quotient.inductionOn'
  intro a
  exact h a.arrow
#align category_theory.subobject.ind CategoryTheory.Subobject.ind

protected theorem ind₂ {X : C} (p : Subobject X → Subobject X → Prop)
    (h : ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g],
      p (Subobject.mk f) (Subobject.mk g))
    (P Q : Subobject X) : p P Q := by
  apply Quotient.inductionOn₂'
  intro a b
  exact h a.arrow b.arrow
#align category_theory.subobject.ind₂ CategoryTheory.Subobject.ind₂

end

/-- Declare a function on subobjects of `X` by specifying a function on monomorphisms with
    codomain `X`. -/
protected def lift {α : Sort _} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
    (h :
      ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] (i : A ≅ B),
        i.hom ≫ g = f → F f = F g) :
    Subobject X → α := fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom)
#align category_theory.subobject.lift CategoryTheory.Subobject.lift

@[simp]
protected theorem lift_mk {α : Sort _} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α) {h A}
    (f : A ⟶ X) [Mono f] : Subobject.lift F h (Subobject.mk f) = F f :=
  rfl
#align category_theory.subobject.lift_mk CategoryTheory.Subobject.lift_mk

/-- The category of subobjects is equivalent to the `MonoOver` category. It is more convenient to
use the former due to the partial order instance, but oftentimes it is easier to define structures
on the latter. -/
noncomputable def equivMonoOver (X : C) : Subobject X ≌ MonoOver X :=
  ThinSkeleton.equivalence _
#align category_theory.subobject.equiv_mono_over CategoryTheory.Subobject.equivMonoOver

/-- Use choice to pick a representative `MonoOver X` for each `Subobject X`.
-/
noncomputable def representative {X : C} : Subobject X ⥤ MonoOver X :=
  (equivMonoOver X).functor
#align category_theory.subobject.representative CategoryTheory.Subobject.representative

/-- Starting with `A : MonoOver X`, we can take its equivalence class in `Subobject X`
then pick an arbitrary representative using `representative.obj`.
This is isomorphic (in `MonoOver X`) to the original `A`.
-/
noncomputable def representativeIso {X : C} (A : MonoOver X) :
    representative.obj ((toThinSkeleton _).obj A) ≅ A :=
  (equivMonoOver X).counitIso.app A
#align category_theory.subobject.representative_iso CategoryTheory.Subobject.representativeIso

/-- Use choice to pick a representative underlying object in `C` for any `Subobject X`.

Prefer to use the coercion `P : C` rather than explicitly writing `underlying.obj P`.
-/
noncomputable def underlying {X : C} : Subobject X ⥤ C :=
  representative ⋙ MonoOver.forget _ ⋙ Over.forget _
#align category_theory.subobject.underlying CategoryTheory.Subobject.underlying

instance : CoeOut (Subobject X) C where coe Y := underlying.obj Y

-- porting note: removed as it has become a syntactic tautology
-- @[simp]
-- theorem underlying_as_coe {X : C} (P : Subobject X) : underlying.obj P = P :=
--   rfl
-- #align category_theory.subobject.underlying_as_coe CategoryTheory.Subobject.underlying_as_coe

/-- If we construct a `Subobject Y` from an explicit `f : X ⟶ Y` with `[Mono f]`,
then pick an arbitrary choice of underlying object `(Subobject.mk f : C)` back in `C`,
it is isomorphic (in `C`) to the original `X`.
-/
noncomputable def underlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] : (Subobject.mk f : C) ≅ X :=
  (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk' f))
#align category_theory.subobject.underlying_iso CategoryTheory.Subobject.underlyingIso

/-- The morphism in `C` from the arbitrarily chosen underlying object to the ambient object.
-/
noncomputable def arrow {X : C} (Y : Subobject X) : (Y : C) ⟶ X :=
  (representative.obj Y).obj.hom
#align category_theory.subobject.arrow CategoryTheory.Subobject.arrow

instance arrow_mono {X : C} (Y : Subobject X) : Mono Y.arrow :=
  (representative.obj Y).property
#align category_theory.subobject.arrow_mono CategoryTheory.Subobject.arrow_mono

@[simp]
theorem arrow_congr {A : C} (X Y : Subobject A) (h : X = Y) :
    eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.arrow = X.arrow := by
  induction h
  simp
#align category_theory.subobject.arrow_congr CategoryTheory.Subobject.arrow_congr

@[simp]
theorem representative_coe (Y : Subobject X) : (representative.obj Y : C) = (Y : C) :=
  rfl
#align category_theory.subobject.representative_coe CategoryTheory.Subobject.representative_coe

@[simp]
theorem representative_arrow (Y : Subobject X) : (representative.obj Y).arrow = Y.arrow :=
  rfl
#align category_theory.subobject.representative_arrow CategoryTheory.Subobject.representative_arrow

@[reassoc (attr := simp)]
theorem underlying_arrow {X : C} {Y Z : Subobject X} (f : Y ⟶ Z) :
    underlying.map f ≫ arrow Z = arrow Y :=
  Over.w (representative.map f)
#align category_theory.subobject.underlying_arrow CategoryTheory.Subobject.underlying_arrow

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem underlyingIso_arrow {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f :=
  Over.w _
#align category_theory.subobject.underlying_iso_arrow CategoryTheory.Subobject.underlyingIso_arrow

@[reassoc (attr := simp)]
theorem underlyingIso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).hom ≫ f = (mk f).arrow :=
  (Iso.eq_inv_comp _).1 (underlyingIso_arrow f).symm
#align category_theory.subobject.underlying_iso_hom_comp_eq_mk CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk

/-- Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal -/
@[ext]
theorem eq_of_comp_arrow_eq {X Y : C} {P : Subobject Y} {f g : X ⟶ P}
    (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
  (cancel_mono P.arrow).mp h
#align category_theory.subobject.eq_of_comp_arrow_eq CategoryTheory.Subobject.eq_of_comp_arrow_eq

theorem mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
    (w : g ≫ f₂ = f₁) : mk f₁ ≤ mk f₂ :=
  ⟨MonoOver.homMk _ w⟩
#align category_theory.subobject.mk_le_mk_of_comm CategoryTheory.Subobject.mk_le_mk_of_comm

@[simp]
theorem mk_arrow (P : Subobject X) : mk P.arrow = P :=
  Quotient.inductionOn' P fun Q => by
    obtain ⟨e⟩ := @Quotient.mk_out' _ (isIsomorphicSetoid _) Q
    exact Quotient.sound' ⟨MonoOver.isoMk (Iso.refl _) (by aesop_cat) ≪≫ e⟩
#align category_theory.subobject.mk_arrow CategoryTheory.Subobject.mk_arrow

theorem le_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) :
    X ≤ Y := by
  convert mk_le_mk_of_comm _ w <;> simp
#align category_theory.subobject.le_of_comm CategoryTheory.Subobject.le_of_comm

theorem le_mk_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A)
    (w : g ≫ f = X.arrow) : X ≤ mk f :=
  le_of_comm (g ≫ (underlyingIso f).inv) <| by simp [w]
#align category_theory.subobject.le_mk_of_comm CategoryTheory.Subobject.le_mk_of_comm

theorem mk_le_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C))
    (w : g ≫ X.arrow = f) : mk f ≤ X :=
  le_of_comm ((underlyingIso f).hom ≫ g) <| by simp [w]
#align category_theory.subobject.mk_le_of_comm CategoryTheory.Subobject.mk_le_of_comm

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext]
theorem eq_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C))
    (w : f.hom ≫ Y.arrow = X.arrow) : X = Y :=
  le_antisymm (le_of_comm f.hom w) <| le_of_comm f.inv <| f.inv_comp_eq.2 w.symm
#align category_theory.subobject.eq_of_comm CategoryTheory.Subobject.eq_of_comm

-- porting note: removed @[ext]
/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
theorem eq_mk_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A)
    (w : i.hom ≫ f = X.arrow) : X = mk f :=
  eq_of_comm (i.trans (underlyingIso f).symm) <| by simp [w]
#align category_theory.subobject.eq_mk_of_comm CategoryTheory.Subobject.eq_mk_of_comm

-- porting note: removed @[ext]
/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
theorem mk_eq_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C))
    (w : i.hom ≫ X.arrow = f) : mk f = X :=
  Eq.symm <| eq_mk_of_comm _ i.symm <| by rw [Iso.symm_hom, Iso.inv_comp_eq, w]
#align category_theory.subobject.mk_eq_of_comm CategoryTheory.Subobject.mk_eq_of_comm

-- porting note: removed @[ext]
/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
theorem mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂)
    (w : i.hom ≫ g = f) : mk f = mk g :=
  eq_mk_of_comm _ ((underlyingIso f).trans i) <| by simp [w]
#align category_theory.subobject.mk_eq_mk_of_comm CategoryTheory.Subobject.mk_eq_mk_of_comm

-- We make `X` and `Y` explicit arguments here so that when `ofLE` appears in goal statements
-- it is possible to see its source and target
-- (`h` will just display as `_`, because it is in `Prop`).
/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofLE {B : C} (X Y : Subobject B) (h : X ≤ Y) : (X : C) ⟶ (Y : C) :=
  underlying.map <| h.hom
#align category_theory.subobject.of_le CategoryTheory.Subobject.ofLE

@[reassoc (attr := simp)]
theorem ofLE_arrow {B : C} {X Y : Subobject B} (h : X ≤ Y) : ofLE X Y h ≫ Y.arrow = X.arrow :=
  underlying_arrow _
#align category_theory.subobject.of_le_arrow CategoryTheory.Subobject.ofLE_arrow

instance {B : C} (X Y : Subobject B) (h : X ≤ Y) : Mono (ofLE X Y h) := by
  fconstructor
  intro Z f g w
  replace w := w =≫ Y.arrow
  ext
  simpa using w

theorem ofLE_mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂]
    (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) :
    ofLE _ _ (mk_le_mk_of_comm g w) = (underlyingIso _).hom ≫ g ≫ (underlyingIso _).inv := by
  ext
  simp [w]
#align category_theory.subobject.of_le_mk_le_mk_of_comm CategoryTheory.Subobject.ofLE_mk_le_mk_of_comm

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofLEMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) : (X : C) ⟶ A :=
  ofLE X (mk f) h ≫ (underlyingIso f).hom
#align category_theory.subobject.of_le_mk CategoryTheory.Subobject.ofLEMk

instance {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) :
    Mono (ofLEMk X f h) := by
  dsimp only [ofLEMk]
  infer_instance

@[simp]
theorem ofLEMk_comp {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X ≤ mk f) :
    ofLEMk X f h ≫ f = X.arrow := by simp [ofLEMk]
#align category_theory.subobject.of_le_mk_comp CategoryTheory.Subobject.ofLEMk_comp

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofMkLE {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) : A ⟶ (X : C) :=
  (underlyingIso f).inv ≫ ofLE (mk f) X h
#align category_theory.subobject.of_mk_le CategoryTheory.Subobject.ofMkLE

instance {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) :
    Mono (ofMkLE f X h) := by
  dsimp only [ofMkLE]
  infer_instance

@[simp]
theorem ofMkLE_arrow {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f ≤ X) :
    ofMkLE f X h ≫ X.arrow = f := by simp [ofMkLE]
#align category_theory.subobject.of_mk_le_arrow CategoryTheory.Subobject.ofMkLE_arrow

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofMkLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    A₁ ⟶ A₂ :=
  (underlyingIso f).inv ≫ ofLE (mk f) (mk g) h ≫ (underlyingIso g).hom
#align category_theory.subobject.of_mk_le_mk CategoryTheory.Subobject.ofMkLEMk

instance {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    Mono (ofMkLEMk f g h) := by
  dsimp only [ofMkLEMk]
  infer_instance

@[simp]
theorem ofMkLEMk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f ≤ mk g) :
    ofMkLEMk f g h ≫ g = f := by simp [ofMkLEMk]
#align category_theory.subobject.of_mk_le_mk_comp CategoryTheory.Subobject.ofMkLEMk_comp

@[reassoc (attr := simp)]
theorem ofLE_comp_ofLE {B : C} (X Y Z : Subobject B) (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    ofLE X Y h₁ ≫ ofLE Y Z h₂ = ofLE X Z (h₁.trans h₂) := by
  simp only [ofLE, ← Functor.map_comp underlying]
  congr 1
#align category_theory.subobject.of_le_comp_of_le CategoryTheory.Subobject.ofLE_comp_ofLE

@[reassoc (attr := simp)]
theorem ofLE_comp_ofLEMk {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X ≤ Y)
    (h₂ : Y ≤ mk f) : ofLE X Y h₁ ≫ ofLEMk Y f h₂ = ofLEMk X f (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp_assoc underlying]
  congr 1
#align category_theory.subobject.of_le_comp_of_le_mk CategoryTheory.Subobject.ofLE_comp_ofLEMk

@[reassoc (attr := simp)]
theorem ofLEMk_comp_ofMkLE {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B)
    (h₁ : X ≤ mk f) (h₂ : mk f ≤ Y) : ofLEMk X f h₁ ≫ ofMkLE f Y h₂ = ofLE X Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp underlying, assoc, Iso.hom_inv_id_assoc]
  congr 1
#align category_theory.subobject.of_le_mk_comp_of_mk_le CategoryTheory.Subobject.ofLEMk_comp_ofMkLE

@[reassoc (attr := simp)]
theorem ofLEMk_comp_ofMkLEMk {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
    [Mono g] (h₁ : X ≤ mk f) (h₂ : mk f ≤ mk g) :
    ofLEMk X f h₁ ≫ ofMkLEMk f g h₂ = ofLEMk X g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1
#align category_theory.subobject.of_le_mk_comp_of_mk_le_mk CategoryTheory.Subobject.ofLEMk_comp_ofMkLEMk

@[reassoc (attr := simp)]
theorem ofMkLE_comp_ofLE {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f ≤ X)
    (h₂ : X ≤ Y) : ofMkLE f X h₁ ≫ ofLE X Y h₂ = ofMkLE f Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc]
  congr 1
#align category_theory.subobject.of_mk_le_comp_of_le CategoryTheory.Subobject.ofMkLE_comp_ofLE

@[reassoc (attr := simp)]
theorem ofMkLE_comp_ofLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B)
    [Mono g] (h₁ : mk f ≤ X) (h₂ : X ≤ mk g) :
    ofMkLE f X h₁ ≫ ofLEMk X g h₂ = ofMkLEMk f g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc]
  congr 1
#align category_theory.subobject.of_mk_le_comp_of_le_mk CategoryTheory.Subobject.ofMkLE_comp_ofLEMk

@[reassoc (attr := simp)]
theorem ofMkLEMk_comp_ofMkLE {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (X : Subobject B) (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ X) :
    ofMkLEMk f g h₁ ≫ ofMkLE g X h₂ = ofMkLE f X (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1
#align category_theory.subobject.of_mk_le_mk_comp_of_mk_le CategoryTheory.Subobject.ofMkLEMk_comp_ofMkLE

@[reassoc (attr := simp)]
theorem ofMkLEMk_comp_ofMkLEMk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (h : A₃ ⟶ B) [Mono h] (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ mk h) :
    ofMkLEMk f g h₁ ≫ ofMkLEMk g h h₂ = ofMkLEMk f h (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc,
    Iso.hom_inv_id_assoc]
  congr 1
#align category_theory.subobject.of_mk_le_mk_comp_of_mk_le_mk CategoryTheory.Subobject.ofMkLEMk_comp_ofMkLEMk

@[simp]
theorem ofLE_refl {B : C} (X : Subobject B) : ofLE X X le_rfl = 𝟙 _ := by
  apply (cancel_mono X.arrow).mp
  simp
#align category_theory.subobject.of_le_refl CategoryTheory.Subobject.ofLE_refl

@[simp]
theorem ofMkLEMk_refl {B A₁ : C} (f : A₁ ⟶ B) [Mono f] : ofMkLEMk f f le_rfl = 𝟙 _ := by
  apply (cancel_mono f).mp
  simp
#align category_theory.subobject.of_mk_le_mk_refl CategoryTheory.Subobject.ofMkLEMk_refl

-- As with `ofLE`, we have `X` and `Y` as explicit arguments for readability.
/-- An equality of subobjects gives an isomorphism of the corresponding objects.
(One could use `underlying.mapIso (eqToIso h))` here, but this is more readable.) -/
@[simps]
def isoOfEq {B : C} (X Y : Subobject B) (h : X = Y) : (X : C) ≅ (Y : C) where
  hom := ofLE _ _ h.le
  inv := ofLE _ _ h.ge
#align category_theory.subobject.iso_of_eq CategoryTheory.Subobject.isoOfEq

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfEqMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f) : (X : C) ≅ A where
  hom := ofLEMk X f h.le
  inv := ofMkLE f X h.ge
#align category_theory.subobject.iso_of_eq_mk CategoryTheory.Subobject.isoOfEqMk

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfMkEq {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X) : A ≅ (X : C) where
  hom := ofMkLE f X h.le
  inv := ofLEMk X f h.ge
#align category_theory.subobject.iso_of_mk_eq CategoryTheory.Subobject.isoOfMkEq

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfMkEqMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g) :
    A₁ ≅ A₂ where
  hom := ofMkLEMk f g h.le
  inv := ofMkLEMk g f h.ge
#align category_theory.subobject.iso_of_mk_eq_mk CategoryTheory.Subobject.isoOfMkEqMk

end Subobject

open CategoryTheory.Limits

namespace Subobject

/-- Any functor `MonoOver X ⥤ MonoOver Y` descends to a functor
`Subobject X ⥤ Subobject Y`, because `MonoOver Y` is thin. -/
def lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y :=
  ThinSkeleton.map F
#align category_theory.subobject.lower CategoryTheory.Subobject.lower

/-- Isomorphic functors become equal when lowered to `Subobject`.
(It's not as evil as usual to talk about equality between functors
because the categories are thin and skeletal.) -/
theorem lower_iso (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂) : lower F₁ = lower F₂ :=
  ThinSkeleton.map_iso_eq h
#align category_theory.subobject.lower_iso CategoryTheory.Subobject.lower_iso

/-- A ternary version of `Subobject.lower`. -/
def lower₂ (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z) : Subobject X ⥤ Subobject Y ⥤ Subobject Z :=
  ThinSkeleton.map₂ F
#align category_theory.subobject.lower₂ CategoryTheory.Subobject.lower₂

@[simp]
theorem lower_comm (F : MonoOver Y ⥤ MonoOver X) :
    toThinSkeleton _ ⋙ lower F = F ⋙ toThinSkeleton _ :=
  rfl
#align category_theory.subobject.lower_comm CategoryTheory.Subobject.lower_comm

/-- An adjunction between `MonoOver A` and `MonoOver B` gives an adjunction
between `Subobject A` and `Subobject B`. -/
def lowerAdjunction {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A}
    (h : L ⊣ R) : lower L ⊣ lower R :=
  ThinSkeleton.lowerAdjunction _ _ h
#align category_theory.subobject.lower_adjunction CategoryTheory.Subobject.lowerAdjunction

/-- An equivalence between `MonoOver A` and `MonoOver B` gives an equivalence
between `Subobject A` and `Subobject B`. -/
@[simps]
def lowerEquivalence {A : C} {B : D} (e : MonoOver A ≌ MonoOver B) : Subobject A ≌ Subobject B where
  functor := lower e.functor
  inverse := lower e.inverse
  unitIso := by
    apply eqToIso
    convert ThinSkeleton.map_iso_eq e.unitIso
    · exact ThinSkeleton.map_id_eq.symm
    · exact (ThinSkeleton.map_comp_eq _ _).symm
  counitIso := by
    apply eqToIso
    convert ThinSkeleton.map_iso_eq e.counitIso
    · exact (ThinSkeleton.map_comp_eq _ _).symm
    · exact ThinSkeleton.map_id_eq.symm
#align category_theory.subobject.lower_equivalence CategoryTheory.Subobject.lowerEquivalence

section Pullback

variable [HasPullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `Subobject Y ⥤ Subobject X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X :=
  lower (MonoOver.pullback f)
#align category_theory.subobject.pullback CategoryTheory.Subobject.pullback

theorem pullback_id (x : Subobject X) : (pullback (𝟙 X)).obj x = x := by
  induction' x using Quotient.inductionOn' with f
  exact Quotient.sound ⟨MonoOver.pullbackId.app f⟩
#align category_theory.subobject.pullback_id CategoryTheory.Subobject.pullback_id

theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z) :
    (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) := by
  induction' x using Quotient.inductionOn' with t
  exact Quotient.sound ⟨(MonoOver.pullbackComp _ _).app t⟩
#align category_theory.subobject.pullback_comp CategoryTheory.Subobject.pullback_comp

instance (f : X ⟶ Y) : Faithful (pullback f) where

end Pullback

section Map

/-- We can map subobjects of `X` to subobjects of `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.map f)
#align category_theory.subobject.map CategoryTheory.Subobject.map

theorem map_id (x : Subobject X) : (map (𝟙 X)).obj x = x := by
  induction' x using Quotient.inductionOn' with f
  exact Quotient.sound ⟨MonoOver.mapId.app f⟩
#align category_theory.subobject.map_id CategoryTheory.Subobject.map_id

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X) :
    (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) := by
  induction' x using Quotient.inductionOn' with t
  exact Quotient.sound ⟨(MonoOver.mapComp _ _).app t⟩
#align category_theory.subobject.map_comp CategoryTheory.Subobject.map_comp

/-- Isomorphic objects have equivalent subobject lattices. -/
def mapIso {A B : C} (e : A ≅ B) : Subobject A ≌ Subobject B :=
  lowerEquivalence (MonoOver.mapIso e)
#align category_theory.subobject.map_iso CategoryTheory.Subobject.mapIso

-- @[simps] here generates a lemma `map_iso_to_order_iso_to_equiv_symm_apply`
-- whose left hand side is not in simp normal form.
/-- In fact, there's a type level bijection between the subobjects of isomorphic objects,
which preserves the order. -/
def mapIsoToOrderIso (e : X ≅ Y) : Subobject X ≃o Subobject Y where
  toFun := (map e.hom).obj
  invFun := (map e.inv).obj
  left_inv g := by simp_rw [← map_comp, e.hom_inv_id, map_id]
  right_inv g := by simp_rw [← map_comp, e.inv_hom_id, map_id]
  map_rel_iff' {A B} := by
    dsimp
    constructor
    . intro h
      apply_fun (map e.inv).obj at h
      . simpa only [← map_comp, e.hom_inv_id, map_id] using h
      . apply Functor.monotone
    . intro h
      apply_fun (map e.hom).obj  at h
      . exact h
      . apply Functor.monotone
#align category_theory.subobject.map_iso_to_order_iso CategoryTheory.Subobject.mapIsoToOrderIso

@[simp]
theorem mapIsoToOrderIso_apply (e : X ≅ Y) (P : Subobject X) :
    mapIsoToOrderIso e P = (map e.hom).obj P :=
  rfl
#align category_theory.subobject.map_iso_to_order_iso_apply CategoryTheory.Subobject.mapIsoToOrderIso_apply

@[simp]
theorem mapIsoToOrderIso_symm_apply (e : X ≅ Y) (Q : Subobject Y) :
    (mapIsoToOrderIso e).symm Q = (map e.inv).obj Q :=
  rfl
#align category_theory.subobject.map_iso_to_order_iso_symm_apply CategoryTheory.Subobject.mapIsoToOrderIso_symm_apply

/-- `map f : Subobject X ⥤ Subobject Y` is
the left adjoint of `pullback f : Subobject Y ⥤ Subobject X`. -/
def mapPullbackAdj [HasPullbacks C] (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  lowerAdjunction (MonoOver.mapPullbackAdj f)
#align category_theory.subobject.map_pullback_adj CategoryTheory.Subobject.mapPullbackAdj

@[simp]
theorem pullback_map_self [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) :
    (pullback f).obj ((map f).obj g) = g := by
  revert g
  exact Quotient.ind (fun g' => Quotient.sound ⟨(MonoOver.pullbackMapSelf f).app _⟩)
#align category_theory.subobject.pullback_map_self CategoryTheory.Subobject.pullback_map_self

theorem map_pullback [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
    [Mono h] [Mono g] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk f g comm))
    (p : Subobject Y) : (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) := by
  revert p
  apply Quotient.ind'
  intro a
  apply Quotient.sound
  apply ThinSkeleton.equiv_of_both_ways
  · refine' MonoOver.homMk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _)
    change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _
    rw [assoc, ← comm, pullback.condition_assoc]
  · refine' MonoOver.homMk (pullback.lift pullback.fst
      (PullbackCone.IsLimit.lift t (pullback.fst ≫ a.arrow) pullback.snd _)
      (PullbackCone.IsLimit.lift_fst _ _ _ _).symm) _
    · rw [← pullback.condition, assoc]
      rfl
    · dsimp
      rw [pullback.lift_snd_assoc]
      apply PullbackCone.IsLimit.lift_snd
#align category_theory.subobject.map_pullback CategoryTheory.Subobject.map_pullback

end Map

section Exists

variable [HasImages C]

-- porting note: renamed `exists` as `exists_` because it is a reserved word
/-- The functor from subobjects of `X` to subobjects of `Y` given by
sending the subobject `S` to its "image" under `f`, usually denoted $\exists_f$.
For instance, when `C` is the category of types,
viewing `Subobject X` as `Set X` this is just `Set.image f`.

This functor is left adjoint to the `pullback f` functor (shown in `existsPullbackAdj`)
provided both are defined, and generalises the `map f` functor, again provided it is defined.
-/
def exists_ (f : X ⟶ Y) : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.exists_ f)
#align category_theory.subobject.exists CategoryTheory.Subobject.exists_

/-- When `f : X ⟶ Y` is a monomorphism, `exists_ f` agrees with `map f`.
-/
theorem exists_iso_map (f : X ⟶ Y) [Mono f] : exists_ f = map f :=
  lower_iso _ _ (MonoOver.existsIsoMap f)
#align category_theory.subobject.exists_iso_map CategoryTheory.Subobject.exists_iso_map

/-- `exists_ f : Subobject X ⥤ Subobject Y` is
left adjoint to `pullback f : Subobject Y ⥤ Subobject X`.
-/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : exists_ f ⊣ pullback f :=
  lowerAdjunction (MonoOver.existsPullbackAdj f)
#align category_theory.subobject.exists_pullback_adj CategoryTheory.Subobject.existsPullbackAdj

end Exists

end Subobject

end CategoryTheory
