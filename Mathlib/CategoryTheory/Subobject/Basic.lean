/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
import Mathlib.CategoryTheory.Subobject.MonoOver
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.CategoryTheory.Elementwise

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
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : Subobject Y ⥤ Subobject X`
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
and was ported to mathlib by Kim Morrison.

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
as the quotient by isomorphisms of `MonoOver X`.

Since `MonoOver X` is a thin category, we use `ThinSkeleton` to take the quotient.

Essentially all the structure defined above on `MonoOver X` descends to `Subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/


/-- The category of subobjects of `X : C`, defined as isomorphism classes of monomorphisms into `X`.
-/
def Subobject (X : C) :=
  ThinSkeleton (MonoOver X)

instance (X : C) : PartialOrder (Subobject X) := by
  dsimp only [Subobject]
  infer_instance

namespace Subobject

-- Porting note: made it a def rather than an abbreviation
-- because Lean would make it too transparent
/-- Convenience constructor for a subobject. -/
def mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X :=
  (toThinSkeleton _).obj (MonoOver.mk' f)

section

attribute [local ext] CategoryTheory.Comma

protected theorem ind {X : C} (p : Subobject X → Prop)
    (h : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], p (Subobject.mk f)) (P : Subobject X) : p P := by
  apply Quotient.inductionOn'
  intro a
  exact h a.arrow

protected theorem ind₂ {X : C} (p : Subobject X → Subobject X → Prop)
    (h : ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g],
      p (Subobject.mk f) (Subobject.mk g))
    (P Q : Subobject X) : p P Q := by
  apply Quotient.inductionOn₂'
  intro a b
  exact h a.arrow b.arrow

end

/-- Declare a function on subobjects of `X` by specifying a function on monomorphisms with
    codomain `X`. -/
protected def lift {α : Sort*} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
    (h :
      ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] (i : A ≅ B),
        i.hom ≫ g = f → F f = F g) :
    Subobject X → α := fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom)

@[simp]
protected theorem lift_mk {α : Sort*} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α) {h A}
    (f : A ⟶ X) [Mono f] : Subobject.lift F h (Subobject.mk f) = F f :=
  rfl

/-- The category of subobjects is equivalent to the `MonoOver` category. It is more convenient to
use the former due to the partial order instance, but oftentimes it is easier to define structures
on the latter. -/
noncomputable def equivMonoOver (X : C) : Subobject X ≌ MonoOver X :=
  ThinSkeleton.equivalence _

/-- Use choice to pick a representative `MonoOver X` for each `Subobject X`.
-/
noncomputable def representative {X : C} : Subobject X ⥤ MonoOver X :=
  (equivMonoOver X).functor

/-- Starting with `A : MonoOver X`, we can take its equivalence class in `Subobject X`
then pick an arbitrary representative using `representative.obj`.
This is isomorphic (in `MonoOver X`) to the original `A`.
-/
noncomputable def representativeIso {X : C} (A : MonoOver X) :
    representative.obj ((toThinSkeleton _).obj A) ≅ A :=
  (equivMonoOver X).counitIso.app A

/-- Use choice to pick a representative underlying object in `C` for any `Subobject X`.

Prefer to use the coercion `P : C` rather than explicitly writing `underlying.obj P`.
-/
noncomputable def underlying {X : C} : Subobject X ⥤ C :=
  representative ⋙ MonoOver.forget _ ⋙ Over.forget _

instance : CoeOut (Subobject X) C where coe Y := underlying.obj Y

-- Porting note: removed as it has become a syntactic tautology
-- @[simp]
-- theorem underlying_as_coe {X : C} (P : Subobject X) : underlying.obj P = P :=
--   rfl

/-- If we construct a `Subobject Y` from an explicit `f : X ⟶ Y` with `[Mono f]`,
then pick an arbitrary choice of underlying object `(Subobject.mk f : C)` back in `C`,
it is isomorphic (in `C`) to the original `X`.
-/
noncomputable def underlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] : (Subobject.mk f : C) ≅ X :=
  (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk' f))

/-- The morphism in `C` from the arbitrarily chosen underlying object to the ambient object.
-/
noncomputable def arrow {X : C} (Y : Subobject X) : (Y : C) ⟶ X :=
  (representative.obj Y).obj.hom

instance arrow_mono {X : C} (Y : Subobject X) : Mono Y.arrow :=
  (representative.obj Y).property

@[simp]
theorem arrow_congr {A : C} (X Y : Subobject A) (h : X = Y) :
    eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.arrow = X.arrow := by
  induction h
  simp

@[simp]
theorem representative_coe (Y : Subobject X) : (representative.obj Y : C) = (Y : C) :=
  rfl

@[simp]
theorem representative_arrow (Y : Subobject X) : (representative.obj Y).arrow = Y.arrow :=
  rfl

@[reassoc (attr := simp)]
theorem underlying_arrow {X : C} {Y Z : Subobject X} (f : Y ⟶ Z) :
    underlying.map f ≫ arrow Z = arrow Y :=
  Over.w (representative.map f)

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem underlyingIso_arrow {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f :=
  Over.w _

@[reassoc (attr := simp)]
theorem underlyingIso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).hom ≫ f = (mk f).arrow :=
  (Iso.eq_inv_comp _).1 (underlyingIso_arrow f).symm

/-- Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal -/
@[ext]
theorem eq_of_comp_arrow_eq {X Y : C} {P : Subobject Y} {f g : X ⟶ P}
    (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
  (cancel_mono P.arrow).mp h

theorem mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
    (w : g ≫ f₂ = f₁) : mk f₁ ≤ mk f₂ :=
  ⟨MonoOver.homMk _ w⟩

@[simp]
theorem mk_arrow (P : Subobject X) : mk P.arrow = P :=
  Quotient.inductionOn' P fun Q => by
    obtain ⟨e⟩ := @Quotient.mk_out' _ (isIsomorphicSetoid _) Q
    exact Quotient.sound' ⟨MonoOver.isoMk (Iso.refl _) ≪≫ e⟩

theorem le_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) :
    X ≤ Y := by
  convert mk_le_mk_of_comm _ w <;> simp

theorem le_mk_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A)
    (w : g ≫ f = X.arrow) : X ≤ mk f :=
  le_of_comm (g ≫ (underlyingIso f).inv) <| by simp [w]

theorem mk_le_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C))
    (w : g ≫ X.arrow = f) : mk f ≤ X :=
  le_of_comm ((underlyingIso f).hom ≫ g) <| by simp [w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext (iff := false)]
theorem eq_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C))
    (w : f.hom ≫ Y.arrow = X.arrow) : X = Y :=
  le_antisymm (le_of_comm f.hom w) <| le_of_comm f.inv <| f.inv_comp_eq.2 w.symm

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
theorem eq_mk_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A)
    (w : i.hom ≫ f = X.arrow) : X = mk f :=
  eq_of_comm (i.trans (underlyingIso f).symm) <| by simp [w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
theorem mk_eq_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C))
    (w : i.hom ≫ X.arrow = f) : mk f = X :=
  Eq.symm <| eq_mk_of_comm _ i.symm <| by rw [Iso.symm_hom, Iso.inv_comp_eq, w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
theorem mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂)
    (w : i.hom ≫ g = f) : mk f = mk g :=
  eq_mk_of_comm _ ((underlyingIso f).trans i) <| by simp [w]

-- We make `X` and `Y` explicit arguments here so that when `ofLE` appears in goal statements
-- it is possible to see its source and target
-- (`h` will just display as `_`, because it is in `Prop`).
/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofLE {B : C} (X Y : Subobject B) (h : X ≤ Y) : (X : C) ⟶ (Y : C) :=
  underlying.map <| h.hom

@[reassoc (attr := simp)]
theorem ofLE_arrow {B : C} {X Y : Subobject B} (h : X ≤ Y) : ofLE X Y h ≫ Y.arrow = X.arrow :=
  underlying_arrow _

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

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofLEMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) : (X : C) ⟶ A :=
  ofLE X (mk f) h ≫ (underlyingIso f).hom

instance {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) :
    Mono (ofLEMk X f h) := by
  dsimp only [ofLEMk]
  infer_instance

@[simp]
theorem ofLEMk_comp {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X ≤ mk f) :
    ofLEMk X f h ≫ f = X.arrow := by simp [ofLEMk]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofMkLE {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) : A ⟶ (X : C) :=
  (underlyingIso f).inv ≫ ofLE (mk f) X h

instance {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) :
    Mono (ofMkLE f X h) := by
  dsimp only [ofMkLE]
  infer_instance

@[simp]
theorem ofMkLE_arrow {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f ≤ X) :
    ofMkLE f X h ≫ X.arrow = f := by simp [ofMkLE]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofMkLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    A₁ ⟶ A₂ :=
  (underlyingIso f).inv ≫ ofLE (mk f) (mk g) h ≫ (underlyingIso g).hom

instance {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    Mono (ofMkLEMk f g h) := by
  dsimp only [ofMkLEMk]
  infer_instance

@[simp]
theorem ofMkLEMk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f ≤ mk g) :
    ofMkLEMk f g h ≫ g = f := by simp [ofMkLEMk]

@[reassoc (attr := simp)]
theorem ofLE_comp_ofLE {B : C} (X Y Z : Subobject B) (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    ofLE X Y h₁ ≫ ofLE Y Z h₂ = ofLE X Z (h₁.trans h₂) := by
  simp only [ofLE, ← Functor.map_comp underlying]
  congr 1

@[reassoc (attr := simp)]
theorem ofLE_comp_ofLEMk {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X ≤ Y)
    (h₂ : Y ≤ mk f) : ofLE X Y h₁ ≫ ofLEMk Y f h₂ = ofLEMk X f (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp_assoc underlying]
  congr 1

@[reassoc (attr := simp)]
theorem ofLEMk_comp_ofMkLE {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B)
    (h₁ : X ≤ mk f) (h₂ : mk f ≤ Y) : ofLEMk X f h₁ ≫ ofMkLE f Y h₂ = ofLE X Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp underlying, assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
theorem ofLEMk_comp_ofMkLEMk {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
    [Mono g] (h₁ : X ≤ mk f) (h₂ : mk f ≤ mk g) :
    ofLEMk X f h₁ ≫ ofMkLEMk f g h₂ = ofLEMk X g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
theorem ofMkLE_comp_ofLE {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f ≤ X)
    (h₂ : X ≤ Y) : ofMkLE f X h₁ ≫ ofLE X Y h₂ = ofMkLE f Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc]
  congr 1

@[reassoc (attr := simp)]
theorem ofMkLE_comp_ofLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B)
    [Mono g] (h₁ : mk f ≤ X) (h₂ : X ≤ mk g) :
    ofMkLE f X h₁ ≫ ofLEMk X g h₂ = ofMkLEMk f g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc]
  congr 1

@[reassoc (attr := simp)]
theorem ofMkLEMk_comp_ofMkLE {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (X : Subobject B) (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ X) :
    ofMkLEMk f g h₁ ≫ ofMkLE g X h₂ = ofMkLE f X (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
theorem ofMkLEMk_comp_ofMkLEMk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (h : A₃ ⟶ B) [Mono h] (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ mk h) :
    ofMkLEMk f g h₁ ≫ ofMkLEMk g h h₂ = ofMkLEMk f h (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc,
    Iso.hom_inv_id_assoc]
  congr 1

@[simp]
theorem ofLE_refl {B : C} (X : Subobject B) : ofLE X X le_rfl = 𝟙 _ := by
  apply (cancel_mono X.arrow).mp
  simp

@[simp]
theorem ofMkLEMk_refl {B A₁ : C} (f : A₁ ⟶ B) [Mono f] : ofMkLEMk f f le_rfl = 𝟙 _ := by
  apply (cancel_mono f).mp
  simp

-- As with `ofLE`, we have `X` and `Y` as explicit arguments for readability.
/-- An equality of subobjects gives an isomorphism of the corresponding objects.
(One could use `underlying.mapIso (eqToIso h))` here, but this is more readable.) -/
@[simps]
def isoOfEq {B : C} (X Y : Subobject B) (h : X = Y) : (X : C) ≅ (Y : C) where
  hom := ofLE _ _ h.le
  inv := ofLE _ _ h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfEqMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f) : (X : C) ≅ A where
  hom := ofLEMk X f h.le
  inv := ofMkLE f X h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfMkEq {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X) : A ≅ (X : C) where
  hom := ofMkLE f X h.le
  inv := ofLEMk X f h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfMkEqMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g) :
    A₁ ≅ A₂ where
  hom := ofMkLEMk f g h.le
  inv := ofMkLEMk g f h.ge

lemma mk_lt_mk_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) (hf : ¬ IsIso f) :
    Subobject.mk i₁ < Subobject.mk i₂ := by
  obtain _ | h := (mk_le_mk_of_comm _ fac).lt_or_eq
  · assumption
  · exfalso
    apply hf
    convert (isoOfMkEqMk i₁ i₂ h).isIso_hom
    rw [← cancel_mono i₂, isoOfMkEqMk_hom, ofMkLEMk_comp, fac]

lemma mk_lt_mk_iff_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) :
    Subobject.mk i₁ < Subobject.mk i₂ ↔ ¬ IsIso f :=
  ⟨fun h hf ↦ by simp only [mk_eq_mk_of_comm i₁ i₂ (asIso f) fac, lt_self_iff_false] at h,
    mk_lt_mk_of_comm f fac⟩

end Subobject

lemma MonoOver.subobjectMk_le_mk_of_hom {P Q : MonoOver X} (f : P ⟶ Q) :
    Subobject.mk P.obj.hom ≤ Subobject.mk Q.obj.hom :=
  Subobject.mk_le_mk_of_comm f.left (by simp)

open CategoryTheory.Limits

namespace Subobject

/-- Any functor `MonoOver X ⥤ MonoOver Y` descends to a functor
`Subobject X ⥤ Subobject Y`, because `MonoOver Y` is thin. -/
def lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y :=
  ThinSkeleton.map F

/-- Isomorphic functors become equal when lowered to `Subobject`.
(It's not as evil as usual to talk about equality between functors
because the categories are thin and skeletal.) -/
theorem lower_iso (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂) : lower F₁ = lower F₂ :=
  ThinSkeleton.map_iso_eq h

/-- A ternary version of `Subobject.lower`. -/
def lower₂ (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z) : Subobject X ⥤ Subobject Y ⥤ Subobject Z :=
  ThinSkeleton.map₂ F

@[simp]
theorem lower_comm (F : MonoOver Y ⥤ MonoOver X) :
    toThinSkeleton _ ⋙ lower F = F ⋙ toThinSkeleton _ :=
  rfl

/-- An adjunction between `MonoOver A` and `MonoOver B` gives an adjunction
between `Subobject A` and `Subobject B`. -/
def lowerAdjunction {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A}
    (h : L ⊣ R) : lower L ⊣ lower R :=
  ThinSkeleton.lowerAdjunction _ _ h

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

section Pullback

variable [HasPullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `Subobject Y ⥤ Subobject X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X :=
  lower (MonoOver.pullback f)

theorem pullback_id (x : Subobject X) : (pullback (𝟙 X)).obj x = x := by
  induction' x using Quotient.inductionOn' with f
  exact Quotient.sound ⟨MonoOver.pullbackId.app f⟩

theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z) :
    (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) := by
  induction' x using Quotient.inductionOn' with t
  exact Quotient.sound ⟨(MonoOver.pullbackComp _ _).app t⟩

instance (f : X ⟶ Y) : (pullback f).Faithful where

end Pullback

section Map

/-- We can map subobjects of `X` to subobjects of `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.map f)

lemma map_mk {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f] :
    (map f).obj (mk i) = mk (i ≫ f) :=
  rfl

theorem map_id (x : Subobject X) : (map (𝟙 X)).obj x = x := by
  induction' x using Quotient.inductionOn' with f
  exact Quotient.sound ⟨(MonoOver.mapId _).app f⟩

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X) :
    (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) := by
  induction' x using Quotient.inductionOn' with t
  exact Quotient.sound ⟨(MonoOver.mapComp _ _).app t⟩

lemma map_obj_injective {X Y : C} (f : X ⟶ Y) [Mono f] :
    Function.Injective (Subobject.map f).obj := by
  intro X₁ X₂ h
  induction' X₁ using Subobject.ind with X₁ i₁ _
  induction' X₂ using Subobject.ind with X₂ i₂ _
  simp only [map_mk] at h
  exact mk_eq_mk_of_comm _ _ (isoOfMkEqMk _ _ h) (by simp [← cancel_mono f])

/-- Isomorphic objects have equivalent subobject lattices. -/
def mapIso {A B : C} (e : A ≅ B) : Subobject A ≌ Subobject B :=
  lowerEquivalence (MonoOver.mapIso e)

-- Porting note: the note below doesn't seem true anymore
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
    · intro h
      apply_fun (map e.inv).obj at h
      · simpa only [← map_comp, e.hom_inv_id, map_id] using h
      · apply Functor.monotone
    · intro h
      apply_fun (map e.hom).obj at h
      · exact h
      · apply Functor.monotone

@[simp]
theorem mapIsoToOrderIso_apply (e : X ≅ Y) (P : Subobject X) :
    mapIsoToOrderIso e P = (map e.hom).obj P :=
  rfl

@[simp]
theorem mapIsoToOrderIso_symm_apply (e : X ≅ Y) (Q : Subobject Y) :
    (mapIsoToOrderIso e).symm Q = (map e.inv).obj Q :=
  rfl

/-- `map f : Subobject X ⥤ Subobject Y` is
the left adjoint of `pullback f : Subobject Y ⥤ Subobject X`. -/
def mapPullbackAdj [HasPullbacks C] (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  lowerAdjunction (MonoOver.mapPullbackAdj f)

@[simp]
theorem pullback_map_self [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) :
    (pullback f).obj ((map f).obj g) = g := by
  revert g
  exact Quotient.ind (fun g' => Quotient.sound ⟨(MonoOver.pullbackMapSelf f).app _⟩)

theorem map_pullback [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
    [Mono h] [Mono g] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk f g comm))
    (p : Subobject Y) : (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) := by
  revert p
  apply Quotient.ind'
  intro a
  apply Quotient.sound
  apply ThinSkeleton.equiv_of_both_ways
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _) _ ?_) (pullback.lift_snd _ _ _)
    change _ ≫ a.arrow ≫ h = (pullback.snd _ _ ≫ g) ≫ _
    rw [assoc, ← comm, pullback.condition_assoc]
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _)
      (PullbackCone.IsLimit.lift t (pullback.fst _ _ ≫ a.arrow) (pullback.snd _ _) _)
      (PullbackCone.IsLimit.lift_fst _ _ _ ?_).symm) ?_
    · rw [← pullback.condition, assoc]
      rfl
    · dsimp
      rw [pullback.lift_snd_assoc]
      apply PullbackCone.IsLimit.lift_snd

end Map

section Exists

variable [HasImages C]

/-- The functor from subobjects of `X` to subobjects of `Y` given by
sending the subobject `S` to its "image" under `f`, usually denoted $\exists_f$.
For instance, when `C` is the category of types,
viewing `Subobject X` as `Set X` this is just `Set.image f`.

This functor is left adjoint to the `pullback f` functor (shown in `existsPullbackAdj`)
provided both are defined, and generalises the `map f` functor, again provided it is defined.
-/
def «exists» (f : X ⟶ Y) : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.exists f)

/-- When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
theorem exists_iso_map (f : X ⟶ Y) [Mono f] : «exists» f = map f :=
  lower_iso _ _ (MonoOver.existsIsoMap f)

/-- `exists f : Subobject X ⥤ Subobject Y` is
left adjoint to `pullback f : Subobject Y ⥤ Subobject X`.
-/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  lowerAdjunction (MonoOver.existsPullbackAdj f)

end Exists

end Subobject

end CategoryTheory
