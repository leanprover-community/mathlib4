/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Isomorphisms

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure Iso` : a bundled isomorphism between two objects of a category;
- `class IsIso` : an unbundled version of `Iso`;
  note that `IsIso f` is a `Prop`, and only asserts the existence of an inverse.
  Of course, this inverse is unique, so it doesn't cost us much to use choice to retrieve it.
- `inv f`, for the inverse of a morphism with `[IsIso f]`
- `asIso` : convert from `IsIso` to `Iso` (noncomputable);
- `of_iso` : convert from `Iso` to `IsIso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notation

- `X ≅ Y` : same as `Iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `Iso.trans`

## Tags

category, category theory, isomorphism
-/

@[expose] public section

set_option mathlib.tactic.category.grind true

universe v u

-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

open Category

/-- An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `CategoryTheory.Core` for the category with the same objects and isomorphisms playing
the role of morphisms. -/
@[stacks 0017]
structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  /-- The forward direction of an isomorphism. -/
  hom : X ⟶ Y
  /-- The backwards direction of an isomorphism. -/
  inv : Y ⟶ X
  /-- Composition of the two directions of an isomorphism is the identity on the source. -/
  hom_inv_id : hom ≫ inv = 𝟙 X := by cat_disch
  /-- Composition of the two directions of an isomorphism in reverse order
  is the identity on the target. -/
  inv_hom_id : inv ≫ hom = 𝟙 Y := by cat_disch

attribute [to_dual existing inv] Iso.hom
attribute [to_dual self] Iso.mk Iso.casesOn
attribute [to_dual none] Iso.mk.hcongr_8 -- needed in `Iso.ext`

attribute [reassoc +to_dual (attr := simp), grind =] Iso.hom_inv_id Iso.inv_hom_id

/-- Notation for an isomorphism in a category. -/
infixr:10 " ≅ " => Iso -- type as \cong or \iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace Iso

set_option linter.style.whitespace false in -- manual alignment is not recognised
set_option linter.existingAttributeWarning false in
@[ext, grind ext, to_dual ext_inv]
theorem ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β :=
  suffices α.inv = β.inv by grind [Iso]
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by grind
    _     = β.inv                 := by grind

/-- Inverse isomorphism. -/
@[symm]
def symm (I : X ≅ Y) : Y ≅ X where
  hom := I.inv
  inv := I.hom

@[to_dual (attr := simp, grind =) symm_inv]
theorem symm_hom (α : X ≅ Y) : α.symm.hom = α.inv :=
  rfl

@[simp, grind =, to_dual self]
theorem symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) :
    Iso.symm { hom, inv, hom_inv_id := hom_inv_id, inv_hom_id := inv_hom_id } =
      { hom := inv, inv := hom, hom_inv_id := inv_hom_id, inv_hom_id := hom_inv_id } :=
  rfl

@[simp, grind =]
theorem symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α := rfl

theorem symm_bijective {X Y : C} : Function.Bijective (symm : (X ≅ Y) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm_eq, symm_symm_eq⟩

@[simp]
theorem symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β :=
  symm_bijective.injective.eq_iff

theorem nonempty_iso_symm (X Y : C) : Nonempty (X ≅ Y) ↔ Nonempty (Y ≅ X) :=
  ⟨fun h => ⟨h.some.symm⟩, fun h => ⟨h.some.symm⟩⟩

/-- Identity isomorphism. -/
@[refl, simps (attr := grind =)]
def refl (X : C) : X ≅ X where
  hom := 𝟙 X
  inv := 𝟙 X

set_option linter.existingAttributeWarning false in
attribute [to_dual existing refl_inv] refl_hom

instance : Inhabited (X ≅ X) := ⟨Iso.refl X⟩

theorem nonempty_iso_refl (X : C) : Nonempty (X ≅ X) := ⟨default⟩

@[simp, grind =]
theorem refl_symm (X : C) : (Iso.refl X).symm = Iso.refl X := rfl

/-- Composition of two isomorphisms -/
@[simps (attr := grind =)]
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
  hom := α.hom ≫ β.hom
  inv := β.inv ≫ α.inv

set_option linter.existingAttributeWarning false in
attribute [to_dual existing trans_inv] trans_hom

@[simps]
instance instTransIso : Trans (α := C) (· ≅ ·) (· ≅ ·) (· ≅ ·) where
  trans := trans

/-- Notation for composition of isomorphisms. -/
infixr:80 " ≪≫ " => Iso.trans -- type as `\ll \gg`.

-- Annotating this with `@[grind =]` triggers a run-away chain of `Category.assoc` instantiations.
-- Hopefully this can be restored when `grind` has support for associative/commutative operations,
-- or direct support for category theory.
@[simp, to_dual self]
theorem trans_mk {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
    (hom' : Y ⟶ Z) (inv' : Z ⟶ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
    Iso.trans ⟨hom, inv, hom_inv_id, inv_hom_id⟩ ⟨hom', inv', hom_inv_id', inv_hom_id'⟩ =
     ⟨hom ≫ hom', inv' ≫ inv, hom_inv_id'', inv_hom_id''⟩ :=
  rfl

@[simp, grind _=_]
theorem trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl

@[simp, grind _=_]
theorem trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') :
    (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ := by
  ext; simp only [trans_hom, Category.assoc]

@[simp]
theorem refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α = α := by ext; apply Category.id_comp

@[simp]
theorem trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y = α := by ext; apply Category.comp_id

@[simp]
theorem symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = Iso.refl Y :=
  ext α.inv_hom_id

@[simp]
theorem self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = Iso.refl X :=
  ext α.hom_inv_id

@[simp]
theorem symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β := by
  rw [← trans_assoc, symm_self_id, refl_trans]

@[simp]
theorem self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β := by
  rw [← trans_assoc, self_symm_id, refl_trans]

@[to_dual none]
theorem inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]
theorem eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f :=
  (inv_comp_eq α.symm).symm

@[to_dual none]
theorem comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]
theorem eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f :=
  (comp_inv_eq α.symm).symm

@[to_dual none]
theorem inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.hom = g.hom :=
  have : ∀ {X Y : C} (f g : X ≅ Y), f.hom = g.hom → f.inv = g.inv := fun f g h => by rw [ext h]
  ⟨this f.symm g.symm, this f g⟩

@[to_dual comp_inv_eq_id]
theorem hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.hom ≫ f = 𝟙 X ↔ f = α.inv := by
  rw [← eq_inv_comp, comp_id]

@[to_dual inv_comp_eq_id]
theorem comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv := by
  rw [← eq_comp_inv, id_comp]

@[to_dual inv_eq_hom]
theorem hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.hom = β.inv ↔ β.hom = α.inv := by
  rw [← symm_inv, inv_eq_inv α.symm β, eq_comm]
  rfl

attribute [local grind] Function.LeftInverse Function.RightInverse

/-- The bijection `(Z ⟶ X) ≃ (Z ⟶ Y)` induced by `α : X ≅ Y`. -/
@[to_dual (attr := simps) homFromEquiv
/-- The bijection `(X ⟶ Z) ≃ (Y ⟶ Z)` induced by `α : X ≅ Y`. -/]
def homToEquiv (α : X ≅ Y) {Z : C} : (Z ⟶ X) ≃ (Z ⟶ Y) where
  toFun f := f ≫ α.hom
  invFun g := g ≫ α.inv
  left_inv := by cat_disch
  right_inv := by cat_disch

end Iso

/-- The `IsIso` typeclass expresses that a morphism is invertible.

Given a morphism `f` with `IsIso f`, one can view `f` as an isomorphism via `asIso f` and get
the inverse using `inv f`. -/
@[to_dual self]
class IsIso (f : X ⟶ Y) : Prop where
  /-- The existence of an inverse morphism. -/
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

set_option linter.translateOverwrite false in
/-- `IsIso.mk'` is the dual of `IsIso.mk`, which we need for `to_dual`. -/
@[to_dual existing mk]
theorem IsIso.mk' {f : Y ⟶ X} (out : ∃ inv : X ⟶ Y, inv ≫ f = 𝟙 X ∧ f ≫ inv = 𝟙 Y) : IsIso f where
  out := by simp_all only [and_comm]

/-- The inverse of a morphism `f` when we have `[IsIso f]`. -/
@[to_dual self, no_expose]
noncomputable def inv (f : X ⟶ Y) [I : IsIso f] : Y ⟶ X :=
  Classical.choose I.1

namespace IsIso

theorem hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X :=
  (Classical.choose_spec I.1).left

@[to_dual existing (attr := reassoc (attr := simp), grind =) hom_inv_id]
theorem inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.choose_spec I.1).right

end IsIso

instance Iso.isIso_hom (e : X ≅ Y) : IsIso e.hom :=
  ⟨e.inv, by simp only [hom_inv_id], by simp⟩

@[to_dual existing isIso_hom]
instance Iso.isIso_inv (e : X ≅ Y) : IsIso e.inv := e.symm.isIso_hom

open IsIso

/-- Reinterpret a morphism `f : X ⟶ Y` with an `IsIso f` instance as `X ≅ Y`. -/
@[to_dual asIso' /-- Reinterpret a morphism `f : X ⟶ Y` with an `IsIso f` instance as `Y ≅ X`. -/]
noncomputable def asIso (f : X ⟶ Y) [IsIso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[to_dual (attr := simp) asIso'_hom]
theorem asIso_hom (f : X ⟶ Y) [IsIso f] : (asIso f).hom = f :=
  rfl

@[to_dual (attr := simp) asIso'_inv]
theorem asIso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).inv = inv f :=
  rfl

namespace IsIso

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) epi_of_iso (f : X ⟶ Y) [IsIso f] : Epi f where
  left_cancellation g h w := by
    rw [← IsIso.inv_hom_id_assoc f g, w, IsIso.inv_hom_id_assoc f h]

@[aesop apply safe (rule_sets := [CategoryTheory]), grind ←=, to_dual inv_eq_of_inv_hom_id]
theorem inv_eq_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    inv f = g := by
  have := congrArg (inv f ≫ ·) hom_inv_id
  grind

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual eq_inv_of_inv_hom_id]
theorem eq_inv_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    g = inv f :=
  (inv_eq_of_hom_inv_id hom_inv_id).symm

instance id (X : C) : IsIso (𝟙 X) := ⟨⟨𝟙 X, by simp⟩⟩

variable {f : X ⟶ Y} {h : Y ⟶ Z}

@[to_dual self]
instance inv_isIso [IsIso f] : IsIso (inv f) :=
  (asIso f).isIso_inv

/- The following instance has lower priority for the following reason:
Suppose we are given `f : X ≅ Y` with `X Y : Type u`.
Without the lower priority, typeclass inference cannot deduce `IsIso f.hom`
because `f.hom` is defeq to `(fun x ↦ x) ≫ f.hom`, triggering a loop. -/
@[to_dual self (reorder := X Z, f h, 8 9)]
instance (priority := 900) comp_isIso [IsIso f] [IsIso h] : IsIso (f ≫ h) :=
  (asIso f ≪≫ asIso h).isIso_hom

/--
The composition of isomorphisms is an isomorphism. Here the arguments of type `IsIso` are
explicit, to make this easier to use with the `refine` tactic, for instance.
-/
@[to_dual self (reorder := X Z, f h, 8 9)]
lemma comp_isIso' (_ : IsIso f) (_ : IsIso h) : IsIso (f ≫ h) := inferInstance

@[simp]
theorem inv_id : inv (𝟙 X) = 𝟙 X := by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, reassoc, push, to_dual self]
theorem inv_comp [IsIso f] [IsIso h] : inv (f ≫ h) = inv h ≫ inv f := by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, push, to_dual self]
theorem inv_inv [IsIso f] : inv (inv f) = f := by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp, push) inv_hom]
theorem Iso.inv_inv (f : X ≅ Y) : inv f.inv = f.hom := by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp) comp_inv_eq]
theorem inv_comp_eq (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g :=
  (asIso α).inv_comp_eq

@[to_dual (attr := simp) eq_comp_inv]
theorem eq_inv_comp (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f :=
  (asIso α).eq_inv_comp

@[to_dual (reorder := f g) of_isIso_comp_right]
theorem of_isIso_comp_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] :
    IsIso g := by
  rw [← id_comp g, ← inv_hom_id f, assoc]
  infer_instance

@[to_dual of_isIso_fac_right]
theorem of_isIso_fac_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f]
    [hh : IsIso h] (w : f ≫ g = h) : IsIso g := by
  rw [← w] at hh
  exact of_isIso_comp_left f g

end IsIso

@[to_dual (attr := simp) (reorder := f g) isIso_comp_right_iff]
theorem isIso_comp_left_iff {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsIso (f ≫ g) ↔ IsIso g :=
  ⟨fun _ ↦ IsIso.of_isIso_comp_left f g, fun _ ↦ inferInstance⟩

open IsIso

@[to_dual self]
theorem eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g) : f = g := by
  apply (cancel_epi (inv f)).1
  rw [inv_hom_id, p, inv_hom_id]

@[to_dual self]
theorem IsIso.inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] : inv f = inv g ↔ f = g :=
  Iso.inv_eq_inv (asIso f) (asIso g)

@[to_dual comp_hom_eq_id]
theorem hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
  (asIso g).hom_comp_eq_id

@[to_dual comp_inv_eq_id]
theorem inv_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : inv g ≫ f = 𝟙 Y ↔ f = g :=
  (asIso g).inv_comp_eq_id

@[to_dual isIso_of_comp_hom_eq_id]
theorem isIso_of_hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X) : IsIso f := by
  rw [(hom_comp_eq_id _).mp h]
  infer_instance

namespace Iso

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]
theorem inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : f.inv = g :=
  ((hom_comp_eq_id f).1 hom_inv_id).symm

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]
theorem inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : g = f.inv :=
  (hom_comp_eq_id f).1 hom_inv_id

/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/


@[to_dual (attr := simp) (reorder := f g' g) cancel_iso_inv_right]
theorem cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) :
    f.hom ≫ g = f.hom ≫ g' ↔ g = g' := by
  simp only [cancel_epi]

@[to_dual (attr := simp) (reorder := f f' g) cancel_iso_inv_left]
theorem cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) :
    f ≫ g.hom = f' ≫ g.hom ↔ f = f' := by
  simp only [cancel_mono]

/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/
@[simp, to_dual none]
theorem cancel_iso_hom_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Y ≅ Z) : f ≫ g ≫ h.hom = f' ≫ g' ≫ h.hom ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
theorem cancel_iso_inv_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Z ≅ Y) : f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

section

variable {D : Type*} [Category* D] {X Y : C} (e : X ≅ Y)

@[reassoc +to_dual (attr := simp), grind =]
lemma map_hom_inv_id (F : C ⥤ D) :
    F.map e.hom ≫ F.map e.inv = 𝟙 _ := by grind

@[reassoc +to_dual (attr := simp), grind =]
lemma map_inv_hom_id (F : C ⥤ D) :
    F.map e.inv ≫ F.map e.hom = 𝟙 _ := by grind

end

end Iso

namespace Functor

universe u₁ v₁ u₂ v₂

variable {D : Type u₂}
variable [Category.{v₂} D]

/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
@[simps]
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map i.hom
  inv := F.map i.inv

set_option linter.existingAttributeWarning false in
attribute [to_dual existing mapIso_inv] mapIso_hom

@[simp]
theorem mapIso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.mapIso i.symm = (F.mapIso i).symm :=
  rfl

@[simp]
theorem mapIso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
    F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j := by
  ext; apply Functor.map_comp

@[simp]
theorem mapIso_refl (F : C ⥤ D) (X : C) : F.mapIso (Iso.refl X) = Iso.refl (F.obj X) :=
  Iso.ext <| F.map_id X

@[to_dual self]
instance map_isIso (F : C ⥤ D) (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) :=
  (F.mapIso (asIso f)).isIso_hom

@[simp, push ←, to_dual self]
theorem map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) = inv (F.map f) := by
  apply eq_inv_of_hom_inv_id
  simp [← F.map_comp]

@[to_dual (attr := reassoc) map_inv_hom]
theorem map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) := by simp

end Functor

end CategoryTheory
