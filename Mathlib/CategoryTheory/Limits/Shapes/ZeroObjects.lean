/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

#align_import category_theory.limits.shapes.zero_objects from "leanprover-community/mathlib"@"74333bd53d25b6809203a2bfae80eea5fc1fc076"

/-!
# Zero objects

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object;
see `CategoryTheory.Limits.Shapes.ZeroMorphisms`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v u v' u'

open CategoryTheory

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

namespace CategoryTheory

namespace Limits

/-- An object `X` in a category is a *zero object* if for every object `Y`
there is a unique morphism `to : X → Y` and a unique morphism `from : Y → X`.

This is a characteristic predicate for `has_zero_object`. -/
structure IsZero (X : C) : Prop where
  /-- there are unique morphisms to the object -/
  unique_to : ∀ Y, Nonempty (Unique (X ⟶ Y))
  /-- there are unique morphisms from the object -/
  unique_from : ∀ Y, Nonempty (Unique (Y ⟶ X))
#align category_theory.limits.is_zero CategoryTheory.Limits.IsZero

namespace IsZero

variable {X Y : C}

-- Porting note: `to` is a reserved word, it was replaced by `to_`
/-- If `h : IsZero X`, then `h.to_ Y` is a choice of unique morphism `X → Y`. -/
protected def to_ (h : IsZero X) (Y : C) : X ⟶ Y :=
  @default _ <| (h.unique_to Y).some.toInhabited
#align category_theory.limits.is_zero.to CategoryTheory.Limits.IsZero.to_

theorem eq_to (h : IsZero X) (f : X ⟶ Y) : f = h.to_ Y :=
  @Unique.eq_default _ (id _) _
#align category_theory.limits.is_zero.eq_to CategoryTheory.Limits.IsZero.eq_to

theorem to_eq (h : IsZero X) (f : X ⟶ Y) : h.to_ Y = f :=
  (h.eq_to f).symm
#align category_theory.limits.is_zero.to_eq CategoryTheory.Limits.IsZero.to_eq

-- Porting note: `from` is a reserved word, it was replaced by `from_`
/-- If `h : is_zero X`, then `h.from_ Y` is a choice of unique morphism `Y → X`. -/
protected def from_ (h : IsZero X) (Y : C) : Y ⟶ X :=
  @default _ <| (h.unique_from Y).some.toInhabited
#align category_theory.limits.is_zero.from CategoryTheory.Limits.IsZero.from_

theorem eq_from (h : IsZero X) (f : Y ⟶ X) : f = h.from_ Y :=
  @Unique.eq_default _ (id _) _
#align category_theory.limits.is_zero.eq_from CategoryTheory.Limits.IsZero.eq_from

theorem from_eq (h : IsZero X) (f : Y ⟶ X) : h.from_ Y = f :=
  (h.eq_from f).symm
#align category_theory.limits.is_zero.from_eq CategoryTheory.Limits.IsZero.from_eq

theorem eq_of_src (hX : IsZero X) (f g : X ⟶ Y) : f = g :=
  (hX.eq_to f).trans (hX.eq_to g).symm
#align category_theory.limits.is_zero.eq_of_src CategoryTheory.Limits.IsZero.eq_of_src

theorem eq_of_tgt (hX : IsZero X) (f g : Y ⟶ X) : f = g :=
  (hX.eq_from f).trans (hX.eq_from g).symm
#align category_theory.limits.is_zero.eq_of_tgt CategoryTheory.Limits.IsZero.eq_of_tgt

/-- Any two zero objects are isomorphic. -/
def iso (hX : IsZero X) (hY : IsZero Y) : X ≅ Y where
  hom := hX.to_ Y
  inv := hX.from_ Y
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := hY.eq_of_src _ _
#align category_theory.limits.is_zero.iso CategoryTheory.Limits.IsZero.iso

/-- A zero object is in particular initial. -/
protected def isInitial (hX : IsZero X) : IsInitial X :=
  @IsInitial.ofUnique _ _ X fun Y => (hX.unique_to Y).some
#align category_theory.limits.is_zero.is_initial CategoryTheory.Limits.IsZero.isInitial

/-- A zero object is in particular terminal. -/
protected def isTerminal (hX : IsZero X) : IsTerminal X :=
  @IsTerminal.ofUnique _ _ X fun Y => (hX.unique_from Y).some
#align category_theory.limits.is_zero.is_terminal CategoryTheory.Limits.IsZero.isTerminal

/-- The (unique) isomorphism between any initial object and the zero object. -/
def isoIsInitial (hX : IsZero X) (hY : IsInitial Y) : X ≅ Y :=
  IsInitial.uniqueUpToIso hX.isInitial hY
#align category_theory.limits.is_zero.iso_is_initial CategoryTheory.Limits.IsZero.isoIsInitial

/-- The (unique) isomorphism between any terminal object and the zero object. -/
def isoIsTerminal (hX : IsZero X) (hY : IsTerminal Y) : X ≅ Y :=
  IsTerminal.uniqueUpToIso hX.isTerminal hY
#align category_theory.limits.is_zero.iso_is_terminal CategoryTheory.Limits.IsZero.isoIsTerminal

theorem of_iso (hY : IsZero Y) (e : X ≅ Y) : IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ e.inv⟩, fun f => ?_⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt
#align category_theory.limits.is_zero.of_iso CategoryTheory.Limits.IsZero.of_iso

theorem op (h : IsZero X) : IsZero (Opposite.op X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩
#align category_theory.limits.is_zero.op CategoryTheory.Limits.IsZero.op

theorem unop {X : Cᵒᵖ} (h : IsZero X) : IsZero (Opposite.unop X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_src _ _)⟩⟩⟩
#align category_theory.limits.is_zero.unop CategoryTheory.Limits.IsZero.unop

end IsZero

end Limits

open CategoryTheory.Limits

theorem Iso.isZero_iff {X Y : C} (e : X ≅ Y) : IsZero X ↔ IsZero Y :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩
#align category_theory.iso.is_zero_iff CategoryTheory.Iso.isZero_iff

theorem Functor.isZero (F : C ⥤ D) (hF : ∀ X, IsZero (F.obj X)) : IsZero F := by
  constructor <;> intro G <;> refine ⟨⟨⟨?_⟩, ?_⟩⟩
  · refine
      { app := fun X => (hF _).to_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_src _ _
  · intro f
    ext
    apply (hF _).eq_of_src _ _
  · refine
      { app := fun X => (hF _).from_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_tgt _ _
  · intro f
    ext
    apply (hF _).eq_of_tgt _ _
#align category_theory.functor.is_zero CategoryTheory.Functor.isZero

namespace Limits

variable (C)

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class HasZeroObject : Prop where
  /-- there exists a zero object -/
  zero : ∃ X : C, IsZero X
#align category_theory.limits.has_zero_object CategoryTheory.Limits.HasZeroObject

instance hasZeroObject_pUnit : HasZeroObject (Discrete PUnit) where zero :=
  ⟨⟨⟨⟩⟩,
    { unique_to := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := fun _ => Subsingleton.elim _ _ }⟩
      unique_from := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := fun _ => Subsingleton.elim _ _ }⟩}⟩
#align category_theory.limits.has_zero_object_punit CategoryTheory.Limits.hasZeroObject_pUnit

section

variable [HasZeroObject C]

/-- Construct a `Zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `Zero C` typeclass search.
-/
protected def HasZeroObject.zero' : Zero C where zero := HasZeroObject.zero.choose
#align category_theory.limits.has_zero_object.has_zero CategoryTheory.Limits.HasZeroObject.zero'

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'

open ZeroObject

theorem isZero_zero : IsZero (0 : C) :=
  HasZeroObject.zero.choose_spec
#align category_theory.limits.is_zero_zero CategoryTheory.Limits.isZero_zero

instance hasZeroObject_op : HasZeroObject Cᵒᵖ :=
  ⟨⟨Opposite.op 0, IsZero.op (isZero_zero C)⟩⟩
#align category_theory.limits.has_zero_object_op CategoryTheory.Limits.hasZeroObject_op

end

open ZeroObject

theorem hasZeroObject_unop [HasZeroObject Cᵒᵖ] : HasZeroObject C :=
  ⟨⟨Opposite.unop 0, IsZero.unop (isZero_zero Cᵒᵖ)⟩⟩
#align category_theory.limits.has_zero_object_unop CategoryTheory.Limits.hasZeroObject_unop

variable {C}

theorem IsZero.hasZeroObject {X : C} (hX : IsZero X) : HasZeroObject C :=
  ⟨⟨X, hX⟩⟩
#align category_theory.limits.is_zero.has_zero_object CategoryTheory.Limits.IsZero.hasZeroObject

/-- Every zero object is isomorphic to *the* zero object. -/
def IsZero.isoZero [HasZeroObject C] {X : C} (hX : IsZero X) : X ≅ 0 :=
  hX.iso (isZero_zero C)
#align category_theory.limits.is_zero.iso_zero CategoryTheory.Limits.IsZero.isoZero

theorem IsZero.obj [HasZeroObject D] {F : C ⥤ D} (hF : IsZero F) (X : C) : IsZero (F.obj X) := by
  let G : C ⥤ D := (CategoryTheory.Functor.const C).obj 0
  have hG : IsZero G := Functor.isZero _ fun _ => isZero_zero _
  let e : F ≅ G := hF.iso hG
  exact (isZero_zero _).of_iso (e.app X)
#align category_theory.limits.is_zero.obj CategoryTheory.Limits.IsZero.obj

namespace HasZeroObject

variable [HasZeroObject C]

/-- There is a unique morphism from the zero object to any object `X`. -/
protected def uniqueTo (X : C) : Unique (0 ⟶ X) :=
  ((isZero_zero C).unique_to X).some
#align category_theory.limits.has_zero_object.unique_to CategoryTheory.Limits.HasZeroObject.uniqueTo

/-- There is a unique morphism from any object `X` to the zero object. -/
protected def uniqueFrom (X : C) : Unique (X ⟶ 0) :=
  ((isZero_zero C).unique_from X).some
#align category_theory.limits.has_zero_object.unique_from CategoryTheory.Limits.HasZeroObject.uniqueFrom

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[ext]
theorem to_zero_ext {X : C} (f g : X ⟶ 0) : f = g :=
  (isZero_zero C).eq_of_tgt _ _
#align category_theory.limits.has_zero_object.to_zero_ext CategoryTheory.Limits.HasZeroObject.to_zero_ext

@[ext]
theorem from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g :=
  (isZero_zero C).eq_of_src _ _
#align category_theory.limits.has_zero_object.from_zero_ext CategoryTheory.Limits.HasZeroObject.from_zero_ext

instance (X : C) : Subsingleton (X ≅ 0) := ⟨fun f g => by ext⟩

instance {X : C} (f : 0 ⟶ X) : Mono f where right_cancellation g h _ := by ext

instance {X : C} (f : X ⟶ 0) : Epi f where left_cancellation g h _ := by ext

instance zero_to_zero_isIso (f : (0 : C) ⟶ 0) : IsIso f := by
  convert show IsIso (𝟙 (0 : C)) by infer_instance
  apply Subsingleton.elim
#align category_theory.limits.has_zero_object.zero_to_zero_is_iso CategoryTheory.Limits.HasZeroObject.zero_to_zero_isIso

/-- A zero object is in particular initial. -/
def zeroIsInitial : IsInitial (0 : C) :=
  (isZero_zero C).isInitial
#align category_theory.limits.has_zero_object.zero_is_initial CategoryTheory.Limits.HasZeroObject.zeroIsInitial

/-- A zero object is in particular terminal. -/
def zeroIsTerminal : IsTerminal (0 : C) :=
  (isZero_zero C).isTerminal
#align category_theory.limits.has_zero_object.zero_is_terminal CategoryTheory.Limits.HasZeroObject.zeroIsTerminal

/-- A zero object is in particular initial. -/
instance (priority := 10) hasInitial : HasInitial C :=
  hasInitial_of_unique 0
#align category_theory.limits.has_zero_object.has_initial CategoryTheory.Limits.HasZeroObject.hasInitial

/-- A zero object is in particular terminal. -/
instance (priority := 10) hasTerminal : HasTerminal C :=
  hasTerminal_of_unique 0
#align category_theory.limits.has_zero_object.has_terminal CategoryTheory.Limits.HasZeroObject.hasTerminal

/-- The (unique) isomorphism between any initial object and the zero object. -/
def zeroIsoIsInitial {X : C} (t : IsInitial X) : 0 ≅ X :=
  zeroIsInitial.uniqueUpToIso t
#align category_theory.limits.has_zero_object.zero_iso_is_initial CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial

/-- The (unique) isomorphism between any terminal object and the zero object. -/
def zeroIsoIsTerminal {X : C} (t : IsTerminal X) : 0 ≅ X :=
  zeroIsTerminal.uniqueUpToIso t
#align category_theory.limits.has_zero_object.zero_iso_is_terminal CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal

/-- The (unique) isomorphism between the chosen initial object and the chosen zero object. -/
def zeroIsoInitial [HasInitial C] : 0 ≅ ⊥_ C :=
  zeroIsInitial.uniqueUpToIso initialIsInitial
#align category_theory.limits.has_zero_object.zero_iso_initial CategoryTheory.Limits.HasZeroObject.zeroIsoInitial

/-- The (unique) isomorphism between the chosen terminal object and the chosen zero object. -/
def zeroIsoTerminal [HasTerminal C] : 0 ≅ ⊤_ C :=
  zeroIsTerminal.uniqueUpToIso terminalIsTerminal
#align category_theory.limits.has_zero_object.zero_iso_terminal CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal

instance (priority := 100) initialMonoClass : InitialMonoClass C :=
  InitialMonoClass.of_isInitial zeroIsInitial fun X => by infer_instance
#align category_theory.limits.has_zero_object.has_strict_initial CategoryTheory.Limits.HasZeroObject.initialMonoClass

end HasZeroObject

end Limits

open CategoryTheory.Limits

open ZeroObject

theorem Functor.isZero_iff [HasZeroObject D] (F : C ⥤ D) : IsZero F ↔ ∀ X, IsZero (F.obj X) :=
  ⟨fun hF X => hF.obj X, Functor.isZero _⟩
#align category_theory.functor.is_zero_iff CategoryTheory.Functor.isZero_iff

end CategoryTheory
