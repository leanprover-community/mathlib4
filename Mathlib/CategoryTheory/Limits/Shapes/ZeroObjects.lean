/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Zero objects

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object;
see `CategoryTheory.Limits.Shapes.ZeroMorphisms`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe v u v' u'

open CategoryTheory

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

namespace CategoryTheory

namespace Limits

to_dual_name_hint To From

/-- An object `X` in a category is a *zero object* if for every object `Y`
there is a unique morphism `to : X → Y` and a unique morphism `from : Y → X`.

This is a characteristic predicate for `HasZeroObject`. -/
structure IsZero (X : C) : Prop where
  /-- there are unique morphisms to the object -/
  unique_to : ∀ Y, Nonempty (Unique (X ⟶ Y))
  /-- there are unique morphisms from the object -/
  unique_from : ∀ Y, Nonempty (Unique (Y ⟶ X))

attribute [to_dual existing] IsZero.unique_to
attribute [to_dual self (reorder := unique_to unique_from)] IsZero.mk
namespace IsZero

variable {X Y : C}

/-- If `h : IsZero X`, then `h.to_ Y` is a choice of unique morphism `X → Y`.

`to` is a reserved word, it was replaced by `to_`
-/
@[no_expose, to_dual
/-- If `h : is_zero X`, then `h.from_ Y` is a choice of unique morphism `Y → X`.

`from` is a reserved word, it was replaced by `from_`
-/]
protected def to_ (h : IsZero X) (Y : C) : X ⟶ Y :=
  (h.unique_to Y).some.default

@[to_dual]
theorem eq_to (h : IsZero X) (f : X ⟶ Y) : f = h.to_ Y :=
  @Unique.eq_default _ (id _) _

@[to_dual]
theorem to_eq (h : IsZero X) (f : X ⟶ Y) : h.to_ Y = f :=
  (h.eq_to f).symm

@[to_dual eq_of_tgt]
theorem eq_of_src (hX : IsZero X) (f g : X ⟶ Y) : f = g :=
  (hX.eq_to f).trans (hX.eq_to g).symm

@[to_dual]
lemma epi (h : IsZero X) {Y : C} (f : Y ⟶ X) : Epi f where
  left_cancellation _ _ _ := h.eq_of_src _ _

/-- Any two zero objects are isomorphic. -/
def iso (hX : IsZero X) (hY : IsZero Y) : X ≅ Y where
  hom := hX.to_ Y
  inv := hX.from_ Y
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := hY.eq_of_src _ _

@[to_dual self (reorder := X Y, hX hY)]
lemma isIso (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f :=
  ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

/-- A zero object is in particular initial. -/
@[to_dual /-- A zero object is in particular terminal. -/]
protected def isInitial (hX : IsZero X) : IsInitial X :=
  @IsInitial.ofUnique _ _ X fun Y => (hX.unique_to Y).some

/-- The (unique) isomorphism between any initial object and the zero object. -/
@[to_dual /-- The (unique) isomorphism between any terminal object and the zero object. -/]
def isoIsInitial (hX : IsZero X) (hY : IsInitial Y) : X ≅ Y :=
  IsInitial.uniqueUpToIso hX.isInitial hY

theorem of_iso (hY : IsZero Y) (e : X ≅ Y) : IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ e.inv⟩, fun f => ?_⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt

theorem op (h : IsZero X) : IsZero (Opposite.op X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩

theorem unop {X : Cᵒᵖ} (h : IsZero X) : IsZero (Opposite.unop X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

variable (Y) in
/-- A zero object is a retract of every object. -/
def retract (h : IsZero X) : Retract X Y where
  i := h.to_ Y
  r := h.from_ Y
  retract := h.isInitial.hom_ext _ _

end IsZero

end Limits

open CategoryTheory.Limits

theorem Iso.isZero_iff {X Y : C} (e : X ≅ Y) : IsZero X ↔ IsZero Y :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

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

namespace Limits

variable (C)

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class HasZeroObject : Prop where
  /-- there exists a zero object -/
  zero : ∃ X : C, IsZero X

instance hasZeroObject_pUnit : HasZeroObject (Discrete PUnit) where zero :=
  ⟨⟨⟨⟩⟩,
    { unique_to := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩
      unique_from := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩}⟩

section

variable [HasZeroObject C]

/-- Construct a `Zero C` for a category with a zero object.
This cannot be a global instance as it will trigger for every `Zero C` typeclass search.
-/
@[instance_reducible]
protected def HasZeroObject.zero' : Zero C where zero := HasZeroObject.zero.choose

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'

open ZeroObject

theorem isZero_zero : IsZero (0 : C) :=
  HasZeroObject.zero.choose_spec

instance hasZeroObject_op : HasZeroObject Cᵒᵖ :=
  ⟨⟨Opposite.op 0, IsZero.op (isZero_zero C)⟩⟩

end

open ZeroObject

theorem hasZeroObject_unop [HasZeroObject Cᵒᵖ] : HasZeroObject C :=
  ⟨⟨Opposite.unop 0, IsZero.unop (isZero_zero Cᵒᵖ)⟩⟩

variable {C}

theorem IsZero.hasZeroObject {X : C} (hX : IsZero X) : HasZeroObject C :=
  ⟨⟨X, hX⟩⟩

/-- Every zero object is isomorphic to *the* zero object. -/
def IsZero.isoZero [HasZeroObject C] {X : C} (hX : IsZero X) : X ≅ 0 :=
  hX.iso (isZero_zero C)

theorem IsZero.obj [HasZeroObject D] {F : C ⥤ D} (hF : IsZero F) (X : C) : IsZero (F.obj X) := by
  let G : C ⥤ D := (CategoryTheory.Functor.const C).obj 0
  have hG : IsZero G := Functor.isZero _ fun _ => isZero_zero _
  let e : F ≅ G := hF.iso hG
  exact (isZero_zero _).of_iso (e.app X)

lemma IsZero.of_full_of_faithful_of_isZero
    (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) (hX : IsZero (F.obj X)) :
    IsZero X := by
  have h : F.FullyFaithful := .ofFullyFaithful _
  have (Y : C) := (hX.unique_to (F.obj Y)).some
  have (Y : C) := (hX.unique_from (F.obj Y)).some
  exact ⟨fun Y ↦ ⟨h.homEquiv.unique⟩, fun Y ↦ ⟨h.homEquiv.unique⟩⟩

namespace HasZeroObject

variable [HasZeroObject C]

/-- There is a unique morphism from the zero object to any object `X`. -/
@[to_dual (attr := instance_reducible)
/-- There is a unique morphism from any object `X` to the zero object. -/]
protected def uniqueTo (X : C) : Unique (0 ⟶ X) :=
  ((isZero_zero C).unique_to X).some

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo
scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[to_dual (attr := ext)]
theorem to_zero_ext {X : C} (f g : X ⟶ 0) : f = g :=
  (isZero_zero C).eq_of_tgt _ _

instance (X : C) : Subsingleton (X ≅ 0) := ⟨fun f g => by ext⟩

@[to_dual]
instance {X : C} (f : X ⟶ 0) : Epi f where left_cancellation g h _ := by ext

instance zero_to_zero_isIso (f : (0 : C) ⟶ 0) : IsIso f := by
  convert! show IsIso (𝟙 (0 : C)) by infer_instance
  subsingleton

/-- A zero object is in particular initial. -/
@[to_dual /-- A zero object is in particular terminal. -/]
def zeroIsInitial : IsInitial (0 : C) :=
  (isZero_zero C).isInitial

/-- A zero object is in particular initial. -/
@[to_dual /-- A zero object is in particular terminal. -/]
instance (priority := 10) hasInitial : HasInitial C :=
  hasInitial_of_unique 0

/-- The (unique) isomorphism between any initial object and the zero object. -/
@[to_dual /-- The (unique) isomorphism between any terminal object and the zero object. -/]
def zeroIsoIsInitial {X : C} (t : IsInitial X) : 0 ≅ X :=
  zeroIsInitial.uniqueUpToIso t

/-- The (unique) isomorphism between the chosen initial object and the chosen zero object. -/
@[to_dual
/-- The (unique) isomorphism between the chosen terminal object and the chosen zero object. -/]
def zeroIsoInitial [HasInitial C] : 0 ≅ ⊥_ C :=
  zeroIsInitial.uniqueUpToIso initialIsInitial

instance (priority := 100) initialMonoClass : InitialMonoClass C :=
  InitialMonoClass.of_isInitial zeroIsInitial fun X => by infer_instance

end HasZeroObject

end Limits

open CategoryTheory.Limits

open ZeroObject

theorem Functor.isZero_iff [HasZeroObject D] (F : C ⥤ D) : IsZero F ↔ ∀ X, IsZero (F.obj X) :=
  ⟨fun hF X => hF.obj X, Functor.isZero _⟩

@[to_dual]
instance {C : Type*} [Category* C] (A : C) [HasZeroObject C] : Epi (terminalIsTerminal.from A) :=
  (((isZero_zero C).of_iso HasZeroObject.zeroIsoTerminal.symm).epi _)

end CategoryTheory
