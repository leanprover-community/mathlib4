/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!

# Equifibered natural transformation

## Main definition
- `CategoryTheory.NatTrans.Equifibered`:
A natural transformation `α : F ⟶ G` is equifibered if every commutative square of the following
form is a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
- `CategoryTheory.NatTrans.Coequifibered`: The dual notion.

-/

@[expose] public section


open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

variable {J K C D ι : Type*} [Category* J] [Category* C] [Category* K] [Category* D]

namespace NatTrans

/-- A natural transformation is equifibered if every commutative square of the following form is
a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def Equifibered : MorphismProperty (J ⥤ C) :=
  fun {F G} α ↦ ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

theorem Equifibered.of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Equifibered α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias equifibered_of_isIso := Equifibered.of_isIso

theorem Equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
    (hβ : Equifibered β) : Equifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)

instance : (Equifibered (J := J) (C := C)).IsMultiplicative where
  id_mem _ := .of_isIso _
  comp_mem _ _ := .comp

instance : (Equifibered (J := J) (C := C)).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ ↦ .of_isIso

theorem Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
    (H : C ⥤ D) [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
    Equifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H

theorem Equifibered.whiskerLeft {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) (H : K ⥤ J) :
    Equifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem Equifibered.of_discrete {F G : Discrete ι ⥤ C} (α : F ⟶ G) : Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

@[deprecated (since := "2026-01-23")]
alias _root_.CategoryTheory.mapPair_equifibered := Equifibered.of_discrete

@[deprecated (since := "2026-01-23")] alias equifibered_of_discrete := Equifibered.of_discrete

/-- A natural transformation is co-equifibered if every commutative square of the following form is
a pushout.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def Coequifibered : MorphismProperty (J ⥤ C) :=
  fun {F G} α ↦ ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPushout (F.map f) (α.app i) (α.app j) (G.map f)

theorem Coequifibered.of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Coequifibered α :=
  fun _ _ f => .of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias Coequifibered_of_isIso := Coequifibered.of_isIso

theorem Coequifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Coequifibered α)
    (hβ : Coequifibered β) : Coequifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)

instance : (Coequifibered (J := J) (C := C)).IsMultiplicative where
  id_mem _ := .of_isIso _
  comp_mem _ _ := .comp

instance : (Coequifibered (J := J) (C := C)).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ ↦ .of_isIso

theorem Coequifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
    (H : C ⥤ D) [∀ (i j : J) (f : j ⟶ i), PreservesColimit (span (F.map f) (α.app j)) H] :
    Coequifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H

theorem Coequifibered.whiskerLeft {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) (H : K ⥤ J) :
    Coequifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem Coequifibered.of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

section Opposite

theorem Coequifibered.op {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered (NatTrans.op α) := fun _ _ f ↦ (hα f.unop).op

theorem Equifibered.op {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered (NatTrans.op α) := fun _ _ f ↦ (hα f.unop).op

theorem Coequifibered.unop {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered (NatTrans.unop α) := fun _ _ f ↦ (hα f.op).unop

theorem Equifibered.unop {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered (NatTrans.unop α) := fun _ _ f ↦ (hα f.op).unop

theorem coequifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} :
    Coequifibered (NatTrans.op α) ↔ Equifibered α := ⟨Coequifibered.unop, Equifibered.op⟩

theorem equifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} :
    Equifibered (NatTrans.op α) ↔ Coequifibered α := ⟨Equifibered.unop, Coequifibered.op⟩

theorem coequifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} :
    Coequifibered (NatTrans.unop α) ↔ Equifibered α := ⟨Coequifibered.op, Equifibered.unop⟩

theorem equifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} :
    Equifibered (NatTrans.unop α) ↔ Coequifibered α := ⟨Equifibered.op, Coequifibered.unop⟩

end Opposite

end NatTrans

end CategoryTheory
