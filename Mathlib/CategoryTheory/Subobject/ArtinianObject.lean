/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Order.OrderIsoNat
import Mathlib.CategoryTheory.Simple

/-!
# Artinian objects

We shall say that an object `X` in a category `C` is Artinian
(type class `IsArtinianObject X`) if the ordered type `Subobject X`
satisfies the descending chain condition. The corresponding property of
objects `isArtinianObject : ObjectProperty C` is always
closed under subobjects.

## Future works

* when `C` is an abelian category, relate `IsArtinianObject` in `C`
with `IsNoetherianObject` in `Cᵒᵖ`.

-/

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

/-- An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Artinian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsArtinianObject` instead. -/
@[stacks 0FCF]
def isArtinianObject : ObjectProperty C :=
  fun X ↦ WellFoundedLT (Subobject X)

variable (X Y : C)

/-- An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition. -/
@[stacks 0FCF]
abbrev IsArtinianObject : Prop := isArtinianObject.Is X

instance [IsArtinianObject X] : WellFoundedLT (Subobject X) :=
  isArtinianObject.prop_of_is X

lemma isArtinianObject_iff_antitone_chain_condition :
    IsArtinianObject X ↔ ∀ (f : ℕ →o (Subobject X)ᵒᵈ),
      ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m := by
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff, isArtinianObject,
    ← wellFoundedGT_dual_iff,
    wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
lemma antitone_chain_condition_of_isArtinianObject
    [IsArtinianObject X] (f : ℕ →o (Subobject X)ᵒᵈ) :
    ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m :=
  (isArtinianObject_iff_antitone_chain_condition X).1 inferInstance f

lemma isArtinianObject_iff_not_strictAnti :
    IsArtinianObject X ↔ ∀ (f : ℕ → Subobject X), ¬ StrictAnti f := by
  refine ⟨fun _ ↦ not_strictAnti_of_wellFoundedLT, fun h ↦ ?_⟩
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff, isArtinianObject, WellFoundedLT,
    isWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
  exact ⟨fun f ↦ h f.toFun (fun a b h ↦ f.map_rel_iff.2 h)⟩

variable {X} in
lemma not_strictAnti_of_isArtinianObject
    [IsArtinianObject X] (f : ℕ → Subobject X) :
    ¬ StrictAnti f :=
  (isArtinianObject_iff_not_strictAnti X).1 inferInstance f

lemma isArtinianObject_iff_isEventuallyConstant :
    IsArtinianObject X ↔ ∀ (F : ℕ ⥤ (MonoOver X)ᵒᵖ),
      IsFiltered.IsEventuallyConstant F := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  refine ⟨fun h G ↦ ?_, fun h F ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h ⟨_, (G ⋙ (Subobject.equivMonoOver X).inverse.op ⋙
      (orderDualEquivalence _).inverse).monotone⟩
    refine ⟨n, fun m hm ↦ ?_⟩
    rw [← isIso_unop_iff, MonoOver.isIso_iff_subobjectMk_eq]
    exact (hn m (leOfHom hm)).symm
  · obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ (orderDualEquivalence _).functor ⋙
      Subobject.representative.op)
    refine ⟨n, fun m hm ↦ Eq.symm ?_⟩
    simpa [isIso_op_iff, isIso_iff_of_reflects_iso, PartialOrder.isIso_iff_eq]
      using hn (homOfLE hm)

variable {X} in
lemma isEventuallyConstant_of_isArtinianObject [IsArtinianObject X]
    (F : ℕ ⥤ (MonoOver X)ᵒᵖ) : IsFiltered.IsEventuallyConstant F :=
  (isArtinianObject_iff_isEventuallyConstant X).1 inferInstance F

variable {X Y}

lemma isArtinianObject_of_isZero (hX : IsZero X) : IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm ↦ Subsingleton.elim _ _⟩

instance [HasZeroObject C] : (isArtinianObject (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    rw [← isArtinianObject.is_iff]
    exact isArtinianObject_of_isZero (isZero_zero C)⟩

lemma isArtinianObject_of_mono (i : X ⟶ Y) [Mono i] [IsArtinianObject Y] :
    IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject
    ⟨fun n ↦ (Subobject.map i).obj (f n),
      fun _ _ h ↦ (Subobject.map i).monotone (f.2 h)⟩
  exact ⟨n, fun m hm ↦ Subobject.map_obj_injective i (hn m hm)⟩

instance : (isArtinianObject (C := C)).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [← isArtinianObject.is_iff] at hY ⊢
    exact isArtinianObject_of_mono f

open Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

theorem exists_simple_subobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    ∃ Y : Subobject X, Simple (Y : C) := by
  haveI : Nontrivial (Subobject X) := nontrivial_of_not_isZero h
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_isAtom _).mpr s.1⟩

/-- Choose an arbitrary simple subobject of a non-zero Artinian object. -/
noncomputable def simpleSubobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) : C :=
  (exists_simple_subobject h).choose

/-- The monomorphism from the arbitrary simple subobject of a non-zero artinian object. -/
noncomputable def simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    simpleSubobject h ⟶ X :=
  (exists_simple_subobject h).choose.arrow

instance mono_simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    Mono (simpleSubobjectArrow h) := by
  dsimp only [simpleSubobjectArrow]
  infer_instance

instance {X : C} [IsArtinianObject X] (h : ¬IsZero X) : Simple (simpleSubobject h) :=
  (exists_simple_subobject h).choose_spec

end CategoryTheory
