/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects

We shall say that an object `X` in a category `C` is Noetherian
(type class `IsNoetherianObject X`) if the ordered type `Subobject X`
satisfies the ascending chain condition. The corresponding property of
objects `isNoetherianObject : ObjectProperty C` is always
closed under subobjects.

## Future works

* show that `isNoetherian` is a Serre class when `C` is an abelian category
  (TODO @joelriou)

-/

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

/-- An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Noetherian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsNoetherianObject` instead. -/
@[stacks 0FCG]
def isNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (Subobject X)

variable (X Y : C)

/-- An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition. -/
@[stacks 0FCG]
abbrev IsNoetherianObject : Prop := isNoetherianObject.Is X

instance [IsNoetherianObject X] : WellFoundedGT (Subobject X) :=
  isNoetherianObject.prop_of_is X

lemma isNoetherianObject_iff_monotone_chain_condition :
    IsNoetherianObject X ↔ ∀ (f : ℕ →o Subobject X),
      ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m := by
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff, isNoetherianObject,
    wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
lemma monotone_chain_condition_of_isNoetherianObject
    [IsNoetherianObject X] (f : ℕ →o Subobject X) :
    ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m :=
  (isNoetherianObject_iff_monotone_chain_condition X).1 inferInstance f

lemma isNoetherianObject_iff_not_strictMono :
    IsNoetherianObject X ↔ ∀ (f : ℕ → Subobject X), ¬ StrictMono f := by
  refine ⟨fun _ ↦ not_strictMono_of_wellFoundedGT, fun h ↦ ?_⟩
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff, isNoetherianObject, WellFoundedGT,
    isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f ↦ h f.toFun (fun a b h ↦ f.map_rel_iff.2 h)⟩

variable {X} in
lemma not_strictMono_of_isNoetherianObject
    [IsNoetherianObject X] (f : ℕ → Subobject X) :
    ¬ StrictMono f :=
  (isNoetherianObject_iff_not_strictMono X).1 inferInstance f

lemma isNoetherianObject_iff_isEventuallyConstant :
    IsNoetherianObject X ↔ ∀ (F : ℕ ⥤ MonoOver X),
      IsFiltered.IsEventuallyConstant F := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  refine ⟨fun h G ↦ ?_, fun h F ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h (G ⋙ (Subobject.equivMonoOver _).inverse).toOrderHom
    refine ⟨n, fun m hm ↦ ?_⟩
    rw [MonoOver.isIso_iff_subobjectMk_eq]
    exact hn m (leOfHom hm)
  · obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ Subobject.representative)
    refine ⟨n, fun m hm ↦ ?_⟩
    simpa [← MonoOver.isIso_iff_isIso_hom_left, isIso_iff_of_reflects_iso,
      PartialOrder.isIso_iff_eq] using hn (homOfLE hm)

variable {X} in
lemma isEventuallyConstant_of_isNoetherianObject [IsNoetherianObject X]
    (F : ℕ ⥤ MonoOver X) : IsFiltered.IsEventuallyConstant F :=
  (isNoetherianObject_iff_isEventuallyConstant X).1 inferInstance F

variable {X Y}

lemma isNoetherianObject_of_isZero (hX : IsZero X) : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm ↦ Subsingleton.elim _ _⟩

instance [HasZeroObject C] : (isNoetherianObject (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    rw [← isNoetherianObject.is_iff]
    exact isNoetherianObject_of_isZero (isZero_zero C)⟩

lemma isNoetherianObject_of_mono (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y] :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.map i).monotone.comp f.2⟩
  exact ⟨n, fun m hm ↦ Subobject.map_obj_injective i (hn m hm)⟩

instance : (isNoetherianObject (C := C)).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [← isNoetherianObject.is_iff] at hY ⊢
    exact isNoetherianObject_of_mono f

end CategoryTheory
