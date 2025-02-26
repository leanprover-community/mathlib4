/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects in an abelian category

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

-- to be moved
namespace ObjectProperty

variable (P : ObjectProperty C)

@[mk_iff]
class Is (X : C) : Prop where
  prop : P X

lemma prop_of_is (X : C) [P.Is X] : P X := by rwa [← P.is_iff]

lemma is_of_prop {X : C} (hX : P X) : P.Is X := by rwa [P.is_iff]

end ObjectProperty

namespace Abelian

def isNoetherian : ObjectProperty C :=
  fun X ↦ WellFoundedGT (Subobject X)

variable (X Y : C)

abbrev IsNoetherian : Prop := isNoetherian.Is X

instance [IsNoetherian X] : WellFoundedGT (Subobject X) :=
  isNoetherian.prop_of_is X

lemma isNoetherian_iff_monotone_chain_condition :
    IsNoetherian X ↔ ∀ (f : ℕ →o Subobject X),
      ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m := by
  dsimp only [IsNoetherian]
  rw [ObjectProperty.is_iff, isNoetherian,
    wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
lemma monotone_chain_condition_of_isNoetherian [IsNoetherian X] (f : ℕ →o Subobject X) :
    ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m :=
  (isNoetherian_iff_monotone_chain_condition X).1 inferInstance f

lemma isNoetherian_iff_not_strictMono :
    IsNoetherian X ↔ ∀ (f : ℕ → Subobject X), ¬ StrictMono f := by
  refine ⟨fun _ ↦ not_strictMono_of_wellFoundedGT, fun h ↦ ?_⟩
  dsimp only [IsNoetherian]
  rw [ObjectProperty.is_iff, isNoetherian, WellFoundedGT,
    isWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
  exact ⟨fun f ↦ h f.toFun (fun a b h ↦ f.map_rel_iff.2 h)⟩

lemma not_strictMono_of_isNoetherian [IsNoetherian X] (f : ℕ → Subobject X) :
    ¬ StrictMono f :=
  (isNoetherian_iff_not_strictMono X).1 inferInstance f

variable {X Y}

lemma isNoetherian_of_mono (f : X ⟶ Y) [Mono f] [IsNoetherian Y] :
    IsNoetherian X := by
  rw [isNoetherian_iff_monotone_chain_condition]
  intro g
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherian
    ⟨_, (Subobject.map f).monotone.comp g.2⟩
  exact ⟨n, fun m hm ↦ Subobject.map_obj_injective f (hn m hm)⟩

end Abelian

end CategoryTheory
