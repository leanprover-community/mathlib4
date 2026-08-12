/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Galois.Basic

/-!
# Induction principle for objects of a Galois category

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits PreGaloisCategory

variable {C : Type*} [Category* C]

namespace PreGaloisCategory

lemma has_decomp_of_not_isConnected [PreGaloisCategory C] (X : C)
    (hX₁ : ¬ PreGaloisCategory.IsConnected X) (hX₂ : IsInitial X → False) :
    ∃ (X₁ X₂ : C) (_ : IsInitial X₁ → False) (_ : IsInitial X₂ → False)
      (inl : X₁ ⟶ X) (inr : X₂ ⟶ X),
        Nonempty (IsColimit (BinaryCofan.mk inl inr)) := by
  -- from `has_decomp_connected_components_aux` in `Decomposition.lean`
  obtain ⟨X₁, inl, hX₁, _, h⟩ :=
    has_non_trivial_subobject_of_not_isConnected_of_not_initial X hX₁ hX₂
  obtain ⟨X₂, inr, ⟨H⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand inl
  refine ⟨X₁, X₂, hX₁, fun hX₂ ↦ h ?_, inl, inr, ⟨H⟩⟩
  obtain ⟨l : X ⟶ X₁, hl : inl ≫ l = 𝟙 X₁, _⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X₁) (hX₂.to _)
  refine ⟨l, hl, BinaryCofan.IsColimit.hom_ext H ?_ (hX₂.hom_ext _ _)⟩
  change inl ≫ l ≫ inl = inl ≫ 𝟙 X
  simp [reassoc_of% hl]

end PreGaloisCategory

namespace GaloisCategory

lemma obj_rec [GaloisCategory C] {motive : C → Prop}
    (of_isInitial : ∀ (X : C), IsInitial X → motive X)
    (of_isConnected : ∀ (X : C), PreGaloisCategory.IsConnected X → motive X)
    (of_isColimit : ∀ (X Y : C) (b : BinaryCofan X Y) (_ : IsColimit b),
      motive X → motive Y → motive b.pt) (X : C) :
      motive X := by
  let F := getFiberFunctor C
  generalize hn : Nat.card (F.obj X) = n
  induction n using Nat.strongRecOn generalizing X with | _ n hi
  by_cases h₁ : Nonempty (IsInitial X)
  · exact of_isInitial _ h₁.some
  · by_cases h₂ : PreGaloisCategory.IsConnected X
    · exact of_isConnected _ h₂
    · obtain ⟨X₁, X₂, h₁, h₂, inl, inr, ⟨h⟩⟩ :=
        has_decomp_of_not_isConnected X h₂ (fun h ↦ h₁ ⟨h⟩)
      have := card_fiber_eq_add_of_isColimit F h
      simp only [BinaryCofan.mk_pt, hn] at this
      have := non_zero_card_fiber_of_not_initial F _ h₁
      have := non_zero_card_fiber_of_not_initial F _ h₂
      exact of_isColimit _ _ _ h (hi _ (by lia) _ rfl) (hi _ (by lia) _ rfl)

end GaloisCategory

end CategoryTheory
