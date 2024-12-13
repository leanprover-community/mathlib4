/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinal of Arrow

If `A` is a (small) category, `Arrow A` is finite iff `FinCategory A` holds.

-/

universe u

namespace CategoryTheory

@[simp]
lemma cardinal_arrow_discrete (S : Type u) :
    Cardinal.mk (Arrow (Discrete S)) = Cardinal.mk S :=
  Cardinal.mk_congr (Arrow.discreteEquiv S)

lemma Arrow.finite_iff (A : Type u) [SmallCategory A] :
    Finite (Arrow A) ↔ Nonempty (FinCategory A) := by
  constructor
  · intro
    refine ⟨?_, fun a b ↦ ?_⟩
    · have := Finite.of_injective (fun (a : A) ↦ Arrow.mk (𝟙 a))
        (fun _ _  ↦ congr_arg Comma.left)
      apply Fintype.ofFinite
    · have := Finite.of_injective (fun (f : a ⟶ b) ↦ Arrow.mk f)
        (fun f g h ↦ by
          change (Arrow.mk f).hom = (Arrow.mk g).hom
          congr)
      apply Fintype.ofFinite
  · rintro ⟨_⟩
    have := Fintype.ofEquiv  _ (Arrow.equivSigma A).symm
    infer_instance

instance Arrow.finite {A : Type u} [SmallCategory A] [FinCategory A] :
    Finite (Arrow A) := by
  rw [Arrow.finite_iff]
  exact ⟨inferInstance⟩

lemma cardinal_le_cardinal_arrow (A : Type u) [SmallCategory A] :
    Cardinal.mk A ≤ Cardinal.mk (Arrow A) :=
  Cardinal.mk_le_of_injective (f := fun a ↦ Arrow.mk (𝟙 a)) (fun _ _ ↦ congr_arg Comma.left)

end CategoryTheory
