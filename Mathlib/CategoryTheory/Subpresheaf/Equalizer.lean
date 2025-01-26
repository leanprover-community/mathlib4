/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subpresheaf.Image

/-!
# The equalizer of two morphisms of presheaves, as a subpresheaf

If `F₁` and `F₂` are presheaves of types, `A : Subpresheaf F₁`, and
`f` and `g` are two morphisms `A.toPresheaf ⟶ F₂`, we introduce
`Subcomplex.equalizer f g`, which is the subpresheaf of `F₁` contained in `A`.

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F₁ F₂ : Cᵒᵖ ⥤ Type w} {A : Subpresheaf F₁}
  (f g : A.toPresheaf ⟶ F₂)

namespace Subpresheaf

/-- The equalizer of two morphisms of presheaves of types of the form
`A.toPresheaf ⟶ F₂` with `A : Subpresheaf F₁`, as a subcomplex of `F₁`. -/
@[simps (config := .lemmasOnly)]
protected def equalizer : Subpresheaf F₁ where
  obj U := setOf (fun x ↦ ∃ (hx : x ∈ A.obj _), f.app _ ⟨x, hx⟩ = g.app _ ⟨x, hx⟩)
  map φ x := by
    rintro ⟨hx, h⟩
    exact ⟨A.map _ hx,
      (FunctorToTypes.naturality _ _ f φ ⟨x, hx⟩).trans (Eq.trans (by rw [h])
        (FunctorToTypes.naturality _ _ g φ ⟨x, hx⟩).symm)⟩

attribute [local simp] equalizer_obj

lemma equalizer_le : Subpresheaf.equalizer f g ≤ A :=
  fun _ _ h ↦ h.1

@[simp]
lemma equalizer_self : Subpresheaf.equalizer f f = A := by aesop

lemma equalizer_eq_iff :
    Subpresheaf.equalizer f g = A ↔ f = g := by
  constructor
  · intro h
    ext i ⟨x, hx⟩
    rw [← h] at hx
    exact hx.choose_spec
  · rintro rfl
    simp

lemma mem_equalizer_iff {i : Cᵒᵖ} (x : A.toPresheaf.obj i) :
    x.1 ∈ (Subpresheaf.equalizer f g).obj i ↔ f.app i x = g.app i x := by
  simp

end Subpresheaf

end CategoryTheory
