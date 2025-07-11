/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.HomEquiv
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Induction principles for structured and costructured arrows

Assume that `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`.
Given `X : C` and a predicate `P` on `StructuredArrow (L.obj X) L`, we obtain
the lemma `Localization.induction_structuredArrow` which shows that `P` holds for
all structured arrows if `P` holds for the identity map `𝟙 (L.obj X)`,
if `P` is stable by post-composition with `L.map f` for any `f`
and if `P` is stable by post-composition with the inverse of `L.map w` when `W w`.

We obtain a similar lemma `Localization.induction_costructuredArrow` for
costructured arrows.

-/

namespace CategoryTheory

open Opposite

variable {C D D' : Type*} [Category C] [Category D] [Category D']

namespace Localization

section

variable (W : MorphismProperty C) (L : C ⥤ D) (L' : C ⥤ D')
  [L.IsLocalization W] [L'.IsLocalization W] {X : C}

/-- The bijection `StructuredArrow (L.obj X) L ≃ StructuredArrow (L'.obj X) L'`
when `L` and `L'` are two localization functors for the same class of morphisms. -/
@[simps]
noncomputable def structuredArrowEquiv :
    StructuredArrow (L.obj X) L ≃ StructuredArrow (L'.obj X) L' where
  toFun f := StructuredArrow.mk (homEquiv W L L' f.hom)
  invFun f := StructuredArrow.mk (homEquiv W L' L f.hom)
  left_inv f := by
    obtain ⟨Y, f, rfl⟩ := f.mk_surjective
    dsimp
    rw [← homEquiv_symm_apply, Equiv.symm_apply_apply]
  right_inv f := by
    obtain ⟨Y, f, rfl⟩ := f.mk_surjective
    dsimp
    rw [← homEquiv_symm_apply, Equiv.symm_apply_apply]

end

section

variable (W : MorphismProperty C) {X : C}
  (P : StructuredArrow (W.Q.obj X) W.Q → Prop)

open Construction in
private lemma induction_structuredArrow'
    (hP₀ : P (StructuredArrow.mk (𝟙 (W.Q.obj X))))
    (hP₁ : ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂) (φ : W.Q.obj X ⟶ W.Q.obj Y₁),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ W.Q.map f)))
    (hP₂ : ∀ ⦃Y₁ Y₂ : C⦄ (w : Y₁ ⟶ Y₂) (hw : W w) (φ : W.Q.obj X ⟶ W.Q.obj Y₂),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ (isoOfHom W.Q W w hw).inv)))
    (g : StructuredArrow (W.Q.obj X) W.Q) : P g := by
  let X₀ : Paths (LocQuiver W) := ⟨X⟩
  suffices ∀ ⦃Y₀ : Paths (LocQuiver W)⦄ (f : X₀ ⟶ Y₀),
      P (StructuredArrow.mk ((Quotient.functor (relations W)).map f)) by
    obtain ⟨Y, g, rfl⟩ := g.mk_surjective
    obtain ⟨g, rfl⟩ := (Quotient.functor (relations W)).map_surjective g
    exact this g
  intro Y₀ f
  induction f with
  | nil => exact hP₀
  | cons f g hf =>
      obtain (g|⟨w, hw⟩) := g
      · exact hP₁ g _ hf
      · simpa only [← Construction.wInv_eq_isoOfHom_inv w hw] using hP₂ w hw _ hf

end

section

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {X : C}
  (P : StructuredArrow (L.obj X) L → Prop)


@[elab_as_elim]
lemma induction_structuredArrow
    (hP₀ : P (StructuredArrow.mk (𝟙 (L.obj X))))
    (hP₁ : ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂) (φ : L.obj X ⟶ L.obj Y₁),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ L.map f)))
    (hP₂ : ∀ ⦃Y₁ Y₂ : C⦄ (w : Y₁ ⟶ Y₂) (hw : W w) (φ : L.obj X ⟶ L.obj Y₂),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ (isoOfHom L W w hw).inv)))
    (g : StructuredArrow (L.obj X) L) : P g := by
  let P' : StructuredArrow (W.Q.obj X) W.Q → Prop :=
    fun g ↦ P (structuredArrowEquiv W W.Q L g)
  rw [← (structuredArrowEquiv W W.Q L).apply_symm_apply g]
  apply induction_structuredArrow' W P'
  · convert hP₀
    simp
  · intros Y₁ Y₂ f φ hφ
    convert hP₁ f (homEquiv W W.Q L φ) hφ
    simp [homEquiv_comp]
  · intros Y₁ Y₂ w hw φ hφ
    convert hP₂ w hw (homEquiv W W.Q L φ) hφ
    simp [homEquiv_comp, homEquiv_isoOfHom_inv]

end

section

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {Y : C}
  (P : CostructuredArrow L (L.obj Y) → Prop)

@[elab_as_elim]
lemma induction_costructuredArrow
    (hP₀ : P (CostructuredArrow.mk (𝟙 (L.obj Y))))
    (hP₁ : ∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂) (φ : L.obj X₂ ⟶ L.obj Y),
      P (CostructuredArrow.mk φ) → P (CostructuredArrow.mk (L.map f ≫ φ)))
    (hP₂ : ∀ ⦃X₁ X₂ : C⦄ (w : X₁ ⟶ X₂) (hw : W w) (φ : L.obj X₁ ⟶ L.obj Y),
      P (CostructuredArrow.mk φ) → P (CostructuredArrow.mk ((isoOfHom L W w hw).inv ≫ φ)))
    (g : CostructuredArrow L (L.obj Y)) : P g := by
  let g' := StructuredArrow.mk (T := L.op) (Y := op g.left) g.hom.op
  change P (CostructuredArrow.mk g'.hom.unop)
  induction g' using induction_structuredArrow L.op W.op with
  | hP₀ => exact hP₀
  | hP₁ f φ hφ => exact hP₁ f.unop φ.unop hφ
  | hP₂ w hw φ hφ => simpa [isoOfHom_op_inv L W w hw] using hP₂ w.unop hw φ.unop hφ

end

end Localization

end CategoryTheory
