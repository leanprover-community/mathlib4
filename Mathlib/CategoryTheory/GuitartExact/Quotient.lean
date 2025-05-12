/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GuitartExact.Basic

/-!
# Guitart exact squares given by quotient categories

In this file we produce certain Guitart exact squares
```
   T
 C₀ ⥤ H₀
L|    |R
 v    v
 C  ⥤ H
    B
```
that are given by an isomorphism `T ⋙ R ⟶ L ⋙ B`,
when `T` is full and essentially surjective, `B` is full,
and the following additional condition holds. Given
two morphisms `f₀` and `f₁` in `L.obj X₀ ⟶ Y` (for any
`X₀ : C₀` and `Y : C`), there exists a "cylinder"
object `Cyl : C₀` equipped with two morphisms
`i₀ : X₀ ⟶ Cyl` and `i₁ : X₀ ⟶ Cyl` such that `T.map i₀ = T.map i₁`,
and `φ : L.obj Cyl ⟶ Y`, such that `L.map i₀ ≫ φ = f₀`
and `L.map i₁ ≫ φ = f₁`.

This is meant to be applied in the case `C` is the category
of cochain complexes in an additive category, `H` is its
homotopy category, `H₀` is a (strictly full)
triangulated subcategory of `H`, and `C₀` is the corresponding
full subcategory of `C`.

-/

namespace CategoryTheory

namespace TwoSquare

variable {C₀ C H₀ H : Type*} [Category C₀] [Category C] [Category H₀] [Category H]
  {T : C₀ ⥤ H₀} {L : C₀ ⥤ C} {R : H₀ ⥤ H} {B : C ⥤ H}
  [T.EssSurj] [T.Full] [B.Full]

namespace GuitartExact

lemma quotient (e : T ⋙ R ≅ L ⋙ B)
    (h : ∀ ⦃X₀ : C₀⦄ ⦃Y : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y),
      ∃ (Cyl : C₀) (i₀ i₁ : X₀ ⟶ Cyl) (_ : T.map i₀ = T.map i₁)
          (φ : L.obj Cyl ⟶ Y), L.map i₀ ≫ φ = f₀ ∧
        L.map i₁ ≫ φ = f₁) : GuitartExact e.hom := by
  rw [guitartExact_iff_isConnected_downwards]
  intro Y₀ X g
  obtain ⟨X₀, ⟨e₀⟩⟩ := T.exists_of_essSurj Y₀
  let S := { f : L.obj X₀ ⟶ X // B.map f = e.inv.app X₀ ≫ R.map e₀.hom ≫ g }
  have : Nonempty S := by
    obtain ⟨f, hf⟩ := B.map_surjective (e.inv.app _ ≫ R.map e₀.hom ≫ g)
    exact ⟨⟨f, hf⟩⟩
  let Z (s : S) : CostructuredArrowDownwards e.hom g :=
      CostructuredArrowDownwards.mk _ _ X₀ e₀.inv s.1 (by rw [s.2]; simp)
  have : Nonempty (CostructuredArrowDownwards e.hom g) := ⟨Z (Classical.arbitrary _)⟩
  have hZ₀ (s₀ s₁) : Zigzag (Z s₀) (Z s₁) := by
    obtain ⟨Cyl, i₀, i₁, hi, φ, fac₀, fac₁⟩ := h s₀.1 s₁.1
    let Z' : CostructuredArrowDownwards e.hom g :=
      CostructuredArrowDownwards.mk _ _ Cyl (e₀.inv ≫ T.map i₀) φ (by
        have := e.hom.naturality i₀
        dsimp at this
        rw [Functor.map_comp_assoc, reassoc_of% this, ← Functor.map_comp, fac₀, s₀.2,
          Iso.hom_inv_id_app_assoc, Iso.map_inv_hom_id_assoc])
    exact (Zigzag.of_hom (j₂ := Z')
      (CostructuredArrow.homMk (StructuredArrow.homMk i₀ rfl))).trans
        (Zigzag.of_inv (CostructuredArrow.homMk (StructuredArrow.homMk i₁)))
  have H (A) : ∃ s, Nonempty (Z s ⟶ A) := by
    obtain ⟨a, ha⟩ := T.map_surjective (e₀.hom ≫ A.left.hom)
    refine ⟨⟨L.map a ≫ A.hom.right, ?_⟩,
      ⟨CostructuredArrow.homMk (StructuredArrow.homMk a (by simp [Z, ha])) rfl⟩⟩
    have h₁ := NatIso.naturality_1 e a
    have h₂ := StructuredArrow.w A.hom
    dsimp at h₁ h₂ ⊢
    simp only [Functor.map_comp, ← h₁, ← h₂, Category.assoc, ha]
  refine zigzag_isConnected (fun A₀ A₁ ↦ ?_)
  obtain ⟨s₀, ⟨f₀⟩⟩ := H A₀
  obtain ⟨s₁, ⟨f₁⟩⟩ := H A₁
  exact (Zigzag.of_inv f₀).trans ((hZ₀ s₀ s₁).trans (Zigzag.of_hom f₁))

end GuitartExact

end TwoSquare

end CategoryTheory
