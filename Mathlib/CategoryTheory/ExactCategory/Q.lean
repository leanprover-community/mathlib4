import Mathlib.CategoryTheory.ExactCategory.Basic
import Mathlib.CategoryTheory.Subobject.Basic

open CategoryTheory Category Limits

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

namespace CategoryTheory

namespace ExactCategory

structure Q where
  obj : C

namespace Q

variable {C}

structure Hom (X Y : Q C) where
  i : Subobject Y.obj
  hi : AdmissibleMono i.arrow
  j : (i : C) ⟶ X.obj
  hj : AdmissibleEpi j

attribute [instance] Hom.hi Hom.hj

noncomputable def Hom.mk' (X Y : Q C) {Z : C} (j : Z ⟶ X.obj) (i : Z ⟶ Y.obj)
  [AdmissibleMono i] [AdmissibleEpi j] : Hom X Y where
  i := Subobject.mk i
  hi := by
    have eq := Subobject.underlyingIso_arrow i
    rw [Iso.inv_comp_eq] at eq
    rw [eq]
    infer_instance
  j := (Subobject.underlyingIso i).hom ≫ j
  hj := inferInstance

lemma Hom.ext {X Y : Q C} (φ₁ φ₂ : Hom X Y) (e : (φ₁.i : C) ≅ φ₂.i)
    (h₁ : φ₁.i.arrow = e.hom ≫ φ₂.i.arrow) (h₂ : φ₁.j = e.hom ≫ φ₂.j) : φ₁ = φ₂ := by
  rcases φ₁ with ⟨i₁, hi₁, j₁, hj₁⟩
  rcases φ₂ with ⟨i₂, hi₂, j₂, hj₂⟩
  dsimp at e h₁ h₂
  obtain rfl := Subobject.eq_of_comm e h₁.symm
  have : e.hom = 𝟙 _ := by rw [← cancel_mono (Subobject.arrow i₁), id_comp, ← h₁]
  obtain rfl : j₁ = j₂ := by rw [h₂, this, id_comp]
  rfl

lemma Hom.mk'_surjective {X Y : Q C} (φ : Hom X Y) : ∃ (Z : C) (j : Z ⟶ X.obj) (i : Z ⟶ Y.obj)
    (hi : AdmissibleMono i) (hj : AdmissibleEpi j), φ = Hom.mk' _ _ j i  := by
  refine' ⟨_ , φ.j, φ.i.arrow, inferInstance, inferInstance, _⟩
  refine' Hom.ext _ _ (Subobject.isoOfEq _ _ (Subobject.mk_arrow φ.i).symm) _ _
  . dsimp
    simp
  . dsimp [mk']
    simp only [← assoc]
    refine' (Category.id_comp φ.j).symm.trans _
    congr
    aesop_cat

noncomputable def Hom.id (X : Q C) : Hom X X :=
  Hom.mk' X X (𝟙 _) (𝟙 _)

noncomputable def Hom.comp {X Y Z : Q C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z :=
  Hom.mk' X Z (pullback.fst ≫ α.j : pullback α.i.arrow β.j ⟶ _) (pullback.snd ≫ β.i.arrow)

/-instance : Category (Q C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry-/

end Q

end ExactCategory

end CategoryTheory
