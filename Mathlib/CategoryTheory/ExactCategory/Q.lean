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
  · dsimp
    simp
  · dsimp [mk']
    simp only [← assoc]
    refine' (Category.id_comp φ.j).symm.trans _
    congr
    aesop_cat

lemma Hom.ext' {X Y : Q C} {Z₁ Z₂ : C}
    (j₁ : Z₁ ⟶ X.obj) (i₁ : Z₁ ⟶ Y.obj) [AdmissibleMono i₁] [AdmissibleEpi j₁]
    (j₂ : Z₂ ⟶ X.obj) (i₂ : Z₂ ⟶ Y.obj) [AdmissibleMono i₂] [AdmissibleEpi j₂]
    (e : Z₁ ≅ Z₂) (comm₁ : i₁ = e.hom ≫ i₂) (comm₂ : j₁ = e.hom ≫ j₂) :
    Hom.mk' X Y j₁ i₁ = Hom.mk' X Y j₂ i₂ := by
  refine' Hom.ext _ _ (Subobject.underlyingIso i₁ ≪≫ e ≪≫ (Subobject.underlyingIso i₂).symm)
    _ _
  · dsimp [mk']
    simp only [assoc, Subobject.underlyingIso_arrow, ← comm₁,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · dsimp [mk']
    simp only [assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left, comm₂]

noncomputable def Hom.id (X : Q C) : Hom X X :=
  Hom.mk' X X (𝟙 _) (𝟙 _)

noncomputable def Hom.comp {X Y Z : Q C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z :=
  Hom.mk' X Z (pullback.fst ≫ α.j : pullback α.i.arrow β.j ⟶ _) (pullback.snd ≫ β.i.arrow)

lemma Hom.comp_eq {X₁ X₂ X₃ : Q C} {Z₁₂ Z₂₃ Z₁₃ : C} (j₁ : Z₁₂ ⟶ X₁.obj) (i₁ : Z₁₂ ⟶ X₂.obj)
    (j₂ : Z₂₃ ⟶ X₂.obj) (i₂ : Z₂₃ ⟶ X₃.obj) [AdmissibleMono i₁] [AdmissibleMono i₂]
    [AdmissibleEpi j₁] [AdmissibleEpi j₂] (j₂' : Z₁₃ ⟶ Z₁₂) (i₁' : Z₁₃ ⟶ Z₂₃)
    [AdmissibleEpi j₂'] [AdmissibleMono i₁'] (H : IsPullback j₂' i₁' i₁ j₂):
    (Hom.mk' X₁ X₂ j₁ i₁).comp (Hom.mk' X₂ X₃ j₂ i₂) = Hom.mk' X₁ X₃ (j₂' ≫ j₁) (i₁' ≫ i₂) := by
  let φ : Z₁₃ ⟶ pullback (Subobject.arrow (mk' X₁ X₂ j₁ i₁).i) (mk' X₂ X₃ j₂ i₂).j :=
    pullback.lift (j₂' ≫ (Subobject.underlyingIso i₁).inv)
      (i₁' ≫ (Subobject.underlyingIso i₂).inv ) (by
        dsimp [mk']
        simp only [assoc, Subobject.underlyingIso_arrow, Iso.inv_hom_id_assoc, H.w])
  have : IsIso φ := by
    let e : cospan (Subobject.arrow (mk' X₁ X₂ j₁ i₁).i) (mk' X₂ X₃ j₂ i₂).j ≅
        cospan i₁ j₂ := cospanExt (Subobject.underlyingIso i₁) (Subobject.underlyingIso i₂)
          (Iso.refl _) (by dsimp [mk'] ; simp) (by dsimp [mk'] ; simp)
    convert IsIso.of_iso (IsLimit.conePointUniqueUpToIso
      ((IsLimit.postcomposeHomEquiv e.symm _).symm H.isLimit) (limit.isLimit _))
    aesop_cat
  symm
  refine' Hom.ext' _ _ _ _ (asIso φ) _ _
  all_goals
    dsimp [mk', asIso]
    simp

noncomputable instance : Category (Q C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp {X Y} f := by
    obtain ⟨Z, j, i, hj, hi, rfl⟩ := Hom.mk'_surjective f
    simpa only [comp_id, id_comp]
      using (Hom.comp_eq (𝟙 X.obj) (𝟙 X.obj) j i j (𝟙 Z) (IsPullback.of_vert_isIso ⟨by simp⟩))
  comp_id {X Y} f := by
    obtain ⟨Z, j, i, hj, hi, rfl⟩ := Hom.mk'_surjective f
    change Hom.comp _ (Hom.mk' _ _ _ _) = _
    simpa [id_comp, comp_id]
      using Hom.comp_eq j i (𝟙 Y.obj) (𝟙 Y.obj) (𝟙 _) i (IsPullback.of_horiz_isIso ⟨by simp⟩)
  assoc {X₁ X₂ X₃ X₄} f₁ f₂ f₃ := by
    obtain ⟨Z₁₂, j₁₂, i₁₂, hj₁₂, hi₁₂, rfl⟩ := Hom.mk'_surjective f₁
    obtain ⟨Z₂₃, j₂₃, i₂₃, hj₂₃, hi₂₃, rfl⟩ := Hom.mk'_surjective f₂
    obtain ⟨Z₃₄, j₃₄, i₃₄, hj₃₄, hi₃₄, rfl⟩ := Hom.mk'_surjective f₃
    change Hom.comp (Hom.comp _ _) _ = Hom.comp _ (Hom.comp _ _)
    let Z₁₃ := pullback i₁₂ j₂₃
    let Z₂₄ := pullback i₂₃ j₃₄
    let Z₁₄ := pullback (pullback.snd : Z₁₃ ⟶ _) (pullback.fst : Z₂₄ ⟶ _)
    rw [Hom.comp_eq j₁₂ i₁₂ j₂₃ i₂₃ (pullback.fst : Z₁₃ ⟶ _) pullback.snd,
      Hom.comp_eq j₂₃ i₂₃ j₃₄ i₃₄ (pullback.fst : Z₂₄ ⟶ _) pullback.snd,
      Hom.comp_eq _ _ j₃₄ i₃₄ (pullback.fst : Z₁₄ ⟶ _) (pullback.snd ≫ pullback.snd),
      Hom.comp_eq j₁₂ i₁₂ _ _ (pullback.fst ≫ pullback.fst : Z₁₄ ⟶ _) pullback.snd]
    · simp only [assoc]
    · exact (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback i₁₂ j₂₃) pullback.condition).2
        (IsPullback.of_hasPullback (pullback.snd : Z₁₃ ⟶ _) (pullback.fst : Z₂₄ ⟶ _))
    · exact (IsPullback.paste_vert_iff (IsPullback.of_hasPullback i₂₃ j₃₄) pullback.condition).2
        (IsPullback.of_hasPullback (pullback.snd : Z₁₃ ⟶ _) (pullback.fst : Z₂₄ ⟶ _))
    · exact (IsPullback.of_hasPullback i₂₃ j₃₄)
    · exact (IsPullback.of_hasPullback i₁₂ j₂₃)

end Q

end ExactCategory

end CategoryTheory
