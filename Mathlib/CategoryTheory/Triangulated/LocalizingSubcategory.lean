/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
public import Mathlib.CategoryTheory.Localization.Triangulated

/-!
# Localizing subcategories



## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Triangulated Pretriangulated.Opposite

namespace ObjectProperty

variable {C D D' : Type*} [Category* C] [Category* D] [Category* D']

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
right `B`-localizing if any morphism `X ⟶ Y` with `X` in `B` and
`Y` in `A` factors through an object that is in `A` and `B`.
See `isTriangulatedRightLocalizing_iff` for another characterization. -/
class IsTriangulatedRightLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : B X) (hY : A Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
left `B`-localizing if any morphism `X ⟶ Y` with `X` in `A` and
`Y` in `B` factors through an object that is in `A` and `B`.
See `isTriangulatedLeftLocalizing_iff` for another characterization. -/
class IsTriangulatedLeftLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : A X) (hY : B Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

instance (A B : ObjectProperty C) [A.IsTriangulatedLeftLocalizing B] :
    A.op.IsTriangulatedRightLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ :=
      IsTriangulatedLeftLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsTriangulatedLeftLocalizing B] :
    A.unop.IsTriangulatedRightLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsTriangulatedLeftLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

instance (A B : ObjectProperty C) [A.IsTriangulatedRightLocalizing B] :
    A.op.IsTriangulatedLeftLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsTriangulatedRightLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsTriangulatedRightLocalizing B] :
    A.unop.IsTriangulatedLeftLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsTriangulatedRightLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

variable (A B : ObjectProperty C)

lemma isTriangulatedLeftLocalizing_op_iff :
    A.op.IsTriangulatedLeftLocalizing B.op ↔ A.IsTriangulatedRightLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsTriangulatedRightLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩

lemma isTriangulatedRightLocalizing_op_iff :
    A.op.IsTriangulatedRightLocalizing B.op ↔ A.IsTriangulatedLeftLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsTriangulatedLeftLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

lemma isTriangulatedRightLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsTriangulatedRightLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A X) (_ : B.trW s),
        ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' := by
  refine ⟨fun _ X Y s hX hs ↦ ?_, fun hA ↦ ⟨fun {X Y} f hX hY ↦ ?_⟩⟩
  · rw [ObjectProperty.trW_iff'] at hs
    obtain ⟨W, a, b, hT, hW⟩ := hs
    obtain ⟨W', c, d, h₁, h₂, fac⟩ := IsTriangulatedRightLocalizing.fac a hW hX
    obtain ⟨U, hU, e, f, hT'⟩ := A.distinguished_cocone_triangle d h₁ hX
    obtain ⟨g, hg, _⟩ := complete_distinguished_triangle_morphism _ _ hT hT'
      c (𝟙 _) (by cat_disch)
    refine ⟨U, e, g, hU, ?_, by cat_disch⟩
    rw [ObjectProperty.trW_iff']
    exact ⟨_, _, _, hT', h₁, h₂⟩
  · obtain ⟨Z, s, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    have hs : B.trW s := by
      rw [trW_iff']
      exact ⟨_, _, _, hT, hX⟩
    obtain ⟨W, s', g, hW, hs', fac⟩ := hA s hY hs
    obtain ⟨U, hU, a, c, hT'⟩ := A.distinguished_cocone_triangle₁ s' hY hW
    obtain ⟨t, ht, ht'⟩ :=
      complete_distinguished_triangle_morphism₁ _ _ hT hT' (𝟙 Y) g (by cat_disch)
    exact ⟨U, t, a, hU, (B.trW_iff_of_distinguished' _ hT').1 (trW_monotone (by simp) _ hs'),
      by cat_disch⟩

variable {A B} in
lemma IsTriangulatedRightLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsTriangulatedRightLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hX : A X) (hs : B.trW s) :
    ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' :=
  (isTriangulatedRightLocalizing_iff A B).1 inferInstance s hX hs

-- to be moved
instance [A.ContainsZero] [B.ContainsZero] [B.IsClosedUnderIsomorphisms] :
    (A ⊓ B).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hA⟩ := A.exists_prop_of_containsZero
    exact ⟨Z, hZ, hA, B.prop_of_isZero hZ⟩

-- to be moved
instance [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms] :
    (A ⊓ B).IsTriangulated where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨Y, hY, ⟨e⟩⟩ := A.ext_of_isTriangulatedClosed₂' T hT h₁.1 h₃.1
    exact ⟨Y, ⟨hY, B.prop_of_iso e (B.ext_of_isTriangulatedClosed₂ T hT h₁.2 h₃.2)⟩, ⟨e⟩⟩

lemma isTriangulatedLeftLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsTriangulatedLeftLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A Y) (_ : B.trW s),
        ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' := by
  rw [← isTriangulatedRightLocalizing_op_iff, isTriangulatedRightLocalizing_iff]
  refine ⟨fun hA X Y s hY hs ↦ ?_, fun hA X Y s hX hs ↦ ?_⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.op hY (by simpa [trW_op_iff])
    exact ⟨Z'.unop, s'.unop, b.unop, hZ', trW_of_op _ hs', by cat_disch⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.unop hX (trW_of_op _ hs)
    exact ⟨_, s'.op, b.op, hZ', trW_of_unop _ hs', by cat_disch⟩

variable {A B} in
lemma IsTriangulatedLeftLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsTriangulatedLeftLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hY : A Y) (hs : B.trW s) :
    ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' :=
  (isTriangulatedLeftLocalizing_iff A B).1 inferInstance s hY hs

/-- If `A` is a triangulated subcategory of a pretriangulated category `C`,
and `B : ObjectProperty C`, this is the inclusion functor
`A.ι : A.FullSubcategory ⥤ C`, considered as a localized morphism,
where `C` is equipped with the property of morphisms `B.trW`
and `A.FullSubcategory` with the property of morphisms `(B.inverseImage A.ι).trW`. -/
@[simps]
def triangulatedLocalizedMorphism [A.IsTriangulated] :
    LocalizerMorphism (B.inverseImage A.ι).trW B.trW where
  functor := A.ι
  map X Y f hf := by
    simp only [MorphismProperty.inverseImage_iff, trW_iff] at hf ⊢
    obtain ⟨Z, a, b, hT, hZ⟩ := hf
    exact ⟨_, _, _, A.ι.map_distinguished _ hT, hZ⟩

variable [IsTriangulated C] [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]

instance [A.IsTriangulatedRightLocalizing B] :
    (A.triangulatedLocalizedMorphism B).IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := by
    let L₁ := (B.inverseImage A.ι).trW.Q
    let L₂ := B.trW.Q
    let F : (B.inverseImage A.ι).trW.Localization ⥤ B.trW.Localization :=
      (A.triangulatedLocalizedMorphism B).localizedFunctor L₁ L₂
    let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F :=
      CatCommSq.iso (A.triangulatedLocalizedMorphism B).functor L₁ L₂ F
    have : F.Full :=
      Functor.full_of_precomp_essSurj _ L₁ (fun X₁ X₂ φ ↦ by
        obtain ⟨φ', hφ'⟩ : ∃ φ', φ = e.inv.app X₁ ≫ φ' ≫ e.hom.app X₂ :=
          ⟨e.hom.app X₁ ≫ φ ≫ e.inv.app X₂, by
            simp [dsimp% e.inv_hom_id_app_assoc, dsimp% e.inv_hom_id_app]⟩
        dsimp at φ' hφ'
        obtain ⟨f, hf⟩ := Localization.exists_leftFraction L₂ B.trW φ'
        have := IsTriangulatedRightLocalizing.fac' f.s X₂.property f.hs
        sorry )
    have : F.Faithful := by
      sorry
    exact ⟨.ofFullyFaithful F⟩

instance [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsTriangulatedLeftLocalizing B] :
    (A.triangulatedLocalizedMorphism B).IsLocalizedFullyFaithful := by
  sorry

end ObjectProperty

end CategoryTheory
