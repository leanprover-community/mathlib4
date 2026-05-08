/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated

/-!
# Localizing subcategories

Let `C` be a pretriangulated category. If `A` and `B` are triangulated
subcategories of `C`, we define predicates (typeclasses
`IsVerdierRightLocalizing` and `IsVerdierLeftLocalizing`)
saying that `A` is right `B`-localizing (or left `B`-localizing).
When `B` is closed under isomorphisms, we show that this implies that
the functor from the Verdier quotient `A/(A ⊓ B)` to `C/B` is fully
faithful.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*,
  Proposition 2.3.5, Chapitre II][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Opposite

namespace ObjectProperty

variable {C D D₁ D₂ : Type*} [Category* C] [Category* D] [Category* D₁] [Category* D₂]

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
right `B`-localizing if any morphism `X ⟶ Y` with `X` in `B` and
`Y` in `A` factors through an object that is in `A` and `B`.
Note that the definition does not use the (pre)triangulated structure:
see `isVerdierRightLocalizing_iff` for a characterization which
relies on it. -/
class IsVerdierRightLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : B X) (hY : A Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
left `B`-localizing if any morphism `X ⟶ Y` with `X` in `A` and
`Y` in `B` factors through an object that is in `A` and `B`.
Note that the definition does not use the (pre)triangulated structure:
see `isVerdierLeftLocalizing_iff` for a characterization which
relies on it. -/
class IsVerdierLeftLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : A X) (hY : B Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

instance (A B : ObjectProperty C) [A.IsVerdierLeftLocalizing B] :
    A.op.IsVerdierRightLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ :=
      IsVerdierLeftLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsVerdierLeftLocalizing B] :
    A.unop.IsVerdierRightLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierLeftLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

instance (A B : ObjectProperty C) [A.IsVerdierRightLocalizing B] :
    A.op.IsVerdierLeftLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsVerdierRightLocalizing B] :
    A.unop.IsVerdierLeftLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

variable (A B : ObjectProperty C)

lemma isVerdierLeftLocalizing_op_iff :
    A.op.IsVerdierLeftLocalizing B.op ↔ A.IsVerdierRightLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsVerdierRightLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩

lemma isVerdierRightLocalizing_op_iff :
    A.op.IsVerdierRightLocalizing B.op ↔ A.IsVerdierLeftLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsVerdierLeftLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

lemma isVerdierRightLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsVerdierRightLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A X) (_ : B.trW s),
        ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' := by
  refine ⟨fun _ X Y s hX hs ↦ ?_, fun hA ↦ ⟨fun {X Y} f hX hY ↦ ?_⟩⟩
  · rw [ObjectProperty.trW_iff'] at hs
    obtain ⟨W, a, b, hT, hW⟩ := hs
    obtain ⟨W', c, d, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac a hW hX
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
lemma IsVerdierRightLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsVerdierRightLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hX : A X) (hs : B.trW s) :
    ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' :=
  (isVerdierRightLocalizing_iff A B).1 inferInstance s hX hs

lemma isVerdierLeftLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsVerdierLeftLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A Y) (_ : B.trW s),
        ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' := by
  rw [← isVerdierRightLocalizing_op_iff, isVerdierRightLocalizing_iff]
  refine ⟨fun hA X Y s hY hs ↦ ?_, fun hA X Y s hX hs ↦ ?_⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.op hY (by simpa [trW_op_iff])
    exact ⟨Z'.unop, s'.unop, b.unop, hZ', trW_of_op _ hs', by cat_disch⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.unop hX (trW_of_op _ hs)
    exact ⟨_, s'.op, b.op, hZ', trW_of_unop _ hs', by cat_disch⟩

variable {A B} in
lemma IsVerdierLeftLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsVerdierLeftLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hY : A Y) (hs : B.trW s) :
    ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' :=
  (isVerdierLeftLocalizing_iff A B).1 inferInstance s hY hs

/-- If `A` is a triangulated subcategory of a pretriangulated category `C`,
and `B : ObjectProperty C`, this is the inclusion functor
`A.ι : A.FullSubcategory ⥤ C`, considered as a localized morphism,
where `C` is equipped with the property of morphisms `B.trW`
and `A.FullSubcategory` with the property of morphisms `(B.inverseImage A.ι).trW`. -/
@[implicit_reducible]
def triangulatedLocalizerMorphism [A.IsTriangulated] :
    LocalizerMorphism (B.inverseImage A.ι).trW B.trW where
  functor := A.ι
  map X Y f hf := by
    simp only [MorphismProperty.inverseImage_iff, trW_iff] at hf ⊢
    obtain ⟨Z, a, b, hT, hZ⟩ := hf
    exact ⟨_, _, _, A.ι.map_distinguished _ hT, hZ⟩

instance [A.IsTriangulated] :
    (triangulatedLocalizerMorphism A B).functor.CommShift ℤ :=
  inferInstanceAs (A.ι.CommShift ℤ)

instance [A.IsTriangulated] :
    (triangulatedLocalizerMorphism A B).functor.IsTriangulated :=
  inferInstanceAs A.ι.IsTriangulated

lemma trW_inverseImage_ι_iff [A.IsTriangulated] {X Y : A.FullSubcategory} (f : X ⟶ Y) :
    (B.inverseImage A.ι).trW f ↔ (A ⊓ B).trW f.hom := by
  simp only [trW_iff]
  constructor
  · rintro ⟨Z, a, b, h, hZ⟩
    exact ⟨_, _, _, A.ι.map_distinguished _ h, Z.property, hZ⟩
  · rintro ⟨Z, a, b, h, hZ⟩
    refine ⟨⟨Z, hZ.1⟩, A.homMk a, A.homMk (b ≫ (A.ι.commShiftIso 1).inv.app _), ?_, hZ.2⟩
    rw [← A.ι.map_distinguished_iff]
    refine isomorphic_distinguished _ h _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
    · cat_disch
    · cat_disch
    · simp [dsimp% (A.ι.commShiftIso (1 : ℤ)).inv_hom_id_app X]

lemma inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op [A.IsTriangulated]
    [B.IsTriangulated] [B.IsClosedUnderIsomorphisms] :
    (B.op.inverseImage A.op.ι).trW.inverseImage A.opEquivalence.inverse =
      (B.inverseImage A.ι).op.trW := by
  ext ⟨X₁⟩ ⟨X₂⟩ a
  simp [trW_op, trW_inverseImage_ι_iff, ← op_inf]

variable [IsTriangulated C] [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]

section

variable [A.IsVerdierRightLocalizing B]
  (L₁ : A.FullSubcategory ⥤ D₁) (L₂ : C ⥤ D₂)
  [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]

instance : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  have : L₁.EssSurj := Localization.essSurj L₁ (B.inverseImage A.ι).trW
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine F.full_of_comp_essSurj L₁ (fun X₁ X₂ φ ↦ ?_)
  obtain ⟨φ', hφ'⟩ : ∃ φ', φ = e.inv.app X₁ ≫ φ' ≫ e.hom.app X₂ :=
    ⟨e.hom.app X₁ ≫ φ ≫ e.inv.app X₂, by
      simp [dsimp% e.inv_hom_id_app_assoc, dsimp% e.inv_hom_id_app]⟩
  obtain ⟨f, hf⟩ := Localization.exists_leftFraction L₂ B.trW φ'
  obtain ⟨X₃, s', a, hX₃, hs', fac⟩ :=
    IsVerdierRightLocalizing.fac' f.s X₂.property f.hs
  let g : (B.inverseImage A.ι).trW.LeftFraction X₁ X₂ :=
    { Y' := ⟨X₃, hX₃⟩
      f := A.homMk (f.f ≫ a)
      s := A.homMk s'
      hs := by rwa [trW_inverseImage_ι_iff] }
  have := Localization.inverts L₁ _ _ g.hs
  refine ⟨g.map L₁ (Localization.inverts _ _), ?_⟩
  rw [← cancel_mono (F.map (L₁.map g.s)), ← Functor.map_comp,
    MorphismProperty.LeftFraction.map_comp_map_s]
  simp [g, ← fac, hφ', hf, ← dsimp% NatIso.naturality_1 e,
    dsimp% e.hom_inv_id_app_assoc]

instance [Preadditive D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Additive := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

instance : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful := by
  letI := Localization.preadditive L₁ (B.inverseImage A.ι).trW
  letI := Localization.preadditive L₂ B.trW
  have := Localization.functor_additive L₁ (B.inverseImage A.ι).trW
  have := Localization.functor_additive L₂ B.trW
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F :=
    CatCommSq.iso (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions L₁
    (B.inverseImage A.ι).trW F (fun X₁ X₂ f hf ↦ ?_)
  replace hf : L₂.map f.hom = L₂.map 0 := by
    simp [← dsimp% NatIso.naturality_2 e f, hf]
  rw [MorphismProperty.map_eq_iff_postcomp L₂ B.trW] at hf
  obtain ⟨X₃, s, hs, fac⟩ := hf
  obtain ⟨X₄, t, a, hX₄, ht, fac'⟩ :=
    IsVerdierRightLocalizing.fac' s X₂.property hs
  let t' : X₂ ⟶ ⟨X₄, hX₄⟩ := A.homMk t
  have := Localization.inverts L₁ (B.inverseImage A.ι).trW t'
    (by rwa [trW_inverseImage_ι_iff])
  rw [← cancel_mono (L₁.map t'), zero_comp, ← L₁.map_comp, ← L₁.map_zero]
  congr 1
  ext
  simp [t', ← fac', reassoc_of% fac]

end

instance [A.IsVerdierRightLocalizing B] :
    (A.triangulatedLocalizerMorphism B).IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := ⟨.ofFullyFaithful _⟩

instance [A.IsVerdierLeftLocalizing B] :
    (A.triangulatedLocalizerMorphism B).IsLocalizedFullyFaithful := by
  let L₁ := (B.inverseImage A.ι).trW.Q
  let L₂ := B.trW.Q
  let F : (B.inverseImage A.ι).trW.Localization ⥤ B.trW.Localization :=
    (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  letI : CatCommSq (A.op.triangulatedLocalizerMorphism B.op).functor
    (A.opEquivalence.functor ⋙ L₁.op) L₂.op F.op :=
    ⟨Functor.isoWhiskerLeft A.opEquivalence.functor
      (NatIso.op (CatCommSq.iso (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F).symm)⟩
  have : L₂.op.IsLocalization B.op.trW := by rw [trW_op]; infer_instance
  have : (A.opEquivalence.functor ⋙ L₁.op).IsLocalization (B.op.inverseImage A.op.ι).trW := by
    refine Functor.IsLocalization.of_equivalence_source L₁.op (B.inverseImage A.ι).trW.op
      _ _ A.opEquivalence.symm ?_ ?_
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight A.opEquivalence.counitIso _ ≪≫ Functor.leftUnitor _)
    · rw [← trW_op, ← inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op]
      intro _ _ f hf
      simp only [MorphismProperty.inverseImage_iff, Equivalence.symm_functor] at hf ⊢
      exact MorphismProperty.le_isoClosure _ _ hf
    · refine fun _ _ _ hf ↦ Localization.inverts L₁.op (B.inverseImage A.ι).trW.op _ ?_
      simpa [trW_inverseImage_ι_iff, ← op_inf, trW_op] using hf
  exact LocalizerMorphism.IsLocalizedFullyFaithful.mk' (A.triangulatedLocalizerMorphism B)
    L₁ L₂ F (((A.op.triangulatedLocalizerMorphism B.op).fullyFaithful
    (A.opEquivalence.functor ⋙ L₁.op) L₂.op F.op).unop)

section

variable [A.IsVerdierLeftLocalizing B] (L₁ : A.FullSubcategory ⥤ D₁) (L₂ : C ⥤ D₂)
  [L₁.IsLocalization (B.inverseImage A.ι).trW]
  [L₂.IsLocalization B.trW]

example : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full := by
  infer_instance

example : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful := by
  infer_instance

instance [A.IsVerdierLeftLocalizing B] [Preadditive D₁] [Preadditive D₂]
    [L₁.Additive] [L₂.Additive] :
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Additive := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

/-- If `A` is a left `B`-localizing triangulated subcategory in the sense of Verdier,
then the induced functor between the localizations with respect to `(B.inverseImage A.ι).trW`
and `B.trW` is fully faithful. -/
@[no_expose]
noncomputable def IsVerdierLeftLocalizing.fullyFaithful [A.IsVerdierLeftLocalizing B]
    {L₁ : A.FullSubcategory ⥤ D₁} {L₂ : C ⥤ D₂} {F : D₁ ⥤ D₂}
    [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]
    (e : L₁ ⋙ F ≅ A.ι ⋙ L₂) :
    F.FullyFaithful :=
  Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

/-- If `A` is a right `B`-localizing triangulated subcategory in the sense of Verdier,
then the induced functor between the localizations with respect to `(B.inverseImage A.ι).trW`
and `B.trW` is fully faithful. -/
@[no_expose]
noncomputable def IsVerdierRightLocalizing.fullyFaithful [A.IsVerdierRightLocalizing B]
    {L₁ : A.FullSubcategory ⥤ D₁} {L₂ : C ⥤ D₂} {F : D₁ ⥤ D₂}
    [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]
    (e : L₁ ⋙ F ≅ A.ι ⋙ L₂) :
    F.FullyFaithful :=
  Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

end

end ObjectProperty

end CategoryTheory
