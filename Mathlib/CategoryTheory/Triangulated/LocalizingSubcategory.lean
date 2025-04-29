/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Lemmas

/-!
# Localizing subcategories

-/

namespace CategoryTheory

open Category Limits Pretriangulated Triangulated Pretriangulated.Opposite

namespace ObjectProperty

variable {A C D D' : Type*} [Category A] [Category C] [Category D] [Category D']
  [HasZeroObject C]
  [HasShift C ℤ]
  [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]
  (B : ObjectProperty C) (F : A ⥤ C)

class IsRightLocalizing [B.IsTriangulated] : Prop where
  fac {Y : C} {X : A} (φ : Y ⟶ F.obj X) (hY : B Y) :
    ∃ (Y' : A) (_ : B (F.obj Y')) (a : Y ⟶ F.obj Y') (b : Y' ⟶ X),
      a ≫ F.map b = φ

class IsLeftLocalizing [B.IsTriangulated]: Prop where
  fac {X : A} {Y : C} (φ : F.obj X ⟶ Y) (hY : B Y) :
    ∃ (Y' : A) (_ : B (F.obj Y')) (a : F.obj Y' ⟶ Y) (b : X ⟶ Y'),
      F.map b ≫ a = φ

variable [B.IsTriangulated]

lemma fac_of_isRightLocalizing [B.IsRightLocalizing F]
    {Y : C} {X : A} (φ : Y ⟶ F.obj X) (hY : B Y) :
    ∃ (Y' : A) (_ : B (F.obj Y')) (a : Y ⟶ F.obj Y') (b : Y' ⟶ X),
      a ≫ F.map b = φ :=
  IsRightLocalizing.fac φ hY

lemma fac_of_isLeftLocalizing [B.IsLeftLocalizing F]
    {X : A} {Y : C} (φ : F.obj X ⟶ Y) (hY : B Y) :
    ∃ (Y' : A) (_ : B (F.obj Y')) (a : F.obj Y' ⟶ Y) (b : X ⟶ Y'),
      F.map b ≫ a = φ :=
  IsLeftLocalizing.fac φ hY

open CategoryTheory.Pretriangulated.Opposite

instance [B.IsLeftLocalizing F] : B.op.IsRightLocalizing F.op where
  fac {Y X} φ hY := by
    obtain ⟨Y', hY', a, b, fac⟩ := B.fac_of_isLeftLocalizing F φ.unop hY
    exact ⟨Opposite.op Y', hY', a.op, b.op, Quiver.Hom.unop_inj fac⟩

lemma isLeftLocalizing_of_op [B.op.IsRightLocalizing F.op] : B.IsLeftLocalizing F where
  fac {X Y} φ hY := by
    obtain ⟨Y', hY', a, b, fac⟩ := B.op.fac_of_isRightLocalizing F.op φ.op hY
    exact ⟨Y'.unop, hY', a.unop, b.unop, Quiver.Hom.op_inj fac⟩

variable [HasZeroObject A]
  [HasShift A ℤ]
  [Preadditive A]
  [∀ (n : ℤ), (shiftFunctor A n).Additive]
  [Pretriangulated A]
  [F.CommShift ℤ] [F.IsTriangulated]

section

variable [B.IsClosedUnderIsomorphisms]

/-- Factorization property of right localizing subcategories. -/
lemma fac_of_isRightLocalizing' [B.IsRightLocalizing F]
    {X : A} {Y : C} (s : F.obj X ⟶ Y) (hs : B.trW s) :
    ∃ (X' : A) (s' : X ⟶ X') (_ : (B.inverseImage F).trW s') (b : Y ⟶ F.obj X'),
      s ≫ b = F.map s' := by
  rw [ObjectProperty.trW_iff'] at hs
  obtain ⟨W, a, b, hT, hW⟩ := hs
  obtain ⟨W', hW', c, d, fac⟩ := B.fac_of_isRightLocalizing F a hW
  obtain ⟨U, e, f, hT'⟩ := Pretriangulated.distinguished_cocone_triangle d
  obtain ⟨β, hβ, _⟩ := complete_distinguished_triangle_morphism _ _ hT (F.map_distinguished _ hT')
    c (𝟙 _) (by simpa using fac.symm)
  dsimp at β hβ
  refine ⟨U, e, ?_, β, by simpa using hβ⟩
  rw [ObjectProperty.trW_iff']
  exact ⟨_, _, _, hT', hW'⟩

/-- Factorization property of left localizing subcategories. -/
lemma fac_of_isLeftLocalizing' [B.IsLeftLocalizing F]
    {X : A} {Y : C} (s : Y ⟶ F.obj X) (hs : B.trW s) :
    ∃ (X' : A) (s' : X' ⟶ X) (_ : (B.inverseImage F).trW s') (b : F.obj X' ⟶ Y),
      b ≫ s = F.map s' := by
  obtain ⟨X', s', hs', b, fac⟩ := B.op.fac_of_isRightLocalizing' F.op s.op
    (by simpa only [ObjectProperty.trW_op_iff] using hs)
  refine ⟨X'.unop, s'.unop, ?_, b.unop, Quiver.Hom.op_inj fac⟩
  rw [← trW_op_iff]
  exact hs'

variable {B F} in
/-- Constructor for right localizing categories. -/
lemma IsRightLocalizing.mk'
    (h : ∀ ⦃X : A⦄ ⦃Y : C⦄ (s : F.obj X ⟶ Y) (_ : B.trW s),
      ∃ (X' : A) (s' : X ⟶ X') (_ : (B.inverseImage F).trW s')
        (b : Y ⟶ F.obj X'), s ≫ b = F.map s') :
    B.IsRightLocalizing F where
  fac {Y X} φ hY := by
    obtain ⟨Z, s, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
    have hs : B.trW s := by
      rw [trW_iff']
      exact ⟨_, _, _, hT, hY⟩
    obtain ⟨W, s', hs', c, fac⟩ := h s hs
    obtain ⟨U, d, e, hT'⟩ := distinguished_cocone_triangle₁ s'
    obtain ⟨β, hβ, _⟩ := complete_distinguished_triangle_morphism₁ _ _ hT
      (F.map_distinguished _ hT') (𝟙 _) c (by simpa using fac)
    dsimp at β hβ
    refine ⟨U, (B.trW_iff_of_distinguished' _ (F.map_distinguished _ hT')).1 ?_,
      β, d, by simpa using hβ.symm⟩
    rw [trW_iff] at hs' ⊢
    obtain ⟨_, _, _, hT'', hV⟩ := hs'
    exact ⟨_, _, _, F.map_distinguished _ hT'', hV⟩

variable {B F} in
/-- Constructor for left localizing categories. -/
lemma IsLeftLocalizing.mk'
    (h : ∀ ⦃Y : C⦄ ⦃X : A⦄ (s : Y ⟶ F.obj X) (_ : B.trW s),
      ∃ (X' : A) (s' : X' ⟶ X) (_ : (B.inverseImage F).trW s')
        (b : F.obj X' ⟶ Y), b ≫ s = F.map s') :
    B.IsLeftLocalizing F := by
  have : B.op.IsRightLocalizing F.op := IsRightLocalizing.mk' (fun X Y s hs => by
    obtain ⟨X', s', h, b, fac⟩ := h s.unop (trW_of_op _ _ hs)
    exact ⟨Opposite.op X', s'.op, trW_of_unop _ _ h, b.op, Quiver.Hom.unop_inj fac⟩)
  exact B.isLeftLocalizing_of_op F

end

variable (L : C ⥤ D) [L.IsLocalization B.trW]

section

variable [B.IsClosedUnderIsomorphisms]
  (L' : A ⥤ D') [L'.IsLocalization (B.inverseImage F).trW]
  (F' : D' ⥤ D) [Localization.Lifting L' (B.inverseImage F).trW (F ⋙ L) F']
  [IsTriangulated C]

noncomputable def full_of_isRightLocalizing [B.IsRightLocalizing F] [F.Full] : F'.Full := by
  have := Localization.essSurj L' (B.inverseImage F).trW
  apply F'.full_of_precomp_essSurj L'
  intro X₁ X₂ φ
  have e := Localization.Lifting.iso L' (B.inverseImage F).trW (F ⋙ L) F'
  obtain ⟨φ', hφ'⟩ : ∃ φ', φ = e.hom.app X₁ ≫ φ' ≫ e.inv.app X₂ :=
    ⟨e.inv.app X₁ ≫ φ ≫ e.hom.app X₂, by simp⟩
  obtain ⟨f, hf⟩ := Localization.exists_leftFraction L B.trW φ'
  obtain ⟨X₃, s', hs', t, fac⟩ := B.fac_of_isRightLocalizing' F f.s f.hs
  let f' : (B.inverseImage F).trW.LeftFraction X₁ X₂ :=
    { f := F.preimage (f.f ≫ t)
      s := F.preimage (f.s ≫ t)
      hs := by
        rw [B.inverseImage_trW_iff, F.map_preimage, fac, ← B.inverseImage_trW_iff F]
        exact hs' }
  have hf' : φ' ≫ L.map (F.map f'.s) = L.map (F.map f'.f) := by
    replace hf := hf =≫ L.map (f.s)
    rw [f.map_comp_map_s] at hf
    dsimp
    rw [F.map_preimage, F.map_preimage, L.map_comp, L.map_comp, reassoc_of% hf]
  have : IsIso (F'.map (L'.map f'.s)) :=
    ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff
      ((Arrow.isoOfNatIso e) (Arrow.mk f'.s))).2
        (Localization.inverts _ B.trW _
          (by simpa only [← B.inverseImage_trW_iff F] using f'.hs))
  refine ⟨f'.map L' (Localization.inverts _ _), ?_⟩
  rw [hφ', ← cancel_mono (F'.map (L'.map f'.s)), ← F'.map_comp, f'.map_comp_map_s,
    assoc, assoc]
  erw [← e.inv.naturality]
  rw [Functor.comp_map, reassoc_of% hf']
  erw [e.inv.naturality, e.hom_inv_id_app_assoc]
  rfl

include L L' in
lemma faithful_of_isRightLocalizing [B.IsRightLocalizing F] [F.Full] [F.Faithful] :
    F'.Faithful := by
  have e := Localization.Lifting.iso L' (B.inverseImage F).trW (F ⋙ L) F'
  have := IsTriangulated.of_fully_faithful_triangulated_functor F
  letI := Localization.preadditive L' (B.inverseImage F).trW
  letI := Localization.functor_additive L' (B.inverseImage F).trW
  letI := Localization.preadditive L B.trW
  letI := Localization.functor_additive L B.trW
  have : (B.inverseImage F).trW.HasLeftCalculusOfFractions := inferInstance
  have : F'.Additive := by
    rw [Localization.functor_additive_iff L' (B.inverseImage F).trW]
    exact Functor.additive_of_iso e.symm
  apply F'.faithful_of_precomp_cancel_zero_of_hasLeftCalculusOfFractions L' (B.inverseImage F).trW
  intro X₁ X₂ f hf
  replace hf : L.map (F.map f) = L.map 0 := by
    erw [L.map_zero, ← NatIso.naturality_1 e f, hf, zero_comp, comp_zero]
  rw [MorphismProperty.map_eq_iff_postcomp L B.trW] at hf
  obtain ⟨Z, s, hs, fac⟩ := hf
  rw [zero_comp] at fac
  obtain ⟨W, s', hs', t, fac'⟩ := B.fac_of_isRightLocalizing' F s hs
  have hfs' : f ≫ s' = 0 := F.map_injective (by
    rw [F.map_zero, F.map_comp, ← fac', reassoc_of% fac, zero_comp])
  have := Localization.inverts L' (B.inverseImage F).trW s' hs'
  rw [← cancel_mono (L'.map s'), zero_comp, ← L'.map_comp, hfs', L'.map_zero]

end

variable {L : C ⥤ D} {L' : A ⥤ D'} {H : D' ⥤ D} (e : L' ⋙ H ≅ F ⋙ L)
  [L'.EssSurj] [H.Full] [H.Faithful] [L.IsLocalization B.trW]
  [IsTriangulated C] [B.IsClosedUnderIsomorphisms]

include e in
lemma isLocalization_of_isRightLocalizing [B.IsRightLocalizing F] [F.Full] [F.Faithful]:
    L'.IsLocalization (B.inverseImage F).trW := by
  have hL' : (B.inverseImage F).trW.IsInvertedBy L' := fun X₁ X₂ f hf => by
    rw [B.inverseImage_trW_iff] at hf
    have : IsIso (H.map (L'.map f)) :=
      ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff
        (Arrow.isoOfNatIso e f)).2 (Localization.inverts L B.trW _ hf)
    apply isIso_of_fully_faithful H
  let G := Localization.lift _ hL' (B.inverseImage F).trW.Q
  have eG : (B.inverseImage F).trW.Q ⋙ G ≅ L' :=
    Localization.Lifting.iso _ (B.inverseImage F).trW _ _
  have : Localization.Lifting (B.inverseImage F).trW.Q (B.inverseImage F).trW
    (F ⋙ L) (G ⋙ H) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eG H ≪≫ e⟩
  have := full_of_isRightLocalizing B F L (B.inverseImage F).trW.Q (G ⋙ H)
  have := faithful_of_isRightLocalizing B F L (B.inverseImage F).trW.Q (G ⋙ H)
  have : G.EssSurj :=
    { mem_essImage := fun X =>
        ⟨_, ⟨eG.app (L'.objPreimage X) ≪≫ L'.objObjPreimageIso X⟩⟩ }
  have : G.Full := Functor.Full.of_comp_faithful G H
  have : G.Faithful := Functor.Faithful.of_comp_iso (Iso.refl (G ⋙ H))
  have : G.IsEquivalence := { }
  exact Functor.IsLocalization.of_equivalence_target (B.inverseImage F).trW.Q _ _
    G.asEquivalence eG

include e in
lemma isLocalization_of_isLeftLocalizing [B.IsLeftLocalizing F] [F.Full] [F.Faithful] :
    L'.IsLocalization (B.inverseImage F).trW := by
  rw [Functor.isLocalization_iff_op, ← trW_op]
  have : Functor.IsLocalization L.op (B.op.trW) := by
    rw [trW_op]
    infer_instance
  let e' : L'.op ⋙ H.op ≅ F.op ⋙ L.op := NatIso.op e.symm
  exact B.op.isLocalization_of_isRightLocalizing F.op e'

end ObjectProperty

end CategoryTheory
