import Mathlib.CategoryTheory.Triangulated.Opposite
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Lemmas

namespace CategoryTheory

open Category Limits Pretriangulated

namespace Triangulated

variable {A C D D' : Type*} [Category A] [Category C] [Category D] [Category D']
  [HasZeroObject A] [HasZeroObject C]
  [HasShift A ℤ] [HasShift C ℤ]
  [Preadditive A] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor A n).Additive]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated A] [Pretriangulated C] [IsTriangulated C]
  (F : A ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
  [F.Full] [F.Faithful]
  (B : Subcategory C) [ClosedUnderIsomorphisms B.P]

class IsRightLocalizing : Prop where
  fac {Y : C} {X : A} (φ : Y ⟶ F.obj X) (hY : B.P Y) :
    ∃ (Y' : A) (_ : B.P (F.obj Y')) (a : Y ⟶ F.obj Y') (b : Y' ⟶ X),
      a ≫ F.map b = φ

class IsLeftLocalizing : Prop where
  fac {X : A} {Y : C} (φ : F.obj X ⟶ Y) (hY : B.P Y) :
    ∃ (Y' : A) (_ : B.P (F.obj Y')) (a : F.obj Y' ⟶ Y) (b : X ⟶ Y'),
      F.map b ≫ a = φ

lemma fac_of_isRightLocalizing [IsRightLocalizing F B]
    {Y : C} {X : A} (φ : Y ⟶ F.obj X) (hY : B.P Y) :
    ∃ (Y' : A) (_ : B.P (F.obj Y')) (a : Y ⟶ F.obj Y') (b : Y' ⟶ X),
      a ≫ F.map b = φ :=
  IsRightLocalizing.fac φ hY

lemma fac_of_isLeftLocalizing [IsLeftLocalizing F B]
    {X : A} {Y : C} (φ : F.obj X ⟶ Y) (hY : B.P Y) :
    ∃ (Y' : A) (_ : B.P (F.obj Y')) (a : F.obj Y' ⟶ Y) (b : X ⟶ Y'),
      F.map b ≫ a = φ :=
  IsLeftLocalizing.fac φ hY

open CategoryTheory.Pretriangulated.Opposite

instance [IsLeftLocalizing F B] : IsRightLocalizing F.op B.op where
  fac {Y X} φ hY := by
    obtain ⟨Y', hY', a, b, fac⟩ := fac_of_isLeftLocalizing F B φ.unop hY
    exact ⟨Opposite.op Y', hY', a.op, b.op, Quiver.Hom.unop_inj fac⟩

lemma fac_of_isRightLocalizing' [IsRightLocalizing F B]
    {X : A} {Y : C} (s : F.obj X ⟶ Y) (hs : B.W s) :
    ∃ (X' : A) (s' : X ⟶ X') (_ : (B.inverseImage F).W s') (b : Y ⟶ F.obj X'),
      s ≫ b = F.map s' := by
  rw [Subcategory.W_iff'] at hs
  obtain ⟨W, a, b, hT, hW⟩ := hs
  obtain ⟨W', hW', c, d, fac⟩ := fac_of_isRightLocalizing F B a hW
  obtain ⟨U, e, f, hT'⟩ := Pretriangulated.distinguished_cocone_triangle d
  obtain ⟨β, hβ, _⟩ := complete_distinguished_triangle_morphism _ _ hT (F.map_distinguished _ hT')
    c (𝟙 _) (by simpa using fac.symm)
  dsimp at β hβ
  refine' ⟨U, e, _, β, by simpa using hβ⟩
  rw [Subcategory.W_iff']
  exact ⟨_, _, _, hT', hW'⟩

/-lemma fac_of_isLeftLocalizing' [IsLeftLocalizing F B]
    {X : A} {Y : C} (s : Y ⟶ F.obj X) (hs : B.W s) :
    ∃ (X' : A) (s' : X' ⟶ X) (_ : (B.inverseImage F).W s') (b : F.obj X' ⟶ Y),
      b ≫ s = F.map s' := by
  have : F.op.IsTriangulated := sorry
  obtain ⟨X', s', hs', b, fac⟩ := fac_of_isRightLocalizing' F.op B.op s.op (by
    sorry)
  refine' ⟨X'.unop, s'.unop, sorry, b.unop, Quiver.Hom.op_inj fac⟩-/

lemma IsRightLocalizing.mk'
    (h : ∀ ⦃X : A⦄ ⦃Y : C⦄ (s : F.obj X ⟶ Y) (_ : B.W s),
      ∃ (X' : A) (s' : X ⟶ X') (_ : (B.inverseImage F).W s')
        (b : Y ⟶ F.obj X'), s ≫ b = F.map s') :
    IsRightLocalizing F B where
  fac {Y X} φ hY := by
    obtain ⟨Z, s, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
    have hs : B.W s := by
      rw [Subcategory.W_iff']
      exact ⟨_, _, _, hT, hY⟩
    obtain ⟨W, s', hs', c, fac⟩ := h s hs
    obtain ⟨U, d, e, hT'⟩ := distinguished_cocone_triangle₁ s'
    obtain ⟨β, hβ, _⟩ := complete_distinguished_triangle_morphism₁ _ _ hT
      (F.map_distinguished _ hT') (𝟙 _) c (by simpa using fac)
    dsimp at β hβ
    refine' ⟨U, (B.mem_W_iff_of_distinguished' _ (F.map_distinguished _ hT')).1 _,
      β, d, by simpa using hβ.symm⟩
    rw [Subcategory.W_iff] at hs' ⊢
    obtain ⟨_, _, _, hT'', hV⟩ := hs'
    exact ⟨_, _, _, F.map_distinguished _ hT'', hV⟩

variable (L : C ⥤ D) [L.IsLocalization B.W] [IsRightLocalizing F B]

section

variable (L' : A ⥤ D') [L'.IsLocalization (B.inverseImage F).W]
  (F' : D' ⥤ D) [Localization.Lifting L' (B.inverseImage F).W (F ⋙ L) F']

noncomputable def full_of_isRightLocalizing : F'.Full := by
  have := Localization.essSurj L' (B.inverseImage F).W
  apply F'.full_of_precomp_essSurj L'
  intro X₁ X₂ φ
  have e := Localization.Lifting.iso L' (B.inverseImage F).W (F ⋙ L) F'
  obtain ⟨φ', hφ'⟩ : ∃ φ', φ = e.hom.app X₁ ≫ φ' ≫ e.inv.app X₂ :=
    ⟨e.inv.app X₁ ≫ φ ≫ e.hom.app X₂, by simp⟩
  obtain ⟨f, hf⟩ := Localization.exists_leftFraction L B.W φ'
  obtain ⟨X₃, s', hs', t, fac⟩ := fac_of_isRightLocalizing' F B f.s f.hs
  let f' : (B.inverseImage F).W.LeftFraction X₁ X₂ :=
    { f := F.preimage (f.f ≫ t)
      s := F.preimage (f.s ≫ t)
      hs := by
        rw [B.mem_inverseImage_W_iff, F.image_preimage, fac, ← B.mem_inverseImage_W_iff F]
        exact hs' }
  have hf' : φ' ≫ L.map (F.map f'.s) = L.map (F.map f'.f) := by
    replace hf := hf =≫ L.map (f.s)
    rw [f.map_comp_map_s] at hf
    dsimp
    rw [F.image_preimage, F.image_preimage, L.map_comp, L.map_comp, reassoc_of% hf]
  have : IsIso (F'.map (L'.map f'.s)) :=
    ((MorphismProperty.RespectsIso.isomorphisms D).arrow_mk_iso_iff
      ((Arrow.isoOfNatIso e) (Arrow.mk f'.s))).2
        (Localization.inverts _ B.W _
          (by simpa only [← B.mem_inverseImage_W_iff F] using f'.hs))
  refine' ⟨f'.map L' (Localization.inverts _ _), _⟩
  rw [hφ', ← cancel_mono (F'.map (L'.map f'.s)), ← F'.map_comp, f'.map_comp_map_s,
    assoc, assoc]
  erw [← e.inv.naturality]
  rw [Functor.comp_map, reassoc_of% hf']
  erw [e.inv.naturality, e.hom_inv_id_app_assoc]
  rfl

lemma faithful_of_isRightLocalizing : F'.Faithful := by
  have e := Localization.Lifting.iso L' (B.inverseImage F).W (F ⋙ L) F'
  have := IsTriangulated.of_fully_faithful_triangulated_functor F
  letI := Localization.preadditive L' (B.inverseImage F).W
  letI := Localization.functor_additive L' (B.inverseImage F).W
  letI := Localization.preadditive L B.W
  letI := Localization.functor_additive L B.W
  have : (B.inverseImage F).W.HasLeftCalculusOfFractions := inferInstance
  have : F'.Additive := by
    rw [Localization.functor_additive_iff L' (B.inverseImage F).W]
    exact Functor.additive_of_iso e.symm
  apply F'.faithful_of_precomp_cancel_zero_of_hasLeftCalculusOfFractions L' (B.inverseImage F).W
  intro X₁ X₂ f hf
  replace hf : L.map (F.map f) = L.map 0 := by
    erw [L.map_zero, ← NatIso.naturality_1 e f, hf, zero_comp, comp_zero]
  rw [MorphismProperty.map_eq_iff_postcomp L B.W] at hf
  obtain ⟨Z, s, hs, fac⟩ := hf
  rw [zero_comp] at fac
  obtain ⟨W, s', hs', t, fac'⟩ := fac_of_isRightLocalizing' F B s hs
  have hfs' : f ≫ s' = 0 := F.map_injective (by
    rw [F.map_zero, F.map_comp, ← fac', reassoc_of% fac, zero_comp])
  have := Localization.inverts L' (B.inverseImage F).W s' hs'
  rw [← cancel_mono (L'.map s'), zero_comp, ← L'.map_comp, hfs', L'.map_zero]

end

variable {L : C ⥤ D} {L' : A ⥤ D'} {H : D' ⥤ D} (e : L' ⋙ H ≅ F ⋙ L)
  [L'.EssSurj] [H.Full] [H.Faithful] [L.IsLocalization B.W]

lemma isLocalization_of_isRightLocalizing :
    L'.IsLocalization (B.inverseImage F).W := by
  have hL' : (B.inverseImage F).W.IsInvertedBy L' := fun X₁ X₂ f hf => by
    rw [B.mem_inverseImage_W_iff] at hf
    have : IsIso (H.map (L'.map f)) :=
      ((MorphismProperty.RespectsIso.isomorphisms D).arrow_mk_iso_iff
        (Arrow.isoOfNatIso e f)).2 (Localization.inverts L B.W _ hf)
    apply isIso_of_fully_faithful H
  let G := Localization.lift _ hL' (B.inverseImage F).W.Q
  have eG : (B.inverseImage F).W.Q ⋙ G ≅ L' :=
    Localization.Lifting.iso _ (B.inverseImage F).W _ _
  have : Localization.Lifting (B.inverseImage F).W.Q (B.inverseImage F).W
    (F ⋙ L) (G ⋙ H) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eG H ≪≫ e⟩
  have := full_of_isRightLocalizing F B L (B.inverseImage F).W.Q (G ⋙ H)
  have := faithful_of_isRightLocalizing F B L (B.inverseImage F).W.Q (G ⋙ H)
  have : G.EssSurj :=
    { mem_essImage := fun X =>
        ⟨_, ⟨eG.app (L'.objPreimage X) ≪≫ L'.objObjPreimageIso X⟩⟩ }
  have : G.Full := Functor.Full.ofCompFaithful G H
  have : G.Faithful := Functor.Faithful.of_comp_iso (Iso.refl (G ⋙ H))
  have := Functor.IsEquivalence.ofFullyFaithfullyEssSurj G
  exact Functor.IsLocalization.of_equivalence_target (B.inverseImage F).W.Q _ _
    G.asEquivalence eG

end Triangulated

end CategoryTheory
