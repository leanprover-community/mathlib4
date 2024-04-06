import Mathlib.CategoryTheory.Triangulated.Subcategory
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
  [Full F] [Faithful F]
  (B : Subcategory C) [ClosedUnderIsomorphisms B.P]

class IsRightLocalizing where
  fac {Y : C} {X : A} (φ : Y ⟶ F.obj X) (hY : B.P Y) :
    ∃ (Y' : A) (_ : B.P (F.obj Y')) (a : Y ⟶ F.obj Y') (b : Y' ⟶ X),
      a ≫ F.map b = φ

lemma fac_of_isRightLocalizing [IsRightLocalizing F B]
    {Y : C} {X : A} (φ : Y ⟶ F.obj X) (hY : B.P Y) :
    ∃ (Y' : A) (_ : B.P (F.obj Y')) (a : Y ⟶ F.obj Y') (b : Y' ⟶ X),
      a ≫ F.map b = φ :=
  IsRightLocalizing.fac φ hY

lemma fac_of_isRightLocalizing' [IsRightLocalizing F B]
    {X : A} {Y : C} (s : F.obj X ⟶ Y) (hs : B.W s) :
    ∃ (X' : A) (s' : X ⟶ X') (_ : (B.inverseImage F).W s') (b : Y ⟶ F.obj X'),
      s ≫ b = F.map s' := by
  rw [Subcategory.W_iff'] at hs
  obtain ⟨W, a, b, hT, hW⟩ := hs
  obtain ⟨W', hW', c, d, fac⟩ := fac_of_isRightLocalizing F B a hW
  obtain ⟨U, e, f, hT'⟩ := distinguished_cocone_triangle d
  obtain ⟨β, hβ, _⟩ := complete_distinguished_triangle_morphism _ _ hT (F.map_distinguished _ hT')
    c (𝟙 _) (by simpa using fac.symm)
  dsimp at β hβ
  refine' ⟨U, e, _, β, by simpa using hβ⟩
  rw [Subcategory.W_iff']
  exact ⟨_, _, _, hT', hW'⟩

lemma IsRightLocalizing.mk'
    (h : ∀ ⦃X : A⦄ ⦃Y : C⦄ (s : F.obj X ⟶ Y) (_ : B.W s),
      ∃ (X' : A) (s' : X ⟶ X') (_ : (B.inverseImage F).W s')
        (b : Y ⟶ F.obj X'), s ≫ b = F.map s') :
    IsRightLocalizing F B where
  fac {Y X} φ hY := by
    obtain ⟨Z, s, b, hT⟩ := distinguished_cocone_triangle φ
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

noncomputable def full_of_isRightLocalizing : Full F' := by
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

--noncomputable def faithful_of_isRightLocalizing : Faithful F' := by
--  sorry


end

variable {L : C ⥤ D} {L' : A ⥤ D'} {H : D' ⥤ D} (e : L' ⋙ H ≅ F ⋙ L)
  [Full H] [Faithful H] [L.IsLocalization B.W]

--lemma isLocalization_of_isRightLocalizing : L'.IsLocalization (B.inverseImage F).W := by
--  sorry

-- TODO: Verdier, b) p. 131

end Triangulated

end CategoryTheory
