import Mathlib.CategoryTheory.Localization.DerivabilityStructure

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) [Φ.IsRightDerivabilityStructure]

namespace IsRightDerivabilityStructure

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (F : D₁ ⥤ D₂)
  [Full F] [Faithful F] [W₁.IsMultiplicative] [W₂.ContainsIdentities]
  [∀ X₂, IsConnected (Φ.RightResolution X₂)]
  [HasRightResolutions Φ.arrow]

namespace Constructor

variable {L₁ L₂ F} (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
  {X₂ X₂' : C₂} {X₃ : D₁} (g : L₂.obj X₂ ⟶ F.obj X₃)

namespace FromRightResolution

@[simps! left]
noncomputable def obj (f : Φ.RightResolution X₂) : TwoSquare.JDownwards e.hom g := by
  refine' CostructuredArrow.mk (_ : (TwoSquare.structuredArrowDownwards e.hom X₂).obj (StructuredArrow.mk f.w) ⟶ _)
  exact StructuredArrow.homMk (F.preimage (e.inv.app _ ≫ (Localization.isoOfHom L₂ W₂ _ f.hw).inv ≫ g))

@[simp]
lemma map_obj_hom_right (f : Φ.RightResolution X₂) :
    F.map (obj Φ e g f).hom.right =
      e.inv.app _ ≫ (Localization.isoOfHom L₂ W₂ _ f.hw).inv ≫ g := by
  simp [obj]

noncomputable def map {f f' : Φ.RightResolution X₂} (φ : f ⟶ f') : obj Φ e g f ⟶ obj Φ e g f' :=
  CostructuredArrow.homMk (StructuredArrow.homMk φ.f) (by
    ext
    dsimp
    apply F.map_injective
    simp only [Functor.map_comp, map_obj_hom_right, Functor.comp_obj]
    erw [e.inv.naturality_assoc]
    congr 1
    rw [← cancel_epi (isoOfHom L₂ W₂ f.w f.hw).hom]
    simp only [isoOfHom_hom, Functor.comp_obj, Functor.comp_map, isoOfHom_hom_inv_id_assoc,
      ← L₂.map_comp_assoc, φ.comm])

end FromRightResolution

noncomputable def fromRightResolution : Φ.RightResolution X₂ ⥤
      TwoSquare.JDownwards e.hom g where
  obj := FromRightResolution.obj Φ e g
  map := FromRightResolution.map Φ e g

set_option maxHeartbeats 800000 in
@[simps]
def precompJDownwards (γ : X₂' ⟶ X₂) :
    TwoSquare.JDownwards e.hom g ⥤ TwoSquare.JDownwards e.hom (L₂.map γ ≫ g) where
  obj f := CostructuredArrow.mk' (StructuredArrow.mk' f.left.right (γ ≫ f.left.hom))
      (StructuredArrow.homMk f.hom.right (by simpa using L₂.map γ ≫= StructuredArrow.w f.hom))
  map {f₁ f₂} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right) (by
    ext
    have eq := CostructuredArrow.w φ
    dsimp at eq ⊢
    rw [← eq]
    rfl)

example : ℕ := 42

/-lemma isConnected_JDownwards :
    IsConnected (TwoSquare.JDownwards e.hom g) := by
  have : Nonempty (TwoSquare.JDownwards e.hom g) :=
    ⟨(fromRightResolution Φ e g).obj (Classical.arbitrary _)⟩
  suffices ∀ (X : TwoSquare.JDownwards e.hom g),
      ∃ (Y : Φ.RightResolution X₂), Zigzag X ((fromRightResolution Φ e g).obj Y) by
    refine' zigzag_isConnected (fun X X' => _)
    obtain ⟨Y, hX⟩ := this X
    obtain ⟨Y', hX'⟩ := this X'
    exact hX.trans ((zigzag_obj_of_zigzag _ (isConnected_zigzag Y Y')).trans (zigzag_symmetric hX'))
  intro γ₀
  -- γ is named g in Kahn-Maltsiniotis
  -- X₂ is named d
  -- X₃ is named c bar
  -- L₁ is named P
  -- L₂ is named Q
  -- Φ.functor is named K
  -- F is named K bar
  obtain ⟨c, γ, x, comm, hγ⟩ := γ₀.cases
  sorry
  --have R : Φ.arrow.RightResolution (Arrow.mk γ.left.hom) := Classical.arbitrary _
  --have : EssSurj L₁ := Localization.essSurj L₁ W₁
  --sorry-/

end Constructor

/-
-- Kahn-Maltsiniotis, Lemme 6.5
lemma mk' [CatCommSq Φ.functor L₁ L₂ F] : Φ.IsRightDerivabilityStructure := by
  rw [Φ.isRightDerivabilityStructure_iff L₁ L₂ F (CatCommSq.iso _ _ _ _)]
  rw [TwoSquare.guitartExact_iff_isConnected_downwards]
  apply Constructor.isConnected_JDownwards-/

end IsRightDerivabilityStructure

end LocalizerMorphism

end CategoryTheory
