import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization

namespace TwoSquare

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (w : TwoSquare T L R B)

@[simps]
def costructuredArrowDownwardsPrecomp
    {X₂ X₂' : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) (g' : R.obj X₂' ⟶ B.obj X₃)
    (γ : X₂' ⟶ X₂) (hγ : R.map γ ≫ g = g') :
    w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g' where
  obj A := CostructuredArrowDownwards.mk _ _ A.left.right (γ ≫ A.left.hom) A.hom.right
    (by simpa [← hγ] using R.map γ ≫= StructuredArrow.w A.hom)
  map {A A'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right (by
      dsimp
      rw [assoc, StructuredArrow.w])) (by
    ext
    dsimp
    rw [← CostructuredArrow.w φ, structuredArrowDownwards_map]
    dsimp)
  map_id A := by ext; dsimp
  map_comp φ φ' := by ext; dsimp

end TwoSquare

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism


namespace IsRightDerivabilityStructure

section

variable (Φ : LocalizerMorphism W₁ W₂) [Φ.IsLocalizedEquivalence]
  [W₁.IsMultiplicative] [∀ X₂, IsConnected (Φ.RightResolution X₂)]
  [Φ.arrow.HasRightResolutions] [W₂.ContainsIdentities]

namespace Constructor

variable {D : Type*} [Category D] (L : C₂ ⥤ D) [L.IsLocalization W₂]
  {d : C₂} {X₃ : D} (y : L.obj d ⟶ X₃)

@[simps]
noncomputable def fromRightResolution :
    Φ.RightResolution d ⥤ ((TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y) where
  obj R := CostructuredArrow.mk (Y := StructuredArrow.mk R.w)
    (StructuredArrow.homMk ((Localization.isoOfHom L W₂ R.w R.hw).inv ≫ y))
  map {R R'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.f) (by
    ext
    dsimp
    rw [← assoc, ← cancel_epi (Localization.isoOfHom L W₂ R.w R.hw).hom,
      isoOfHom_hom, isoOfHom_hom_inv_id_assoc, assoc, ← L.map_comp_assoc,
      φ.comm, isoOfHom_hom_inv_id_assoc])

lemma isConnected :
    IsConnected ((TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y) := by
  let w := (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv)
  have : Φ.HasRightResolutions := Φ.hasRightResolutions_of_arrow
  have : Nonempty (w.CostructuredArrowDownwards y) :=
    ⟨(fromRightResolution Φ L y).obj (Classical.arbitrary _)⟩
  suffices ∀ (X : w.CostructuredArrowDownwards y),
    ∃ Y, Zigzag X ((fromRightResolution Φ L y).obj Y) by
    refine' zigzag_isConnected (fun X X' => _)
    obtain ⟨Y, hX⟩ := this X
    obtain ⟨Y', hX'⟩ := this X'
    exact hX.trans ((zigzag_obj_of_zigzag _ ((isPreconnected_zigzag Y Y'))).trans hX'.symm)
  intro X
  obtain ⟨c, g, x, fac, rfl⟩ := TwoSquare.CostructuredArrowDownwards.mk_surjective X
  dsimp [w] at x fac
  rw [id_comp] at fac
  let ρ : Φ.arrow.RightResolution (Arrow.mk g) := Classical.arbitrary _
  refine' ⟨RightResolution.mk ρ.w.left ρ.hw.1, _⟩
  have := zigzag_obj_of_zigzag (fromRightResolution Φ L x ⋙ w.costructuredArrowDownwardsPrecomp x y g fac)
      (isPreconnected_zigzag  (RightResolution.mk (𝟙 _) (W₂.id_mem _))
      (RightResolution.mk ρ.w.right ρ.hw.2))
  refine' Zigzag.trans _ (Zigzag.trans this _)
  · exact Zigzag.of_hom (eqToHom (by aesop))
  · apply Zigzag.of_inv
    refine' CostructuredArrow.homMk (StructuredArrow.homMk ρ.X₁.hom (by simp)) ?_
    ext
    dsimp
    rw [← cancel_epi (isoOfHom L W₂ ρ.w.left ρ.hw.1).hom, isoOfHom_hom, isoOfHom_hom_inv_id_assoc,
      ← L.map_comp_assoc, Arrow.w_mk_right, Arrow.mk_hom, L.map_comp, assoc, isoOfHom_hom_inv_id_assoc, fac]

end Constructor

lemma mk' : Φ.IsRightDerivabilityStructure := by
  rw [Φ.isRightDerivabilityStructure_iff (Φ.functor ⋙ W₂.Q) W₂.Q (𝟭 _)
    (Functor.rightUnitor _).symm, TwoSquare.guitartExact_iff_isConnected_downwards]
  intro X₂ X₃ g
  apply Constructor.isConnected

end

section

variable (Φ : LocalizerMorphism W₁ W₂) {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (F : D₁ ⥤ D₂)
  [F.Full] [F.Faithful] [W₁.IsMultiplicative] [W₂.ContainsIdentities]
  [∀ X₂, IsConnected (Φ.RightResolution X₂)]
  [HasRightResolutions Φ.arrow]

-- Kahn-Maltsiniotis, Lemme 6.5
lemma mk'' [CatCommSq Φ.functor L₁ L₂ F] : Φ.IsRightDerivabilityStructure := by
  have : Φ.IsLocalizedEquivalence := by
    have := Localization.essSurj L₂ W₂
    have : F.EssSurj := ⟨fun Y => by
      let R : Φ.RightResolution (L₂.objPreimage Y) := Classical.arbitrary _
      exact ⟨L₁.obj R.X₁, ⟨(CatCommSq.iso Φ.functor L₁ L₂ F).symm.app R.X₁ ≪≫
        (Localization.isoOfHom L₂ W₂ R.w R.hw).symm ≪≫ L₂.objObjPreimageIso Y⟩⟩⟩
    have := Functor.IsEquivalence.ofFullyFaithfullyEssSurj F
    exact IsLocalizedEquivalence.mk' Φ L₁ L₂ F
  apply mk'

end

end IsRightDerivabilityStructure

end LocalizerMorphism

end CategoryTheory
