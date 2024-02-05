import Mathlib.CategoryTheory.Localization.DerivabilityStructure

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

@[simp]
lemma Localization.isoOfHom_id (L : C₁ ⥤ C₂) (W : MorphismProperty C₁)
    [L.IsLocalization W] (X : C₁) (hX : W (𝟙 X)) :
    isoOfHom L W (𝟙 X) hX = Iso.refl _ := by aesop_cat

lemma Arrow.mk_surjective (f : Arrow C₁) : ∃ (X Y : C₁) (g : X ⟶ Y), f = Arrow.mk g := ⟨_, _, f.hom, rfl⟩
lemma Arrow.homMk_surjective {f g : Arrow C₁} (φ : f ⟶ g) :
  ∃ (φ₁ : f.left ⟶ g.left) (φ₂ : f.right ⟶ g.right) (comm : φ₁ ≫ g.hom = f.hom ≫ φ₂),
    φ = Arrow.homMk comm := ⟨φ.left, φ.right, Arrow.w φ, rfl⟩

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

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

@[simps!]
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

@[simps]
noncomputable def fromRightResolution : Φ.RightResolution X₂ ⥤
      TwoSquare.JDownwards e.hom g where
  obj := FromRightResolution.obj Φ e g
  map := FromRightResolution.map Φ e g

-- this is extravagant...
set_option maxHeartbeats 1600000 in
@[simps]
def precompJDownwards (γ : X₂' ⟶ X₂) (g' : L₂.obj X₂' ⟶ F.obj X₃) (hg' : L₂.map γ ≫ g = g'):
    TwoSquare.JDownwards e.hom g ⥤ TwoSquare.JDownwards e.hom g' where
  obj f := CostructuredArrow.mk (Y := StructuredArrow.mk (Y := f.left.right) (γ ≫ f.left.hom))
      (StructuredArrow.homMk f.hom.right (by
        have eq := L₂.map γ ≫= StructuredArrow.w f.hom
        dsimp at eq ⊢
        simp only [Functor.map_comp, assoc] at eq ⊢
        rw [eq, hg']))
  map {f₁ f₂} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right) (by
    ext
    have eq := CostructuredArrow.w φ
    dsimp at eq ⊢
    rw [← eq]
    rfl)

lemma isConnected_JDownwards :
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
  -- γ' is named g'
  -- g is named y
  -- X₂ is named d
  -- X₃ is named c bar
  -- L₁ is named P
  -- L₂ is named Q
  -- Φ.functor is named K
  -- F is named K bar
  obtain ⟨c, γ, x, comm, hγ₀⟩ := γ₀.mk_surjective
  have R : Φ.arrow.RightResolution (Arrow.mk γ) := Classical.arbitrary _
  obtain ⟨ρ, w, ⟨ht'', ht'⟩, rfl⟩ := R.mk_surjective
  obtain ⟨c'', c', f, rfl⟩ := ρ.mk_surjective
  obtain ⟨t'', t', commf, rfl⟩ := Arrow.homMk_surjective w
  dsimp at commf t' t'' ht' ht''
  obtain ⟨z, hz⟩ : ∃ (z : L₁.obj c ⟶ L₁.obj c'), F.map z = e.inv.app c ≫ L₂.map t' ≫ e.hom.app c' :=
    F.map_surjective _
  have : IsIso (L₂.map t') := Localization.inverts _ _ _ ht'
  have : IsIso (F.map z) := by rw [hz]; infer_instance
  have : IsIso z := isIso_of_reflects_iso z F
  have hz' : inv (F.map z) = e.inv.app c' ≫ (isoOfHom L₂ _ _ ht').inv ≫ e.hom.app c := by
    rw [← cancel_epi (F.map z), IsIso.hom_inv_id, hz]
    simp only [Functor.comp_obj, assoc, Iso.hom_inv_id_app_assoc,
      isoOfHom_hom_inv_id_assoc, Iso.inv_hom_id_app]
  let x' := inv z ≫ x
  let γ' := γ ≫ t'
  let cgx' : TwoSquare.JDownwards e.hom g := TwoSquare.JDownwards.mk e.hom g c' γ' x' (by
    dsimp
    simp only [Functor.map_comp, Functor.map_inv, assoc, hz',
      Functor.comp_obj, Iso.hom_inv_id_app_assoc, isoOfHom_hom_inv_id_assoc, comm])
  let x'' := L₁.map f ≫ x'
  let cgx'' : TwoSquare.JDownwards e.hom g := TwoSquare.JDownwards.mk e.hom g c'' t'' x'' (by
    dsimp
    simp only [F.map_comp, F.map_inv, hz', ← comm, ← assoc]
    congr 2
    simp only [assoc, ← cancel_mono (isoOfHom L₂ W₂ t' ht').hom,
      Functor.comp_obj, isoOfHom_hom, isoOfHom_inv_hom_id, comp_id, ← L₂.map_comp, ← commf]
    rw [L₂.map_comp]
    erw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, comp_id]
    rfl)
  let y' := F.map x
  let d' := Φ.functor.obj c
  have hy' : g = L₂.map γ ≫ e.hom.app c ≫ y' := comm.symm
  let R₁ : Φ.RightResolution d' :=
    { X₁ := c
      w := 𝟙 _
      hw := W₂.id_mem _ }
  let R₂ : Φ.RightResolution d' :=
    { X₁ := c'
      w := t'
      hw := ht' }
  let R₃ : Φ.RightResolution X₂ := RightResolution.mk _ ht''
  have hR₃ : cgx'' ⟶ (fromRightResolution Φ e g).obj R₃ :=
    CostructuredArrow.homMk (StructuredArrow.homMk (𝟙 _)) (by
      ext
      apply F.map_injective
      dsimp
      simp only [Functor.map_id, id_comp, FromRightResolution.map_obj_hom_right,
        Functor.comp_obj, ← comm, Functor.map_comp, Functor.map_inv, hz', assoc]
      simp only [← assoc]
      congr 2
      simp only [← cancel_mono (isoOfHom L₂ W₂ t' ht').hom,
        assoc, isoOfHom_hom, isoOfHom_inv_hom_id, comp_id, ← L₂.map_comp, ← commf]
      simp only [Functor.map_comp, isoOfHom_inv_hom_id_assoc]
      erw [e.inv.naturality f]
      rfl)
  let κ : Φ.RightResolution d' ⥤ TwoSquare.JDownwards e.hom g :=
    fromRightResolution Φ e (e.hom.app c ≫ y') ⋙
      precompJDownwards Φ e (e.hom.app c ≫ y') γ g comm
  have hκ₁ : γ₀ ⟶ κ.obj R₁ := by
    rw [hγ₀]
    refine' CostructuredArrow.homMk (StructuredArrow.homMk (𝟙 _)) _
    ext
    apply F.map_injective
    dsimp
    simp
  have hκ₂ : κ.obj R₂ ⟶ cgx' :=
    CostructuredArrow.homMk (StructuredArrow.homMk (𝟙 _)) (by
      ext
      apply F.map_injective
      dsimp
      simp [hz])
  have zigzag₁ : Zigzag γ₀ cgx' :=
    (Relation.ReflTransGen.single (Or.inl ⟨hκ₁⟩) : Zigzag γ₀ (κ.obj R₁)).trans
      ((zigzag_obj_of_zigzag κ (isConnected_zigzag R₁ R₂)).trans (Relation.ReflTransGen.single (Or.inl ⟨hκ₂⟩)))
  have zigzag₂ : Zigzag cgx' cgx'' :=
    Relation.ReflTransGen.single (Or.inr ⟨CostructuredArrow.homMk (StructuredArrow.homMk f commf)⟩)
  exact ⟨R₃, zigzag₁.trans (zigzag₂.trans (Relation.ReflTransGen.single (Or.inl ⟨hR₃⟩)))⟩

end Constructor

-- Kahn-Maltsiniotis, Lemme 6.5
lemma mk' [CatCommSq Φ.functor L₁ L₂ F] : Φ.IsRightDerivabilityStructure := by
  rw [Φ.isRightDerivabilityStructure_iff L₁ L₂ F (CatCommSq.iso _ _ _ _),
    TwoSquare.guitartExact_iff_isConnected_downwards]
  apply Constructor.isConnected_JDownwards

end IsRightDerivabilityStructure

end LocalizerMorphism

end CategoryTheory
