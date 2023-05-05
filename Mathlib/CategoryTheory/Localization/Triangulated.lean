import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Localization.FiniteProducts

namespace CategoryTheory

open Category Limits Pretriangulated

section

variable {C : Type _} [Category C]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive ] [Pretriangulated C]

class MorphismProperty.IsCompatibleWithTriangulation (W : MorphismProperty C) : Prop :=
  condition : ∀ (T₁ T₂ : Triangle C) (_ : T₁ ∈ distTriang C) (_ : T₂ ∈ distTriang C)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : W a) (_ : W b)
  (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁), ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (_ : W c),
  (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃)

end

namespace Functor

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ]
  (L : C ⥤ D) [HasCommShift L ℤ]

def essImageDistTriang : Set (Triangle D) :=
  fun T => ∃ (T' : Triangle C) (_ : T ≅ L.mapTriangle.obj T'), T' ∈ distTriang C

lemma essImageDistTriang_mem_of_iso {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁)
    (h : T₁ ∈ L.essImageDistTriang) : T₂ ∈ L.essImageDistTriang := by
  obtain ⟨T', e', hT'⟩ := h
  exact ⟨T', e ≪≫ e', hT'⟩

lemma contractible_mem_essImageDistTriang [EssSurj L] [HasZeroObject D]
    [HasZeroMorphisms D] [L.PreservesZeroMorphisms] (X : D) :
    contractibleTriangle X ∈ L.essImageDistTriang := by
  refine' ⟨contractibleTriangle (L.objPreimage X), _, Pretriangulated.contractible_distinguished _⟩
  exact ((contractibleTriangleFunctor D).mapIso (L.objObjPreimageIso X)).symm ≪≫
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) L.mapZeroObject.symm (by simp) (by simp) (by simp)

lemma rotate_essImageDistTriang [Preadditive D] [L.Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (T : Triangle D) :
  T ∈ L.essImageDistTriang ↔ T.rotate ∈ L.essImageDistTriang := by
  constructor
  . rintro ⟨T', e', hT'⟩
    exact ⟨T'.rotate, (rotate D).mapIso e' ≪≫ L.mapTriangleRotateIso.app T',
      rot_of_dist_triangle T' hT'⟩
  . rintro ⟨T', e', hT'⟩
    exact ⟨T'.invRotate, (triangleRotation D).unitIso.app T ≪≫ (invRotate D).mapIso e' ≪≫
      L.mapTriangleInvRotateIso.app T',  inv_rot_of_dist_triangle T' hT'⟩

end Functor

namespace Triangulated

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Additive]
    [L.HasCommShift ℤ]  [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
    [W.IsCompatibleWithShift ℤ] [W.IsCompatibleWithTriangulation]

namespace Localization

lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ L.essImageDistTriang := by
  have := Localization.essSurj L W
  let f' := MorphismProperty.HasLeftCalculusOfFractions.liftMap L W f
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle _ _ f'
  refine' ⟨L.obj Z, (MorphismProperty.HasLeftCalculusOfFractions.liftMapIso₂ L W f).hom ≫ L.map g,
    L.map h ≫ (L.commShiftIso (1 : ℤ)).hom.app _ ≫
      (MorphismProperty.HasLeftCalculusOfFractions.liftMapIso₁ L W f).inv⟦(1 : ℤ)⟧',
      _, _, H⟩
  refine' Triangle.isoMk _ _ (MorphismProperty.HasLeftCalculusOfFractions.liftMapIso₁ L W f)
    (MorphismProperty.HasLeftCalculusOfFractions.liftMapIso₂ L W f)
     (Iso.refl _) (MorphismProperty.HasLeftCalculusOfFractions.liftMap_fac L W f) (by simp) _
  dsimp
  simp only [assoc, id_comp, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, comp_id]

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ Functor.essImageDistTriang L) (hT₂ : T₂ ∈ Functor.essImageDistTriang L)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  suffices ∀ (T'₁ T'₂ : Triangle C) (_ : T'₁ ∈ distTriang C) (_ : T'₂ ∈ distTriang C)
      (a : L.obj (T'₁.obj₁) ⟶ L.obj (T'₂.obj₁)) (b : L.obj (T'₁.obj₂) ⟶ L.obj (T'₂.obj₂))
      (_ : L.map T'₁.mor₁ ≫ b = a ≫ L.map T'₂.mor₁),
      ∃ (c : L.obj T'₁.obj₃ ⟶ L.obj T'₂.obj₃), L.map T'₁.mor₂ ≫ c = b ≫ L.map T'₂.mor₂ ∧
        L.map T'₁.mor₃ ≫ (L.commShiftIso 1).hom.app _ ≫ (shiftFunctor D (1 : ℤ)).map a ≫
          (L.commShiftIso 1).inv.app _ = c ≫ L.map T'₂.mor₃ by
    obtain ⟨T'₁, e₁, hT'₁⟩ := hT₁
    obtain ⟨T'₂, e₂, hT'₂⟩ := hT₂
    have comm₁ := e₁.inv.comm₁
    have comm₁' := e₂.hom.comm₁
    have comm₂ := e₁.hom.comm₂
    have comm₂' := e₂.hom.comm₂
    have comm₃ := e₂.inv.comm₃
    have comm₃' := e₁.hom.comm₃
    dsimp at comm₁ comm₂ comm₃ comm₁' comm₂' comm₃'
    simp only [assoc] at comm₃
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := this T'₁ T'₂ hT'₁ hT'₂ (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
      (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) (by
        rw [reassoc_of% comm₁, reassoc_of% fac, assoc, assoc, comm₁'])
    refine' ⟨e₁.hom.hom₃ ≫ c ≫ e₂.inv.hom₃, _, _⟩
    . rw [reassoc_of% comm₂, reassoc_of% hc₁, ← reassoc_of% comm₂',
        Iso.hom_inv_id_triangle_hom₃, comp_id, Iso.hom_inv_id_triangle_hom₂_assoc]
    . simp only [← comm₃, ← reassoc_of% hc₂, ← reassoc_of% comm₃',
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
        Iso.hom_inv_id_triangle_hom₁_assoc, ← Functor.map_comp, assoc,
        Iso.hom_inv_id_triangle_hom₁, comp_id]
  clear T₁ T₂ hT₁ hT₂ a b fac
  intro T₁ T₂ hT₁ hT₂ a b fac₁
  obtain ⟨Y₁, a', s₁, hs₁, ha'⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.fac L W a
  obtain ⟨Y₂, f₂, s₂, hs₂, hf₂⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.toSq s₁ hs₁ T₂.mor₁
  obtain ⟨Y₂', b', s₂', hs₂', hb'⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.fac L W (b ≫ L.map s₂)
  dsimp at ha' hb'
  have := Localization.inverts L W s₁ hs₁
  have := Localization.inverts L W s₂' hs₂'
  have hf₂' := L.congr_map hf₂
  simp only [L.map_comp] at hf₂'
  obtain ⟨Y₂'', s₂'', hs₂'', fac₂⟩ :=
    (MorphismProperty.HasLeftCalculusOfFractions.map_eq_iff L W
      (a' ≫ f₂ ≫ s₂') (T₁.mor₁ ≫ b')).mp (by
        simp only [assoc, L.map_comp, ← cancel_mono (inv (L.map s₂')), ← hb', IsIso.hom_inv_id,
          comp_id, reassoc_of% fac₁, ha', hf₂', IsIso.inv_hom_id_assoc])
  simp only [assoc] at fac₂
  obtain ⟨Y₃, g, h, hT₃⟩ := Pretriangulated.distinguished_cocone_triangle _ _ (f₂ ≫ s₂' ≫ s₂'')
  let T₃ := Triangle.mk (f₂ ≫ s₂' ≫ s₂'') g h
  change T₃ ∈ distTriang C at hT₃
  have hf₂'' : T₂.mor₁ ≫ s₂ ≫ s₂' ≫ s₂'' = s₁ ≫ f₂ ≫ s₂' ≫ s₂'' := by rw [← reassoc_of% hf₂]
  have hs₃ : W (s₂ ≫ s₂' ≫ s₂'') := MorphismProperty.IsMultiplicative.comp _ _ _ hs₂
      (MorphismProperty.IsMultiplicative.comp _ _ _ hs₂' hs₂'')
  obtain ⟨α, hα₀, hα₁, hα₂⟩ := MorphismProperty.IsCompatibleWithTriangulation.condition
    T₂ T₃ hT₂ hT₃ s₁ _ hs₁ hs₃ hf₂''
  have := Localization.inverts L W α hα₀
  obtain ⟨c, hc₁, hc₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism
    T₁ T₃ hT₁ hT₃ a' (b' ≫ s₂'') fac₂.symm
  refine' ⟨L.map c ≫ inv (L.map α), _, _⟩
  . simp only [assoc, ← cancel_mono (L.map α), IsIso.inv_hom_id, comp_id, ← L.map_comp, hc₁, hα₁]
    simp only [Triangle.mk_obj₃, Triangle.mk_obj₂, Triangle.mk_mor₂, Functor.map_comp,
      reassoc_of% hb', IsIso.inv_hom_id_assoc]
  . simp only [ha', Functor.map_comp, assoc, ← L.commShiftIso_hom_naturality_assoc a' (1 : ℤ)]
    simp only [← Functor.map_comp_assoc, hc₂, Triangle.mk_mor₃, assoc,
      ← cancel_mono ((L.commShiftIso (1 : ℤ)).hom.app T₂.obj₁), Iso.inv_hom_id_app]
    simp only [comp_id, Functor.comp_obj, ← cancel_mono ((L.map s₁)⟦(1 : ℤ)⟧'), assoc,
      ← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id]
    simp only [← L.commShiftIso_hom_naturality s₁ (1 : ℤ), ← Functor.map_comp_assoc, hα₂]
    simp only [Functor.map_comp, assoc, Triangle.mk_mor₃, IsIso.inv_hom_id_assoc]

lemma pretriangulated : Pretriangulated D where
  distinguishedTriangles := L.essImageDistTriang
  isomorphic_distinguished _ hT₁ _ e := L.essImageDistTriang_mem_of_iso e hT₁
  contractible_distinguished :=
    have := Localization.essSurj L W ; L.contractible_mem_essImageDistTriang
  distinguished_cocone_triangle _ _ f := distinguished_cocone_triangle L W f
  rotate_distinguished_triangle := L.rotate_essImageDistTriang
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism L W

noncomputable example : HasShift W.Localization ℤ := inferInstance
noncomputable example : W.Q.HasCommShift ℤ := inferInstance

variable
  [HasFiniteProducts C]
  [W.IsStableUnderFiniteProducts]
  [Preadditive W.Localization]
  [HasZeroObject W.Localization]
  [∀ (n : ℤ), (shiftFunctor W.Localization n).Additive]
  [PreservesFiniteProducts W.Q]

lemma _root_.CategoryTheory.Functor.additive_of_preserves_binary_products
    {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
    [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [F.PreservesZeroMorphisms] : F.Additive := by
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproductsOfPreservesBinaryProducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

lemma _root_.CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal
    {C D : Type _} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) F] : F.PreservesZeroMorphisms := ⟨by
  have : F.map (𝟙 (⊤_ C)) = 0 := (IsTerminal.isTerminalObj _ _ terminalIsTerminal).hom_ext _ _
  intro X Y
  have eq : (0 : X ⟶ Y) = 0 ≫ 𝟙 (⊤_ C) ≫ 0 := by simp
  rw [eq, F.map_comp, F.map_comp, this, zero_comp, comp_zero]⟩

lemma _root_.CategoryTheory.Functor.additive_of_preserves_binary_products_of_preserves_terminal
    {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
    [HasBinaryProducts C] [HasTerminal C] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimit (Functor.empty.{0} C) F] : F.Additive := by
  have : Functor.PreservesZeroMorphisms F := F.preservesZeroMorphisms_of_preserves_terminal
  exact F.additive_of_preserves_binary_products

lemma _root_.CategoryTheory.Functor.additive_of_preserves_finite_products
    {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
    [HasFiniteProducts C] [PreservesFiniteProducts F] : F.Additive := by
  have : PreservesLimitsOfShape (Discrete WalkingPair) F := PreservesFiniteProducts.preserves _
  have : PreservesLimitsOfShape (Discrete PEmpty) F := PreservesFiniteProducts.preserves _
  exact F.additive_of_preserves_binary_products_of_preserves_terminal

example : HasFiniteProducts W.Localization := inferInstance

instance : W.Q.Additive := Functor.additive_of_preserves_finite_products _

noncomputable instance : Pretriangulated W.Localization := pretriangulated W.Q W

end Localization

end Triangulated

end CategoryTheory
