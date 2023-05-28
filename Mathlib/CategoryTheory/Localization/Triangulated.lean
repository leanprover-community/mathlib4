import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Localization.Preadditive
import Mathlib.CategoryTheory.Adjunction.Limits

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
  (L : C ⥤ D) [CommShift L ℤ]

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

namespace Localization

section

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.IsCompatibleWithShift ℤ] [W.IsCompatibleWithTriangulation]
    [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
    [HasShift D ℤ] [L.CommShift ℤ]

section

variable [Preadditive D] [HasZeroObject D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [L.Additive]

lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ L.essImageDistTriang := by
  let f' := MorphismProperty.HasLeftCalculusOfFractions.liftMap L W f
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle f'
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
  obtain ⟨Y₃, g, h, hT₃⟩ := Pretriangulated.distinguished_cocone_triangle (f₂ ≫ s₂' ≫ s₂'')
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

def pretriangulated : Pretriangulated D where
  distinguishedTriangles := L.essImageDistTriang
  isomorphic_distinguished _ hT₁ _ e := L.essImageDistTriang_mem_of_iso e hT₁
  contractible_distinguished :=
    have := Localization.essSurj L W ; L.contractible_mem_essImageDistTriang
  distinguished_cocone_triangle f := distinguished_cocone_triangle L W f
  rotate_distinguished_triangle := L.rotate_essImageDistTriang
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism L W

lemma isTriangulated_functor :
    letI : Pretriangulated D := pretriangulated L W ; L.IsTriangulated :=
    letI : Pretriangulated D := pretriangulated L W ; ⟨fun T hT => ⟨T, Iso.refl _, hT⟩⟩

lemma essSurj_mapArrow : EssSurj L.mapArrow :=
  MorphismProperty.HasLeftCalculusOfFractions.essSurj_mapArrow L W

lemma isTriangulated_of_exists_lifting_composable_morphisms [Pretriangulated D]
    [L.IsTriangulated] [IsTriangulated C]
    (hF : ∀ ⦃X₁ X₂ X₃ : D⦄ (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃),
      ∃ (Y₁ Y₂ Y₃ : C) (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃)
        (e₁ : L.obj Y₁ ≅ X₁) (e₂ : L.obj Y₂ ≅ X₂) (e₃ : L.obj Y₃ ≅ X₃),
        L.map f' ≫ e₂.hom = e₁.hom ≫ f ∧ L.map g' ≫ e₃.hom = e₂.hom ≫ g) :
    IsTriangulated D := by
  apply IsTriangulated.mk'
  intro X₁ X₂ X₃ f g
  obtain ⟨Y₁, Y₂, Y₃, f', g', e₁, e₂, e₃, comm₁, comm₂⟩ := hF f g
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := Pretriangulated.distinguished_cocone_triangle f'
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := Pretriangulated.distinguished_cocone_triangle g'
  obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := Pretriangulated.distinguished_cocone_triangle (f' ≫ g')
  let H := Triangulated.someOctahedron rfl h₁₂ h₂₃ h₁₃
  let T₁₃' := Triangle.mk (L.map f' ≫ L.map g') (L.map v₁₃) (L.map w₁₃ ≫ (L.commShiftIso (1 : ℤ)).hom.app Y₁)
  have h₁₃' : T₁₃' ∈ distTriang D := isomorphic_distinguished _ (L.map_distinguished _ h₁₃) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))
  refine' ⟨L.obj Y₁, L.obj Y₂, L.obj Y₃, L.obj Z₁₂, L.obj Z₂₃, L.obj Z₁₃, L.map f', L.map g',
    e₁.symm, e₂.symm, e₃.symm, _, _,
      _, _, L.map_distinguished _ h₁₂,
      _, _, L.map_distinguished _ h₂₃,
      _, _, h₁₃', ⟨_⟩⟩
  . dsimp
    simp only [← cancel_epi e₁.hom, ← reassoc_of% comm₁, Iso.hom_inv_id,
      Iso.hom_inv_id_assoc, comp_id]
  . dsimp
    simp only [← cancel_epi e₂.hom, ← reassoc_of% comm₂, Iso.hom_inv_id,
      Iso.hom_inv_id_assoc, comp_id]
  . exact
    { m₁ := L.map H.m₁
      m₃ := L.map H.m₃
      comm₁ := by simpa using L.congr_map H.comm₁
      comm₂ := by simpa using L.congr_map H.comm₂ =≫ (L.commShiftIso 1).hom.app Y₁
      comm₃ := by simpa using L.congr_map H.comm₃
      comm₄ := by simpa using L.congr_map H.comm₄ =≫ (L.commShiftIso 1).hom.app Y₂
      mem := isomorphic_distinguished _ (L.map_distinguished _ H.mem) _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp) (by simp)) }

lemma isTriangulated [Pretriangulated D] [L.IsTriangulated] [IsTriangulated C] :
    IsTriangulated D := by
  have := Localization.essSurj L W
  apply isTriangulated_of_exists_lifting_composable_morphisms L
  intros X₁ X₂ X₃ f g
  let Y₂ := L.objPreimage X₂
  obtain ⟨Y₁, f', s, hs, hf'⟩ :=
    MorphismProperty.HasRightCalculusOfFractions.fac L W
      ((L.objObjPreimageIso X₁).hom ≫ f ≫ (L.objObjPreimageIso X₂).inv)
  obtain ⟨Y₃, g', s', hs', hg'⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.fac L W
      ((L.objObjPreimageIso X₂).hom ≫ g ≫ (L.objObjPreimageIso X₃).inv)
  refine' ⟨Y₁, Y₂, Y₃, f', g',
    (Localization.isoOfHom L W s hs) ≪≫ L.objObjPreimageIso X₁, L.objObjPreimageIso X₂,
    (Localization.isoOfHom L W s' hs').symm ≪≫ L.objObjPreimageIso X₃, _, _⟩
  . simp only [← cancel_epi (Localization.isoOfHom L W s hs).inv, Iso.trans_hom, assoc,
      Iso.inv_hom_id_assoc, ← reassoc_of% hf', Iso.inv_hom_id, comp_id]
  . simp only [← cancel_mono (Localization.isoOfHom L W s' hs').inv, Iso.trans_hom, Iso.symm_hom,
      ← reassoc_of% hg', Iso.inv_hom_id, comp_id]

end

/-
instance [is_triangulated C] : is_triangulated (localization L W) :=
is_triangulated.mk'
(λ X₁' X₂' X₃' u₁₂' u₂₃', begin
  haveI := localization.ess_surj L W,
  let Y₁' := L.obj_preimage X₁',
  let X₂ := L.obj_preimage X₂',
  let Y₃' := L.obj_preimage X₃',
  let e₁ : L.obj Y₁' ≅ X₁' := functor.obj_obj_preimage_iso L X₁',
  let e₂ : L.obj X₂ ≅ X₂' := functor.obj_obj_preimage_iso L X₂',
  let e₃ : L.obj Y₃' ≅ X₃' := functor.obj_obj_preimage_iso L X₃',
  let y₁₂' : L.obj Y₁' ⟶ L.obj X₂ := e₁.hom ≫ u₁₂' ≫ e₂.inv,
  let y₂₃' : L.obj X₂ ⟶ L.obj Y₃' := e₂.hom ≫ u₂₃' ≫ e₃.inv,
  obtain ⟨⟨X₁, s₁, u₁₂, hs₁⟩, hz₁⟩ := right_calculus_of_fractions.L_map_fac L W y₁₂',
  obtain ⟨⟨X₃, u₂₃, s₂, hs₂⟩, hz₂⟩ := left_calculus_of_fractions.L_map_fac L W y₂₃',
  haveI := localization.inverts L W _ hs₁,
  haveI := localization.inverts L W _ hs₂,
  dsimp [right_calculus_of_fractions.map_roof] at hz₁,
  dsimp [left_calculus_of_fractions.map_roof] at hz₂,
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := pretriangulated.distinguished_cocone_triangle _ _ u₁₂,
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := pretriangulated.distinguished_cocone_triangle _ _ u₂₃,
  obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := pretriangulated.distinguished_cocone_triangle _ _ (u₁₂ ≫ u₂₃),
  let H := (is_triangulated.octahedron_axiom rfl h₁₂ h₂₃ h₁₃).some,
  refine ⟨L.obj X₁, L.obj X₂, L.obj X₃, L.obj Z₁₂, L.obj Z₂₃, L.obj Z₁₃,
    L.map u₁₂, L.map u₂₃, e₁.symm ≪≫ (as_iso (L.map s₁)).symm, e₂.symm,
    e₃.symm ≪≫ (as_iso (L.map s₂)), _, _, _, _, ⟨_, by refl, h₁₂⟩,
    _, _, ⟨_, by refl, h₂₃⟩,
    L.map v₁₃, L.map w₁₃ ≫ (L.comm_shift_iso 1).hom.app X₁,
      ⟨_, _, h₁₃⟩, _⟩,
  { dsimp,
    rw [assoc, ← hz₁, e₁.inv_hom_id_assoc], },
  { dsimp,
    rw [← cancel_mono (inv (L.map s₂)), assoc, assoc, assoc, is_iso.hom_inv_id, comp_id, ← hz₂,
      e₂.inv_hom_id_assoc], },
  { refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
    { dsimp, simp only [comp_id, functor.map_comp, id_comp], },
    { dsimp, simp only [comp_id, id_comp], },
    { dsimp, simp only [functor.map_id, comp_id, id_comp], }, },
  have comm₁₂ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₁.comm₂,
  have comm₁₃ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₁.comm₃,
  have comm₂₂ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₂.comm₂,
  have comm₂₃ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₂.comm₃,
  dsimp at comm₁₂ comm₁₃ comm₂₂ comm₂₃,
  simp only [L.map_comp, functor.map_id, id_comp, comp_id] at comm₁₂ comm₁₃ comm₂₂ comm₂₃,
  refine ⟨⟨L.map H.m₁, L.map H.m₃, comm₁₂, _, comm₂₂, _, _⟩⟩,
  { dsimp,
    rw reassoc_of comm₁₃, },
  { dsimp,
    rw [← reassoc_of comm₂₃, assoc],
    erw ← nat_trans.naturality,
    refl, },
  refine ⟨_, _, H.mem⟩,
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
  { dsimp, simp only [comp_id, id_comp], },
  { dsimp, simp only [comp_id, id_comp], },
  { dsimp, simp only [assoc, functor.map_id, comp_id, functor.map_comp, id_comp],
    erw ← nat_trans.naturality, refl, },
end)-/

noncomputable example : HasShift W.Localization ℤ := inferInstance
noncomputable example : W.Q.CommShift ℤ := inferInstance

variable
  [HasFiniteProducts C]
  [W.IsStableUnderFiniteProducts]
  [W.HasLocalization]

example : HasTerminal W.Localization := inferInstance
example : HasFiniteProducts W.Localization := inferInstance
noncomputable example : PreservesFiniteProducts W.Q := inferInstance

instance : HasZeroObject W.Localization :=
  Limits.hasZeroObject_of_additive_functor W.Q

instance : HasZeroObject W.Localization' :=
  Limits.hasZeroObject_of_additive_functor W.Q'

noncomputable instance (n : ℤ) :
    PreservesFiniteProducts (shiftFunctor (MorphismProperty.Localization W) n) := by
  constructor
  intros
  infer_instance

noncomputable instance (n : ℤ) :
    PreservesFiniteProducts (shiftFunctor (MorphismProperty.Localization' W) n) := by
  constructor
  intros
  infer_instance

instance (n : ℤ) : (shiftFunctor W.Localization n).Additive :=
  Functor.additive_of_preserves_finite_products _

instance (n : ℤ) : (shiftFunctor W.Localization' n).Additive :=
  Functor.additive_of_preserves_finite_products _

noncomputable instance : Pretriangulated W.Localization := pretriangulated W.Q W
noncomputable instance : Pretriangulated W.Localization' := pretriangulated W.Q' W
noncomputable instance : W.Q.IsTriangulated := isTriangulated_functor W.Q W
noncomputable instance : W.Q'.IsTriangulated := isTriangulated_functor W.Q' W

instance : EssSurj W.Q.mapArrow := essSurj_mapArrow W.Q W
instance : EssSurj W.Q'.mapArrow := essSurj_mapArrow W.Q' W

noncomputable instance [IsTriangulated C] : IsTriangulated W.Localization := isTriangulated W.Q W
noncomputable instance [IsTriangulated C] : IsTriangulated W.Localization' := isTriangulated W.Q' W

end

section

variable {C D : Type _} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [EssSurj L.mapArrow]
  [L.CommShift ℤ] [L.IsTriangulated]

lemma distTriang_iff (T : Triangle D) :
    (T ∈ distTriang D) ↔ T ∈ L.essImageDistTriang := by
  constructor
  . intro hT
    let f := L.mapArrow.objPreimage T.mor₁
    obtain ⟨Z, g : f.right ⟶ Z, h : Z ⟶ f.left⟦(1 : ℤ)⟧, mem⟩ :=
      Pretriangulated.distinguished_cocone_triangle f.hom
    exact ⟨_, (exists_iso_of_arrow_iso T _ hT (L.map_distinguished _ mem)
      (L.mapArrow.objObjPreimageIso T.mor₁).symm).choose, mem⟩
  . rintro ⟨T₀, e, hT₀⟩
    exact isomorphic_distinguished _ (L.map_distinguished _ hT₀) _ e

end

end Localization

end Triangulated

end CategoryTheory
