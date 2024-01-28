import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.RespectsIso

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

namespace Limits

variable {C J₁ J₂ : Type _} [Category C]
  (X : J₂ → C) (e : J₁ ≃ J₂) [HasProduct X]

noncomputable def fanOfEquiv : Fan (X ∘ e) := Fan.mk (∏ X) (fun _ => Pi.π _ _)

@[simp]
lemma fanOfEquiv_proj (j : J₁) : (fanOfEquiv X e).proj j = Pi.π _ (e j) := rfl

@[reassoc]
lemma Fan.congr_proj {J : Type _} {F : J → C} (s : Fan F)
    {j₁ j₂ : J} (h : j₁ = j₂) : s.proj j₁ ≫ eqToHom (by rw [h]) = s.proj j₂ := by
  subst h
  simp

@[reassoc]
lemma Pi.congr_π {J : Type _} (F : J → C) [HasProduct F] {j₁ j₂ : J} (h : j₁ = j₂) :
    Pi.π F j₁ ≫ eqToHom (by rw [h]) = Pi.π F j₂ := by
  subst h
  simp

noncomputable def isLimitFanOfEquiv : IsLimit (fanOfEquiv X e) :=
  mkFanLimit _ (fun s => Pi.lift (fun j₂ => s.proj (e.symm j₂) ≫ eqToHom (by simp) ))
    (fun s j => by simp [Fan.congr_proj _ (e.symm_apply_apply j)])
    (fun s m hm => Pi.hom_ext _ _ (fun j => by
      dsimp
      simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app, ← hm,
        Function.comp_apply, fanOfEquiv_proj, assoc]
      rw [Pi.congr_π]
      simp))

lemma hasProductOfEquiv : HasProduct (X ∘ e) :=
  ⟨⟨_, isLimitFanOfEquiv X e⟩⟩

noncomputable def productIsoOfEquiv [HasProduct (X ∘ e)] :  ∏ (X ∘ e) ≅ ∏ X :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimitFanOfEquiv X e)

noncomputable def productOptionIso {C J : Type _} [Category C]
    (X : Option J → C) [HasProduct X] [HasProduct (fun j => X (some j))]
    [HasBinaryProduct (∏ (fun j => X (some j))) (X none)] :
    (∏ X) ≅ (∏ (fun j => X (some j))) ⨯ (X none) where
  hom := prod.lift (Pi.lift (fun j => Pi.π _ (some j))) (Pi.π _ none)
  inv := Pi.lift (fun b => match b with
    | some j => prod.fst ≫ Pi.π _ j
    | none => prod.snd)

end Limits

namespace Arrow

-- should be moved to Arrow.lean

variable {C D : Type _} [Category C] [Category D]

@[simps]
def mapArrowNatTransOfNatTrans {F G : C ⥤ D} (τ : F ⟶ G) : F.mapArrow ⟶ G.mapArrow where
  app f :=
    { left := τ.app _
      right := τ.app _}

@[simps]
def mapArrowNatIsoOfNatIso {F G : C ⥤ D} (e : F ≅ G) : F.mapArrow ≅ G.mapArrow where
  hom := mapArrowNatTransOfNatTrans e.hom
  inv := mapArrowNatTransOfNatTrans e.inv

end Arrow

namespace Triangulated

open Pretriangulated

variable (C : Type _) [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

structure Subcategory where
  set : Set C
  zero' : ∃ (Z : C) (_ : IsZero Z), Z ∈ set
  shift : ∀ (X : C) (n : ℤ) (_ : X ∈ set), X⟦n⟧ ∈ set
  ext₂' : ∀ (T : Triangle C) (_ : T ∈ distTriang C), T.obj₁ ∈ set → T.obj₃ ∈ set → T.obj₂ ∈ set.isoClosure

namespace Subcategory

variable {C}

def isoClosure (S : Subcategory C) : Subcategory C where
  set := S.set.isoClosure
  zero' := by
    obtain ⟨Z, hZ, hZ'⟩ := S.zero'
    exact ⟨Z, hZ, Z, hZ', ⟨Iso.refl _⟩⟩
  shift X n := by
    rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦n⟧, S.shift Y n hY, ⟨(shiftFunctor C n).mapIso e⟩⟩
  ext₂' := by
    intro T hT
    rintro ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    let T' := Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧')
    have hT' : T' ∈ distTriang C := isomorphic_distinguished _ hT _ (by
      refine' Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by aesop_cat) (by aesop_cat) _
      dsimp
      simp only [assoc, ← Functor.map_comp, e₁.hom_inv_id, Functor.map_id, comp_id])
    exact Set.subset_isoClosure _ (S.ext₂' T' hT' h₁ h₃)

instance (S : Subcategory C) : S.isoClosure.set.RespectsIso := by
  dsimp only [isoClosure]
  infer_instance

section

variable (set : Set C) (zero : 0 ∈ set)
  (shift : ∀ (X : C) (n : ℤ) (_ : X ∈ set), X⟦n⟧ ∈ set)
  (ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C), T.obj₁ ∈ set → T.obj₃ ∈ set → T.obj₂ ∈ set)

def mk' : Subcategory C where
  set := set
  zero' := ⟨0, isZero_zero _, zero⟩
  shift := shift
  ext₂' T hT h₁ h₃ := set.subset_isoClosure (ext₂ T hT h₁ h₃)

instance : (mk' set zero shift ext₂).set.RespectsIso := ⟨fun X Y e hX => by
  refine' ext₂ (Triangle.mk e.hom (0 : Y ⟶ 0) 0) _ hX zero
  refine' isomorphic_distinguished _ (contractible_distinguished X) _ _
  exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
    (by aesop_cat) (by aesop_cat) (by aesop_cat)⟩

end

variable (S : Subcategory C)

variable {S}

lemma ext₂ [S.set.RespectsIso] (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : T.obj₁ ∈ S.set)
    (h₃ : T.obj₃ ∈ S.set) : T.obj₂ ∈ S.set := by
  simpa only [S.set.isoClosure_eq_self] using S.ext₂' T hT h₁ h₃

variable (S)

noncomputable def zeroObject : C := S.zero'.choose

lemma isZero_zeroObject : IsZero S.zeroObject := S.zero'.choose_spec.choose

lemma zeroObject_mem : S.zeroObject ∈ S.set := S.zero'.choose_spec.choose_spec

lemma zero'' [S.set.RespectsIso] (X : C) (hX : IsZero X) : X ∈ S.set :=
  S.set.mem_of_iso (S.isZero_zeroObject.isoZero.trans hX.isoZero.symm) S.zeroObject_mem

lemma zero [S.set.RespectsIso] : 0 ∈ S.set := S.zero'' _ (isZero_zero _)

def W : MorphismProperty C := fun X Y f => ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), Z ∈ S.set

def W' : MorphismProperty C := fun Y Z g => ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), X ∈ S.set

variable {S}

lemma W.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₃ ∈ S.set) : S.W T.mor₁ :=
  ⟨T.obj₃, T.mor₂, T.mor₃, hT, h⟩

lemma W'.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₁ ∈ S.set) : S.W' T.mor₂ :=
  ⟨T.obj₁, T.mor₁, T.mor₃, hT, h⟩

noncomputable def W.triangle {X Y : C} (f : X ⟶ Y) (hf : S.W f) : Triangle C :=
  Triangle.mk f hf.choose_spec.choose hf.choose_spec.choose_spec.choose

lemma W.triangle_distinguished {X Y : C} (f : X ⟶ Y) (hf : S.W f) :
   (W.triangle f hf) ∈ distTriang C :=
  hf.choose_spec.choose_spec.choose_spec.choose

lemma W.triangle_obj₃_mem {X Y : C} (f : X ⟶ Y) (hf : S.W f) :
  (W.triangle f hf).obj₃ ∈ S.set :=
  hf.choose_spec.choose_spec.choose_spec.choose_spec

variable (S)

lemma mem_W_iff_of_distinguished [S.set.RespectsIso] (T : Triangle C) (hT : T ∈ distTriang C) :
    S.W T.mor₁ ↔ T.obj₃ ∈ S.set := by
  constructor
  · intro hf
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso _ _ (W.triangle_distinguished _ hf) hT (Iso.refl _)
    exact S.set.mem_of_iso (Triangle.π₃.mapIso e) (W.triangle_obj₃_mem _ hf)
  · intro h
    exact ⟨_, _, _, hT, h⟩

lemma W_eq_W' : S.W = S.W' := by
  apply MorphismProperty.ext
  intro X Y f
  constructor
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, inv_rot_of_distTriang _ H, S.shift _ (-1) mem⟩
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, rot_of_distTriang _ H, S.shift _ 1 mem⟩

variable {S}

lemma W.mk' {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₁ ∈ S.set) : S.W T.mor₂ := by
  simpa only [W_eq_W'] using W'.mk hT h

variable (S)

lemma isoClosure_W : S.isoClosure.W = S.W := by
  ext X Y f
  constructor
  · rintro ⟨Z, g, h, mem, ⟨Z', hZ', ⟨e⟩⟩⟩
    refine' ⟨Z', g ≫ e.hom, e.inv ≫ h, isomorphic_distinguished _ mem _ _, hZ'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  · rintro ⟨Z, g, h, mem, hZ⟩
    exact ⟨Z, g, h, mem, Set.subset_isoClosure _ hZ⟩

instance instContainsIdentitiesW : S.W.ContainsIdentities := by
  rw [← isoClosure_W]
  exact ⟨fun X => ⟨_, _, _, contractible_distinguished X, S.isoClosure.zero⟩⟩

lemma stableUnderCompositionW [IsTriangulated C] : (W S).StableUnderComposition := by
  rw [← isoClosure_W]
  rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
  obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
  refine' ⟨_, _, _, H₁₃, S.isoClosure.ext₂ _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

instance multiplicativeW [IsTriangulated C] : S.W.IsMultiplicative where
  stableUnderComposition := S.stableUnderCompositionW

lemma respectsIsoW : S.W.RespectsIso where
  left := by
    rintro X' X Y e f ⟨Z, g, h, mem, mem'⟩
    refine' ⟨Z, g, h ≫ e.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ mem _ _, mem'⟩
    refine' Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (by aesop_cat) (by aesop_cat) _
    dsimp
    simp only [assoc, ← Functor.map_comp, e.inv_hom_id, Functor.map_id, comp_id, id_comp]
  right := by
    rintro X Y Y' e f ⟨Z, g, h, mem, mem'⟩
    refine' ⟨Z, e.inv ≫ g, h, isomorphic_distinguished _ mem _ _, mem'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)


instance [IsTriangulated C] : S.W.HasLeftCalculusOfFractions where
  exists_leftFraction := by
    rintro X Y φ
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨Y', s', f', mem'⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ H mem' φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, mem', mem⟩, hb₁.symm⟩
  ext := by
    rintro X' X Y f₁ f₂ s ⟨Z, g, h, H, mem⟩ hf₁
    have hf₂ : s ≫ (f₁ - f₂) = 0 := by rw [comp_sub, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle q
    refine' ⟨Y', r, _, _⟩
    · exact ⟨_, _, _, rot_of_distTriang _ mem', S.shift _ _ mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero, ← sub_comp, hq, assoc, eq, comp_zero]

instance [IsTriangulated C] : S.W.HasRightCalculusOfFractions where
  exists_rightFraction := by
    rintro X Y φ
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _
      mem' H φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext := by
    rintro Y Z Z' f₁ f₂ s hs hf₁
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [sub_comp, hf₁, sub_self]
    rw [W_eq_W'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine' ⟨Y', r, _, _⟩
    · exact ⟨_, _, _, mem', mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero, ← comp_sub, hq, reassoc_of% eq, zero_comp]

lemma W_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : S.W f := by
  rw [← isoClosure_W]
  refine' ⟨0, 0, 0, isomorphic_distinguished _ (contractible_distinguished Y) _ _, S.isoClosure.zero⟩
  exact Triangle.isoMk _ _ (asIso f) (Iso.refl _) (Iso.refl _)
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

lemma mul_mem_W_iff {X Y : C} (f : X ⟶ Y) (n : ℤˣ) :
    S.W (n • f) ↔ S.W f :=
  S.respectsIsoW.arrow_mk_iso_iff
    (Arrow.isoMk (n • (Iso.refl _)) (Iso.refl _))

instance WIsCompatibleWithShift : S.W.IsCompatibleWithShift ℤ := ⟨by
  have : ∀ {X Y : C} (f : X ⟶ Y) (hf : S.W f) (n : ℤ), S.W (f⟦n⟧') := by
    rintro X Y f ⟨Z, g, h, H, mem⟩ n
    rw [← mul_mem_W_iff S _ n.negOnePow]
    exact ⟨_, _, _, Triangle.shift_distinguished _ H n, S.shift _ n mem⟩
  intro n
  apply MorphismProperty.ext
  intro X Y f
  constructor
  · intro hf
    have H := S.respectsIsoW.arrow_mk_iso_iff
     ((Arrow.mapArrowNatIsoOfNatIso (shiftEquiv C n).unitIso).app (Arrow.mk f))
    dsimp at H
    rw [H]
    exact this _ hf (-n)
  · intro hf
    exact this _ hf n⟩

variable {S}

lemma W.shift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : S.W f) (n : ℤ) : S.W (f⟦n⟧') := by
  simpa only [MorphismProperty.IsCompatibleWithShift.iff S.W f n] using hf

lemma W.unshift {X₁ X₂ : C} {f : X₁ ⟶ X₂} {n : ℤ} (hf : S.W (f⟦n⟧')) : S.W f := by
  simpa only [← MorphismProperty.IsCompatibleWithShift.iff S.W f n] using hf

variable (S)

lemma binary_product_stable [S.set.RespectsIso] (X₁ X₂ : C) (hX₁ : X₁ ∈ S.set) (hX₂ : X₂ ∈ S.set) :
    (X₁ ⨯ X₂) ∈ S.set :=
  S.ext₂ _ (binaryProductTriangle_distinguished X₁ X₂) hX₁ hX₂

lemma pi_finite_stable [S.set.RespectsIso] {J : Type} [Finite J] (X : J → C) (hX : ∀ j, X j ∈ S.set) :
    (∏ X) ∈ S.set := by
  revert hX X
  let P : Type → Prop := fun J =>
    ∀ [hJ : Finite J] (X : J → C) (_ : ∀ j, X j ∈ S.set), (∏ X) ∈ S.set
  change P J
  apply @Finite.induction_empty_option
  · intro J₁ J₂ e hJ₁ _ X hX
    have : Finite J₁ := Finite.of_equiv _ e.symm
    exact Set.mem_of_iso _ (productIsoOfEquiv X e) (hJ₁ (fun j₁ => X (e j₁)) (fun j₁ => hX _))
  · intro _ X _
    refine' Set.mem_of_iso _ (IsZero.isoZero _).symm S.zero
    rw [IsZero.iff_id_eq_zero]
    ext ⟨⟩
  · intro J _ hJ _ X hX
    exact Set.mem_of_iso _ (productOptionIso  X).symm
      (S.binary_product_stable _ _ (hJ (fun j => X (some j)) (fun j => hX _)) (hX none))

instance : S.W.IsStableUnderFiniteProducts := by
  rw [← isoClosure_W]
  exact ⟨fun J _ => by
    refine' MorphismProperty.IsStableUnderProductsOfShape.mk _ _ (S.isoClosure.respectsIsoW) _
    intro X₁ X₂ f hf
    exact W.mk (productTriangle_distinguished _ (fun j => W.triangle_distinguished _ (hf j)))
      (pi_finite_stable _ _ (fun j => W.triangle_obj₃_mem _ _))⟩

instance [IsTriangulated C] : S.W.IsCompatibleWithTriangulation := ⟨by
  rintro T₁ T₃ mem₁ mem₃ a b ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩ ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩ comm
  obtain ⟨Z₂, g₂, h₂, mem₂⟩ := distinguished_cocone_triangle (T₁.mor₁ ≫ b)
  have H := someOctahedron rfl mem₁ mem₄ mem₂
  have H' := someOctahedron comm.symm mem₅ mem₃ mem₂
  let φ : T₁ ⟶ T₃ := H.triangleMorphism₁ ≫ H'.triangleMorphism₂
  exact ⟨φ.hom₃,
    S.W.comp_mem _ _ (W.mk H.mem mem₄') (W.mk' H'.mem mem₅'),
    ⟨by simpa using φ.comm₂, by simpa using φ.comm₃⟩⟩⟩

lemma ext₁ [S.set.RespectsIso] (T : Triangle C) (hT : T ∈ distTriang C) (h₂ : T.obj₂ ∈ S.set)
    (h₃ : T.obj₃ ∈ S.set) : T.obj₁ ∈ S.set :=
  S.ext₂ _ (inv_rot_of_distTriang _ hT) (S.shift _ _ h₃) h₂

lemma ext₃ [S.set.RespectsIso] (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : T.obj₁ ∈ S.set)
    (h₂ : T.obj₂ ∈ S.set) : T.obj₃ ∈ S.set :=
  S.ext₂ _ (rot_of_distTriang _ hT) h₂ (S.shift _ _ h₁)

lemma ext₁' (T : Triangle C) (hT : T ∈ distTriang C) (h₂ : T.obj₂ ∈ S.set)
    (h₃ : T.obj₃ ∈ S.set) : T.obj₁ ∈ S.set.isoClosure :=
  S.ext₂' _ (inv_rot_of_distTriang _ hT) (S.shift _ _ h₃) h₂

lemma ext₃' (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : T.obj₁ ∈ S.set)
    (h₂ : T.obj₂ ∈ S.set) : T.obj₃ ∈ S.set.isoClosure :=
  S.ext₂' _ (rot_of_distTriang _ hT) h₂ (S.shift _ _ h₁)

noncomputable example [IsTriangulated C] : Pretriangulated (S.W.Localization) := inferInstance

def category := FullSubcategory S.set

instance : Category S.category := FullSubcategory.category _

def ι : S.category ⥤ C := fullSubcategoryInclusion _

instance : Full S.ι := FullSubcategory.full _
instance : Faithful S.ι := FullSubcategory.faithful _

instance : Preadditive S.category := by
  dsimp [category]
  infer_instance

instance : S.ι.Additive := by
  dsimp [ι, category]
  infer_instance

noncomputable instance hasShift : HasShift S.category ℤ :=
  hasShiftOfFullyFaithful S.ι (fun n => FullSubcategory.lift _ (S.ι ⋙ shiftFunctor C n)
    (fun X => S.shift _ _ X.2)) (fun _ => FullSubcategory.lift_comp_inclusion _ _ _)

instance commShiftι : S.ι.CommShift ℤ :=
  Functor.CommShift.of_hasShiftOfFullyFaithful _ _ _

-- these definitions are made irreducible to prevent (at least temporarily) any abuse of defeq
attribute [irreducible] hasShift commShiftι

instance (n : ℤ) : (shiftFunctor S.category n).Additive := by
  have := Functor.additive_of_iso (S.ι.commShiftIso n).symm
  apply Functor.additive_of_comp_faithful _ S.ι

instance : HasZeroObject S.category where
  zero := by
    refine' ⟨⟨S.zeroObject, S.zeroObject_mem⟩, _⟩
    rw [IsZero.iff_id_eq_zero]
    apply S.ι.map_injective
    change 𝟙 (S.zeroObject) = 0
    apply S.isZero_zeroObject.eq_of_tgt

instance : Pretriangulated S.category where
  distinguishedTriangles := fun T => S.ι.mapTriangle.obj T ∈ distTriang C
  isomorphic_distinguished := fun T₁ hT₁ T₂ e =>
    isomorphic_distinguished _ hT₁ _ (S.ι.mapTriangle.mapIso e)
  contractible_distinguished X := by
    refine' isomorphic_distinguished _ (contractible_distinguished (S.ι.obj X)) _ _
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) S.ι.mapZeroObject
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z', g', h', mem⟩ := distinguished_cocone_triangle (S.ι.map f)
    obtain ⟨Z'', hZ'', ⟨e⟩⟩ := S.ext₃' _ mem X.2 Y.2
    let Z : S.category := ⟨Z'', hZ''⟩
    refine' ⟨Z, S.ι.preimage (g' ≫ e.hom),
      S.ι.preimage (e.inv ≫ h' ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app X),
      isomorphic_distinguished _ mem _ _⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (S.ι.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (S.ι.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism (S.ι.mapTriangle.obj T₁)
      (S.ι.mapTriangle.obj T₂) hT₁ hT₂ (S.ι.map a) (S.ι.map b)
      (by simpa using S.ι.congr_map comm)
    have ⟨c', hc'⟩ : ∃ (c' : T₁.obj₃ ⟶ T₂.obj₃), c = S.ι.map c' := ⟨S.ι.preimage c, by simp⟩
    dsimp at hc₁ hc₂
    rw [hc'] at hc₁
    rw [hc', assoc, ← Functor.commShiftIso_hom_naturality] at hc₂
    refine' ⟨c', ⟨S.ι.map_injective _, S.ι.map_injective _⟩⟩
    · simpa using hc₁
    · rw [← cancel_mono ((Functor.commShiftIso (ι S) (1 : ℤ)).hom.app T₂.obj₁),
        S.ι.map_comp, S.ι.map_comp, assoc, assoc, hc₂]

instance : S.ι.IsTriangulated := ⟨fun _ hT => hT⟩

instance [IsTriangulated C] : IsTriangulated S.category :=
  IsTriangulated.of_fully_faithful_triangulated_functor S.ι

/-inductive setSpan (S : Set C) : C → Prop
  | subset (X : C) (hX : X ∈ S) : setSpan S X
  | zero : setSpan S 0
  | shift (X : C) (n : ℤ) (hX : setSpan S X) : setSpan S (X⟦n⟧)
  | ext₂ (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : setSpan S T.obj₁) (h₃ : setSpan S T.obj₃) :
      setSpan S T.obj₂

def span (S : Set C) : Subcategory C where
  set := setSpan S
  zero := setSpan.zero
  shift X n hX := setSpan.shift X n hX
  ext₂ T hT h₁ h₃ := setSpan.ext₂ T hT h₁ h₃

lemma subset_span_set (S : Set C) : S ⊆ (span S).set :=
  setSpan.subset

instance : PartialOrder (Subcategory C) where
  le S₁ S₂ := S₁.set ⊆ S₂.set
  le_refl S := (by rfl : S.set ⊆ S.set)
  le_trans := by
    intro S₁ S₂ S₃ (h₁₂ : S₁.set ⊆ S₂.set) (h₂₃ : S₂.set ⊆ S₃.set)
    exact h₁₂.trans h₂₃
  le_antisymm := by
    rintro S₁ S₂ (h₁₂ : S₁.set ⊆ S₂.set) (h₂₁ : S₂.set ⊆ S₁.set)
    have := le_antisymm h₁₂ h₂₁
    cases S₁
    cases S₂
    congr

lemma span_LE (S : Set C) (A : Subcategory C) (hA : S ⊆ A.set ) :
    span S ≤ A := by
  intro X (hX : setSpan S X)
  induction' hX with Y hY Y n _ hY T hT _ _ h₁ h₃
  · exact hA hY
  · exact A.zero
  · exact A.shift Y n hY
  · exact A.ext₂ T hT h₁ h₃

def iInf {ι : Type _} (S : ι → Subcategory C) : Subcategory C where
  set := Set.iInter (fun i => (S i).set)
  zero := by
    rw [Set.mem_iInter]
    intro i
    exact (S i).zero
  shift X n hX := by
    simp only [Set.mem_iInter] at hX ⊢
    intro i
    exact (S i).shift X n (hX i)
  ext₂ T hT h₁ h₃ := by
    simp only [Set.mem_iInter] at h₁ h₃ ⊢
    intro i
    exact (S i).ext₂ T hT (h₁ i) (h₃ i)

lemma mem_iInf_set_iff {ι : Type _} (S : ι → Subcategory C) (X : C) :
    X ∈ (iInf S).set ↔ ∀ (i : ι), X ∈ (S i).set := by
  dsimp [iInf]
  rw [Set.mem_iInter]

def sInf (S : Set (Subcategory C)) : Subcategory C :=
  iInf (Subtype.val : S → _)

lemma mem_sInf_set_iff (S : Set (Subcategory C)) (X : C) :
    X ∈ (sInf S).set ↔ ∀ (A : Subcategory C) (_ : A ∈ S), X ∈ A.set := by
  dsimp [sInf]
  rw [mem_iInf_set_iff]
  constructor
  · intro hX A hA
    exact hX ⟨_, hA⟩
  · intro hX A
    exact hX A.1 A.2

instance : InfSet (Subcategory C) where
  sInf := sInf

instance : CompleteSemilatticeInf (Subcategory C) where
  sInf_le := by
    intro S A hA X hX
    erw [mem_sInf_set_iff] at hX
    exact hX _ hA
  le_sInf := by
    intro B A hA X hX
    erw [mem_sInf_set_iff]
    intro A' hA'
    exact hA _ hA' hX

instance : SupSet (Subcategory C) where
  sSup S := span (sSup (Subcategory.set '' S))

instance : CompleteSemilatticeSup (Subcategory C) where
  le_sSup := by
    intro S A hA X hX
    refine' subset_span_set _ _
    simp only [Set.sSup_eq_sUnion, Set.sUnion_image,
      Set.mem_iUnion, exists_prop]
    exact ⟨A, hA, hX⟩
  sSup_le := by
    intro S A hA
    apply span_LE
    rintro X ⟨_, ⟨B, hB, rfl⟩, hX⟩
    exact hA B hB hX

instance : Lattice (Subcategory C) where
  sup S₁ S₂ := sSup {S₁, S₂}
  le_sup_left S₁ S₂ := le_sSup (Set.mem_insert _ _ )
  le_sup_right S₁ S₂ := le_sSup (Set.mem_insert_of_mem _ rfl)
  sup_le := by
    rintro S₁ S₂ S₃ (h₁₃ : S₁.set ⊆ S₃.set) (h₂₃ : S₂.set ⊆ S₃.set)
    apply span_LE
    rintro X ⟨_, ⟨B, hB, rfl⟩, hX⟩
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hB
    obtain (rfl|rfl) := hB
    · exact h₁₃ hX
    · exact h₂₃ hX
  inf S₁ S₂ :=
    { set := S₁.set ∩ S₂.set
      zero := ⟨S₁.zero, S₂.zero⟩
      shift := fun X n hX => ⟨S₁.shift X n hX.1, S₂.shift X n hX.2⟩
      ext₂ := fun T hT h₁ h₃ => ⟨S₁.ext₂ T hT h₁.1 h₃.1,
        S₂.ext₂ T hT h₁.2 h₃.2⟩ }
  inf_le_left := fun S₁ S₂ X hX => hX.1
  inf_le_right := fun S₁ S₂ X hX => hX.2
  le_inf := fun S₁ S₂ S₃ h₁₂ h₂₃ X hX => ⟨h₁₂ hX, h₂₃ hX⟩

variable (C)

def top : Subcategory C where
  set := ⊤
  zero := by tauto
  shift := by tauto
  ext₂ := by tauto


variable {C}

instance : CompleteLattice (Subcategory C) where
  le_sSup := CompleteSemilatticeSup.le_sSup
  sSup_le := CompleteSemilatticeSup.sSup_le
  le_sInf := CompleteSemilatticeInf.le_sInf
  sInf_le := CompleteSemilatticeInf.sInf_le
  top :=
    { set := ⊤
      zero := by tauto
      shift := by tauto
      ext₂ := by tauto }
  bot :=
    { set := IsZero
      zero := isZero_zero _
      shift := fun X n (hX : IsZero X) => by
        change IsZero _
        simp only [IsZero.iff_id_eq_zero] at hX ⊢
        rw [← (shiftFunctor C n).map_id, hX, Functor.map_zero]
      ext₂ := fun T hT h₁ h₃ => T.isZero₂_of_isZero₁₃ hT h₁ h₃ }
  le_top _ _ _ := Set.mem_univ _
  bot_le := fun A X (hX : IsZero X) => A.zero' _ hX-/

section

variable {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [Full F]

-- note: does not require `[Faithful F]` !

def essImage : Subcategory D :=
  Subcategory.mk' F.essImage ⟨0, ⟨F.mapZeroObject⟩⟩
    (fun X n ⟨Y, ⟨e⟩⟩ => ⟨(shiftFunctor C n).obj Y,
      ⟨(F.commShiftIso n).app Y ≪≫ (shiftFunctor D n).mapIso e⟩⟩)
    (fun T hT ⟨X₁, ⟨e₁⟩⟩ ⟨X₃, ⟨e₃⟩⟩ => by
      have ⟨h, hh⟩ := F.map_surjective (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦1⟧' ≫
        (F.commShiftIso (1 : ℤ)).inv.app X₁)
      obtain ⟨X₂, f, g, H⟩ := distinguished_cocone_triangle₂ h
      exact ⟨X₂, ⟨Triangle.π₂.mapIso
        (isoTriangleOfIso₁₃ _ _ (F.map_distinguished _ H) hT e₁ e₃ (by
          dsimp
          simp only [hh, assoc, Iso.inv_hom_id_app, Functor.comp_obj,
            comp_id, Iso.cancel_iso_hom_left, ← Functor.map_comp,
            Iso.inv_hom_id, Functor.map_id]))⟩⟩)

instance : (essImage F).set.RespectsIso := by
  dsimp only [essImage]
  infer_instance

end

section

variable {D : Type*} [Category D] (F : D ⥤ C) (hF : ∀ (X : D), F.obj X ∈ S.set)

def lift : D ⥤ S.category := FullSubcategory.lift S.set F hF

lemma lift_comp_inclusion_eq : S.lift F hF ⋙ S.ι = F :=
  FullSubcategory.lift_comp_inclusion_eq _ _ _

def liftCompInclusion : S.lift F hF ⋙ S.ι ≅ F := Iso.refl _

instance [Faithful F] : Faithful (S.lift F hF) :=
  Faithful.of_comp_iso (S.liftCompInclusion F hF)

instance [Full F] : Full (S.lift F hF) :=
  Full.ofCompFaithfulIso (S.liftCompInclusion F hF)

-- should be generalized
instance [Preadditive D] [F.Additive] : (S.lift F hF).Additive where
  map_add {X Y f g} := by
    apply S.ι.map_injective
    apply F.map_add

noncomputable instance [HasShift D ℤ] [F.CommShift ℤ] : (S.lift F hF).CommShift ℤ :=
  Functor.CommShift.ofComp (S.liftCompInclusion F hF) ℤ

noncomputable instance [HasShift D ℤ] [F.CommShift ℤ] :
  NatTrans.CommShift (S.liftCompInclusion F hF).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _

instance isTriangulated_lift [HasShift D ℤ] [Preadditive D] [F.CommShift ℤ] [HasZeroObject D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated]:
    (S.lift F hF).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (S.liftCompInclusion F hF)]
  infer_instance

end

section

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : D ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
  [S.set.RespectsIso]

def inverseImage : Subcategory D :=
  Subcategory.mk' (fun X => F.obj X ∈ S.set)
    (S.set.mem_of_iso F.mapZeroObject.symm S.zero)
    (fun X n hX => S.set.mem_of_iso ((F.commShiftIso n).symm.app X) (S.shift _ n hX))
    (fun _ hT h₁ h₃ => S.ext₂ _ (F.map_distinguished _ hT) h₁ h₃)

lemma mem_inverseImage_iff (X : D) :
    X ∈ (S.inverseImage F).set ↔ F.obj X ∈ S.set := by rfl

instance : (S.inverseImage F).set.RespectsIso where
  condition X Y e hX := by
    rw [mem_inverseImage_iff] at hX ⊢
    exact S.set.mem_of_iso (F.mapIso e) hX

end

end Subcategory

end Triangulated

end CategoryTheory

namespace CategoryTheory

open Category Limits

variable {C : Type _} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (S : Triangulated.Subcategory C)

noncomputable example : Pretriangulated S.W.Localization := inferInstance
noncomputable example : IsTriangulated S.W.Localization := inferInstance
noncomputable example : S.W.Q.IsTriangulated := inferInstance

end CategoryTheory
