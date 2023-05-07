import Mathlib.CategoryTheory.Localization.Triangulated

namespace Set

open CategoryTheory

variable {C : Type _} [Category C]

class RespectsIso (S : Set C) where
  condition : ∀ ⦃X Y : C⦄ (_ : X ≅ Y), X ∈ S → Y ∈ S

lemma mem_of_iso (S : Set C) [S.RespectsIso] (e : X ≅ Y) (hX : X ∈ S) : Y ∈ S :=
  RespectsIso.condition e hX

lemma mem_iff_of_iso (S : Set C) [S.RespectsIso] (e : X ≅ Y) : X ∈ S ↔ Y ∈ S :=
  ⟨S.mem_of_iso e, S.mem_of_iso e.symm⟩

end Set

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
  zero : (0 : C) ∈ set
  shift : ∀ (X : C) (n : ℤ) (_ : X ∈ set), X⟦n⟧ ∈ set
  ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C)
    (_ : T.obj₁ ∈ set) (_ : T.obj₃ ∈ set), T.obj₂ ∈ set

namespace Subcategory

variable {C}
variable (S : Subcategory C)

instance : S.set.RespectsIso := ⟨fun X Y e hX => by
  refine' S.ext₂ (Triangle.mk e.hom (0 : Y ⟶ 0) 0) _ hX S.zero
  refine' isomorphic_distinguished _ (contractible_distinguished X) _ _
  exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
    (by aesop_cat) (by aesop_cat) (by aesop_cat)⟩

def W : MorphismProperty C := fun X Y f => ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), Z ∈ S.set

def W' : MorphismProperty C := fun Y Z g => ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), X ∈ S.set

variable {S}

def W.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₃ ∈ S.set) : S.W T.mor₁ :=
  ⟨T.obj₃, T.mor₂, T.mor₃, hT, h⟩

def W'.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₁ ∈ S.set) : S.W' T.mor₂ :=
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

lemma W_eq_W' : S.W = S.W' := by
  apply MorphismProperty.ext
  intro X Y f
  constructor
  . rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, inv_rot_of_dist_triangle _ H, S.shift _ (-1) mem⟩
  . rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, rot_of_dist_triangle _ H, S.shift _ 1 mem⟩

def W.mk' {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₁ ∈ S.set) : S.W T.mor₂ := by
  simpa only [W_eq_W'] using W'.mk hT h

instance instContainsIdentitiesW : S.W.ContainsIdentities :=
  ⟨fun X => ⟨_, _, _, contractible_distinguished X, S.zero⟩⟩

lemma stableUnderCompositionW [IsTriangulated C] : (W S).StableUnderComposition := by
  rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
  obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
  refine' ⟨_, _, _, H₁₃, S.ext₂ _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

instance multiplicativeW [IsTriangulated C] : S.W.IsMultiplicative where
  comp' := S.stableUnderCompositionW

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
  nonempty_toSq := by
    rintro X' X Y s ⟨Z, f, g, H, mem⟩ u
    obtain ⟨Y', s', f', mem'⟩ := distinguished_cocone_triangle₂ (g ≫ u⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ H mem' u (𝟙 Z) (by simp)
    exact ⟨⟨Y', b, s', ⟨Z, f', g ≫ u⟦1⟧', mem', mem⟩, hb₁.symm⟩⟩
  ext := by
    rintro X' X Y f₁ f₂ s ⟨Z, g, h, H, mem⟩ hf₁
    have hf₂ : s ≫ (f₁ - f₂) = 0 := by rw [comp_sub, hf₁, sub_self]
    obtain ⟨q, hq⟩ := contravariant_yoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle q
    refine' ⟨Y', r, _, _⟩
    . exact ⟨_, _, _, rot_of_dist_triangle _ mem', S.shift _ _ mem⟩
    . have eq := comp_dist_triangle_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero, ← sub_comp, hq, assoc, eq, comp_zero]

instance [IsTriangulated C] : S.W.HasRightCalculusOfFractions where
  nonempty_toSq := by
    rintro X Y Y' s ⟨Z, f, g, H, mem⟩ u
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (u ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _ mem' H u (𝟙 Z) (by simp)
    exact ⟨⟨X', a, f', ⟨Z, u ≫ f, h', mem', mem⟩, ha₁⟩⟩
  ext := by
    rintro Y Z Z' f₁ f₂ s hs hf₁
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [sub_comp, hf₁, sub_self]
    rw [W_eq_W'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    obtain ⟨q, hq⟩ := covariant_yoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine' ⟨Y', r, _, _⟩
    . exact ⟨_, _, _, mem', mem⟩
    . have eq := comp_dist_triangle_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero, ← comp_sub, hq, reassoc_of% eq, zero_comp]

lemma W_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : S.W f := by
  refine' ⟨0, 0, 0, isomorphic_distinguished _ (contractible_distinguished Y) _ _, S.zero⟩
  exact Triangle.isoMk _ _ (asIso f) (Iso.refl _) (Iso.refl _)
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

lemma mul_mem_W_iff {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    S.W ((↑((-1 : Units ℤ)^n) : ℤ)  • f) ↔ S.W f :=
  S.respectsIsoW.arrow_mk_iso_iff
    (Arrow.isoMk (Preadditive.mulIso ((-1 : Units ℤ)^n) (Iso.refl _)) (Iso.refl _)
      (by dsimp ; simp only [Preadditive.zsmul_comp, id_comp, comp_id]))

instance WIsCompatibleWIthShift : S.W.IsCompatibleWithShift ℤ := ⟨by
  have : ∀ {X Y : C} (f : X ⟶ Y) (hf : S.W f) (n : ℤ), S.W (f⟦n⟧') := by
    rintro X Y f ⟨Z, g, h, H, mem⟩ n
    rw [← mul_mem_W_iff S _ n]
    exact ⟨_, _, _, shift_distinguished _ H n, S.shift _ n mem⟩
  intro n
  apply MorphismProperty.ext
  intro X Y f
  constructor
  . intro hf
    have H := S.respectsIsoW.arrow_mk_iso_iff
     ((Arrow.mapArrowNatIsoOfNatIso (shiftEquiv C n).unitIso).app (Arrow.mk f))
    dsimp at H
    rw [H]
    exact this _ hf (-n)
  . intro hf
    exact this _ hf n⟩

variable {S}

lemma W.shift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : S.W f) (n : ℤ) : S.W (f⟦n⟧') := by
  simpa only [MorphismProperty.IsCompatibleWithShift.iff S.W f n] using hf

lemma W.unshift {X₁ X₂ : C} {f : X₁ ⟶ X₂} {n : ℤ} (hf : S.W (f⟦n⟧')) : S.W f := by
  simpa only [← MorphismProperty.IsCompatibleWithShift.iff S.W f n] using hf

variable (S)

lemma binary_product_stable (X₁ X₂ : C) (hX₁ : X₁ ∈ S.set) (hX₂ : X₂ ∈ S.set) :
    (X₁ ⨯ X₂) ∈ S.set :=
  S.ext₂ _ (binaryProductTriangle_distinguished X₁ X₂) hX₁ hX₂

/-
lemma pi_finite_stable {J : Type} [Finite J] (X : J → C) (hX : ∀ j, X j ∈ S.set) :
    (∏ X) ∈ S.set := by
  revert hX X
  let P : Type → Prop := fun J =>
    ∀ [hJ : Finite J] (X : J → C) (hX : ∀ j, X j ∈ S.set), (∏ X) ∈ S.set
  change P J
  apply @Finite.induction_empty_option
  . intro J₁ J₂ e hJ₁ _ X hX
    have : Finite J₁ := Finite.of_equiv _ e.symm
    exact Set.mem_of_iso _ (productIsoOfEquiv X e) (hJ₁ (fun j₁ => X (e j₁)) (fun j₁ => hX _))
  . intro _ X hX
    refine' Set.mem_of_iso _ (IsZero.isoZero _).symm S.zero
    rw [IsZero.iff_id_eq_zero]
    ext ⟨⟩
  . sorry

def productTriangle {J : Type _} (T : J → Triangle C)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] : Triangle C :=
  Triangle.mk (Pi.map (fun j => (T j).mor₁))
    (Pi.map (fun j => (T j).mor₂))
    (Pi.map (fun j => (T j).mor₃) ≫ inv (piComparison _ _))

lemma productTriangle_distinguished {J : Type _} (T : J → Triangle C)
    (hT : ∀ j, T j ∈ distTriang C)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] :
  productTriangle T ∈ distTriang C := sorry

instance : S.W.IsStableUnderFiniteProducts := ⟨fun J _ => by
  refine' MorphismProperty.IsStableUnderProductsOfShape.mk _ _ (S.respectsIsoW) _
  intro X₁ X₂ f hf
  exact W.mk (productTriangle_distinguished _ (fun j => W.triangle_distinguished _ (hf j)))
    (pi_finite_stable _ _ (fun j => W.triangle_obj₃_mem _ _))⟩

variable [IsTriangulated C]

example : S.W.HasLeftCalculusOfFractions := inferInstance
example : S.W.HasRightCalculusOfFractions := inferInstance
example : S.W.IsCompatibleWithShift ℤ := inferInstance

instance : S.W.IsCompatibleWithTriangulation := sorry

example : Pretriangulated (S.W.Localization) := inferInstance
-/

end Subcategory

end Triangulated

end CategoryTheory
