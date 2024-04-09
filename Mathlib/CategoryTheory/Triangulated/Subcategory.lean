/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Shift.Localization

/-! # Triangulated subcategories

In this file, we introduce the notion of triangulated subcategory of
a pretriangulated category `C`. If `S : Subcategory W`, we define the
class of morphisms `S.W : MorphismProperty C` consisting of morphisms
whose "cone" belongs to `S` (up to isomorphisms). We show that `S.W`
has both calculus of left and right fractions.

## TODO

* obtain (pre)triangulated instances on the localized category with respect to `S.W`
* define the type `S.category` as `Fullsubcategory S.set` and show that it
is a pretriangulated category.

## Implementation notes

In the definition of `Triangulated.Subcategory`, we do not assume that the predicate
on objects is closed under isomorphisms (i.e. that the subcategory is "strictly full").
Part of the theory would be more convenient under this stronger assumption
(e.g. `Subcategory C` would be a lattice), but some applications require this:
for example, the subcategory of bounded below complexes in the homotopy category
of an additive category is not closed under isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

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

namespace Triangulated

open Pretriangulated

variable (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangulated subcategory of a pretriangulated category `C` consists of
a predicate `P : C → Prop` which contains a zero object, is stable by shifts, and such that
if `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle such that if `X₁` and `X₃` satisfy
`P` then `X₂` is isomorphic to an object satisfying `P`. -/
structure Subcategory where
  /-- the underlying predicate on objects of a triangulated subcategory -/
  P : C → Prop
  zero' : ∃ (Z : C) (_ : IsZero Z), P Z
  shift (X : C) (n : ℤ) : P X → P (X⟦n⟧)
  ext₂' (T : Triangle C) (_ : T ∈ distTriang C) : P T.obj₁ → P T.obj₃ → isoClosure P T.obj₂

namespace Subcategory

variable {C}
variable (S : Subcategory C)

lemma zero [ClosedUnderIsomorphisms S.P] : S.P 0 := by
  obtain ⟨X, hX, mem⟩ := S.zero'
  exact mem_of_iso _ hX.isoZero mem

/-- The closure under isomorphisms of a triangulated subcategory. -/
def isoClosure : Subcategory C where
  P := CategoryTheory.isoClosure S.P
  zero' := by
    obtain ⟨Z, hZ, hZ'⟩ := S.zero'
    exact ⟨Z, hZ, Z, hZ', ⟨Iso.refl _⟩⟩
  shift X n := by
    rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦n⟧, S.shift Y n hY, ⟨(shiftFunctor C n).mapIso e⟩⟩
  ext₂' := by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact subset_isoClosure _ _
      (S.ext₂' (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by aesop_cat) (by aesop_cat) (by
          dsimp
          simp only [assoc, Iso.cancel_iso_inv_left, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

instance : ClosedUnderIsomorphisms S.isoClosure.P := by
  dsimp only [isoClosure]
  infer_instance

section

variable (P : C → Prop) (zero : P 0)
  (shift : ∀ (X : C) (n : ℤ), P X → P (X⟦n⟧))
  (ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C), P T.obj₁ → P T.obj₃ → P T.obj₂)

/-- An alternative constructor for "strictly full" triangulated subcategory. -/
def mk' : Subcategory C where
  P := P
  zero' := ⟨0, isZero_zero _, zero⟩
  shift := shift
  ext₂' T hT h₁ h₃ := subset_isoClosure P _ (ext₂ T hT h₁ h₃)

instance : ClosedUnderIsomorphisms (mk' P zero shift ext₂).P where
  mem_of_iso {X Y} e hX := by
    refine' ext₂ (Triangle.mk e.hom (0 : Y ⟶ 0) 0) _ hX zero
    refine' isomorphic_distinguished _ (contractible_distinguished X) _ _
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)

end

@[simp]
lemma shift_iff [ClosedUnderIsomorphisms S.P] (X : C) (n : ℤ) :
    S.P (X⟦n⟧) ↔ S.P X := by
  constructor
  · intro h
    exact mem_of_iso _ ((shiftEquiv C n).unitIso.symm.app X) (S.shift _ (-n) h)
  · exact S.shift X n

lemma ext₂ [ClosedUnderIsomorphisms S.P]
    (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : S.P T.obj₁)
    (h₃ : S.P T.obj₃) : S.P T.obj₂ := by
  simpa only [isoClosure_eq_self] using S.ext₂' T hT h₁ h₃

/-- Given `S : Triangulated.Subcategory C`, this is the class of morphisms on `C` which
consists of morphisms whose cone satisfies `S.P`. -/
def W : MorphismProperty C := fun X Y f => ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), S.P Z

lemma W_iff {X Y : C} (f : X ⟶ Y) :
    S.W f ↔ ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
      (_ : Triangle.mk f g h ∈ distTriang C), S.P Z := by rfl

lemma W_iff' {Y Z : C} (g : Y ⟶ Z) :
    S.W g ↔ ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧)
      (_ : Triangle.mk f g h ∈ distTriang C), S.P X := by
  rw [S.W_iff]
  constructor
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, inv_rot_of_distTriang _ H, S.shift _ (-1) mem⟩
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, rot_of_distTriang _ H, S.shift _ 1 mem⟩

lemma W.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : S.P T.obj₃) : S.W T.mor₁ :=
  ⟨_, _, _, hT, h⟩

lemma W.mk' {T : Triangle C} (hT : T ∈ distTriang C) (h : S.P T.obj₁) : S.W T.mor₂ := by
  rw [W_iff']
  exact ⟨_, _, _, hT, h⟩

lemma isoClosure_W : S.isoClosure.W = S.W := by
  ext X Y f
  constructor
  · rintro ⟨Z, g, h, mem, ⟨Z', hZ', ⟨e⟩⟩⟩
    refine' ⟨Z', g ≫ e.hom, e.inv ≫ h, isomorphic_distinguished _ mem _ _, hZ'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
  · rintro ⟨Z, g, h, mem, hZ⟩
    exact ⟨Z, g, h, mem, subset_isoClosure _ _ hZ⟩

lemma respectsIso_W : S.W.RespectsIso where
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

instance : S.W.ContainsIdentities := by
  rw [← isoClosure_W]
  exact ⟨fun X => ⟨_, _, _, contractible_distinguished X, zero _⟩⟩

lemma W_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : S.W f := by
  refine (S.respectsIso_W.arrow_mk_iso_iff ?_).1 (MorphismProperty.id_mem _ X)
  exact Arrow.isoMk (Iso.refl _) (asIso f)

lemma smul_mem_W_iff {X Y : C} (f : X ⟶ Y) (n : ℤˣ) :
    S.W (n • f) ↔ S.W f :=
  S.respectsIso_W.arrow_mk_iso_iff (Arrow.isoMk (n • (Iso.refl _)) (Iso.refl _))

variable {S}

lemma W.shift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : S.W f) (n : ℤ) : S.W (f⟦n⟧') := by
  rw [← smul_mem_W_iff _ _ (n.negOnePow)]
  obtain ⟨X₃, g, h, hT, mem⟩ := hf
  exact ⟨_, _, _, Pretriangulated.Triangle.shift_distinguished _ hT n, S.shift _ _ mem⟩

lemma W.unshift {X₁ X₂ : C} {f : X₁ ⟶ X₂} {n : ℤ} (hf : S.W (f⟦n⟧')) : S.W f :=
  (S.respectsIso_W.arrow_mk_iso_iff
     (Arrow.isoOfNatIso (shiftEquiv C n).unitIso (Arrow.mk f))).2 (hf.shift (-n))

instance : S.W.IsCompatibleWithShift ℤ where
  condition n := by
    ext K L f
    exact ⟨fun hf => hf.unshift, fun hf => hf.shift n⟩

instance [IsTriangulated C] : S.W.IsMultiplicative where
  stableUnderComposition := by
    rw [← isoClosure_W]
    rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
    obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
    exact ⟨_, _, _, H₁₃, S.isoClosure.ext₂ _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

variable (S)

lemma mem_W_iff_of_distinguished
    [ClosedUnderIsomorphisms S.P] (T : Triangle C) (hT : T ∈ distTriang C) :
    S.W T.mor₁ ↔ S.P T.obj₃ := by
  constructor
  · rintro ⟨Z, g, h, hT', mem⟩
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso _ _ hT' hT (Iso.refl _)
    exact mem_of_iso S.P (Triangle.π₃.mapIso e) mem
  · intro h
    exact ⟨_, _, _, hT, h⟩

lemma mem_W_iff_of_distinguished'
    [ClosedUnderIsomorphisms S.P] (T : Triangle C) (hT : T ∈ distTriang C) :
    S.W T.mor₂ ↔ S.P T.obj₁ := by
  have := S.mem_W_iff_of_distinguished _ (rot_of_distTriang _ hT)
  dsimp at this
  rw [this, shift_iff]

instance [IsTriangulated C] : S.W.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
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
  exists_rightFraction X Y φ := by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _
      mem' H φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext Y Z Z' f₁ f₂ s hs hf₁ := by
    rw [S.W_iff'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [sub_comp, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine' ⟨Y', r, _, _⟩
    · exact ⟨_, _, _, mem', mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero, ← comp_sub, hq, reassoc_of% eq, zero_comp]

instance [IsTriangulated C] : S.W.IsCompatibleWithTriangulation := ⟨by
  rintro T₁ T₃ mem₁ mem₃ a b ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩ ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩ comm
  obtain ⟨Z₂, g₂, h₂, mem₂⟩ := distinguished_cocone_triangle (T₁.mor₁ ≫ b)
  have H := someOctahedron rfl mem₁ mem₄ mem₂
  have H' := someOctahedron comm.symm mem₅ mem₃ mem₂
  let φ : T₁ ⟶ T₃ := H.triangleMorphism₁ ≫ H'.triangleMorphism₂
  exact ⟨φ.hom₃, S.W.comp_mem _ _ (W.mk S H.mem mem₄') (W.mk' S H'.mem mem₅'),
    by simpa [φ] using φ.comm₂, by simpa [φ] using φ.comm₃⟩⟩

section

variable (T : Triangle C) (hT : T ∈ distTriang C)

lemma ext₁ [ClosedUnderIsomorphisms S.P] (h₂ : S.P T.obj₂) (h₃ : S.P T.obj₃) :
    S.P T.obj₁ :=
  S.ext₂ _ (inv_rot_of_distTriang _ hT) (S.shift _ _ h₃) h₂

lemma ext₃ [ClosedUnderIsomorphisms S.P] (h₁ : S.P T.obj₁) (h₂ : S.P T.obj₂) :
    S.P T.obj₃ :=
  S.ext₂ _ (rot_of_distTriang _ hT) h₂ (S.shift _ _ h₁)

lemma ext₁' (h₂ : S.P T.obj₂) (h₃ : S.P T.obj₃) :
    CategoryTheory.isoClosure S.P T.obj₁ :=
  S.ext₂' _ (inv_rot_of_distTriang _ hT) (S.shift _ _ h₃) h₂

lemma ext₃' (h₁ : S.P T.obj₁) (h₂ : S.P T.obj₂) :
    CategoryTheory.isoClosure S.P T.obj₃ :=
  S.ext₂' _ (rot_of_distTriang _ hT) h₂ (S.shift _ _ h₁)

lemma binary_product_stable [ClosedUnderIsomorphisms S.P] (X₁ X₂ : C) (hX₁ : S.P X₁) (hX₂ : S.P X₂) :
    S.P (X₁ ⨯ X₂)  :=
  S.ext₂ _ (binaryProductTriangle_distinguished X₁ X₂) hX₁ hX₂

lemma pi_finite_stable [ClosedUnderIsomorphisms S.P] {J : Type} [Finite J] (X : J → C) (hX : ∀ j, S.P (X j)) :
    S.P (∏ X) := by
  revert hX X
  let P : Type → Prop := fun J =>
    ∀ [hJ : Finite J] (X : J → C) (_ : ∀ j, S.P (X j)), S.P (∏ X)
  change P J
  apply @Finite.induction_empty_option
  · intro J₁ J₂ e hJ₁ _ X hX
    have : Finite J₁ := Finite.of_equiv _ e.symm
    exact mem_of_iso _ (productIsoOfEquiv X e) (hJ₁ (fun j₁ => X (e j₁)) (fun j₁ => hX _))
  · intro _ X _
    refine' mem_of_iso _ (IsZero.isoZero _).symm S.zero
    rw [IsZero.iff_id_eq_zero]
    ext ⟨⟩
  · intro J _ hJ _ X hX
    exact mem_of_iso _ (productOptionIso  X).symm
      (S.binary_product_stable _ _ (hJ (fun j => X (some j)) (fun j => hX _)) (hX none))

instance : S.W.IsStableUnderFiniteProducts := by
  rw [← isoClosure_W]
  exact ⟨fun J _ => by
    refine' MorphismProperty.IsStableUnderProductsOfShape.mk _ _ (S.isoClosure.respectsIso_W) _
    intro X₁ X₂ f hf
    exact W.mk _ (productTriangle_distinguished _
      (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose))
      (pi_finite_stable _ _ (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose_spec))⟩

section

variable [IsTriangulated C]
example : Pretriangulated (S.W.Localization) := inferInstance
example : IsTriangulated (S.W.Localization) := inferInstance
example : S.W.Q.IsTriangulated := inferInstance

end

end

def category := FullSubcategory S.P

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
    obtain ⟨Z, hZ, mem⟩ := S.zero'
    refine' ⟨⟨Z, mem⟩, _⟩
    rw [IsZero.iff_id_eq_zero]
    apply hZ.eq_of_src

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

instance : ClosedUnderIsomorphisms (essImage F).P  := by
  dsimp only [essImage]
  infer_instance

end

section

variable {D : Type*} [Category D] (F : D ⥤ C) (hF : ∀ (X : D), S.P (F.obj X))

def lift : D ⥤ S.category := FullSubcategory.lift S.P F hF

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
  [ClosedUnderIsomorphisms S.P]

def inverseImage : Subcategory D :=
  Subcategory.mk' (fun X => S.P (F.obj X))
    (mem_of_iso _ F.mapZeroObject.symm S.zero)
    (fun X n hX => mem_of_iso _ ((F.commShiftIso n).symm.app X) (S.shift _ n hX))
    (fun _ hT h₁ h₃ => S.ext₂ _ (F.map_distinguished _ hT) h₁ h₃)

lemma mem_inverseImage_iff (X : D) :
    (S.inverseImage F).P X ↔ S.P (F.obj X) := by rfl

instance : ClosedUnderIsomorphisms (S.inverseImage F).P where
  mem_of_iso {X Y} e hX := by
    rw [mem_inverseImage_iff] at hX ⊢
    exact mem_of_iso _ (F.mapIso e) hX

lemma mem_inverseImage_W_iff {X Y : D} (s : X ⟶ Y) :
    (S.inverseImage F).W s ↔ S.W (F.map s) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have eq₁ := (S.inverseImage F).mem_W_iff_of_distinguished _ hT
  have eq₂ := S.mem_W_iff_of_distinguished _ (F.map_distinguished _ hT)
  dsimp at eq₁ eq₂
  rw [eq₁, mem_inverseImage_iff, eq₂]

lemma inverseImage_W_isInverted {E : Type*} [Category E]
    (L : C ⥤ E) [L.IsLocalization S.W] :
    (S.inverseImage F).W.IsInvertedBy (F ⋙ L) :=
  fun X Y f hf => Localization.inverts L S.W (F.map f)
    (by simpa only [mem_inverseImage_W_iff] using hf)

end

section

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

def ofNatTrans : Subcategory C :=
  Subcategory.mk' (fun X => IsIso (τ.app X))
    ⟨0, by rw [comp_zero, ← F.map_id, id_zero, F.map_zero],
        by rw [zero_comp, ← G.map_id, id_zero, G.map_zero]⟩
    (fun X n (_ : IsIso (τ.app X)) => by
      dsimp
      rw [NatTrans.CommShift.app_shift τ n]
      infer_instance)
    (fun T hT h₁ h₃ => by
      exact Pretriangulated.isIso₂_of_isIso₁₃ (by
        refine' (Pretriangulated.Triangle.homMk _ _ (τ.app _) (τ.app _) (τ.app _) (by simp) (by simp)
          (by simp [NatTrans.CommShift.comm_app τ])))
        (F.map_distinguished _ hT) (G.map_distinguished _ hT) (by exact h₁) (by exact h₃))

instance : ClosedUnderIsomorphisms (ofNatTrans τ).P := by
  dsimp [ofNatTrans]
  infer_instance

end

end Subcategory

end Triangulated

end CategoryTheory
