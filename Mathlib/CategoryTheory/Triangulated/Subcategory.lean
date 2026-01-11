/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Triangulated subcategories

In this file, given a pretriangulated category `C` and `P : ObjectProperty C`,
we introduce a typeclass `P.IsTriangulated` to express that `P`
is a triangulated subcategory of `C`. When `P` is a triangulated
subcategory, we introduce a class of morphisms `P.trW : MorphismProperty C`
consisting of the morphisms whose "cone" belongs to `P` (up to isomorphisms),
and we show that it has both calculus of left and right fractions.

## TODO

* show that the fullsubcategory attached to `P` (such that `P.IsTriangulated`)
  is a pretriangulated category.

## Implementation notes

In the definition of `P.IsTriangulated`, we do not assume that the predicate
on objects is closed under isomorphisms (i.e. that the subcategory is "strictly full").
Part of the theory would be more convenient under this stronger assumption
(e.g. the subtype of `ObjectProperty C` consisting of triangulated subcategories
would be a lattice), but some applications require this:
for example, the subcategory of bounded below complexes in the homotopy category
of an additive category is not closed under isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

namespace Limits

variable {C J₁ J₂ : Type _} [Category C]
  (X : J₂ → C) (e : J₁ ≃ J₂) [HasProduct X]

noncomputable def fanOfEquiv : Fan (X ∘ e) := Fan.mk (∏ᶜ X) (fun _ => Pi.π _ _)

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
    (fun s m hm => Limits.Pi.hom_ext (f := X) _ _ (fun j ↦ by simp [← hm]))

lemma hasProductOfEquiv : HasProduct (X ∘ e) :=
  ⟨⟨_, isLimitFanOfEquiv X e⟩⟩

noncomputable def productIsoOfEquiv [HasProduct (X ∘ e)] : ∏ᶜ (X ∘ e) ≅ ∏ᶜ X :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimitFanOfEquiv X e)

noncomputable def productOptionIso {C J : Type _} [Category C]
    (X : Option J → C) [HasProduct X] [HasProduct (fun j => X (some j))]
    [HasBinaryProduct (∏ᶜ (fun j => X (some j))) (X none)] :
    (∏ᶜ X) ≅ (∏ᶜ (fun j => X (some j))) ⨯ (X none) where
  hom := prod.lift (Pi.lift (fun j => Pi.π _ (some j))) (Pi.π _ none)
  inv := Pi.lift (fun b => match b with
    | some j => prod.fst ≫ Pi.π _ j
    | none => prod.snd)

end Limits

open Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C` with `C` a pretriangulated category, this
is the property that whenever `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle
such that `P X₂` and `P X₃` hold, then `P.isoClosure X₁` holds. -/
class IsTriangulatedClosed₁ : Prop where
  ext₁' (T : Triangle C) (_ : T ∈ distTriang C) : P T.obj₂ → P T.obj₃ → P.isoClosure T.obj₁

/-- Given `P : ObjectProperty C` with `C` a pretriangulated category, this
is the property that whenever `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle
such that `P X₁` and `P X₃` hold, then `P.isoClosure X₂` holds. -/
class IsTriangulatedClosed₂ : Prop where
  ext₂' (T : Triangle C) (_ : T ∈ distTriang C) : P T.obj₁ → P T.obj₃ → P.isoClosure T.obj₂

/-- Given `P : ObjectProperty C` with `C` a pretriangulated category, this
is the property that whenever `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle
such that `P X₁` and `P X₂` hold, then `P.isoClosure X₃` holds. -/
class IsTriangulatedClosed₃ : Prop where
  ext₃' (T : Triangle C) (_ : T ∈ distTriang C) : P T.obj₁ → P T.obj₂ → P.isoClosure T.obj₃

lemma ext_of_isTriangulatedClosed₁'
    [P.IsTriangulatedClosed₁] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : P T.obj₂) (h₃ : P T.obj₃) : P.isoClosure T.obj₁ :=
  IsTriangulatedClosed₁.ext₁' T hT h₂ h₃

lemma ext_of_isTriangulatedClosed₂'
    [P.IsTriangulatedClosed₂] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : P T.obj₁) (h₃ : P T.obj₃) : P.isoClosure T.obj₂ :=
  IsTriangulatedClosed₂.ext₂' T hT h₁ h₃

lemma ext_of_isTriangulatedClosed₃'
    [P.IsTriangulatedClosed₃] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) : P.isoClosure T.obj₃ :=
  IsTriangulatedClosed₃.ext₃' T hT h₁ h₂

lemma ext_of_isTriangulatedClosed₁
    [P.IsTriangulatedClosed₁] [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : P T.obj₂) (h₃ : P T.obj₃) : P T.obj₁ := by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₁' T hT h₂ h₃

lemma ext_of_isTriangulatedClosed₂
    [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : P T.obj₁) (h₃ : P T.obj₃) : P T.obj₂ := by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₂' T hT h₁ h₃

lemma ext_of_isTriangulatedClosed₃
    [P.IsTriangulatedClosed₃] [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) : P T.obj₃ := by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₃' T hT h₁ h₂

variable {P}

lemma IsTriangulatedClosed₁.mk' [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (T : Triangle C) (_ : T ∈ distTriang C)
      (_ : P T.obj₂) (_ : P T.obj₃), P T.obj₁) : P.IsTriangulatedClosed₁ where
  ext₁' := by simpa only [isoClosure_eq_self] using hP

lemma IsTriangulatedClosed₂.mk' [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (T : Triangle C) (_ : T ∈ distTriang C)
      (_ : P T.obj₁) (_ : P T.obj₃), P T.obj₂) : P.IsTriangulatedClosed₂ where
  ext₂' := by simpa only [isoClosure_eq_self] using hP

lemma IsTriangulatedClosed₃.mk' [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (T : Triangle C) (_ : T ∈ distTriang C)
      (_ : P T.obj₁) (_ : P T.obj₂), P T.obj₃) : P.IsTriangulatedClosed₃ where
  ext₃' := by simpa only [isoClosure_eq_self] using hP

variable (P)

instance [P.IsTriangulatedClosed₂] : P.isoClosure.IsTriangulatedClosed₂ where
  ext₂' := by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact ObjectProperty.le_isoClosure _ _
      (P.ext_of_isTriangulatedClosed₂'
        (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by simp) (by simp) (by
          dsimp
          simp only [assoc, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

/-- The property that `P : ObjectProperty C` is a triangulated subcategory
(of a pretriangulated category `C`). -/
protected class IsTriangulated : Prop extends P.ContainsZero, P.IsStableUnderShift ℤ,
    P.IsTriangulatedClosed₂ where

instance [P.IsTriangulated] : P.IsTriangulatedClosed₁ where
  ext₁' _ hT h₂ h₃ :=
    P.ext_of_isTriangulatedClosed₂' _ (inv_rot_of_distTriang _ hT) (P.le_shift _ _ h₃) h₂

instance [P.IsTriangulated] : P.IsTriangulatedClosed₃ where
  ext₃' _ hT h₁ h₂ :=
    P.ext_of_isTriangulatedClosed₂' _ (rot_of_distTriang _ hT) h₂ (P.le_shift _ _ h₁)

instance [P.IsTriangulated] : P.isoClosure.IsTriangulated where

/-- Given `P : ObjectProperty C` with `C` a pretriangulated category, this is the class
of morphisms whose cone satisfies `P`. (The name `trW` contains the prefix `tr`
for "triangulated", and `W` is a letter that is often used to refer to classes of
morphisms with respect to which we may consider the localized category.) -/
def trW : MorphismProperty C :=
  fun X Y f => ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (_ : Triangle.mk f g h ∈ distTriang C), P Z

lemma trW_iff {X Y : C} (f : X ⟶ Y) :
    P.trW f ↔ ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
      (_ : Triangle.mk f g h ∈ distTriang C), P Z := by rfl

lemma trW_iff' [P.IsStableUnderShift ℤ] {Y Z : C} (g : Y ⟶ Z) :
    P.trW g ↔ ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧)
      (_ : Triangle.mk f g h ∈ distTriang C), P X := by
  rw [P.trW_iff]
  constructor
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, inv_rot_of_distTriang _ H, P.le_shift (-1) _ mem⟩
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, rot_of_distTriang _ H, P.le_shift 1 _ mem⟩

lemma trW.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : P T.obj₃) : P.trW T.mor₁ :=
  ⟨_, _, _, hT, h⟩

lemma trW.mk' [P.IsStableUnderShift ℤ] {T : Triangle C} (hT : T ∈ distTriang C)
    (h : P T.obj₁) : P.trW T.mor₂ := by
  rw [trW_iff']
  exact ⟨_, _, _, hT, h⟩

lemma trW_isoClosure : P.isoClosure.trW = P.trW := by
  ext X Y f
  constructor
  · rintro ⟨Z, g, h, mem, ⟨Z', hZ', ⟨e⟩⟩⟩
    refine ⟨Z', g ≫ e.hom, e.inv ≫ h, isomorphic_distinguished _ mem _ ?_, hZ'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
  · rintro ⟨Z, g, h, mem, hZ⟩
    exact ⟨Z, g, h, mem, ObjectProperty.le_isoClosure _ _ hZ⟩

instance : P.trW.RespectsIso where
  precomp {X' X Y} e (he : IsIso e) := by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, g, h ≫ inv e⟦(1 : ℤ)⟧', isomorphic_distinguished _ mem _ ?_, mem'⟩
    refine Triangle.isoMk _ _ (asIso e) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    dsimp
    simp only [Functor.map_inv, assoc, IsIso.inv_hom_id, comp_id, id_comp]
  postcomp {X Y Y'} e (he : IsIso e) := by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, inv e ≫ g, h, isomorphic_distinguished _ mem _ ?_, mem'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (asIso e).symm (Iso.refl _)

instance [P.ContainsZero] : P.trW.ContainsIdentities := by
  rw [← trW_isoClosure]
  exact ⟨fun X => ⟨_, _, _, contractible_distinguished X, prop_zero _⟩⟩

lemma trW_of_isIso [P.ContainsZero] {X Y : C} (f : X ⟶ Y) [IsIso f] : P.trW f := by
  refine (P.trW.arrow_mk_iso_iff ?_).1 (MorphismProperty.id_mem _ X)
  exact Arrow.isoMk (Iso.refl _) (asIso f)

lemma smul_mem_trW_iff {X Y : C} (f : X ⟶ Y) (n : ℤˣ) :
    P.trW (n • f) ↔ P.trW f :=
  P.trW.arrow_mk_iso_iff (Arrow.isoMk (n • (Iso.refl _)) (Iso.refl _))

variable {P} in
lemma trW.shift [P.IsStableUnderShift ℤ]
    {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : P.trW f) (n : ℤ) : P.trW (f⟦n⟧') := by
  rw [← smul_mem_trW_iff _ _ (n.negOnePow)]
  obtain ⟨X₃, g, h, hT, mem⟩ := hf
  exact ⟨_, _, _, Pretriangulated.Triangle.shift_distinguished _ hT n, P.le_shift _ _ mem⟩

lemma trW.unshift [P.IsStableUnderShift ℤ]
    {X₁ X₂ : C} {f : X₁ ⟶ X₂} {n : ℤ} (hf : P.trW (f⟦n⟧')) : P.trW f :=
  (P.trW.arrow_mk_iso_iff
     (Arrow.isoOfNatIso (shiftEquiv C n).unitIso (Arrow.mk f))).2 (hf.shift (-n))

instance [P.IsStableUnderShift ℤ] : P.trW.IsCompatibleWithShift ℤ where
  condition n := by
    ext K L f
    exact ⟨fun hf => hf.unshift, fun hf => hf.shift n⟩

instance [IsTriangulated C] [P.IsTriangulated] : P.trW.IsMultiplicative where
  comp_mem := by
    rw [← trW_isoClosure]
    rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
    obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
    exact ⟨_, _, _, H₁₃, P.isoClosure.ext_of_isTriangulatedClosed₂
      _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

lemma trW_iff_of_distinguished
    [P.IsClosedUnderIsomorphisms] (T : Triangle C) (hT : T ∈ distTriang C) :
    P.trW T.mor₁ ↔ P T.obj₃ := by
  constructor
  · rintro ⟨Z, g, h, hT', mem⟩
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso _ _ hT' hT (Iso.refl _)
    exact P.prop_of_iso (Triangle.π₃.mapIso e) mem
  · intro h
    exact ⟨_, _, _, hT, h⟩

/-- Variant of `mem_W_iff_of_distinguished`. -/
lemma trW_iff_of_distinguished' [P.IsStableUnderShift ℤ]
    [P.IsClosedUnderIsomorphisms] (T : Triangle C) (hT : T ∈ distTriang C) :
    P.trW T.mor₂ ↔ P T.obj₁ := by
  simpa [P.prop_shift_iff_of_isStableUnderShift]
    using P.trW_iff_of_distinguished _ (rot_of_distTriang _ hT)

instance [IsTriangulated C] [P.IsTriangulated] : P.trW.HasLeftCalculusOfFractions where
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
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, rot_of_distTriang _ mem', P.le_shift _ _ mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero, ← sub_comp, hq, assoc, eq, comp_zero]

instance [IsTriangulated C] [P.IsTriangulated] : P.trW.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _
      mem' H φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext Y Z Z' f₁ f₂ s hs hf₁ := by
    rw [P.trW_iff'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [sub_comp, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, mem', mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero, ← comp_sub, hq, reassoc_of% eq, zero_comp]

instance [IsTriangulated C] [P.IsTriangulated] : P.trW.IsCompatibleWithTriangulation := ⟨by
  rintro T₁ T₃ mem₁ mem₃ a b ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩ ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩ comm
  obtain ⟨Z₂, g₂, h₂, mem₂⟩ := distinguished_cocone_triangle (T₁.mor₁ ≫ b)
  have H := someOctahedron rfl mem₁ mem₄ mem₂
  have H' := someOctahedron comm.symm mem₅ mem₃ mem₂
  let φ : T₁ ⟶ T₃ := H.triangleMorphism₁ ≫ H'.triangleMorphism₂
  exact ⟨φ.hom₃, P.trW.comp_mem _ _ (trW.mk P H.mem mem₄') (trW.mk' P H'.mem mem₅'),
    by simpa [φ] using φ.comm₂, by simpa [φ] using φ.comm₃⟩⟩

lemma binary_product_stable_of_isTriangulated [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (X₁ X₂ : C) (hX₁ : P X₁) (hX₂ : P X₂) :
    P (X₁ ⨯ X₂)  :=
  P.ext_of_isTriangulatedClosed₂ _ (binaryProductTriangle_distinguished X₁ X₂) hX₁ hX₂

lemma pi_finite_stable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    {J : Type} [Finite J] (X : J → C) (hX : ∀ j, P (X j)) :
    P (∏ᶜ X) := by
  revert hX X
  let Q : Type → Prop := fun J =>
    ∀ [hJ : Finite J] (X : J → C) (_ : ∀ j, P (X j)), P (∏ᶜ X)
  suffices Q J by convert this
  apply @Finite.induction_empty_option
  · intro J₁ J₂ e hJ₁ _ X hX
    have : Finite J₁ := Finite.of_equiv _ e.symm
    exact prop_of_iso _ (productIsoOfEquiv X e) (hJ₁ (fun j₁ => X (e j₁)) (fun j₁ => hX _))
  · intro _ X _
    refine prop_of_iso _ (IsZero.isoZero ?_).symm P.prop_zero
    rw [IsZero.iff_id_eq_zero]
    ext ⟨⟩
  · intro J _ hJ _ X hX
    exact prop_of_iso _ (productOptionIso  X).symm
      (P.binary_product_stable_of_isTriangulated _ _
        (hJ (fun j => X (some j)) (fun j => hX _)) (hX none))

instance [P.IsTriangulated] : P.trW.IsStableUnderFiniteProducts := by
  rw [← trW_isoClosure]
  exact ⟨fun J _ => by
    refine MorphismProperty.IsStableUnderProductsOfShape.mk _ _ ?_
    intro _ _ X₁ X₂ f hf
    exact trW.mk _ (productTriangle_distinguished _
      (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose))
      (pi_finite_stable _ _ (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose_spec))⟩

lemma closedUnderLimitsOfShape_discrete_of_isTriangulated
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] (J : Type) [Finite J] :
    P.IsClosedUnderLimitsOfShape (Discrete J) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let G (j : J) : C := p.diag.obj ⟨j⟩
    have e : Discrete.functor G ≅ p.diag := Discrete.natIso (fun _ ↦ Iso.refl _)
    have := IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      ((IsLimit.postcomposeInvEquiv e _).2 p.isLimit)
    exact P.prop_of_iso this (P.pi_finite_stable G (fun j ↦ p.prop_diag_obj _))

section

instance (P' : ObjectProperty C) [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    [P'.IsTriangulatedClosed₂] :
    (P ⊓ P').IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨X₂, h₂, ⟨e⟩⟩ := P'.ext_of_isTriangulatedClosed₂' T hT h₁.2 h₃.2
    exact ⟨X₂, ⟨P.prop_of_iso e (P.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1), h₂⟩, ⟨e⟩⟩

instance (P' : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P'.IsTriangulated] :
    (P ⊓ P').IsTriangulated where

end

section

variable [IsTriangulated C] [P.IsTriangulated]

noncomputable example : Pretriangulated (P.trW.Localization) := inferInstance
example : IsTriangulated (P.trW.Localization) := inferInstance
example : P.trW.Q.IsTriangulated := inferInstance

end

example : Preadditive P.FullSubcategory := inferInstance
example : P.ι.Additive := inferInstance

section

variable [P.IsTriangulated]

noncomputable instance hasShift :
    HasShift P.FullSubcategory ℤ :=
  P.fullyFaithfulι.hasShift (fun n ↦ ObjectProperty.lift _ (P.ι ⋙ shiftFunctor C n)
    (fun X ↦ P.le_shift n _ X.2)) (fun _ => P.liftCompιIso _ _)

instance commShiftι : P.ι.CommShift ℤ :=
  Functor.CommShift.of_hasShiftOfFullyFaithful _ _ _

-- these definitions are made irreducible to prevent (at least temporarily) any abuse of defeq
attribute [irreducible] hasShift commShiftι

instance (n : ℤ) : (shiftFunctor P.FullSubcategory n).Additive := by
  have := Functor.additive_of_iso (P.ι.commShiftIso n).symm
  apply Functor.additive_of_comp_faithful _ P.ι

instance : HasZeroObject P.FullSubcategory where
  zero := by
    obtain ⟨Z, hZ, mem⟩ := P.exists_prop_of_containsZero
    refine ⟨⟨Z, mem⟩, ?_⟩
    rw [IsZero.iff_id_eq_zero]
    apply ObjectProperty.hom_ext
    apply hZ.eq_of_src

attribute [local simp] ObjectProperty.fullyFaithfulι fullyFaithfulInducedFunctor

noncomputable instance : Pretriangulated P.FullSubcategory where
  distinguishedTriangles := fun T => P.ι.mapTriangle.obj T ∈ distTriang C
  isomorphic_distinguished := fun T₁ hT₁ T₂ e =>
    isomorphic_distinguished _ hT₁ _ (P.ι.mapTriangle.mapIso e)
  contractible_distinguished X := by
    refine isomorphic_distinguished _ (contractible_distinguished (P.ι.obj X)) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) P.ι.mapZeroObject
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z', g', h', mem⟩ := distinguished_cocone_triangle (P.ι.map f)
    obtain ⟨Z'', hZ'', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ mem X.2 Y.2
    let Z : P.FullSubcategory := ⟨Z'', hZ''⟩
    refine ⟨Z, P.fullyFaithfulι.preimage (g' ≫ e.hom),
      P.fullyFaithfulι.preimage (e.inv ≫ h' ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app X),
      isomorphic_distinguished _ mem _ ?_⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by aesop_cat) (by simp) (by simp)
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (P.ι.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (P.ι.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism (P.ι.mapTriangle.obj T₁)
      (P.ι.mapTriangle.obj T₂) hT₁ hT₂ (P.ι.map a) (P.ι.map b)
      (by simpa using P.ι.congr_map comm)
    have ⟨c', hc'⟩ : ∃ (c' : T₁.obj₃ ⟶ T₂.obj₃), c = P.ι.map c' :=
      ⟨P.fullyFaithfulι.preimage c, by simp⟩
    dsimp at hc₁ hc₂
    rw [hc'] at hc₁
    rw [hc', assoc] at hc₂
    dsimp at hc₂
    erw [← Functor.commShiftIso_hom_naturality] at hc₂
    refine ⟨c', ⟨P.ι.map_injective ?_, P.ι.map_injective ?_⟩⟩
    · simpa using hc₁
    · rw [← cancel_mono ((Functor.commShiftIso P.ι (1 : ℤ)).hom.app T₂.obj₁),
        P.ι.map_comp, P.ι.map_comp, assoc, assoc]
      erw [hc₂]
      rfl

instance : P.ι.IsTriangulated := ⟨fun _ hT => hT⟩

instance [IsTriangulated C] : IsTriangulated P.FullSubcategory :=
  IsTriangulated.of_fully_faithful_triangulated_functor P.ι

section

variable {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full]

instance : (F.essImage).IsTriangulated where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro Y ⟨X, ⟨e⟩⟩
        exact ⟨X⟦n⟧, ⟨(F.commShiftIso n).app _ ≪≫ (shiftFunctor D n).mapIso e⟩⟩ }
  exists_zero := ⟨0, isZero_zero D, ⟨0, ⟨F.mapZeroObject⟩⟩⟩
  toIsTriangulatedClosed₂ := .mk' (by
    rintro T hT ⟨X₁, ⟨e₁⟩⟩ ⟨X₃, ⟨e₃⟩⟩
    have ⟨h, hh⟩ := F.map_surjective (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦1⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app X₁)
    obtain ⟨X₂, f, g, H⟩ := distinguished_cocone_triangle₂ h
    exact ⟨X₂, ⟨Triangle.π₂.mapIso
      (isoTriangleOfIso₁₃ _ _ (F.map_distinguished _ H) hT e₁ e₃ (by
        dsimp
        simp only [hh, assoc, Iso.inv_hom_id_app, Functor.comp_obj,
          comp_id, ← Functor.map_comp,
          Iso.inv_hom_id, Functor.map_id]))⟩⟩)



end

section

variable {D : Type*} [Category D] (F : D ⥤ C) (hF : ∀ (X : D), P (F.obj X))

-- some of these are general API, not specific to triangulated subcategories

instance [F.Faithful] : (P.lift F hF).Faithful :=
  Functor.Faithful.of_comp_iso (P.liftCompιIso F hF)

instance [F.Full] : (P.lift F hF).Full :=
  Functor.Full.of_comp_faithful_iso (P.liftCompιIso F hF)

-- should be generalized
instance [Preadditive D] [F.Additive] : (P.lift F hF).Additive where
  map_add {X Y f g} := by
    apply P.ι.map_injective
    apply F.map_add

noncomputable instance [HasShift D ℤ] [F.CommShift ℤ] : (P.lift F hF).CommShift ℤ :=
  Functor.CommShift.ofComp (P.liftCompιIso F hF) ℤ

noncomputable instance [HasShift D ℤ] [F.CommShift ℤ] :
  NatTrans.CommShift (P.liftCompιIso F hF).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _

instance isTriangulated_lift [HasShift D ℤ] [Preadditive D] [F.CommShift ℤ] [HasZeroObject D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated] :
    (P.lift F hF).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (P.liftCompιIso F hF)]
  infer_instance

end

section

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : D ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

instance : (P.inverseImage F).IsTriangulated where
  isStableUnderShiftBy n :=
    { le_shift _ hY := P.prop_of_iso ((F.commShiftIso n).symm.app _) (P.le_shift n _ hY) }
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    P.ext_of_isTriangulatedClosed₂ _ (F.map_distinguished T hT) h₁ h₃)

omit [P.IsTriangulated] in
lemma inverseImage_trW_iff {X Y : D} (s : X ⟶ Y) :
    (P.inverseImage F).trW s ↔ P.trW (F.map s) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have eq₁ := (P.inverseImage F).trW_iff_of_distinguished _ hT
  have eq₂ := P.trW_iff_of_distinguished _ (F.map_distinguished _ hT)
  dsimp at eq₁ eq₂
  rw [eq₁, prop_inverseImage_iff, eq₂]

omit [P.IsTriangulated] in
lemma inverseImage_W_isInverted {E : Type*} [Category E]
    (L : C ⥤ E) [L.IsLocalization P.trW] :
    (P.inverseImage F).trW.IsInvertedBy (F ⋙ L) :=
  fun X Y f hf => Localization.inverts L P.trW (F.map f)
    (by simpa only [inverseImage_trW_iff] using hf)

end

section

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

def ofNatTrans : ObjectProperty C := fun X ↦ IsIso (τ.app X)

instance : (ofNatTrans τ).IsClosedUnderIsomorphisms where
  of_iso e h := by
    dsimp [ofNatTrans] at h ⊢
    rwa [← NatTrans.isIso_app_iff_of_iso τ e]

instance : (ofNatTrans τ).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C,
    ⟨0, (F.map_isZero (isZero_zero C)).eq_of_src _ _,
      (G.map_isZero (isZero_zero C)).eq_of_src _ _⟩⟩
  isStableUnderShiftBy n :=
    { le_shift X (hX : IsIso _) := by
        simp only [prop_shift_iff, ofNatTrans, NatTrans.app_shift]
        infer_instance }
  toIsTriangulatedClosed₂ := .mk' (fun T hT _ _ ↦ by
    exact Pretriangulated.isIso₂_of_isIso₁₃
        ((Pretriangulated.Triangle.homMk _ _ (τ.app _) (τ.app _) (τ.app _)
          (by simp) (by simp) (by simp [NatTrans.shift_app_comm])))
        (F.map_distinguished _ hT) (G.map_distinguished _ hT) (by assumption) (by assumption))

end

section

variable {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]

instance : (P.map F).IsTriangulated := by
  convert inferInstanceAs (P.ι ⋙ F).essImage.IsTriangulated
  ext Y
  constructor
  · rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨⟨X, hX⟩, ⟨e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X.1, X.2, ⟨e⟩⟩


end

end

end ObjectProperty

namespace Triangulated

@[deprecated (since := "2025-07-21")]
alias Subcategory := ObjectProperty.IsTriangulated

namespace Subcategory

open ObjectProperty

@[deprecated (since := "2025-07-21")] alias mk' := IsTriangulatedClosed₂.mk'
@[deprecated (since := "2025-07-21")] alias ext₁ := ext_of_isTriangulatedClosed₁
@[deprecated (since := "2025-07-21")] alias ext₁' := ext_of_isTriangulatedClosed₁'
@[deprecated (since := "2025-07-21")] alias ext₂ := ext_of_isTriangulatedClosed₂
@[deprecated (since := "2025-07-21")] alias ext₂' := ext_of_isTriangulatedClosed₂'
@[deprecated (since := "2025-07-21")] alias ext₃ := ext_of_isTriangulatedClosed₃
@[deprecated (since := "2025-07-21")] alias ext₃' := ext_of_isTriangulatedClosed₃'
@[deprecated (since := "2025-07-21")] alias W := trW
@[deprecated (since := "2025-07-21")] alias W_iff := trW_iff
@[deprecated (since := "2025-07-21")] alias W_iff' := trW_iff'
@[deprecated (since := "2025-07-21")] alias W.mk := trW.mk
@[deprecated (since := "2025-07-21")] alias W.mk' := trW.mk'
@[deprecated (since := "2025-07-21")] alias isoClosure_W := trW_isoClosure
@[deprecated (since := "2025-07-21")] alias W_of_isIso := trW_of_isIso
@[deprecated (since := "2025-07-21")] alias smul_mem_W_iff := smul_mem_trW_iff
@[deprecated (since := "2025-07-21")] alias W.shift := trW.shift
@[deprecated (since := "2025-07-21")] alias W.unshift := trW.unshift
@[deprecated (since := "2025-07-21")]
alias mem_W_iff_of_distinguished := trW_iff_of_distinguished

end Subcategory

end Triangulated

end CategoryTheory
