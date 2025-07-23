/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Shift.Localization

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

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

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
