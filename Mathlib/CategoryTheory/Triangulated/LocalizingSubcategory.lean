/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated

/-!
# Localizing subcategories

Let `C` be a pretriangulated category. If `A` and `B` are triangulated
subcategories of `C`, we define predicates (typeclasses
`IsTriangulatedRightLocalizing` and `IsTriangulatedLeftLocalizing`)
saying that `A` is right `B`-localizing (or left `B`-localizing).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*,
  Proposition 2.3.5, Chapitre II][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Opposite

namespace ObjectProperty

variable {C D D' : Type*} [Category* C] [Category* D] [Category* D']

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
right `B`-localizing if any morphism `X ⟶ Y` with `X` in `B` and
`Y` in `A` factors through an object that is in `A` and `B`.
See `isTriangulatedRightLocalizing_iff` for another characterization. -/
class IsTriangulatedRightLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : B X) (hY : A Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
left `B`-localizing if any morphism `X ⟶ Y` with `X` in `A` and
`Y` in `B` factors through an object that is in `A` and `B`.
See `isTriangulatedLeftLocalizing_iff` for another characterization. -/
class IsTriangulatedLeftLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : A X) (hY : B Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

instance (A B : ObjectProperty C) [A.IsTriangulatedLeftLocalizing B] :
    A.op.IsTriangulatedRightLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ :=
      IsTriangulatedLeftLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsTriangulatedLeftLocalizing B] :
    A.unop.IsTriangulatedRightLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsTriangulatedLeftLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

instance (A B : ObjectProperty C) [A.IsTriangulatedRightLocalizing B] :
    A.op.IsTriangulatedLeftLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsTriangulatedRightLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsTriangulatedRightLocalizing B] :
    A.unop.IsTriangulatedLeftLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsTriangulatedRightLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

variable (A B : ObjectProperty C)

lemma isTriangulatedLeftLocalizing_op_iff :
    A.op.IsTriangulatedLeftLocalizing B.op ↔ A.IsTriangulatedRightLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsTriangulatedRightLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩

lemma isTriangulatedRightLocalizing_op_iff :
    A.op.IsTriangulatedRightLocalizing B.op ↔ A.IsTriangulatedLeftLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsTriangulatedLeftLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

lemma isTriangulatedRightLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsTriangulatedRightLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A X) (_ : B.trW s),
        ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' := by
  refine ⟨fun _ X Y s hX hs ↦ ?_, fun hA ↦ ⟨fun {X Y} f hX hY ↦ ?_⟩⟩
  · rw [ObjectProperty.trW_iff'] at hs
    obtain ⟨W, a, b, hT, hW⟩ := hs
    obtain ⟨W', c, d, h₁, h₂, fac⟩ := IsTriangulatedRightLocalizing.fac a hW hX
    obtain ⟨U, hU, e, f, hT'⟩ := A.distinguished_cocone_triangle d h₁ hX
    obtain ⟨g, hg, _⟩ := complete_distinguished_triangle_morphism _ _ hT hT'
      c (𝟙 _) (by cat_disch)
    refine ⟨U, e, g, hU, ?_, by cat_disch⟩
    rw [ObjectProperty.trW_iff']
    exact ⟨_, _, _, hT', h₁, h₂⟩
  · obtain ⟨Z, s, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    have hs : B.trW s := by
      rw [trW_iff']
      exact ⟨_, _, _, hT, hX⟩
    obtain ⟨W, s', g, hW, hs', fac⟩ := hA s hY hs
    obtain ⟨U, hU, a, c, hT'⟩ := A.distinguished_cocone_triangle₁ s' hY hW
    obtain ⟨t, ht, ht'⟩ :=
      complete_distinguished_triangle_morphism₁ _ _ hT hT' (𝟙 Y) g (by cat_disch)
    exact ⟨U, t, a, hU, (B.trW_iff_of_distinguished' _ hT').1 (trW_monotone (by simp) _ hs'),
      by cat_disch⟩

variable {A B} in
lemma IsTriangulatedRightLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsTriangulatedRightLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hX : A X) (hs : B.trW s) :
    ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' :=
  (isTriangulatedRightLocalizing_iff A B).1 inferInstance s hX hs

lemma isTriangulatedLeftLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsTriangulatedLeftLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A Y) (_ : B.trW s),
        ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' := by
  rw [← isTriangulatedRightLocalizing_op_iff, isTriangulatedRightLocalizing_iff]
  refine ⟨fun hA X Y s hY hs ↦ ?_, fun hA X Y s hX hs ↦ ?_⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.op hY (by simpa [trW_op_iff])
    exact ⟨Z'.unop, s'.unop, b.unop, hZ', trW_of_op _ hs', by cat_disch⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.unop hX (trW_of_op _ hs)
    exact ⟨_, s'.op, b.op, hZ', trW_of_unop _ hs', by cat_disch⟩

variable {A B} in
lemma IsTriangulatedLeftLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsTriangulatedLeftLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hY : A Y) (hs : B.trW s) :
    ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' :=
  (isTriangulatedLeftLocalizing_iff A B).1 inferInstance s hY hs

end ObjectProperty

end CategoryTheory
