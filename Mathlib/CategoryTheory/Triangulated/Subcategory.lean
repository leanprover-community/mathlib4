/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Triangulated subcategories

In this file, given a pretriangulated category `C` and `P : ObjectProperty C`,
we introduce a typeclass `P.IsTriangulated` to express that `P`
is a triangulated subcategory of `C`. When `P` is a triangulated
subcategory, we introduce a class of morphisms `P.trW : MorphismProperty C`
consisting of the morphisms whose "cone" belongs to `P` (up to isomorphisms),
and we show that it has both calculus of left and right fractions.

We also show that `P.FullSubcategory` is equipped with a pretriangulated structure,
which is triangulated if `C` is.

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

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  {E : Type*} [Category* E] [HasShift E ℤ]

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

protected lemma distinguished_cocone_triangle [P.IsTriangulatedClosed₃]
    {X Y : C} (a : X ⟶ Y) (hX : P X) (hY : P Y) :
    ∃ (Z : C) (_ : P Z) (b : Y ⟶ Z) (c : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk a b c ∈ distTriang _ := by
  obtain ⟨Z, b, c, h⟩ := distinguished_cocone_triangle a
  obtain ⟨Z', hZ', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ h hX hY
  exact ⟨Z', hZ', b ≫ e.hom, e.inv ≫ c, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm )⟩

protected lemma distinguished_cocone_triangle₁ [P.IsTriangulatedClosed₁]
    {Y Z : C} (b : Y ⟶ Z) (hY : P Y) (hZ : P Z) :
    ∃ (X : C) (_ : P X) (a : X ⟶ Y) (c : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk a b c ∈ distTriang _ := by
  obtain ⟨X, a, c, h⟩ := distinguished_cocone_triangle₁ b
  obtain ⟨X', hX', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₁' _ h hY hZ
  exact ⟨X', hX', e.inv ≫ a, c ≫ e.hom⟦1⟧', isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _))⟩

protected lemma distinguished_cocone_triangle₂ [P.IsTriangulatedClosed₂]
    {X Z : C} (c : Z ⟶ X⟦(1 : ℤ)⟧) (hX : P X) (hZ : P Z) :
    ∃ (Y : C) (_ : P Y) (a : X ⟶ Y) (b : Y ⟶ Z), Triangle.mk a b c ∈ distTriang _ := by
  obtain ⟨Y, a, b, h⟩ := distinguished_cocone_triangle₂ c
  obtain ⟨Y', hY', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ h hX hZ
  exact ⟨Y', hY', a ≫ e.hom, e.inv ≫ b, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _))⟩

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

instance {Q : ObjectProperty C} [P.IsTriangulated] [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] :
    (P ⊓ Q).IsTriangulated where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨Y, hY, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' T hT h₁.1 h₃.1
    exact ⟨Y, ⟨hY, Q.prop_of_iso e (Q.ext_of_isTriangulatedClosed₂ T hT h₁.2 h₃.2)⟩, ⟨e⟩⟩

section

variable (Q R : ObjectProperty C)

/-- An object `X` satisfies `extensionProduct P Q` if there exists a distinguished triangle
`Y ⟶ X ⟶ Z ⟶ Y⟦1⟧` such that `Y` satisfies `P` and `Z` satisfies `Q`. -/
def extensionProduct : ObjectProperty C :=
  fun X => ∃ (Y Z : C) (f : Y ⟶ X) (g : X ⟶ Z) (h : Z ⟶ Y⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ P Y ∧ Q Z

lemma extensionProduct_iff (X : C) : extensionProduct P Q X ↔
  ∃ (Y Z : C) (f : Y ⟶ X) (g : X ⟶ Z) (h : Z ⟶ Y⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ P Y ∧ Q Z := Iff.rfl

instance [P.Nonempty] [Q.Nonempty] : (extensionProduct P Q).Nonempty := by
  obtain ⟨Y, f, g, hT⟩ := distinguished_cocone_triangle₂ (0 : Q.arbitrary ⟶ P.arbitrary⟦(1 : ℤ)⟧)
  exact ⟨_, _, _, _, _, _, hT, P.prop_arbitrary, Q.prop_arbitrary⟩

@[simp]
lemma extensionProduct_bot_left : extensionProduct ⊥ P = ⊥ := by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, h, _⟩
  exact h

@[simp]
lemma extensionProduct_bot_right : extensionProduct P ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, _, h⟩
  exact h

variable {P} in
lemma monotone_extensionProduct_left {P' : ObjectProperty C} (h : P ≤ P') :
    extensionProduct P Q ≤ extensionProduct P' Q := by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, h Y hP, hQ⟩

variable {Q} in
lemma monotone_extensionProduct_right {Q' : ObjectProperty C} (h : Q ≤ Q') :
    extensionProduct P Q ≤ extensionProduct P Q' := by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, hP, h Z hQ⟩

instance : (extensionProduct P Q).IsClosedUnderIsomorphisms where
  of_iso := by
    intro X X' i ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨Y, Z, f ≫ i.hom, i.inv ≫ g, h, ?_, hP, hQ⟩
    exact isomorphic_distinguished _ hT _ <| Triangle.isoMk _ _ (Iso.refl _) i.symm (Iso.refl _)

lemma extensionProduct_isoClosure_left :
    extensionProduct P.isoClosure Q = extensionProduct P Q := by
  refine le_antisymm ?_ (monotone_extensionProduct_left Q P.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, ⟨Y', hP, ⟨i⟩⟩, hQ⟩
  refine ⟨Y', Z, i.inv ≫ f, g, h ≫ i.hom⟦1⟧', ?_, hP, hQ⟩
  exact isomorphic_distinguished _ hT _ <| Triangle.isoMk _ _ i.symm (Iso.refl _) (Iso.refl _)

lemma extensionProduct_isoClosure_right :
    extensionProduct P Q.isoClosure = extensionProduct P Q := by
  refine le_antisymm ?_ (monotone_extensionProduct_right _ Q.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, hP, ⟨Z', hQ, ⟨i⟩⟩⟩
  refine ⟨Y, Z', f, g ≫ i.hom, i.inv ≫ h, ?_, hP, hQ⟩
  exact isomorphic_distinguished _ hT _ <| Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) i.symm

variable {P} in
lemma le_extensionProduct_left [Q.ContainsZero] : P ≤ extensionProduct P Q := by
  intro X hX
  rw [← extensionProduct_isoClosure_right]
  obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, contractible_distinguished X, hX, ?_⟩
  exact ⟨Z, hQ, ⟨IsZero.iso (isZero_zero C) hZ⟩⟩

variable {Q} in
lemma le_extensionProduct_right [P.ContainsZero] : Q ≤ extensionProduct P Q := by
  intro X hX
  rw [← extensionProduct_isoClosure_left]
  obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, inv_rot_of_distTriang _ (contractible_distinguished X), ?_, hX⟩
  exact ⟨Z, hP, ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero C)) hZ⟩⟩

instance [P.IsStableUnderShift ℤ] [Q.IsStableUnderShift ℤ] :
    (extensionProduct P Q).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := IsStableUnderShiftBy.mk <| by
    intro X ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨_, _, _, _, _, Triangle.shift_distinguished _ hT a, ?_, ?_⟩
    all_goals apply IsStableUnderShiftBy.le_shift; assumption

@[stacks 0FX1]
lemma extensionProduct_assoc [IsTriangulated C] :
    extensionProduct (extensionProduct P Q) R = extensionProduct P (extensionProduct Q R) := by
  ext X
  constructor
  · intro ⟨Y, C, f, g, h, hT, ⟨A, B, f', g', h', hT', hP, hQ⟩, hR⟩
    obtain ⟨Y, g'', h'', hT''⟩ := distinguished_cocone_triangle (f' ≫ f)
    let o := someOctahedron rfl hT' hT hT''
    exact ⟨_, _, _, _, _, hT'', hP, ⟨_, _, _, _, _, o.mem, hQ, hR⟩⟩
  · intro ⟨A, Z, f, g, h, hT, hP, ⟨B, C, f', g', h', hT', hQ, hR⟩⟩
    obtain ⟨Y, f'', h'', hT''⟩ := distinguished_cocone_triangle₁ (g ≫ g')
    let o := someOctahedron' rfl hT hT' hT''
    exact ⟨_, _, _, _, _, hT'', ⟨_, _, _, _, _, o.mem, hP, hQ⟩, hR⟩

lemma extensionProduct_le_of_isTriangulatedClosed₂' {P₁ P₂ Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] (h₁ : P₁ ≤ Q) (h₂ : P₂ ≤ Q) :
    extensionProduct P₁ P₂ ≤ Q.isoClosure := by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂' Q _ hT (h₁ _ hY) (h₂ _ hZ)

lemma extensionProduct_le_of_isTriangulatedClosed₂ {P₁ P₂ Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] [Q.IsClosedUnderIsomorphisms] (h₁ : P₁ ≤ Q) (h₂ : P₂ ≤ Q) :
    extensionProduct P₁ P₂ ≤ Q := by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂ Q _ hT (h₁ _ hY) (h₂ _ hZ)

@[stacks 0FX2 "first part"]
lemma extensionProduct_retractClosure_retractClosure_le :
    extensionProduct P.retractClosure Q.retractClosure ≤
      (extensionProduct P Q).retractClosure := by
  intro X ⟨A, B, f₁, f₂, f₃, hT, ⟨A', hP, ⟨a₁, b₁, h₁⟩⟩, ⟨B', hQ, ⟨a₃, b₃, h₃⟩⟩⟩
  obtain ⟨X', g₁, g₂, hT'⟩ := distinguished_cocone_triangle₂ (b₃ ≫ f₃ ≫ a₁⟦(1 : ℤ)⟧')
  obtain ⟨a₂ : X ⟶ X', ha₁₂, ha₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT hT' a₁ a₃ (by dsimp; grind)
  obtain ⟨b₂ : X' ⟶ X, hb₁₂, hb₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT' hT b₁ b₃ (by dsimp; grind)
  dsimp at ha₁₂ ha₂₃ hb₁₂ hb₂₃
  refine ⟨X', ⟨_, _, _, _, _, hT', hP, hQ⟩, ⟨?_⟩⟩
  let φ := Triangle.homMk (Triangle.mk f₁ f₂ f₃) (Triangle.mk f₁ f₂ f₃) (𝟙 A)
    (a₂ ≫ b₂) (𝟙 B) (by dsimp; grind) (by dsimp; grind)
  haveI : IsIso (a₂ ≫ b₂) := isIso₂_of_isIso₁₃ φ hT hT (IsIso.id _) (IsIso.id _)
  exact ⟨a₂, b₂ ≫ inv (a₂ ≫ b₂), by grind⟩

@[stacks 0FX2 "second part"]
lemma retractClosure_extensionProduct_retractClosure_retractClosure :
    (extensionProduct P.retractClosure Q.retractClosure).retractClosure =
      (extensionProduct P Q).retractClosure := by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProduct_retractClosure_retractClosure_le P Q
  · apply monotone_retractClosure
    grw [monotone_extensionProduct_right _ (le_retractClosure Q),
      monotone_extensionProduct_left _ (le_retractClosure P)]

/-- All objects that can be reached by exactly `n` extensions from objects in `P`. -/
def extensionProductIter (n : ℕ) : ObjectProperty C := (extensionProduct P)^[n] P

@[simp]
lemma extensionProductIter_zero : P.extensionProductIter 0 = P := rfl

lemma extensionProductIter_succ (n : ℕ) :
    P.extensionProductIter (n + 1) = extensionProduct P (P.extensionProductIter n) :=
  Function.iterate_succ_apply' _ _ _

lemma extensionProductIter_succ' [IsTriangulated C] (n : ℕ) :
    P.extensionProductIter (n + 1) = extensionProduct (P.extensionProductIter n) P := by
  induction n with
  | zero => rfl
  | succ n h =>
    rw [extensionProductIter_succ, h, ← extensionProduct_assoc, ← extensionProductIter_succ, ← h]

instance [P.Nonempty] (n : ℕ) : (P.extensionProductIter n).Nonempty := by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n h => rw [extensionProductIter_succ]; infer_instance

lemma extensionProductIter_add [IsTriangulated C] {n m n' : ℕ} (h : n = n' + 1) :
    P.extensionProductIter (n + m) =
      extensionProduct (P.extensionProductIter n') (P.extensionProductIter m) := by
  induction m with
  | zero => rw [add_zero, extensionProductIter_zero, h, extensionProductIter_succ']
  | succ m hm =>
    rw [← add_assoc, extensionProductIter_succ', extensionProductIter_succ', hm,
      extensionProduct_assoc]

lemma extensionProductIter_add' [IsTriangulated C] {n m m' : ℕ} (h : m = m' + 1) :
    P.extensionProductIter (n + m) =
      extensionProduct (P.extensionProductIter n) (P.extensionProductIter m') := by
  induction n with
  | zero => rw [zero_add, extensionProductIter_zero, h, extensionProductIter_succ]
  | succ n hn => rw [add_assoc, add_comm 1 m, ← add_assoc, extensionProductIter_succ,
    extensionProductIter_succ, hn, extensionProduct_assoc]

variable {P} in
lemma monotone_extensionProductIter {Q : ObjectProperty C} (hPQ : P ≤ Q) (n : ℕ) :
    P.extensionProductIter n ≤ Q.extensionProductIter n := by
  induction n with
  | zero => exact hPQ
  | succ n h => grw [extensionProductIter_succ, extensionProductIter_succ,
    monotone_extensionProduct_left _ hPQ, monotone_extensionProduct_right _ h]

lemma monotone'_extensionProductIter [P.ContainsZero] {n m : ℕ} (h : n ≤ m) :
    P.extensionProductIter n ≤ P.extensionProductIter m := by
  induction m, h using Nat.le_induction
  case base => rfl
  case succ n m hnm h =>
    refine le_trans h ?_
    rw [extensionProductIter_succ]
    exact le_extensionProduct_right P

lemma le_extensionProductIter [P.ContainsZero] (n : ℕ) : P ≤ P.extensionProductIter n :=
  P.monotone'_extensionProductIter (Nat.zero_le n)

@[simp]
lemma extensionProductIter_bot (n : ℕ) : extensionProductIter (⊥ : ObjectProperty C) n = ⊥ := by
  cases n
  case zero => rw [extensionProductIter_zero]
  case succ n => rw [extensionProductIter_succ, extensionProduct_bot_left]

@[simp]
lemma extensionProductIter_top (n : ℕ) : extensionProductIter (⊤ : ObjectProperty C) n = ⊤ :=
  eq_top_iff.mpr (le_extensionProductIter _ n)

instance [P.IsStableUnderShift ℤ] (n : ℕ) : (P.extensionProductIter n).IsStableUnderShift ℤ := by
  induction n with
  | zero => assumption
  | succ n h =>
    rw [extensionProductIter_succ]
    infer_instance

lemma extensionProductIter_le_of_isTriangulatedClosed₂' {Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] (h : P ≤ Q) (n : ℕ) : P.extensionProductIter n ≤ Q.isoClosure := by
  induction n with
  | zero =>
    rw [extensionProductIter_zero]
    exact h.trans Q.le_isoClosure
  | succ n H =>
    rw [extensionProductIter_succ]
    exact extensionProduct_le_of_isTriangulatedClosed₂ (h.trans Q.le_isoClosure) H

lemma extensionProductIter_le_of_isTriangulatedClosed₂ {Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] [Q.IsClosedUnderIsomorphisms] (h : P ≤ Q) (n : ℕ) :
    P.extensionProductIter n ≤ Q :=
  Q.isoClosure_eq_self ▸ P.extensionProductIter_le_of_isTriangulatedClosed₂' h n

instance [P.IsStableUnderShift ℤ] (n : ℕ) : (P.extensionProductIter n).IsStableUnderShift ℤ := by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n H => rw [extensionProductIter_succ]; infer_instance

lemma extensionProductIter_retractClosure_le {n : ℕ} :
    (P.retractClosure.extensionProductIter n) ≤ (P.extensionProductIter n).retractClosure := by
  induction n with
  | zero => simp
  | succ n H =>
    grw [extensionProductIter_succ, extensionProductIter_succ, monotone_extensionProduct_right _ H,
      extensionProduct_retractClosure_retractClosure_le]

lemma retractClosure_extensionProductIter_retractClosure {n : ℕ} :
    (P.retractClosure.extensionProductIter n).retractClosure =
      (P.extensionProductIter n).retractClosure := by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProductIter_retractClosure_le P
  · exact monotone_retractClosure (monotone_extensionProductIter (le_retractClosure P) n)

end

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

variable {P} in
lemma trW_monotone {Q : ObjectProperty C} (h : P ≤ Q) : P.trW ≤ Q.trW := by
  intro X Y f hf
  rw [trW_iff] at hf ⊢
  obtain ⟨Z, a, b, hT, hZ⟩ := hf
  exact ⟨Z, a, b, hT, h _ hZ⟩

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
lemma trW_of_isIso [P.ContainsZero] {X Y : C} (f : X ⟶ Y) [IsIso f] : P.trW f := by
  refine (P.trW.arrow_mk_iso_iff ?_).1 (MorphismProperty.id_mem _ X)
  exact Arrow.isoMk (Iso.refl _) (asIso f)

set_option backward.isDefEq.respectTransparency false in
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

lemma trW_iff_of_distinguished' [P.IsStableUnderShift ℤ]
    [P.IsClosedUnderIsomorphisms] (T : Triangle C) (hT : T ∈ distTriang C) :
    P.trW T.mor₂ ↔ P T.obj₁ := by
  simpa [P.prop_shift_iff_of_isStableUnderShift]
    using P.trW_iff_of_distinguished _ (rot_of_distTriang _ hT)

section

variable (F : D ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

instance [P.IsTriangulated] : (P.inverseImage F).IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    P.ext_of_isTriangulatedClosed₂ _ (F.map_distinguished T hT) h₁ h₃)

lemma inverseImage_trW_iff {X Y : D} (s : X ⟶ Y) :
    (P.inverseImage F).trW s ↔ P.trW (F.map s) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have eq₁ := (P.inverseImage F).trW_iff_of_distinguished _ hT
  have eq₂ := P.trW_iff_of_distinguished _ (F.map_distinguished _ hT)
  dsimp at eq₁ eq₂
  rw [eq₁, prop_inverseImage_iff, eq₂]

lemma inverseImage_trW_isInverted {E : Type*} [Category E]
    (L : C ⥤ E) [L.IsLocalization P.trW] :
    (P.inverseImage F).trW.IsInvertedBy (F ⋙ L) :=
  fun X Y f hf => Localization.inverts L P.trW (F.map f)
    (by simpa only [inverseImage_trW_iff] using hf)

end

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

instance (P' : ObjectProperty C) [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    [P'.IsTriangulatedClosed₂] :
    (P ⊓ P').IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨X₂, h₂, ⟨e⟩⟩ := P'.ext_of_isTriangulatedClosed₂' T hT h₁.2 h₃.2
    exact ⟨X₂, ⟨P.prop_of_iso e (P.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1), h₂⟩, ⟨e⟩⟩

instance (P' : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P'.IsTriangulated] :
    (P ⊓ P').IsTriangulated where

instance [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_ (P.ext_of_isTriangulatedClosed₂ _
      (binaryProductTriangle_distinguished _ _)
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

instance [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderFiniteProducts := .mk'

instance [P.IsTriangulated] : P.trW.IsStableUnderFiniteProducts := by
  rw [← trW_isoClosure]
  exact ⟨fun J _ => by
    refine MorphismProperty.IsStableUnderProductsOfShape.mk _ _ ?_
    intro _ _ X₁ X₂ f hf
    exact trW.mk _ (productTriangle_distinguished _
      (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose))
      (P.isoClosure.prop_pi _
        (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose_spec))⟩

section

variable [P.IsTriangulated]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : Pretriangulated P.FullSubcategory where
  distinguishedTriangles := P.ι.mapTriangle.obj ⁻¹' (distTriang C)
  isomorphic_distinguished T₁ hT₁ T₂ e :=
    isomorphic_distinguished _ hT₁ _ (P.ι.mapTriangle.mapIso e)
  contractible_distinguished X :=
    isomorphic_distinguished _ (contractible_distinguished (P.ι.obj X)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) P.ι.mapZeroObject)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z', g', h', mem⟩ := distinguished_cocone_triangle (P.ι.map f)
    obtain ⟨Z'', hZ'', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ mem X.2 Y.2
    exact ⟨⟨Z'', hZ''⟩, P.fullyFaithfulι.preimage (g' ≫ e.hom),
      P.fullyFaithfulι.preimage (e.inv ≫ h' ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app X),
      isomorphic_distinguished _ mem _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm)⟩
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (P.ι.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (P.ι.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism (P.ι.mapTriangle.obj T₁)
      (P.ι.mapTriangle.obj T₂) hT₁ hT₂ (P.ι.map a) (P.ι.map b)
      (by simpa using P.ι.congr_map comm)
    refine ⟨P.fullyFaithfulι.preimage c, ⟨by cat_disch, ?_⟩⟩
    ext
    have := P.ι.commShiftIso_hom_naturality a (1 : ℤ)
    rw [← cancel_mono ((Functor.commShiftIso P.ι (1 : ℤ)).hom.app T₂.obj₁)]
    cat_disch

instance : P.ι.IsTriangulated where
  map_distinguished _ hT := hT

instance [IsTriangulated C] : IsTriangulated P.FullSubcategory :=
  IsTriangulated.of_fully_faithful_triangulated_functor P.ι

set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full] :
    F.essImage.IsTriangulated where
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
      (isoTriangleOfIso₁₃ _ _ (F.map_distinguished _ H) hT e₁ e₃
        (by simp [hh, ← Functor.map_comp]))⟩⟩)

instance isTriangulated_lift (F : E ⥤ C) (hF : ∀ (X : E), P (F.obj X))
    [Preadditive E] [F.CommShift ℤ] [HasZeroObject E]
    [∀ (n : ℤ), (shiftFunctor E n).Additive] [Pretriangulated E] [F.IsTriangulated] :
    (P.lift F hF).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (P.liftCompιIso F hF)]
  infer_instance

instance {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full] :
    (P.map F).IsTriangulated := by
  rw [← F.essImage_ι_comp]
  infer_instance

end

end ObjectProperty

end CategoryTheory
