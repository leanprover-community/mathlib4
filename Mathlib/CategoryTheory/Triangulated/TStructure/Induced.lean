/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Induced t-structures

Let `t` be a t-structure on a pretriangulated cateogry `C`.
If `P` is a triangulated subcategory of `C`, we introduce a typeclass
`P.HasInducedTStructure t` which essentially says that up to isomorphisms
`P` is stable by the application of the truncation functors.

In particular, we show that the triangulated subcategory `t.plus`
of `t`-bounded above objects can be endowed with a t-structure `t.onPlus`,
and the same applis to `t.minus` and `t.bounded`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) (t : TStructure C)

namespace ObjectProperty

/-- The property that a full subcategory of a pretriangulated category
equipped with a t-structure can be endowed with an induced t-structure. -/
class HasInducedTStructure [P.IsTriangulated] : Prop where
  exists_triangle_zero_one (A : C) (hA : P A) :
    ∃ (X Y : C) (_ : t.IsLE X 0) (_ : t.IsGE Y 1)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧) (_ : Triangle.mk f g h ∈ distTriang C),
    P.isoClosure X ∧ P.isoClosure Y

variable [P.IsTriangulated] [h : P.HasInducedTStructure t]

/-- The t-structure induced on a full subcategory. -/
noncomputable def tStructure : TStructure P.FullSubcategory where
  le n X := t.le n X.obj
  ge n X := t.ge n X.obj
  le_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX ↦ (t.le n).prop_of_iso (P.ι.mapIso e) hX⟩
  ge_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX ↦ (t.ge n).prop_of_iso (P.ι.mapIso e) hX⟩
  le_shift n a n' h X hX := (t.le n').prop_of_iso ((P.ι.commShiftIso a).symm.app X)
      (t.le_shift n a n' h X.obj hX)
  ge_shift n a n' h X hX := (t.ge n').prop_of_iso ((P.ι.commShiftIso a).symm.app X)
    (t.ge_shift n a n' h X.obj hX)
  zero' {X Y} f hX hY := P.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (P.ι.map f) hX hY)
  le_zero_le X hX := t.le_zero_le _ hX
  ge_one_le X hX := t.ge_one_le _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', hX', ⟨e⟩⟩, ⟨Y', hY', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    exact ⟨⟨X', hX'⟩, ⟨Y', hY'⟩, (t.le 0).prop_of_iso e hX.le,
      (t.ge 1).prop_of_iso e' hY.ge,
      P.fullyFaithfulι.preimage (e.inv ≫ f),
      P.fullyFaithfulι.preimage (g ≫ e'.hom),
      P.fullyFaithfulι.preimage (e'.inv ≫ h ≫ e.hom⟦(1 : ℤ)⟧' ≫
          (P.ι.commShiftIso (1 : ℤ)).inv.app ⟨X', hX'⟩),
      isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e.symm (Iso.refl _) e'.symm)⟩

lemma tStructure_isLE_iff (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsLE X n ↔ t.IsLE X.obj n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

lemma tStructure_isGE_iff (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsGE X n ↔ t.IsGE X.obj n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/-- Constructor for `HasInducedTStructure`. -/
lemma HasInducedTStructure.mk' {P : ObjectProperty C} [P.IsTriangulated] {t : TStructure C}
    (h : ∀ (X : C) (_ : P X) (n : ℤ), P ((t.truncLE n).obj X) ∧ P ((t.truncGE n).obj X)) :
    P.HasInducedTStructure t where
  exists_triangle_zero_one X hX :=
      ⟨_, _, inferInstance, inferInstance, _, _, _,
        t.triangleLEGE_distinguished 0 1 (by lia) X,
          P.le_isoClosure _ ((h X hX _).1), P.le_isoClosure _ ((h X hX _).2)⟩

lemma mem_of_hasInductedTStructure (P : ObjectProperty C) [P.IsTriangulated] (t : TStructure C)
    [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) (h₂ : P T.obj₂)
    (h₃ : t.IsGE T.obj₃ n₁) :
    P T.obj₁ ∧ P T.obj₃ := by
  obtain ⟨e, _⟩ := t.triangle_iso_exists hT
    (P.ι.map_distinguished _ ((P.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) n₀ n₁ inferInstance inferInstance
      (by dsimp; rw [← P.tStructure_isLE_iff]; infer_instance)
      (by dsimp; rw [← P.tStructure_isGE_iff]; infer_instance)
  exact ⟨(P.prop_iff_of_iso (Triangle.π₁.mapIso e)).2 (P.prop_ι_obj _),
    (P.prop_iff_of_iso (Triangle.π₃.mapIso e)).2 (P.prop_ι_obj _)⟩

instance (P P' : ObjectProperty C) [P.IsTriangulated] [P'.IsTriangulated] (t : TStructure C)
    [P.HasInducedTStructure t] [P'.HasInducedTStructure t]
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms] :
    (P ⊓ P').HasInducedTStructure t :=
  .mk' (by
    rintro X ⟨hX, hX'⟩ n
    exact
      ⟨⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX (by dsimp; infer_instance)).1,
      (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).1⟩,
        ⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by lia) X)
        (n - 1) n (by lia) (by dsimp; infer_instance) hX (by dsimp; infer_instance)).2,
      (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by lia) X)
        (n - 1) n (by lia) (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).2⟩⟩)

end ObjectProperty

namespace Triangulated.TStructure

variable [IsTriangulated C]

instance : t.plus.HasInducedTStructure t :=
  .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

instance : t.minus.HasInducedTStructure t :=
  .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

instance : t.bounded.HasInducedTStructure t := by
  dsimp [bounded]
  infer_instance

/-- The t-structure induced on the full subcategory of `t`-bounded above objects. -/
noncomputable abbrev onPlus : TStructure t.plus.FullSubcategory := t.plus.tStructure t

/-- The t-structure induced on the full subcategory of `t`-bounded below objects. -/
noncomputable abbrev onMinus : TStructure t.minus.FullSubcategory := t.minus.tStructure t

/-- The t-structure induced on the full subcategory of `t`-bounded objects. -/
noncomputable abbrev onBounded : TStructure t.bounded.FullSubcategory := t.bounded.tStructure t

end Triangulated.TStructure

end CategoryTheory
