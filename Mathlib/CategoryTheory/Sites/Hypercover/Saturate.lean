/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Homotopy
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Saturation of a `0`-hypercover

Given a `0`-hypercover `E`, we define a `1`-hypercover `E.saturate`
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

variable {C : Type*} [Category* C] {A : Type*} [Category* A]

open Limits

/-- A relation on a pre-`0`-hypercover is a commutative diagram
```
obj ----> E.X i
 |         |
 |         |
 v         v
E.X j ---> S
```
-/
structure Relation {S : C} (E : PreZeroHypercover S) (i j : E.I₀) where
  /-- The object. -/
  obj : C
  /-- The first projection. -/
  fst : obj ⟶ E.X i
  /-- The second projection. -/
  snd : obj ⟶ E.X j
  w : fst ≫ E.f i = snd ≫ E.f j

/-- The maximal pre-`1`-hypercover containing `E`, where the `1`-components are all relations
on `E`. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
def saturate {S : C} (E : PreZeroHypercover S) : PreOneHypercover S where
  __ := E
  I₁ := E.Relation
  Y _ _ r := r.obj
  p₁ _ _ r := r.fst
  p₂ _ _ r := r.snd
  w _ _ r := r.w

/-- For a presheaf of types, sections over the multifork associated to `E.saturate` are equivalent
to compatible families. -/
@[simps]
def sectionsSaturateEquiv {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ TypeCat) :
    (E.saturate.multicospanIndex F).sections ≃ Subtype (Presieve.Arrows.Compatible F E.f) where
  toFun s := ⟨s.val, fun i j _ _ _ hgij ↦ s.property ⟨(i, j), ⟨_, _, _, hgij⟩⟩⟩
  invFun s := ⟨s.val, fun r ↦ s.property _ _ _ _ _ r.snd.w⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma isLimit_saturate_type_iff {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ TypeCat) :
    Nonempty (IsLimit <| E.saturate.multifork F) ↔ E.presieve₀.IsSheafFor F := by
  rw [Multifork.isLimit_types_iff, Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← Function.Bijective.of_comp_iff' (E.sectionsSaturateEquiv F).symm.bijective]
  rfl

/-- If `E` has pairwise pullbacks, this is the canonical map from the minimal `1`-hypercover
to the saturation. -/
@[simps]
noncomputable
def toSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S) [E.HasPullbacks] :
    E.toPreOneHypercover ⟶ E.saturate where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨pullback (E.f i) (E.f j), _, _, pullback.condition⟩
  h₁ {i j} k := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- If `E` has pairwise pullbacks, this is the canonical map to the minimal `1`-hypercover
from the saturation. -/
@[simps]
noncomputable
def fromSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] : E.saturate ⟶ E.toPreOneHypercover where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨⟩
  h₁ {i j} k := pullback.lift k.fst k.snd k.w

variable {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]

/-- The identity of the minimal pre-`1`-hypercover when `E` has pairwise pullbacks
is homotopic to itself. -/
noncomputable
def toPreOneHypercoverHomotopy {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] :
    PreOneHypercover.Homotopy (.id E.toPreOneHypercover) (.id E.toPreOneHypercover) where
  H _ := ⟨⟩
  a i := pullback.diagonal (E.f i)
  wl := by simp
  wr := by simp

variable {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]

@[simp]
lemma toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks :
    E.toSaturateOfHasPullbacks.comp E.fromSaturateOfHasPullbacks = .id _ := by
  refine PreOneHypercover.Hom.ext' rfl (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The composition `E.saturate ⟶ E.toPreOneHypercover ⟶ E.saturate` is homotopic to the
identity. -/
noncomputable
def fromSaturateToSaturateHomotopy : PreOneHypercover.Homotopy
    (E.fromSaturateOfHasPullbacks.comp E.toSaturateOfHasPullbacks) (.id _) where
  H i := ⟨pullback (E.f i) (E.f i), pullback.fst _ _, pullback.snd _ _, pullback.condition⟩
  a i := pullback.diagonal (E.f i)
  wl i := by simp
  wr i := by simp

/-- If the pre-`0`-hypercover `E` has pairwise pullbacks, then the multifork associated to the
full saturated pre-`1`-hypercover is exact if and only if the minimal one given by taking
the pairwise pullbacks is exact. -/
noncomputable
def isLimitSaturateEquivOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ A) :
    IsLimit (E.saturate.multifork F) ≃ IsLimit (E.toPreOneHypercover.multifork F) :=
  PreOneHypercover.Homotopy.isLimitMultiforkEquiv E.fromSaturateOfHasPullbacks
    E.toSaturateOfHasPullbacks E.fromSaturateToSaturateHomotopy
    (by
      rw [toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks]
      exact E.toPreOneHypercoverHomotopy)

end CategoryTheory.PreZeroHypercover
