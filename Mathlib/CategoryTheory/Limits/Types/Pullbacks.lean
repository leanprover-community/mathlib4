/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# Lemmas on pullbacks in the category of types

We show some additional lemmas for pullbacks in the category of types.
-/

universe u

namespace CategoryTheory.Limits.Types

variable {P X Y Z : Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma range_fst_of_isPullback (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  let e := h.isoPullback ≪≫ Types.pullbackIsoPullback f g
  have : fst = _root_.Prod.fst ∘ Subtype.val ∘ e.hom := by
    ext p
    suffices fst p = pullback.fst f g (h.isoPullback.hom p) by simpa
    rw [← types_comp_apply h.isoPullback.hom (pullback.fst f g), IsPullback.isoPullback_hom_fst]
  rw [this, Set.range_comp, Set.range_comp, Set.range_eq_univ.mpr (surjective_of_epi e.hom)]
  ext
  simp [eq_comm]

lemma range_snd_of_isPullback (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  rw [range_fst_of_isPullback (IsPullback.flip h)]

variable (f g)

@[simp]
lemma range_pullbackFst : Set.range (pullback.fst f g) = f ⁻¹' Set.range g :=
  range_fst_of_isPullback (.of_hasPullback f g)

@[simp]
lemma range_pullbackSnd : Set.range (pullback.snd f g) = g ⁻¹' Set.range f :=
  range_snd_of_isPullback (.of_hasPullback f g)

end CategoryTheory.Limits.Types
