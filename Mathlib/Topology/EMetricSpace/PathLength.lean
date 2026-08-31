/-
Copyright (c) 2026 Zhenhua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhenhua Wu
-/
module

public import Mathlib.Topology.EMetricSpace.ArcLength
public import Mathlib.Topology.Path

/-!
# Length of paths

This file defines the length of a path in a `WeakPseudoEMetricSpace` as the arc length of the
underlying map on the unit interval, equivalently as its variation on `Set.univ`, and develops
the basic API for this definition.

## Main declarations

* `Path.length`: the length of a path, defined as `arcLength γ 0 1`.
* `Path.length_eq_eVariationOn`: `Path.length` agrees with `eVariationOn` on `Set.univ`.
* `Path.edist_le_length`: the endpoint distance is bounded above by the length.
* `Path.length_symm`: reversing a path does not change its length.
* `Path.length_trans`: the length of a concatenation is the sum of the lengths.

## TODO

* Prove that path length is invariant under reparametrization. (@Zeta-Wu)
-/

open scoped ENNReal
open Set unitInterval

namespace Path

@[expose] public noncomputable section

variable {E : Type*} [TopologicalSpace E] [WeakPseudoEMetricSpace E] {a b c : E}

local notation "half" => (⟨1 / 2, by norm_num⟩ : I)

/-- Auxiliary lemma: the symmetry of the unit interval fixes `half`. -/
private lemma symm_half : σ half = half := by
  ext
  norm_num [unitInterval.symm]

/-! ## Definition and basic properties -/

/-- The length of a path is the arc length of its underlying map on the unit interval. -/
def length (γ : Path a b) : ℝ≥0∞ :=
  arcLength γ 0 1

/-- The length of a path agrees with the variation of its underlying map on `Set.univ`. -/
theorem length_eq_eVariationOn (γ : Path a b) :
    γ.length = eVariationOn γ Set.univ := by
  rw [length, arcLength, ← unitInterval.univ_eq_Icc]

/-- The endpoint distance of a path is bounded above by its length. -/
theorem edist_le_length (γ : Path a b) :
    edist a b ≤ γ.length :=
  calc
    _ = edist (γ 0) (γ 1) := by rw [γ.source, γ.target]
    _ ≤ arcLength γ 0 1 := edist_le_arcLength γ (a := 0) (b := 1) zero_le_one
    _ = γ.length := by rw [length]

/-- The constant path has zero length. -/
@[simp]
theorem length_refl (x : E) :
    (refl x).length = 0 := by
  rw [length_eq_eVariationOn]
  exact eVariationOn.constant_on (f := refl x) (s := Set.univ) (by simp)

/-- Reversing a path does not change its length. -/
@[simp]
theorem length_symm (γ : Path a b) :
    γ.symm.length = γ.length := by
  rw [length_eq_eVariationOn, length_eq_eVariationOn, symm_eq_comp γ,
    eVariationOn.comp_eq_of_antitoneOn _ _
    (unitInterval.strictAnti_symm.antitone.antitoneOn univ),
    image_univ_of_surjective unitInterval.symm_bijective.surjective]

/-! ## Auxiliary lemmas for concatenation -/

/-- The length of a path is the variation of its extension on `[0,1]`. -/
lemma length_eq_eVariationOn_extend (γ : Path a b) :
    γ.length = eVariationOn γ.extend (Icc (0 : ℝ) 1) := by
  rw [length_eq_eVariationOn, ← restrict_extend γ, eVariationOn.comp_eq_of_monotoneOn _ _
    ((Subtype.mono_coe _).monotoneOn univ), Subtype.coe_image_univ I]

/-- Auxiliary lemma: the affine map `t ↦ 2t` sends the left half
of the unit interval onto `[0,1]`. -/
private lemma image_double_Icc_half :
    (fun t : I ↦ (2 : ℝ) * t) '' Icc (0 : I) half = Icc (0 : ℝ) 1 := by
  rw [ContinuousOn.image_Icc_of_monotoneOn nonneg' (by fun_prop)
    (Subtype.mono_coe _ |>.const_mul zero_le_two |>.monotoneOn _)]
  simp

/-- Auxiliary lemma: the variation of the left half of `γ.symm`
is the variation of the right half of `γ`. -/
private lemma eVariationOn_symm_Icc_left_half (γ : Path a b) :
    eVariationOn γ.symm (Icc 0 half) = eVariationOn γ (Icc half 1) := by
  rw [symm_eq_comp γ]
  calc
    _ = eVariationOn γ (σ '' Icc (0 : I) half) :=
        eVariationOn.comp_eq_of_antitoneOn γ σ fun _ _ _ _ hxy => symm_le_symm.mpr hxy
    _ = eVariationOn γ (Icc half 1) := by
        rw [ContinuousOn.image_Icc_of_antitoneOn nonneg'
          ((unitInterval.continuous_symm.continuousOn : ContinuousOn σ (Icc 0 half)))
          (strictAnti_symm.antitone.antitoneOn _), symm_half, symm_zero]

/-! ## Length of concatenations -/
/-- Auxiliary lemma: the variation of a concatenation on its left half
is the length of the first path. -/
private lemma eVariationOn_trans_left (γ : Path a b) (η : Path b c) :
    eVariationOn (γ.trans η) (Icc 0 half) = γ.length := by
  calc
    _ = eVariationOn (γ.extend ∘ fun t : I ↦ 2 * t) (Icc 0 half) := by
          refine eVariationOn.congr fun t ht => ?_
          rw [Function.comp_apply, ← Path.extend_apply, Path.extend_trans_of_le_half γ η ht.2]
    _ = eVariationOn γ.extend (Icc 0 1) := by
          rw [eVariationOn.comp_eq_of_monotoneOn _ _
            ((Subtype.mono_coe _ |>.const_mul zero_le_two |>.monotoneOn _)), image_double_Icc_half]
    _ = γ.length := (length_eq_eVariationOn_extend γ).symm

/-- Auxiliary lemma: the variation of a concatenation on its right half
is the length of the second path. -/
private lemma eVariationOn_trans_right (γ : Path a b) (η : Path b c) :
    eVariationOn (γ.trans η) (Icc half 1) = η.length := by
  calc
    _ = eVariationOn (γ.trans η).symm (Icc 0 half) :=
      (eVariationOn_symm_Icc_left_half (γ.trans η)).symm
    _ = η.length := by
      rw [← length_symm, Path.trans_symm]
      exact eVariationOn_trans_left η.symm γ.symm

/-- The length of a concatenation is the sum of the lengths of the two pieces. -/
theorem length_trans (γ : Path a b) (η : Path b c) :
    (γ.trans η).length = γ.length + η.length := by
  rw [length_eq_eVariationOn, univ_eq_Icc, ← Icc_union_Icc_eq_Icc nonneg' le_one',
    eVariationOn.union _ (isGreatest_Icc nonneg') (isLeast_Icc le_one'),
    eVariationOn_trans_left, eVariationOn_trans_right]

end

end Path
