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

/-! ## Definition and basic properties -/

/-- The length of a path is the arc length of its underlying map on the unit interval. -/
def length (γ : Path a b) : ℝ≥0∞ :=
  arcLength γ 0 1

/-- The length of a path agrees with the variation of its underlying map on `Set.univ`. -/
theorem length_eq_eVariationOn (γ : Path a b) : γ.length = eVariationOn γ univ := by
  rw [length, arcLength, ← univ_eq_Icc]

/-- The endpoint distance of a path is bounded above by its length. -/
theorem edist_le_length (γ : Path a b) : edist a b ≤ γ.length := by
    simp_rw [length, ← γ.source, ← γ.target]
    exact edist_le_arcLength _ zero_le_one

/-- The constant path has zero length. -/
@[simp]
theorem length_refl (x : E) : (refl x).length = 0 :=
  arcLength_eq_zero_of_constantOn (refl x) (a := 0) (b := 1) (by simp)

/-- Reversing a path does not change its length. -/
@[simp]
theorem length_symm (γ : Path a b) : γ.symm.length = γ.length := by
  rw [length, length, symm_eq_comp γ,
    arcLength_comp_eq_of_antitoneOn _ _
      (strictAnti_symm.antitone.antitoneOn (Icc (0 : I) 1))
      (symm_image_Icc 0 1 nonneg'),
    symm_one, symm_zero]

/-! ## Auxiliary lemmas for concatenation -/

/-- The length of a path is the variation of its extension on `[0,1]`. -/
lemma length_eq_eVariationOn_extend (γ : Path a b) :
    γ.length = eVariationOn γ.extend (Icc (0 : ℝ) 1) := by
  rw [length_eq_eVariationOn, ← extend_comp_subtype_val γ, eVariationOn.comp_eq_of_monotoneOn _ _
    ((Subtype.mono_coe _).monotoneOn univ), Subtype.coe_image_univ I]

/-- Auxiliary lemma: the affine map `t ↦ 2t` sends the left half
of the unit interval onto `[0,1]`. -/
private lemma image_double_Icc_half :
    (fun t : I ↦ (2 : ℝ) * t) '' Icc (0 : I) ((⟨(1 / 2 : ℝ), by norm_num⟩ : I))
        = Icc (0 : ℝ) 1 := by
  simp [ContinuousOn.image_Icc_of_monotoneOn nonneg' (by fun_prop)
    (Subtype.mono_coe _ |>.const_mul zero_le_two |>.monotoneOn _)]

/-- Auxiliary lemma: the arc length of the left half of `γ.symm`
is the arc length of the right half of `γ`. -/
private lemma arcLength_symm_left_half (γ : Path a b) :
    arcLength γ.symm 0 ((⟨(1 / 2 : ℝ), by norm_num⟩ : I)) =
      arcLength γ ((⟨(1 / 2 : ℝ), by norm_num⟩ : I)) 1 := by
  rw [arcLength, symm_eq_comp γ,
    eVariationOn.comp_eq_of_antitoneOn γ σ fun _ _ _ _ hxy => symm_le_symm.mpr hxy,
    symm_image_Icc 0 ((⟨(1 / 2 : ℝ), by norm_num⟩ : I)) nonneg', symm_half,
    symm_zero, arcLength]

/-! ## Length of concatenations -/

/-- Auxiliary lemma: the arc length of a concatenation on its left half
is the length of the first path. -/
private lemma arcLength_trans_left (γ : Path a b) (η : Path b c) :
    arcLength (γ.trans η) 0 ((⟨(1 / 2 : ℝ), by norm_num⟩ : I)) = γ.length := by
  calc
    _ = eVariationOn (γ.extend ∘ fun t : I ↦ 2 * t) (Icc 0 ((⟨(1 / 2 : ℝ), by norm_num⟩ : I))) := by
          rw [arcLength]
          refine eVariationOn.congr fun t ht => ?_
          rw [Function.comp_apply, ← Path.extend_apply, Path.extend_trans_of_le_half γ η ht.2]
    _ = eVariationOn γ.extend (Icc 0 1) := by
          rw [eVariationOn.comp_eq_of_monotoneOn _ _
            ((Subtype.mono_coe _ |>.const_mul zero_le_two |>.monotoneOn _)), image_double_Icc_half]
    _ = γ.length := (length_eq_eVariationOn_extend γ).symm

/-- Auxiliary lemma: the arc length of a concatenation on its right half
is the length of the second path. -/
private lemma arcLength_trans_right (γ : Path a b) (η : Path b c) :
    arcLength (γ.trans η) ((⟨(1 / 2 : ℝ), by norm_num⟩ : I)) 1 = η.length := by
  rw [← arcLength_symm_left_half (γ := γ.trans η), Path.trans_symm, ← length_symm]
  exact arcLength_trans_left η.symm γ.symm

/-- The length of a concatenation is the sum of the lengths of the two pieces. -/
theorem length_trans (γ : Path a b) (η : Path b c) :
    (γ.trans η).length = γ.length + η.length := by
  rw [length_eq_eVariationOn, univ_eq_Icc, ← Icc_union_Icc_eq_Icc nonneg' le_one',
    eVariationOn.union _ (isGreatest_Icc nonneg') (isLeast_Icc le_one'),
    ← arcLength, arcLength_trans_left, ← arcLength, arcLength_trans_right]

end

end Path
