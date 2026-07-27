/-
Copyright (c) 2026 Zhenhua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhenhua Wu
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Path

/-!
# Length of paths

This file defines the length of a path in a `PseudoEMetricSpace` as its variation on the unit
interval. It also establishes the basic properties of path length that are needed in later files:
the endpoint distance bound, invariance under reversal, and additivity under concatenation.

## Main declarations

- `Path.length`: the length of a path, defined as its variation on the unit interval.
- `Path.edist_le_length`: the endpoint distance is bounded above by the length.
- `Path.length_symm`: reversing a path does not change its length.
- `Path.length_trans`: the length of a concatenation is the sum of the lengths.

## TODO

- Prove that path length is invariant under reparametrization.
-/

open scoped ENNReal
open Set unitInterval

namespace Path

@[expose] public section

noncomputable section

variable {E : Type*} [PseudoEMetricSpace E] {a b c : E}

local notation "half" => (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ : I)

private lemma zero_le_half : (0 : I) ≤ half := by
  change (0 : ℝ) ≤ (1 / 2 : ℝ)
  norm_num

private lemma half_le_one : half ≤ (1 : I) := by
  change (1 / 2 : ℝ) ≤ (1 : ℝ)
  norm_num

/-! ## Definition and basic properties -/

/-- The length of a path is its variation on the unit interval. -/
def length (γ : Path a b) : ℝ≥0∞ :=
  eVariationOn γ Set.univ

/-- The length of a path is nonnegative. -/
theorem length_nonneg (γ : Path a b) :
    0 ≤ γ.length := bot_le

/-- The endpoint distance of a path is bounded above by its length. -/
theorem edist_le_length (γ : Path a b) :
    edist a b ≤ γ.length := by
  unfold length
  trans edist (γ 0) (γ 1)
  · simp
  · exact eVariationOn.edist_le γ (by simp) (by simp)

/-- The constant path has zero length. -/
@[simp]
theorem length_refl (x : E) :
    (Path.refl x).length = 0 := by
  unfold length
  apply eVariationOn.constant_on
  simp

private lemma symm_eq_comp (γ : Path a b) : ⇑γ.symm = ⇑γ ∘ σ := rfl

/-- Reversing a path does not change its length. -/
@[simp]
theorem length_symm (γ : Path a b) :
    γ.symm.length = γ.length := by
  unfold length
  rw [symm_eq_comp γ]
  have h : eVariationOn (γ ∘ σ) (Set.univ : Set I) = eVariationOn γ (σ '' (Set.univ : Set I)) := by
    apply eVariationOn.comp_eq_of_antitoneOn (f := γ) (t := (Set.univ : Set I)) (φ := σ)
    intro x hx y hy hxy
    change (σ y : ℝ) ≤ (σ x : ℝ)
    rw [coe_symm_eq, coe_symm_eq]
    linarith [show (x : ℝ) ≤ (y : ℝ) from hxy]
  rw [Set.image_univ, Set.range_eq_univ.2 unitInterval.symm_bijective.surjective] at h
  exact h

/-! ## Auxiliary lemmas for concatenation -/

/-- The length of a path is the variation of its extension on `[0,1]`. -/
lemma length_eq_eVariationOn_extend (γ : Path a b) :
    γ.length = eVariationOn γ.extend (Icc (0 : ℝ) 1) := by
  unfold length
  have himage : ((↑) : I → ℝ) '' (Set.univ : Set I) = Icc (0 : ℝ) 1 := by
    exact Subtype.coe_image_univ I
  calc
    _ = eVariationOn (γ.extend ∘ ((↑) : I → ℝ)) (Set.univ : Set I) := by
      apply eVariationOn.congr
      intro t ht
      exact (Path.extend_extends' γ t).symm
    _ = eVariationOn γ.extend (((↑) : I → ℝ) '' (Set.univ : Set I)) := by
      apply eVariationOn.comp_eq_of_monotoneOn
      intro x hx y hy hxy
      exact hxy
    _ = eVariationOn γ.extend (Icc (0 : ℝ) 1) := by
      rw [himage]

/-- Auxiliary lemma: the affine map `t ↦ 2t` sends the left half
of the unit interval onto `[0,1]`. -/
private lemma image_double_Icc_half :
    (fun t : I ↦ (2 : ℝ) * t) '' Icc (0 : I) half = Icc (0 : ℝ) 1 := by
  ext x
  simp only [one_div, mem_image, mem_Icc, zero_le, true_and, Subtype.exists, Subtype.mk_le_mk,
    exists_and_left, exists_prop]
  constructor
  · grind
  · intros
    exact ⟨2⁻¹ * x, by grind⟩

/-- Auxiliary lemma: the variation of the left half of `γ.symm`
is the variation of the right half of `γ`. -/
private lemma eVariationOn_symm_Icc_left_half (γ : Path a b) :
    eVariationOn γ.symm (Icc 0 half) = eVariationOn γ (Icc half 1) := by
  rw [symm_eq_comp γ]
  calc
    _ = eVariationOn γ (σ '' Icc (0 : I) half) := by
        apply eVariationOn.comp_eq_of_antitoneOn
        intro x hx y hy hxy
        change (σ y : ℝ) ≤ (σ x : ℝ)
        rw [coe_symm_eq, coe_symm_eq]
        linarith [show (x : ℝ) ≤ (y : ℝ) from hxy]
    _ = eVariationOn γ (Icc half (1 : I)) := by
        congr 1
        ext x
        constructor
        · rintro ⟨t, ht, rfl⟩
          constructor
          · exact (half_le_symm_iff t).2 ht.2
          · exact (σ t).2.2
        · intro hx
          refine ⟨σ x, ?_, ?_⟩
          · constructor
            · simp
            · have : (1 / 2 : ℝ) ≤ (σ (σ x) : ℝ) := by
                rw [unitInterval.symm_symm]
                exact hx.1
              exact (half_le_symm_iff (σ x)).1 this
          · simp

/-! ## Length of concatenations -/

/-- The variation of a concatenation on its left half is the variation of the first path. -/
private lemma eVariationOn_trans_left (γ : Path a b) (η : Path b c) :
    eVariationOn (γ.trans η) (Icc 0 half) = γ.length := by
  refine (eVariationOn.congr (g := fun t : I ↦ γ.extend (2 * (t : ℝ))) ?_).trans ?_
  · intro t ht
    have hle : (t : ℝ) ≤ (1 / 2 : ℝ) := ht.2
    rw [Path.trans_apply, dif_pos hle, ← Path.extend_apply γ (by grind)]
  · change eVariationOn (γ.extend ∘ fun t : I ↦ (2 : ℝ) * t) (Icc 0 half) = eVariationOn γ Set.univ
    calc
      _ = eVariationOn γ.extend ((fun t : I ↦ (2 : ℝ) * t) '' Icc (0 : I) half) := by
          apply eVariationOn.comp_eq_of_monotoneOn
          intro x hx y hy hxy
          exact mul_le_mul_of_nonneg_left hxy (by positivity)
      _ = eVariationOn γ.extend (Icc (0 : ℝ) 1) := by
          rw [image_double_Icc_half]
      _ = γ.length := (length_eq_eVariationOn_extend γ).symm

/-- The variation of a concatenation on its right half is the variation of the second path. -/
private lemma eVariationOn_trans_right (γ : Path a b) (η : Path b c) :
    eVariationOn (γ.trans η) (Icc half 1) = η.length := by
  calc
    _ = eVariationOn (γ.trans η).symm (Icc 0 half) := by
        exact (eVariationOn_symm_Icc_left_half (γ := γ.trans η)).symm
    _ = eVariationOn η.symm Set.univ := by
        rw [Path.trans_symm]
        exact eVariationOn_trans_left (γ := η.symm) (η := γ.symm)
    _ = eVariationOn η Set.univ := by
        exact length_symm η

/-- The length of a concatenation is the sum of the lengths of the two pieces. -/
theorem length_trans (γ : Path a b) (η : Path b c) :
    (γ.trans η).length = γ.length + η.length := by
  unfold length
  have h := eVariationOn.Icc_add_Icc (f := γ.trans η) (s := Set.univ)
    zero_le_half half_le_one (Set.mem_univ half)
  simp only [Set.univ_inter] at h
  rw [← unitInterval.univ_eq_Icc] at h
  rw [← h, eVariationOn_trans_left, eVariationOn_trans_right]
  rfl

end

end

end Path
