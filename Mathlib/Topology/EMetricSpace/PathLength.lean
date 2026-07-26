/-
Copyright (c) 2026 Zhenhua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhenhua Wu
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Path
public import Mathlib.Topology.UnitInterval

/-!
# Length of paths

This file defines the length of a path in a `PseudoEMetricSpace` as its variation on the unit
interval. It also establishes the basic properties of path length that are needed in later files:
the endpoint distance bound, invariance under reversal, and additivity under concatenation.

## Main declarations

- `Path.length`
- `Path.edist_le_length`
- `Path.length_symm`
- `Path.length_trans`
-/

@[expose] public section
open scoped ENNReal
open Set unitInterval
namespace Path

noncomputable section
local notation "half" => (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ : I)
variable {E : Type*} [PseudoEMetricSpace E]
variable {a b c : E}

/-! ## Definition and basic properties -/

/-- The length of a path is its variation on the unit interval. -/
def length (γ : Path a b) : ℝ≥0∞ :=
  eVariationOn γ Set.univ

/-- The length of a path is nonnegative. -/
@[simp]
theorem length_nonneg (γ : Path a b) :
    0 ≤ γ.length := by
  exact bot_le

/-- The endpoint distance of a path is bounded above by its length. -/
theorem edist_le_length (γ : Path a b) :
    edist a b ≤ γ.length := by
  unfold length
  simpa using
    (eVariationOn.edist_le γ (x := (0 : I)) (y := (1 : I)) (by simp) (by simp))

/-- The constant path has zero length. -/
@[simp]
theorem length_refl (x : E) :
    (Path.refl x).length = 0 := by
  unfold length
  apply eVariationOn.constant_on
  rintro y ⟨t, ht, rfl⟩ z ⟨s, hs, rfl⟩
  rfl

/-- Reversing a path does not change its length. -/
@[simp]
theorem length_symm (γ : Path a b) :
    γ.symm.length = γ.length := by
  unfold length
  rw [show ⇑γ.symm = ⇑γ ∘ σ by rfl]
  simpa [Set.range_eq_univ.2 unitInterval.symm_bijective.surjective] using
    (eVariationOn.comp_eq_of_antitoneOn
      (f := γ)
      (t := (Set.univ : Set I))
      (φ := σ)
      (by
        intro x hx y hy hxy
        change (σ y : ℝ) ≤ (σ x : ℝ)
        rw [coe_symm_eq, coe_symm_eq]
        linarith [show (x : ℝ) ≤ (y : ℝ) from hxy]))

/-! ## Auxiliary lemmas for concatenation -/

/-- Auxiliary lemma: the variation of `γ.extend` on `[0,1]`
agrees with the variation of `γ`. -/
private lemma eVariationOn_extend_eq (γ : Path a b) :
    eVariationOn γ.extend (Icc (0 : ℝ) 1) = eVariationOn γ Set.univ := by
  have hrestrict :=
    eVariationOn.comp_eq_of_monotoneOn
      (f := γ.extend)
      (t := (Set.univ : Set I))
      ((↑) : I → ℝ)
      (by
        intro x hx y hy hxy
        exact hxy)
  have himage : ((↑) : I → ℝ) '' (Set.univ : Set I) = Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact y.2
    · intro hx
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      trivial
  have hcongr :
      eVariationOn (γ.extend ∘ ((↑) : I → ℝ)) (Set.univ : Set I)
        = eVariationOn γ Set.univ := by
    apply eVariationOn.congr
    intro t ht
    exact Path.extend_extends' γ t
  calc
    eVariationOn γ.extend (Icc (0 : ℝ) 1)
        = eVariationOn (γ.extend ∘ ((↑) : I → ℝ)) (Set.univ : Set I) := by
            symm
            simpa [Function.comp, himage] using hrestrict
    _ = eVariationOn γ Set.univ := hcongr

/-- Auxiliary lemma: the affine map `t ↦ 2t` sends the left half
of the unit interval onto `[0,1]`. -/
private lemma image_double_Icc_half :
    (fun t : I ↦ (2 : ℝ) * t) '' Icc (0 : I) half = Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · exact mul_nonneg (by positivity) t.2.1
    · have : (t : ℝ) ≤ (1 / 2 : ℝ) := ht.2
      nlinarith
  · intro hx
    refine ⟨⟨x / 2, ?_⟩, ?_, ?_⟩
    · constructor
      · nlinarith [hx.1]
      · nlinarith [hx.2]
    · constructor
      · simp
      · change ((x / 2 : ℝ) ≤ (1 / 2 : ℝ))
        nlinarith [hx.2]
    · nlinarith

/-- Auxiliary lemma: the variation of the left half of `γ.symm`
is the variation of the right half of `γ`. -/
private lemma eVariationOn_symm_Icc_left_half (γ : Path a b) :
    eVariationOn γ.symm (Icc 0 half) = eVariationOn γ (Icc half 1) := by
  rw [show ⇑γ.symm = ⇑γ ∘ σ by rfl]
  have hcomp :
      eVariationOn (γ ∘ σ) (Icc (0 : I) half) = eVariationOn γ (σ '' Icc (0 : I) half) := by
    exact eVariationOn.comp_eq_of_antitoneOn
      (f := γ)
      (t := Icc (0 : I) half)
      (φ := σ)
      (by
        intro x hx y hy hxy
        change (σ y : ℝ) ≤ (σ x : ℝ)
        rw [coe_symm_eq, coe_symm_eq]
        linarith [show (x : ℝ) ≤ (y : ℝ) from hxy])
  have himage :
      σ '' Icc (0 : I) half = Icc half (1 : I) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor
      · exact (half_le_symm_iff t).2 ht.2
      · exact (σ t).2.2
    · intro hx
      refine ⟨σ x, ?_, ?_⟩
      · constructor
        · exact (σ x).2.1
        · have hx' : (1 / 2 : ℝ) ≤ (x : ℝ) := hx.1
          have : (1 / 2 : ℝ) ≤ (σ (σ x) : ℝ) := by simpa using hx'
          exact (half_le_symm_iff (σ x)).1 this
      · exact unitInterval.symm_symm x
  rw [himage] at hcomp
  exact hcomp

/-! ## Length of concatenations -/

/-- The variation of a concatenation on its left half is the variation of the first path. -/
private lemma eVariationOn_trans_left
    (γ : Path a b) (η : Path b c) :
    eVariationOn (γ.trans η) (Icc 0 half)
      = eVariationOn γ Set.univ := by
  have hEq :
      EqOn (γ.trans η) (fun t : I ↦ γ.extend (2 * (t : ℝ))) (Icc 0 half) := by
    intro t ht
    have hle : (t : ℝ) ≤ (1 / 2 : ℝ) := ht.2
    simpa [Path.extend_apply, hle] using
      (Path.extend_trans_of_le_half γ η (t := (t : ℝ)) hle)
  rw [eVariationOn.congr hEq]
  change eVariationOn (γ.extend ∘ fun t : I ↦ (2 : ℝ) * t) (Icc 0 half)
      = eVariationOn γ Set.univ
  have hcomp :
      eVariationOn (γ.extend ∘ fun t : I ↦ (2 : ℝ) * t) (Icc 0 half)
        = eVariationOn γ.extend ((fun t : I ↦ (2 : ℝ) * t) '' Icc (0 : I) half) := by
    exact eVariationOn.comp_eq_of_monotoneOn
        (f := γ.extend)
        (t := Icc (0 : I) half)
        (φ := fun t : I ↦ (2 : ℝ) * t)
        (by
          intro x hx y hy hxy
          exact mul_le_mul_of_nonneg_left (show (x : ℝ) ≤ (y : ℝ) from hxy) (by positivity))
  calc
    eVariationOn (γ.extend ∘ fun t : I ↦ (2 : ℝ) * t) (Icc 0 half)
        = eVariationOn γ.extend (Icc (0 : ℝ) 1) := by
            rw [hcomp, image_double_Icc_half]
    _ = eVariationOn γ Set.univ := eVariationOn_extend_eq γ

/-- The variation of a concatenation on its right half is the variation of the second path. -/
private lemma eVariationOn_trans_right
    (γ : Path a b) (η : Path b c) :
    eVariationOn (γ.trans η) (Icc half 1)
      = eVariationOn η Set.univ := by
  calc
    eVariationOn (γ.trans η) (Icc half 1)
        = eVariationOn (γ.trans η).symm (Icc 0 half) := by
            simpa using (eVariationOn_symm_Icc_left_half (γ := γ.trans η)).symm
    _ = eVariationOn η.symm Set.univ := by
          simpa [Path.trans_symm] using eVariationOn_trans_left (γ := η.symm) (η := γ.symm)
    _ = eVariationOn η Set.univ := by
          simpa [length] using (length_symm η)

/-- The length of a concatenation is the sum of the lengths of the two pieces. -/
theorem length_trans
    (γ : Path a b) (η : Path b c) :
    (γ.trans η).length = γ.length + η.length := by
  unfold length
  have h :=
    eVariationOn.Icc_add_Icc
      (f := γ.trans η)
      (s := Set.univ)
      (a := (0 : I))
      (b := half)
      (c := (1 : I))
  have h' := h (by norm_num) (by change (1 / 2 : ℝ) ≤ 1; norm_num) (Set.mem_univ _)
  simp only [Set.univ_inter] at h'
  have hI : (Icc (0 : I) 1 : Set I) = Set.univ := by
    ext t
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨t.2.1, t.2.2⟩
  rw [hI] at h'
  rw [← h']
  rw [eVariationOn_trans_left, eVariationOn_trans_right]

end
end Path
