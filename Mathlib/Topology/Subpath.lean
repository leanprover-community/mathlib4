/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Subpaths

This file defines `Path.subpath` as a restriction of a path to a subinterval,
reparameterized to have domain `[0, 1]` and possibly with a reverse of direction.

The main result `Path.Homotopy.subpathTransSubpath` shows that subpaths concatenate nicely.
In particular: following the subpath of `γ` from `t₀` to `t₁`, and then that from `t₁` to `t₂`,
is in natural homotopy with following the subpath of `γ` from `t₀` to `t₂`.
-/

noncomputable section

open unitInterval Set Function

universe u

variable {X : Type u} [TopologicalSpace X] {a b : X}

namespace Path

/-- Auxillary function for defining subpaths. -/
@[simp]
def subpathAux (t₀ t₁ s : I) : I := ⟨(1 - s) * t₀ + s * t₁,
  (convex_Icc 0 1) t₀.prop t₁.prop (one_minus_nonneg s) s.prop.left (sub_add_cancel 1 _)⟩

lemma subpathAux_zero (t₀ t₁ : I) : subpathAux t₀ t₁ 0 = t₀ := by simp

lemma subpathAux_one (t₀ t₁ : I) : subpathAux t₀ t₁ 1 = t₁ := by simp

/-- `subpathAux` is continuous as an uncurried function `I × I × I → I`. -/
@[continuity, fun_prop]
lemma subpathAux_continuous : Continuous (fun x ↦ subpathAux x.1 x.2.1 x.2.2 : I × I × I → I) := by
  unfold subpathAux
  fun_prop

/-- The subpath of `γ` from `t₀` to `t₁`. -/
def subpath (γ : Path a b) (t₀ t₁ : I) : Path (γ t₀) (γ t₁) where
  toFun := γ ∘ (subpathAux t₀ t₁)
  source' := by rw [comp_apply, subpathAux_zero]
  target' := by rw [comp_apply, subpathAux_one]
  continuous_toFun := by fun_prop

/-- Reversing `γ.subpath t₀ t₁` results in `γ.subpath t₁ t₀`. -/
@[simp]
theorem symm_subpath (γ : Path a b) (t₀ t₁ : I) : symm (γ.subpath t₀ t₁) = γ.subpath t₁ t₀ := by
  ext s
  simp [subpath, add_comm]

@[simp]
lemma range_subpath_of_le (γ : Path a b) (t₀ t₁ : I) (h : t₀ ≤ t₁) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₀ t₁) := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    apply mem_image_of_mem
    exact convex_Icc (t₀ : ℝ) t₁ (left_mem_Icc.mpr h) (right_mem_Icc.mpr h) (one_minus_nonneg s)
      s.prop.left (sub_add_cancel _ _)
  · rintro ⟨t, ht : (t : ℝ) ∈ Icc (t₀ : ℝ) (t₁ : ℝ), rfl⟩
    rw [Convex.mem_Icc (show (t₀ : ℝ) ≤ (t₁ : ℝ) from h)] at ht
    obtain ⟨a, b, ha, hb, hab, ht⟩ := ht
    rw [mem_range]
    use ⟨b, hb, Trans.trans (eq_sub_of_add_eq' hab) (sub_le_self 1 ha)⟩
    simp [subpath, ← eq_sub_of_add_eq hab, ht]

@[simp]
lemma range_subpath_of_ge (γ : Path a b) (t₀ t₁ : I) (h : t₁ ≤ t₀) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₁ t₀) := by
  rw [← symm_subpath, symm_range, range_subpath_of_le _ _ _ h]

/-- The range of a subpath is the image of the original path on the relevant interval. -/
@[simp]
theorem range_subpath (γ : Path a b) (t₀ t₁ : I) :
    range (γ.subpath t₀ t₁) = γ '' (uIcc t₀ t₁) := by
  rcases le_total t₀ t₁ with h | h
  · rw [uIcc_of_le h]
    exact range_subpath_of_le _ _ _ h
  · rw [uIcc_of_ge h]
    exact range_subpath_of_ge _ _ _ h

/-- The subpath of `γ` from `t` to `t` is just the constant path at `γ t`. -/
@[simp]
theorem subpath_self (γ : Path a b) (t : I) : γ.subpath t t = Path.refl (γ t) := by
  ext s
  simp [subpath, ← add_mul, sub_add_cancel, one_mul]

/-- The subpath of `γ` from `0` to `1` is just `γ`, with a slightly different type. -/
@[simp]
theorem subpath_zero_one (γ : Path a b) : γ.subpath 0 1 = γ.cast γ.source γ.target := by
  ext s
  simp [subpath]

/-- For a path `γ`, `γ.subpath` gives a "continuous family of paths", by which we mean
the uncurried function which maps `(t₀, t₁, s)` to `γ.subpath t₀ t₁ s` is continuous. -/
@[continuity]
theorem subpath_continuous_family (γ : Path a b) :
    Continuous (fun x => γ.subpath x.1 x.2.1 x.2.2 : I × I × I → X) :=
  Continuous.comp' (map_continuous γ) subpathAux_continuous

namespace Homotopy

/-- Auxillary homotopy for `Path.Homotopy.subpathTransSubpath` which includes an unnecessary
copy of `Path.refl`. -/
def subpathTransSubpathRefl (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) ((γ.subpath t₀ t₂).trans (Path.refl _)) where
  toFun x := ((γ.subpath t₀ (subpathAux t₁ t₂ x.1)).trans (γ.subpath _ t₂)) x.2
  /- Technical note: One would hope the proof of continuity could be made much simpler by using
  a theorem like `Continuous.pathExtend`, but that does not work in this case because the
  endpoints of our subpaths depend on our input `x` (i.e., the types don't quite match). -/
  continuous_toFun := by
    let γ₁ (t : I) := γ.subpath t₀ (subpathAux t₁ t₂ t)
    let γ₂ (t : I) := γ.subpath (subpathAux t₁ t₂ t) t₂
    refine Path.trans_continuous_family γ₁ ?_ γ₂ ?_ <;>
    refine γ.subpath_continuous_family.comp (.prodMk ?_ <| .prodMk ?_ ?_) <;>
    fun_prop
  map_zero_left := by
    intro _
    congr
    repeat exact subpathAux_zero t₁ t₂
  map_one_left := by
    intro _
    congr
    · exact subpathAux_one t₁ t₂
    · exact subpathAux_one t₁ t₂
    · rw [subpathAux_one, subpath_self]
  prop' := by
    intro _ _ hx
    rcases hx with rfl | rfl
    all_goals simp

/-- Following the subpath of `γ` from `t₀` to `t₁`, and then that from `t₁` to `t₂`,
is in natural homotopy with following the subpath of `γ` from `t₀` to `t₂`. -/
def subpathTransSubpath (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) (γ.subpath t₀ t₂) :=
  trans (subpathTransSubpathRefl γ t₀ t₁ t₂) (transRefl _)

/- Possible extension: It may be worth proving that `Path.truncateOfLE` and `Path.subpath` are
reparameterizations of one another. -/

end Path.Homotopy
end
