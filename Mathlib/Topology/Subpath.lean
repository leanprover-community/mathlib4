/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
module

public import Batteries.Data.Fin.Fold
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Subpaths and concatenation of paths

This file defines `Path.subpath` as a restriction of a path to a subinterval, reparameterized to
have domain `[0, 1]` and possibly with a reverse of direction. It then defines `Path.concat` as
a way to concatenate finite sequences of paths with compatible endpoints.

The main result `Path.Homotopy.concatSubpath` shows that subpaths concatenate nicely.
In particular: following the subpaths of `γ` from `t i` to `t (i + 1)` for `0 ≤ i < n` is
homotopic to the subpath of `γ` from `t 0` to `t n`.

## TODO

Prove that `Path.truncateOfLE` and `Path.subpath` are reparameterizations of each other.
(`Path.subpath` is still a useful definition because it works without assuming an order on `t₀` and
`t₁`, and is convenient for concrete manipulations.)
-/

@[expose] public noncomputable section

open Fin Function Set unitInterval

variable {X : Type*} [TopologicalSpace X] {a b : X}

namespace Path

/-!
## Subpaths
-/

/-- Auxiliary function for defining subpaths. -/
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

lemma range_subpathAux (t₀ t₁ : I) : range (subpathAux t₀ t₁) = uIcc t₀ t₁ := by
  rw [range_eq_iff]
  constructor
  · intro s
    exact convex_uIcc (t₀ : ℝ) t₁ left_mem_uIcc right_mem_uIcc
      (one_minus_nonneg s) (nonneg s) (sub_add_cancel _ _)
  · intro t (ht : (t : ℝ) ∈ uIcc (t₀ : ℝ) (t₁ : ℝ))
    rw [← segment_eq_uIcc, segment_eq_image] at ht
    obtain ⟨s, hs, hst⟩ := ht
    use ⟨s, hs⟩
    ext
    exact hst

/-- The range of a subpath is the image of the original path on the relevant interval. -/
@[simp]
theorem range_subpath (γ : Path a b) (t₀ t₁ : I) :
    range (γ.subpath t₀ t₁) = γ '' (uIcc t₀ t₁) := by
  rw [← range_subpathAux, ← range_comp, subpath, coe_mk', ContinuousMap.coe_mk]

lemma range_subpath_of_le (γ : Path a b) (t₀ t₁ : I) (h : t₀ ≤ t₁) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₀ t₁) := by
  simp [h]

lemma range_subpath_of_ge (γ : Path a b) (t₀ t₁ : I) (h : t₁ ≤ t₀) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₁ t₀) := by
  simp [h]

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

/-- Auxiliary homotopy for `Path.Homotopy.subpathTransSubpath` which includes an unnecessary
copy of `Path.refl`. -/
def subpathTransSubpathRefl (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) ((γ.subpath t₀ t₂).trans (Path.refl _)) where
  toFun x := ((γ.subpath t₀ (subpathAux t₁ t₂ x.1)).trans (γ.subpath _ t₂)) x.2
  continuous_toFun := by
    let γ₁ (t : I) := γ.subpath t₀ (subpathAux t₁ t₂ t)
    let γ₂ (t : I) := γ.subpath (subpathAux t₁ t₂ t) t₂
    refine Path.trans_continuous_family γ₁ ?_ γ₂ ?_ <;>
    refine γ.subpath_continuous_family.comp (.prodMk ?_ <| .prodMk ?_ ?_) <;>
    fun_prop
  map_zero_left _ := by rw [subpathAux_zero, coe_toContinuousMap]
  map_one_left _ := by rw [subpathAux_one, subpath_self, coe_toContinuousMap]
  prop' _ _ hx := by
    rcases hx with rfl | rfl <;>
    simp

/-- Following the subpath of `γ` from `t₀` to `t₁`, and then that from `t₁` to `t₂`,
is in natural homotopy with following the subpath of `γ` from `t₀` to `t₂`. -/
def subpathTransSubpath (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) (γ.subpath t₀ t₂) :=
  trans (subpathTransSubpathRefl γ t₀ t₁ t₂) (transRefl _)

end Homotopy

/-!
## Concatenation of paths
-/

variable {n : ℕ}

/-- Concatenation of a sequence of paths with compatible endpoints. -/
def concat (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) :
    Path (p 0) (p (last n)) :=
  dfoldl n (fun i => Path (p 0) (p i)) (fun i ih => ih.trans (F i)) (refl (p 0))

/-- Concatenating zero paths yields the constant path (the identity of `Path.trans`). -/
@[simp] lemma concat_zero (p : Fin 1 → X) (F) :
    concat p F = refl (p 0) := by
  rw [concat, dfoldl_zero]

/-- Concatenating `n + 1` paths corresponds to concatenating `n` paths and then the last path. -/
lemma concat_succ (p : Fin (n + 2) → X) (F) :
    concat p F = (concat (p ∘ castSucc) (fun k ↦ (F k.castSucc))).trans (F (last n)) := by
  rw [concat, dfoldl_succ_last]
  rfl

/-- Concatenating the constant path at `x` with itself just yields the constant path at `x`. -/
@[simp]
theorem concat_refl (n : ℕ) (x : X) :
    concat (fun (_ : Fin (n + 1)) ↦ x) (fun _ ↦ Path.refl x) = Path.refl x := by
  induction n with
  | zero => rw [concat_zero]
  | succ _ _ =>
    rw [concat_succ]
    convert refl_trans_refl

namespace Homotopy

/-- Given two sequences of paths `F` and `G`, and a sequence `H` of homotopies between them,
there is a natural homotopy between `concat _ F` and `concat _ G`. -/
protected def concat (p : Fin (n + 1) → X) (F G : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (H : (k : Fin n) → (F k).Homotopy (G k)) : Homotopy (concat p F) (concat p G) := by
  induction n with
  | zero =>
    rw [concat_zero, concat_zero]
    exact refl (Path.refl _)
  | succ n ih =>
    rw [concat_succ, concat_succ]
    exact hcomp (ih _ _ _ (fun k ↦ H k.castSucc)) (H (last n))

/-- Given a path `γ` and a sequence `t` of `n + 1` points in `[0, 1]`, there is a natural homotopy
between the concatenation of paths `γ.subpath (t k) (t (k + 1))`, and `γ.subpath (t 0) (t n)`. -/
def concatSubpath (γ : Path a b) (t : Fin (n + 1) → I) :
    Homotopy
      (concat (γ ∘ t) (fun k ↦ γ.subpath (t k.castSucc) (t k.succ)))
      (γ.subpath (t 0) (t (last n))) := by
  induction n with
  | zero =>
    simp only [concat_zero, reduceLast, subpath_self]
    exact refl _
  | succ n ih =>
    rw [concat_succ]
    exact trans ((ih (t ∘ castSucc)).hcomp (refl _)) (subpathTransSubpath γ _ _ _)

end Homotopy

namespace Homotopic

/-- Concatenating one path `F 0` is homotopic to that path. -/
theorem concat_one (p : Fin 2 → X) (F) :
    Homotopic (concat p F) (F 0) := by
  simpa [concat_succ] using ⟨Homotopy.reflTrans _⟩

/-- Concatenating two paths `F 0` and `F 1` is homotopic to `Path.trans (F 0) (F 1)`. -/
theorem concat_two (p : Fin 3 → X) (F) :
    Homotopic (concat p F) ((F 0).trans (F 1)) := by
  simpa [concat_succ] using hcomp ⟨Homotopy.reflTrans _⟩ (refl _)


/-- Alternative to `Path.Homotopy.concatHcomp` in terms of `Path.Homotopic`. -/
theorem concat_hcomp (p : Fin (n + 1) → X) (F G : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (h : (k : Fin n) → (F k).Homotopic (G k)) : Homotopic (concat p F) (concat p G) :=
  ⟨Homotopy.concat p F G (fun k ↦ (h k).some)⟩

/-- Alternative to `Path.Homotopy.concatSubpath` in terms of `Path.Homotopic`. -/
@[simp]
theorem concat_subpath (γ : Path a b) (t : Fin (n + 1) → I) :
    Homotopic
      (concat (γ ∘ t) (fun k ↦ γ.subpath (t k.castSucc) (t k.succ)))
      (γ.subpath (t 0) (t (last n))) :=
  ⟨Homotopy.concatSubpath γ t⟩

end Path.Homotopic

end
