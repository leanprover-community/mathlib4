/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Operator.Conformal

/-!
# Conformal Maps

A continuous linear map between real normed spaces `X` and `Y` is `ConformalAt` some point `x`
if it is real differentiable at that point and its differential is a conformal linear map.

## Main definitions

* `ConformalAt`: the main definition of conformal maps
* `Conformal`: maps that are conformal at every point

## Main results
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by nonzero constants
* `conformalAt_iff_isConformalMap_fderiv`: an equivalent definition of the conformality of a map

In `Analysis.Calculus.Conformal.InnerProduct`:
* `conformalAt_iff`: an equivalent definition of the conformality of a map

In `Geometry.Euclidean.Angle.Unoriented.Conformal`:
* `ConformalAt.preserves_angle`: if a map is conformal at `x`, then its differential preserves
  all angles at `x`

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the complex conjugate are considered to be conformal.
-/


noncomputable section

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z]

section LocConformality

open LinearIsometry ContinuousLinearMap

/-- A map `f` is said to be conformal if it has a conformal differential `f'`. -/
def ConformalAt (f : X → Y) (x : X) :=
  ∃ f' : X →L[ℝ] Y, HasFDerivAt f f' x ∧ IsConformalMap f'

theorem conformalAt_id (x : X) : ConformalAt _root_.id x :=
  ⟨id ℝ X, hasFDerivAt_id _, isConformalMap_id⟩

theorem conformalAt_const_smul {c : ℝ} (h : c ≠ 0) (x : X) : ConformalAt (fun x' : X => c • x') x :=
  ⟨c • ContinuousLinearMap.id ℝ X, (hasFDerivAt_id x).const_smul c, isConformalMap_const_smul h⟩

@[nontriviality]
theorem Subsingleton.conformalAt [Subsingleton X] (f : X → Y) (x : X) : ConformalAt f x :=
  ⟨0, hasFDerivAt_of_subsingleton _ _, isConformalMap_of_subsingleton _⟩

/-- A function is a conformal map if and only if its differential is a conformal linear map -/
theorem conformalAt_iff_isConformalMap_fderiv {f : X → Y} {x : X} :
    ConformalAt f x ↔ IsConformalMap (fderiv ℝ f x) := by
  constructor
  · rintro ⟨f', hf, hf'⟩
    rwa [hf.fderiv]
  · intro H
    by_cases h : DifferentiableAt ℝ f x
    · exact ⟨fderiv ℝ f x, h.hasFDerivAt, H⟩
    · nontriviality X
      exact absurd (fderiv_zero_of_not_differentiableAt h) H.ne_zero

namespace ConformalAt

theorem differentiableAt {f : X → Y} {x : X} (h : ConformalAt f x) : DifferentiableAt ℝ f x :=
  let ⟨_, h₁, _⟩ := h
  h₁.differentiableAt

theorem congr {f g : X → Y} {x : X} {u : Set X} (hx : x ∈ u) (hu : IsOpen u) (hf : ConformalAt f x)
    (h : ∀ x : X, x ∈ u → g x = f x) : ConformalAt g x :=
  let ⟨f', hfderiv, hf'⟩ := hf
  ⟨f', hfderiv.congr_of_eventuallyEq ((hu.eventually_mem hx).mono h), hf'⟩

theorem comp {f : X → Y} {g : Y → Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
    ConformalAt (g ∘ f) x := by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩

theorem const_smul {f : X → Y} {x : X} {c : ℝ} (hc : c ≠ 0) (hf : ConformalAt f x) :
    ConformalAt (c • f) x :=
  (conformalAt_const_smul hc <| f x).comp x hf

end ConformalAt

end LocConformality

section GlobalConformality

/-- A map `f` is conformal if it's conformal at every point. -/
def Conformal (f : X → Y) :=
  ∀ x : X, ConformalAt f x

theorem conformal_id : Conformal (id : X → X) := fun x => conformalAt_id x

theorem conformal_const_smul {c : ℝ} (h : c ≠ 0) : Conformal fun x : X => c • x := fun x =>
  conformalAt_const_smul h x

namespace Conformal

theorem conformalAt {f : X → Y} (h : Conformal f) (x : X) : ConformalAt f x :=
  h x

theorem differentiable {f : X → Y} (h : Conformal f) : Differentiable ℝ f := fun x =>
  (h x).differentiableAt

theorem comp {f : X → Y} {g : Y → Z} (hf : Conformal f) (hg : Conformal g) : Conformal (g ∘ f) :=
  fun x => (hg <| f x).comp x (hf x)

theorem const_smul {f : X → Y} (hf : Conformal f) {c : ℝ} (hc : c ≠ 0) : Conformal (c • f) :=
  fun x => (hf x).const_smul hc

end Conformal

end GlobalConformality
