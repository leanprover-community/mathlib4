/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.Units

/-! # Mapping `C(X, ℝ)` to `C(X, 𝕜)` and back

This file contains the definitions for `ContinuousMap.realToRCLike` and
`ContinuousMap.rclikeToReal`, which map `C(X, ℝ)` to `C(X, 𝕜)` and back for any `RCLike 𝕜`. -/

@[expose] public section

namespace ContinuousMap
variable {X : Type*} (𝕜 : Type*) [TopologicalSpace X] [RCLike 𝕜]

/-- Lifting `C(X, ℝ)` to `C(X, 𝕜)` using `RCLike.ofReal`. -/
@[simps] def realToRCLike (f : C(X, ℝ)) : C(X, 𝕜) where toFun x := RCLike.ofReal (f x)

@[simp, grind .]
lemma isSelfAdjoint_realToRCLike {f : C(X, ℝ)} :
    IsSelfAdjoint (f.realToRCLike 𝕜) := by
  ext; simp

@[simp] lemma spectrum_realToRCLike (f : C(X, ℝ)) :
    spectrum ℝ (f.realToRCLike 𝕜) = spectrum ℝ f := by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]

variable (X) in
open ComplexOrder in
lemma monotone_realToRCLike : Monotone (realToRCLike (X := X) 𝕜) :=
  fun f g hfg x ↦ by simpa using hfg x

variable {𝕜} in
/-- Mapping `C(X, 𝕜)` to `C(X, ℝ)` using `RCLike.re`. -/
@[simps] def rclikeToReal (f : C(X, 𝕜)) : C(X, ℝ) where toFun x := RCLike.re (f x)

@[simp] theorem rclikeToReal_realToRCLike (f : C(X, ℝ)) :
    (f.realToRCLike 𝕜).rclikeToReal = f := by ext; simp

variable {𝕜} in
@[aesop safe apply, grind =]
theorem IsSelfAdjoint.realToRCLike_rclikeToReal {f : C(X, 𝕜)} (hf : IsSelfAdjoint f) :
    f.rclikeToReal.realToRCLike 𝕜 = f := by
  ext
  simp only [realToRCLike_apply, rclikeToReal_apply, ← RCLike.conj_eq_iff_re]
  conv_rhs => rw [← hf.star_eq]
  simp

variable (X) in
open ContinuousMap in
theorem range_realToRCLike_eq_isSelfAdjoint :
    .range (realToRCLike 𝕜) = {f : C(X, 𝕜) | IsSelfAdjoint f} :=
  le_antisymm (fun _ ⟨_, h⟩ ↦ by simp [← h]) fun f hf ↦
    ⟨f.rclikeToReal, hf.realToRCLike_rclikeToReal⟩

variable (X) in
@[simp] theorem isometry_realToRCLike [CompactSpace X] : Isometry (realToRCLike 𝕜 (X := X)) :=
  .of_dist_eq fun f g ↦ by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]

variable (X) in
@[simp, fun_prop]
lemma continuous_realToRCLike [CompactSpace X] : Continuous (realToRCLike 𝕜 (X := X)) :=
  (isometry_realToRCLike X 𝕜).continuous

end ContinuousMap
