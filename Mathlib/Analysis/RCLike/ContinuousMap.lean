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

@[simp, grind .] lemma isSelfAdjoint_realToRCLike {f : C(X, ℝ)} :
    IsSelfAdjoint (f.realToRCLike 𝕜) := by ext; simp

@[simp] lemma spectrum_realToRCLike (f : C(X, ℝ)) :
    spectrum ℝ (f.realToRCLike 𝕜) = spectrum ℝ f := by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]

open ComplexOrder

variable (X) in
/-- `ContinuousMap.realToRCLike` as an order embedding. -/
@[simps] def realToRCLikeOrderEmbedding : C(X, ℝ) ↪o C(X, 𝕜) where
  toFun := realToRCLike 𝕜
  inj' f g hfg := by ext x; simpa using congr($hfg x)
  map_rel_iff' := by simp [le_def]

variable (X) in
lemma realToRCLike_monotone : Monotone (realToRCLike (X := X) 𝕜) :=
  realToRCLikeOrderEmbedding X 𝕜 |>.monotone

variable (X) in
lemma realToRCLike_strictMono : StrictMono (realToRCLike (X := X) 𝕜) :=
  realToRCLikeOrderEmbedding X 𝕜 |>.strictMono

variable (X) in
@[simp] lemma realToRCLike_injective : (realToRCLike (X := X) 𝕜).Injective :=
  realToRCLikeOrderEmbedding X 𝕜 |>.injective

@[simp] lemma realToRCLike_inj {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f = realToRCLike 𝕜 g ↔ f = g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.eq_iff_eq

@[simp] lemma realToRCLike_le_realToRCLike_iff {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f ≤ realToRCLike 𝕜 g ↔ f ≤ g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.le_iff_le

@[simp] lemma realToRCLike_lt_realToRCLike_iff {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f < realToRCLike 𝕜 g ↔ f < g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.lt_iff_lt

variable (X) in
@[simp] theorem isometry_realToRCLike [CompactSpace X] : Isometry (realToRCLike 𝕜 (X := X)) :=
  .of_dist_eq fun f g ↦ by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]

variable (X) in
@[simp, fun_prop] lemma continuous_realToRCLike : Continuous (realToRCLike 𝕜 (X := X)) :=
  continuous_postcomp { toFun x := RCLike.ofReal x }

variable (X) in
/-- `ContinuousMap.realToRCLike` as a ⋆-algebra map. -/
@[simps!] noncomputable def realToRCLikeStarAlgHom : C(X, ℝ) →⋆ₐ[ℝ] C(X, 𝕜) :=
  compStarAlgHom X (RCLike.ofRealStarAlgHom 𝕜) RCLike.continuous_ofReal

@[simp] lemma realToRCLikeStarAlgHom_apply (f : C(X, ℝ)) :
    realToRCLikeStarAlgHom X 𝕜 f = f.realToRCLike 𝕜 := rfl

lemma realToRCLike_star (f : C(X, ℝ)) : (star f).realToRCLike 𝕜 = star (f.realToRCLike 𝕜) :=
  map_star (realToRCLikeStarAlgHom X 𝕜) f

@[simp] lemma realToRCLike_mul (f g : C(X, ℝ)) :
    (f * g).realToRCLike 𝕜 = f.realToRCLike 𝕜 * g.realToRCLike 𝕜 :=
  map_mul (realToRCLikeStarAlgHom X 𝕜) f g

variable {𝕜} in
/-- Mapping `C(X, 𝕜)` to `C(X, ℝ)` using `RCLike.re`. -/
@[simps] def rclikeToReal (f : C(X, 𝕜)) : C(X, ℝ) where toFun x := RCLike.re (f x)

variable (X) in
lemma rclikeToReal_monotone : Monotone (rclikeToReal (X := X) (𝕜 := 𝕜)) := by
  intro a b; simp_all [le_def, RCLike.le_iff_re_im (K := 𝕜)]

variable (X) in
@[simp, fun_prop] lemma continuous_rclikeToReal : Continuous (rclikeToReal (X := X) (𝕜 := 𝕜)) :=
  continuous_postcomp { toFun x := RCLike.re x }

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

end ContinuousMap
