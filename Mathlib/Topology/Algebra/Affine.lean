/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction

#align_import topology.algebra.affine from "leanprover-community/mathlib"@"717c073262cd9d59b1a1dcda7e8ab570c5b63370"

/-!
# Topological properties of affine spaces and maps

For now, this contains only a few facts regarding the continuity of affine maps in the special
case when the point space and vector space are the same.

TODO: Deal with the case where the point spaces are different from the vector spaces. Note that
we do have some results in this direction under the assumption that the topologies are induced by
(semi)norms.
-/


namespace AffineMap

variable {R E F : Type*}
variable [AddCommGroup E] [TopologicalSpace E]
variable [AddCommGroup F] [TopologicalSpace F] [TopologicalAddGroup F]

section Ring

variable [Ring R] [Module R E] [Module R F]

/-- An affine map is continuous iff its underlying linear map is continuous. See also
`AffineMap.continuous_linear_iff`. -/
theorem continuous_iff {f : E →ᵃ[R] F} : Continuous f ↔ Continuous f.linear := by
  constructor
  · intro hc
    rw [decomp' f]
    exact hc.sub continuous_const
  · intro hc
    rw [decomp f]
    exact hc.add continuous_const
#align affine_map.continuous_iff AffineMap.continuous_iff

/-- The line map is continuous. -/
@[continuity]
theorem lineMap_continuous [TopologicalSpace R] [ContinuousSMul R F] {p v : F} :
    Continuous (lineMap p v : R →ᵃ[R] F) :=
  continuous_iff.mpr <|
    (continuous_id.smul continuous_const).add <| @continuous_const _ _ _ _ (0 : F)
#align affine_map.line_map_continuous AffineMap.lineMap_continuous

end Ring

section CommRing

variable [CommRing R] [Module R F] [ContinuousConstSMul R F]

@[continuity]
theorem homothety_continuous (x : F) (t : R) : Continuous <| homothety x t := by
  suffices ⇑(homothety x t) = fun y => t • (y - x) + x by
    rw [this]
    exact ((continuous_id.sub continuous_const).const_smul _).add continuous_const
    -- Porting note: proof was `by continuity`
  ext y
  simp [homothety_apply]
#align affine_map.homothety_continuous AffineMap.homothety_continuous

end CommRing

section Field

variable [Field R] [Module R F] [ContinuousConstSMul R F]

theorem homothety_isOpenMap (x : F) (t : R) (ht : t ≠ 0) : IsOpenMap <| homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]
#align affine_map.homothety_is_open_map AffineMap.homothety_isOpenMap

end Field

end AffineMap
