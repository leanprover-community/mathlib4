/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.UniformSpace.OfFun

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/
noncomputable section

open Set Function Filter Uniformity

namespace AbsoluteValue

variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {R : Type*} [CommRing R] (abv : AbsoluteValue R 𝕜)

/-- The uniform structure coming from an absolute value. -/
def uniformSpace : UniformSpace R :=
  .ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun x y z => (abv.sub_le _ _ _).trans_eq (add_comm _ _))
    fun ε ε0 => ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩

theorem hasBasis_uniformity :
    𝓤[abv.uniformSpace].HasBasis ((0 : 𝕜) < ·) fun ε => { p : R × R | abv (p.2 - p.1) < ε } :=
  UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

/-- A real absolute value on a ring determines a `NormedRing` structure. -/
def toNormedRing {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing R where
  norm := v
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, map_zero]
  dist_comm := v.map_sub
  dist_triangle := v.sub_le
  edist_dist x y := rfl
  norm_mul x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom,
    AbsoluteValue.map_sub_eq_zero_iff, imp_self, implies_true]

/-- A real absolute value on a field determines a `NormedField` structure. -/
def toNormedField {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : NormedField K where
  toField := inferInstanceAs (Field K)
  __ := v.toNormedRing
  norm_mul' := v.map_mul

end AbsoluteValue
