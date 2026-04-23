/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Ring.Action.Pointwise.Set
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# Homeomorphism between a normed space and sphere times `(0, +∞)`

In this file we define a homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) r × Set.Ioi (0 : ℝ)`, `r > 0`.
One may think about it as generalization of polar coordinates to any normed space.

We also specialize this definition to the case `r = 1` and prove
-/

@[expose] public section

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

open Filter Set Metric
open scoped Pointwise Set.Notation Topology

/-- The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) r × Set.Ioi (0 : ℝ)`, `0 < r`.

The forward map sends `⟨x, hx⟩` to `⟨r • ‖x‖⁻¹ • x, ‖x‖ / r⟩`,
the inverse map sends `(x, r)` to `r • x`.

In the case of the unit sphere `r = `,
one may think about it as generalization of polar coordinates to any normed space. -/
@[simps apply_fst_coe apply_snd_coe symm_apply_coe]
noncomputable def homeomorphSphereProd (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) :
    ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) r × Ioi (0 : ℝ)) where
  toFun x :=
    have : 0 < ‖(x : E)‖ := by simpa [-Subtype.coe_prop] using x.2
    (⟨r • ‖x.1‖⁻¹ • x.1, by simp [norm_smul, abs_of_pos hr, this.ne']⟩,
      ⟨‖x.1‖ / r, by rw [mem_Ioi]; positivity⟩)
  invFun x := ⟨x.2.1 • x.1.1, smul_ne_zero x.2.2.out.ne' (ne_of_mem_sphere x.1.2 hr.ne')⟩
  left_inv
  | ⟨x, hx⟩ => by
    have : 0 < ‖x‖ := by simpa using hx
    ext; simp only [smul_smul]; field_simp; simp
  right_inv
  | (⟨x, hx⟩, ⟨d, hd⟩) => by
    rw [mem_Ioi] at hd
    rw [mem_sphere_zero_iff_norm] at hx
    simp (disch := positivity) [norm_smul, smul_smul, abs_of_pos hd, hx]
  continuous_toFun := by
    simp only
    fun_prop (disch := simp)

/-- The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)`.

The forward map sends `⟨x, hx⟩` to `⟨‖x‖⁻¹ • x, ‖x‖⟩`,
the inverse map sends `(x, r)` to `r • x`.

One may think about it as generalization of polar coordinates to any normed space.
See also `homeomorphSphereProd` for a version that works for a sphere of any positive radius. -/
@[simps! apply_fst_coe apply_snd_coe symm_apply_coe]
noncomputable def homeomorphUnitSphereProd :
    ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
  homeomorphSphereProd E 1 one_pos

variable {E}

/-- If `U ∌ 0` is an open set on the real line and `V` is an open set on a sphere of nonzero radius,
then their pointwise scalar product is an open set. -/
theorem IsOpen.smul_sphere {r : ℝ} (hr : r ≠ 0) {U : Set ℝ} {V : Set (Metric.sphere (0 : E) r)}
    (hU : IsOpen U) (hU₀ : 0 ∉ U) (hV : IsOpen V) : IsOpen (U • (V : Set E)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxU, _, ⟨y, hyV, rfl⟩, rfl⟩
  wlog hx₀ : 0 < x generalizing x U
  · replace hx₀ : 0 < -x := by
      rw [not_lt, le_iff_eq_or_lt, ← neg_pos] at hx₀
      exact hx₀.resolve_left <| ne_of_mem_of_not_mem hxU hU₀
    specialize this hU.neg (by simpa) (-x) (by simpa) hx₀
    simp only [neg_smul, nhds_neg, Set.neg_smul, Filter.mem_neg] at this
    simpa using this
  have hr₀ : 0 < r := lt_of_le_of_ne (by simpa using norm_nonneg y.1) hr.symm
  lift x to Ioi (0 : ℝ) using hx₀
  have : V ×ˢ (Ioi (0 : ℝ) ↓∩ U) ∈ 𝓝 (y, x) :=
    prod_mem_nhds (hV.mem_nhds hyV) (hU.preimage_val.mem_nhds hxU)
  replace := image_mem_map (m := Subtype.val ∘ (homeomorphSphereProd E r hr₀).symm) this
  rw [← Filter.map_map, (homeomorphSphereProd _ r hr₀).symm.map_nhds_eq,
    map_nhds_subtype_val, IsOpen.nhdsWithin_eq, homeomorphSphereProd_symm_apply_coe] at this
  · filter_upwards [this]
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [Function.comp_apply, homeomorphSphereProd_symm_apply_coe]
    apply Set.smul_mem_smul
    exacts [hb, mem_image_of_mem _ ha]
  · exact isOpen_compl_singleton
  · simp [x.2.out.ne', ne_zero_of_mem_sphere, hr₀.ne']
