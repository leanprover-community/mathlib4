/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Topology.Algebra.MulAction

/-!
# The quotient topology on projective space

`ℙ K V` is the quotient of the nonzero vectors `{v : V // v ≠ 0}` by the action of `Kˣ`.
When `V` carries a topology we give `ℙ K V` the quotient topology, and we show that the
quotient map `Projectivization.mk'` is an open quotient map as soon as scalar multiplication
by units of `K` is continuous on `V`.

## Main results

* `Projectivization.instTopologicalSpace`: the quotient topology on `ℙ K V`.
* `Projectivization.isQuotientMap_mk'`, `Projectivization.continuous_mk'`:
  `mk' K : {v : V // v ≠ 0} → ℙ K V` is a quotient map, in particular continuous.
* `Projectivization.isOpenQuotientMap_mk'`: `mk' K` is an open quotient map when `Kˣ` acts
  continuously on `V`.
* `Projectivization.continuous_iff`: a map out of `ℙ K V` is continuous iff its composite with
  `mk' K` is.
-/

@[expose] public section

open Set Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Two nonzero vectors have the same image in `ℙ K V` iff one is a unit multiple of the other,
for the action of `Kˣ` on `{v : V // v ≠ 0}`. -/
theorem mk'_eq_mk'_iff (v w : {v : V // v ≠ 0}) :
    mk' K v = mk' K w ↔ ∃ a : Kˣ, a • w = v := by
  rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff]
  simp only [Subtype.ext_iff, Units.smul_coe]

/-- The saturation of a set of nonzero vectors under `mk'` is the union of its translates by the
units of `K`. -/
theorem preimage_image_mk' (U : Set {v : V // v ≠ 0}) :
    mk' K ⁻¹' (mk' K '' U) = ⋃ a : Kˣ, (a • ·) '' U := by
  ext v
  simp only [mem_preimage, mem_image, mk'_eq_mk'_iff, mem_iUnion]
  exact ⟨fun ⟨w, hw, a, h⟩ ↦ ⟨a⁻¹, w, hw, by rw [← h, inv_smul_smul]⟩,
    fun ⟨a, w, hw, h⟩ ↦ ⟨w, hw, a⁻¹, by rw [← h, inv_smul_smul]⟩⟩

variable [TopologicalSpace V]

/-- The quotient topology on `ℙ K V`, coinduced by `Projectivization.mk'`. -/
instance instTopologicalSpace : TopologicalSpace (ℙ K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))

theorem isQuotientMap_mk' : IsQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  isQuotientMap_quotient_mk'

@[continuity, fun_prop]
theorem continuous_mk' : Continuous (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_quotient_mk'

variable {α : Type*} [TopologicalSpace α]

theorem continuous_iff {f : ℙ K V → α} : Continuous f ↔ Continuous (f ∘ mk' K) :=
  isQuotientMap_mk'.continuous_iff

variable [ContinuousConstSMul Kˣ V]

theorem isOpenMap_mk' : IsOpenMap (mk' K : {v : V // v ≠ 0} → ℙ K V) := fun U hU ↦ by
  rw [← isQuotientMap_mk'.isOpen_preimage, preimage_image_mk']
  exact isOpen_iUnion fun a ↦ isOpenMap_smul a U hU

theorem isOpenQuotientMap_mk' : IsOpenQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  ⟨Quotient.mk''_surjective, continuous_mk', isOpenMap_mk'⟩

end Projectivization
