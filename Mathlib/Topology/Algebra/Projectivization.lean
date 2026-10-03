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
* `Projectivization.continuous_mk`, `Projectivization.continuous_map`: `Projectivization.mk`
  and `Projectivization.map` are continuous.
-/

@[expose] public section

open Set Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

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

/-- `Projectivization.mk` is continuous in the vector, as long as the vector stays nonzero. -/
@[continuity, fun_prop]
theorem continuous_mk {f : α → V} (hf : Continuous f) (hf₀ : ∀ x, f x ≠ 0) :
    Continuous fun x ↦ mk K (f x) (hf₀ x) :=
  continuous_mk'.comp (hf.subtype_mk hf₀)

section Map

variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W] [TopologicalSpace W]

/-- An injective continuous semilinear map induces a continuous map on projective spaces. -/
theorem continuous_map {σ : K →+* L} {f : V →ₛₗ[σ] W} (hf : Function.Injective f)
    (hfc : Continuous f) : Continuous (map f hf) :=
  continuous_iff.2 <| continuous_mk (hfc.comp continuous_subtype_val) fun v ↦
    map_zero f ▸ hf.ne v.2

end Map

variable [ContinuousConstSMul Kˣ V]

theorem isOpenMap_mk' : IsOpenMap (mk' K : {v : V // v ≠ 0} → ℙ K V) := fun U hU ↦ by
  rw [← isQuotientMap_mk'.isOpen_preimage, preimage_image_mk']
  exact isOpen_iUnion fun a ↦ isOpenMap_smul a U hU

theorem isOpenQuotientMap_mk' : IsOpenQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  ⟨Quotient.mk''_surjective, continuous_mk', isOpenMap_mk'⟩

end Projectivization
