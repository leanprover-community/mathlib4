/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov, Frédéric Dupuis
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.Basic

#align_import topology.algebra.infinite_sum.module from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-! # Infinite sums in topological vector spaces -/


variable {ι κ R R₂ M M₂ : Type*}

section SMulConst

variable [Semiring R] [TopologicalSpace R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousSMul R M] {f : ι → R}

theorem HasSum.smul_const {r : R} (hf : HasSum f r) (a : M) : HasSum (fun z => f z • a) (r • a) :=
  hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)
#align has_sum.smul_const HasSum.smul_const

theorem Summable.smul_const (hf : Summable f) (a : M) : Summable fun z => f z • a :=
  (hf.hasSum.smul_const _).summable
#align summable.smul_const Summable.smul_const

theorem tsum_smul_const [T2Space M] (hf : Summable f) (a : M) : ∑' z, f z • a = (∑' z, f z) • a :=
  (hf.hasSum.smul_const _).tsum_eq
#align tsum_smul_const tsum_smul_const

end SMulConst

/-!
Note we cannot derive the `mul` lemmas from these `smul` lemmas, as the `mul` versions do not
require associativity, but `Module` does.
-/
section tsum_smul_tsum

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace R] [TopologicalSpace M] [T3Space M]
variable [ContinuousAdd M] [ContinuousSMul R M]
variable {f : ι → R} {g : κ → M} {s : R} {t u : M}

theorem HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ => f x.1 • g x.2) u) : s • t = u :=
  have key₁ : HasSum (fun i => f i • t) (s • t) := hf.smul_const t
  have this : ∀ i : ι, HasSum (fun c : κ => f i • g c) (f i • t) := fun i => hg.const_smul (f i)
  have key₂ : HasSum (fun i => f i • t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

theorem HasSum.smul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ => f x.1 • g x.2) :
    HasSum (fun x : ι × κ => f x.1 • g x.2) (s • t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.smul_eq hg hu).symm ▸ hu

/-- Scalar product of two infinites sums indexed by arbitrary types. -/
theorem tsum_smul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ => f x.1 • g x.2) :
    ((∑' x, f x) • ∑' y, g y) = ∑' z : ι × κ, f z.1 • g z.2 :=
  hf.hasSum.smul_eq hg.hasSum hfg.hasSum

end tsum_smul_tsum

section HasSum

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we
-- don't have bundled continuous additive homomorphisms.
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] {σ : R →+* R₂} {σ' : R₂ →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearMap.hasSum {f : ι → M} (φ : M →SL[σ] M₂) {x : M}
    (hf : HasSum f x) : HasSum (fun b : ι => φ (f b)) (φ x) := by
  simpa only using hf.map φ.toLinearMap.toAddMonoidHom φ.continuous
#align continuous_linear_map.has_sum ContinuousLinearMap.hasSum

alias HasSum.mapL := ContinuousLinearMap.hasSum
set_option linter.uppercaseLean3 false in
#align has_sum.mapL HasSum.mapL

protected theorem ContinuousLinearMap.summable {f : ι → M} (φ : M →SL[σ] M₂) (hf : Summable f) :
    Summable fun b : ι => φ (f b) :=
  (hf.hasSum.mapL φ).summable
#align continuous_linear_map.summable ContinuousLinearMap.summable

alias Summable.mapL := ContinuousLinearMap.summable
set_option linter.uppercaseLean3 false in
#align summable.mapL Summable.mapL

protected theorem ContinuousLinearMap.map_tsum [T2Space M₂] {f : ι → M} (φ : M →SL[σ] M₂)
    (hf : Summable f) : φ (∑' z, f z) = ∑' z, φ (f z) :=
  (hf.hasSum.mapL φ).tsum_eq.symm
#align continuous_linear_map.map_tsum ContinuousLinearMap.map_tsum

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearEquiv.hasSum {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
    HasSum (fun b : ι => e (f b)) y ↔ HasSum f (e.symm y) :=
  ⟨fun h => by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →SL[σ'] M),
    fun h => by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →SL[σ] M₂).hasSum h⟩
#align continuous_linear_equiv.has_sum ContinuousLinearEquiv.hasSum

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearEquiv.hasSum' {f : ι → M} (e : M ≃SL[σ] M₂) {x : M} :
    HasSum (fun b : ι => e (f b)) (e x) ↔ HasSum f x := by
  rw [e.hasSum, ContinuousLinearEquiv.symm_apply_apply]
#align continuous_linear_equiv.has_sum' ContinuousLinearEquiv.hasSum'

protected theorem ContinuousLinearEquiv.summable {f : ι → M} (e : M ≃SL[σ] M₂) :
    (Summable fun b : ι => e (f b)) ↔ Summable f :=
  ⟨fun hf => (e.hasSum.1 hf.hasSum).summable, (e : M →SL[σ] M₂).summable⟩
#align continuous_linear_equiv.summable ContinuousLinearEquiv.summable

theorem ContinuousLinearEquiv.tsum_eq_iff [T2Space M] [T2Space M₂] {f : ι → M} (e : M ≃SL[σ] M₂)
    {y : M₂} : (∑' z, e (f z)) = y ↔ ∑' z, f z = e.symm y := by
  by_cases hf : Summable f
  · exact
      ⟨fun h => (e.hasSum.mp ((e.summable.mpr hf).hasSum_iff.mpr h)).tsum_eq, fun h =>
        (e.hasSum.mpr (hf.hasSum_iff.mpr h)).tsum_eq⟩
  · have hf' : ¬Summable fun z => e (f z) := fun h => hf (e.summable.mp h)
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hf']
    refine ⟨?_, fun H => ?_⟩
    · rintro rfl
      simp
    · simpa using congr_arg (fun z => e z) H
#align continuous_linear_equiv.tsum_eq_iff ContinuousLinearEquiv.tsum_eq_iff

protected theorem ContinuousLinearEquiv.map_tsum [T2Space M] [T2Space M₂] {f : ι → M}
    (e : M ≃SL[σ] M₂) : e (∑' z, f z) = ∑' z, e (f z) := by
  refine' symm (e.tsum_eq_iff.mpr _)
  rw [e.symm_apply_apply _]
#align continuous_linear_equiv.map_tsum ContinuousLinearEquiv.map_tsum

end HasSum
