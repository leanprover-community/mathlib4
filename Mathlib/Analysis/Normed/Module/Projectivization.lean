/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Projectivization

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Projective space is Hausdorff and compact

We show that `ℙ K V`, with the quotient topology of `Mathlib.Topology.Algebra.Projectivization`,
is Hausdorff when `K` is Hausdorff with continuous multiplication, units of `K` act continuously on
`V`, and continuous linear forms separate the points of `V`; and that it is compact when `V` is a
finite-dimensional topological vector space over a locally compact nontrivially normed field.

## Main results

* `SeparatingDual.of_finiteDimensional`: continuous linear forms separate the points of a
  finite-dimensional Hausdorff topological vector space over a complete nontrivially normed field.
  With it, `ℙ K V` is compact Hausdorff for every such `V` over a complete locally compact field,
  such as `ℝ`, `ℂ` or `ℚ_[p]`.
* `Projectivization.mk'_eq_mk'_iff_forall_mul_eq`: if continuous linear forms separate points,
  two nonzero vectors span the same line iff `f v * g w = f w * g v` for all continuous linear
  forms `f` and `g`.
* `Projectivization.instT2Space`: `ℙ K V` is Hausdorff under the hypotheses above.
* `Projectivization.compactSpace_of_properSpace`: `ℙ K V` is compact when `V` is a proper normed
  space over a nontrivially normed field `K`.
* `Projectivization.instCompactSpace`: `ℙ K V` is compact when `V` is a finite-dimensional
  topological vector space over a locally compact nontrivially normed field `K`.

## Implementation notes

The Hausdorff half is adapted from the Tau Ceti project's
`TauCeti/Topology/Algebra/Projectivization.lean`, which builds on the quotient topology of
`Mathlib.Topology.Algebra.Projectivization`:
https://github.com/TauCetiProject/TauCeti/blob/06c598245d42977f79bf09aafd3154dd215c23cd/TauCeti/Topology/Algebra/Projectivization.lean
Its `mk'_eq_mk'_iff_forall_strongDual` is the minors criterion (proved differently here) and its
`instT2Space` has the same statement and argument. The compactness results and
`SeparatingDual.of_finiteDimensional` are new.
-/

public section

open scoped LinearAlgebra.Projectivization

/-- In a finite-dimensional Hausdorff topological vector space over a complete nontrivially normed
field every linear form is continuous, so continuous linear forms separate points. -/
instance SeparatingDual.of_finiteDimensional {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    SeparatingDual 𝕜 E :=
  ⟨fun _ hx ↦ by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero 𝕜 hx
    exact ⟨⟨f, f.continuous_of_finiteDimensional⟩, hf⟩⟩

namespace Projectivization

section T2

variable {K V : Type*} [Field K] [TopologicalSpace K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V]

/-- If continuous linear forms separate the points of `V`, two nonzero vectors span the same line
iff `f v * g w = f w * g v` for all continuous linear forms `f` and `g`. The proof uses that `K` is
commutative. -/
theorem mk'_eq_mk'_iff_forall_mul_eq [SeparatingDual K V] (v w : {v : V // v ≠ 0}) :
    mk' K v = mk' K w ↔ ∀ f g : StrongDual K V, f v * g w = f w * g v := by
  rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩ f g
    simp only [← ha, map_smul, smul_eq_mul]
    ring
  · intro h
    obtain ⟨f, hf⟩ := SeparatingDual.exists_ne_zero (R := K) w.2
    refine ⟨f v / f w, ?_⟩
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := K)).2
    intro g
    rw [map_smul, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hf, h f g, mul_comm]

/-- **Projective space is Hausdorff** when continuous linear forms separate the points of `V`.
Since `mk'` is an open quotient map, it is enough that the relation of spanning the same line is
closed; by `mk'_eq_mk'_iff_forall_mul_eq` it is an intersection of zero sets of continuous
functions. -/
instance instT2Space [T2Space K] [ContinuousMul K] [ContinuousConstSMul Kˣ V]
    [SeparatingDual K V] : T2Space (ℙ K V) := by
  rw [t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_mk']
  simp only [mk'_eq_mk'_iff_forall_mul_eq, Set.ofPred_forall]
  exact isClosed_iInter fun f ↦ isClosed_iInter fun g ↦ isClosed_eq (by fun_prop) (by fun_prop)

end T2

section Proper

variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

/-- **Projective space is compact** when `V` is a proper normed space: every line meets the
compact shell `{v | 1 / ‖c‖ ≤ ‖v‖ ≤ 1}`, for any `c` with `1 < ‖c‖`. -/
theorem compactSpace_of_properSpace [ProperSpace V] : CompactSpace (ℙ K V) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  let S : Set V := {v | 1 / ‖c‖ ≤ ‖v‖ ∧ ‖v‖ ≤ 1}
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : V) 1).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun v hv ↦ mem_closedBall_zero_iff.mpr hv.2
  have h0 : ∀ v ∈ S, v ≠ 0 := by
    rintro v ⟨hv, -⟩ rfl
    rw [norm_zero] at hv
    exact (one_div_pos.mpr (one_pos.trans hc)).not_ge hv
  have := isCompact_iff_compactSpace.mp hS
  refine Function.Surjective.compactSpace (f := fun v : S ↦ mk K (v : V) (h0 v v.2))
    (continuous_mk continuous_subtype_val fun v ↦ h0 v v.2) ?_
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    obtain ⟨d, -, hlt, hle, -⟩ := rescale_to_shell hc one_pos hv
    refine ⟨⟨d • v, hle, hlt.le⟩, ?_⟩
    exact (mk_eq_mk_iff' K _ _ _ hv).mpr ⟨d, rfl⟩

end Proper

section FiniteDimensional

variable {K V : Type*} [NontriviallyNormedField K] [LocallyCompactSpace K] [AddCommGroup V]
  [TopologicalSpace V] [Module K V] [ContinuousAdd V] [ContinuousSMul K V]

/-- **Projective space is compact** when `V` is a finite-dimensional topological vector space
over a locally compact nontrivially normed field: a basis maps the projective space of
`Fin n → K`, compact by `compactSpace_of_properSpace`, continuously onto `ℙ K V`. -/
instance instCompactSpace [FiniteDimensional K V] : CompactSpace (ℙ K V) := by
  have : ProperSpace (Fin (Module.finrank K V) → K) := FiniteDimensional.proper K _
  have : CompactSpace (ℙ K (Fin (Module.finrank K V) → K)) := compactSpace_of_properSpace
  let e := (Module.finBasis K V).equivFun.symm
  refine Function.Surjective.compactSpace (f := map e.toLinearMap e.injective)
    (continuous_map e.injective e.toLinearMap.continuous_on_pi) ?_
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    refine ⟨mk K (e.symm v) fun h ↦ hv (e.symm.map_eq_zero_iff.mp h), ?_⟩
    simp only [map_mk, LinearEquiv.coe_coe, e.apply_symm_apply]

end FiniteDimensional

end Projectivization
