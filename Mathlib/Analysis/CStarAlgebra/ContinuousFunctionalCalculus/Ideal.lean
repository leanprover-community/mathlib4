/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The non-unital continuous functional calculus maps into closed two-sided ideals

Let `A` be a non-unital C⋆-algebra, `I` a closed two-sided ideal of `A`, `a ∈ I`, and
`f : ℝ → ℝ`. In this file we prove that `cfcₙ f a ∈ I`. Since `cfcₙ f a` takes the junk value
`0 ∈ I` whenever `f` is not continuous on the quasispectrum, `f 0 ≠ 0`, or `a` is not selfadjoint,
no hypotheses on `f` beyond `f : ℝ → ℝ` are required: the statement holds unconditionally.

The proof spine is:

* A closed two-sided ideal in a non-unital C⋆-algebra is closed under the scalar action
  (`TwoSidedIdeal.smul_mem_of_isClosed`), proved using the canonical approximate unit
  `CStarAlgebra.approximateUnit`: for `y ∈ I` and a scalar `r`, we have
  `r • y = lim (r • (eₗ * y)) = lim ((r • eₗ) * y)`, and each `(r • eₗ) * y ∈ I`, so `r • y ∈ I`.
* The set of elements `g : C(σₙ ℝ a, ℝ)₀` with `cfcₙHom ha g ∈ I` is closed (preimage of the
  closed set `I` under the continuous map `cfcₙHom ha`), a non-unital `ℝ`-subalgebra containing
  the identity (which maps to `a ∈ I`) and its star (which maps to `star a = a ∈ I`). By the
  Weierstrass approximation theorem for `C(σₙ ℝ a, ℝ)₀`
  (`ContinuousMapZero.induction_on_of_compact`), it is everything.

## Main results

* `TwoSidedIdeal.smul_mem_of_isClosed`: a closed two-sided ideal in a non-unital C⋆-algebra is
  closed under the scalar action.
* `TwoSidedIdeal.cfcₙHom_mem_of_isClosed`: for a selfadjoint `a` in a closed two-sided ideal `I`,
  every value `cfcₙHom ha g` of the underlying homomorphism lies in `I`.
* `TwoSidedIdeal.cfcₙ_mem_of_isClosed`: the main result, `cfcₙ f a ∈ I` for `a ∈ I` and
  `I` closed.
-/

@[expose] public section

open scoped ContinuousMapZero
open Topology Filter CStarAlgebra

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A closed two-sided ideal in a non-unital C⋆-algebra is closed under the scalar action.

This upgrades the purely ring-theoretic notion of a two-sided ideal to a submodule, using that a
closed two-sided ideal in a C⋆-algebra is invariant under the canonical approximate unit. -/
theorem smul_mem_of_isClosed {𝕜 : Type*} [SMul 𝕜 A] [ContinuousConstSMul 𝕜 A]
    [IsScalarTower 𝕜 A A] {I : TwoSidedIdeal A} (hI : IsClosed (I : Set A)) {y : A}
    (hy : y ∈ I) (r : 𝕜) : r • y ∈ I := by
  haveI : (approximateUnit A).NeBot := (increasingApproximateUnit A).neBot
  have h : Tendsto (fun x => r • (x * y)) (approximateUnit A) (𝓝 (r • y)) :=
    ((increasingApproximateUnit A).tendsto_mul_right y).const_smul r
  refine hI.mem_of_tendsto h (Eventually.of_forall fun x => ?_)
  show r • (x * y) ∈ I
  rw [← smul_mul_assoc]
  exact I.mul_mem_left (r • x) y hy

/-- For a selfadjoint element `a` of a closed two-sided ideal `I` in a non-unital C⋆-algebra, every
value of the non-unital continuous functional calculus homomorphism `cfcₙHom` lies in `I`. -/
theorem cfcₙHom_mem_of_isClosed {I : TwoSidedIdeal A} (hI : IsClosed (I : Set A)) {a : A}
    (ha : a ∈ I) (ha' : IsSelfAdjoint a) (g : C(quasispectrum ℝ a, ℝ)₀) :
    cfcₙHom ha' g ∈ I := by
  have h0 : ((0 : quasispectrum ℝ a) : ℝ) = 0 := rfl
  have hid : cfcₙHom ha' (ContinuousMapZero.id h0) = a := by
    rw [show (ContinuousMapZero.id h0 : C(quasispectrum ℝ a, ℝ)₀) =
        ⟨(ContinuousMap.id ℝ).restrict (quasispectrum ℝ a), rfl⟩ from rfl]
    exact cfcₙHom_id ha'
  induction g using ContinuousMapZero.induction_on_of_compact h0 with
  | zero => simp only [map_zero]; exact I.zero_mem
  | id => rw [hid]; exact ha
  | star_id => rw [map_star, hid, ha'.star_eq]; exact ha
  | add f g hf hg => rw [map_add]; exact I.add_mem hf hg
  | mul f g hf hg => rw [map_mul]; exact I.mul_mem_left _ _ hg
  | smul r f hf => rw [map_smul]; exact smul_mem_of_isClosed hI hf r
  | frequently f h => exact h.mem_of_closed (hI.preimage (cfcₙHom_continuous ha'))

/-- **The non-unital continuous functional calculus maps into closed two-sided ideals.** If `I` is a
closed two-sided ideal of a non-unital C⋆-algebra `A`, `a ∈ I`, and `f : ℝ → ℝ`, then
`cfcₙ f a ∈ I`.

No continuity or `f 0 = 0` hypotheses are needed: in every case where `cfcₙ` would take its junk
value, that value is `0 ∈ I`. -/
theorem cfcₙ_mem_of_isClosed {I : TwoSidedIdeal A} (hI : IsClosed (I : Set A)) {a : A}
    (ha : a ∈ I) (f : ℝ → ℝ) : cfcₙ f a ∈ I :=
  cfcₙ_cases (· ∈ I) a f I.zero_mem fun _ _ ha' => cfcₙHom_mem_of_isClosed hI ha ha' _

end TwoSidedIdeal

