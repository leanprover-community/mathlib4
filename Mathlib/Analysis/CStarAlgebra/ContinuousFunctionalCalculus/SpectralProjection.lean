/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Ideal
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Algebra.GroupWithZero.Indicator

/-!
# Spectral projections from clopen subsets of the quasispectrum

Let `A` be a non-unital C⋆-algebra and `a : A` a selfadjoint element. If `U : Set ℝ` is clopen in
the (non-unital) quasispectrum `σₙ ℝ a := quasispectrum ℝ a` and `0 ∉ U`, then the real-valued
indicator function `U.indicator 1` is continuous on `σₙ ℝ a` and vanishes at `0`, so the non-unital
continuous functional calculus produces an element

  `spectralProjection a U := cfcₙ (U.indicator 1) a`.

Because the indicator is idempotent and real-valued, this element is a *projection*: it is
selfadjoint and idempotent. It is nonzero exactly when `U` meets the quasispectrum, and — crucially
for the theory of ideals — it lies inside any closed two-sided ideal containing `a`
(via `TwoSidedIdeal.cfcₙ_mem_of_isClosed`). Thus a clopen spectral set away from `0` manufactures a
genuine projection inside a nonzero ideal.

## Main definitions and results

* `spectralProjection a U`: the value of the non-unital continuous functional calculus at the
  indicator function of `U`.
* `isSelfAdjoint_spectralProjection`: `spectralProjection a U` is selfadjoint.
* `isIdempotentElem_spectralProjection`: for `U` clopen in `σₙ ℝ a` with `0 ∉ U`,
  `spectralProjection a U` is idempotent.
* `spectralProjection_mem`: if `a` belongs to a closed two-sided ideal `I`, then so does
  `spectralProjection a U`.
* `spectralProjection_eq_zero_iff` / `spectralProjection_ne_zero`: `spectralProjection a U`
  vanishes iff `U` misses the quasispectrum, and is nonzero as soon as `U` meets it.
* `spectralProjection_ne_zero_of_finite_quasispectrum`: when the quasispectrum is finite (e.g. in
  AF/UHF or matrix C⋆-algebras) every point is isolated, so a nonzero selfadjoint element yields a
  nonzero projection.
-/

@[expose] public section

open Set
open scoped ContinuousMapZero

namespace CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- If `U : Set ℝ` is clopen in the quasispectrum of `a` (i.e. its preimage under the subtype
coercion is clopen), then the real-valued indicator function `U.indicator 1` is continuous on the
quasispectrum. -/
theorem continuousOn_indicator_one_of_isClopen {a : A} {U : Set ℝ}
    (hU : IsClopen (Subtype.val ⁻¹' U : Set (quasispectrum ℝ a))) :
    ContinuousOn (U.indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (quasispectrum ℝ a).domRestrict (U.indicator (1 : ℝ → ℝ))
      = (Subtype.val ⁻¹' U : Set (quasispectrum ℝ a)).indicator (fun _ => (1 : ℝ)) := by
    ext x
    rw [Set.domRestrict_apply]
    by_cases hx : (x : ℝ) ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_preimage.mpr hx)]; rfl
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h => hx (Set.mem_preimage.mp h))]
  rw [h]
  exact hU.continuous_indicator continuous_const

/-- The **spectral projection** attached to a subset `U` of the reals: the value of the non-unital
continuous functional calculus of `a` at the indicator function of `U`. When `U` is clopen in the
quasispectrum of a selfadjoint `a` and `0 ∉ U`, this is a genuine projection
(`isSelfAdjoint_spectralProjection`, `isIdempotentElem_spectralProjection`). -/
noncomputable def spectralProjection (a : A) (U : Set ℝ) : A :=
  cfcₙ (U.indicator (1 : ℝ → ℝ)) a

/-- A spectral projection is selfadjoint. This needs no hypotheses: it is the defining predicate of
the real non-unital continuous functional calculus, and holds even for the junk value `0`. -/
theorem isSelfAdjoint_spectralProjection (a : A) (U : Set ℝ) :
    IsSelfAdjoint (spectralProjection a U) :=
  cfcₙ_predicate _ a

/-- A spectral projection attached to a clopen set `U` away from `0` is idempotent, because the
indicator function is idempotent pointwise. -/
theorem isIdempotentElem_spectralProjection {a : A} {U : Set ℝ}
    (hU : IsClopen (Subtype.val ⁻¹' U : Set (quasispectrum ℝ a))) (h0 : (0 : ℝ) ∉ U) :
    IsIdempotentElem (spectralProjection a U) := by
  have hcont : ContinuousOn (U.indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
    continuousOn_indicator_one_of_isClopen hU
  have hzero : (U.indicator (1 : ℝ → ℝ)) 0 = 0 := Set.indicator_of_notMem h0 _
  rw [IsIdempotentElem, spectralProjection, ← cfcₙ_mul _ _ a hcont hzero hcont hzero]
  refine cfcₙ_congr (fun x _ => ?_)
  by_cases hx : x ∈ U <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- If `a` lies in a closed two-sided ideal `I`, then so does every spectral projection of `a`.
This is immediate from the fact that the non-unital continuous functional calculus maps into closed
two-sided ideals. -/
theorem spectralProjection_mem [PartialOrder A] [StarOrderedRing A] {I : TwoSidedIdeal A}
    (hI : IsClosed (I : Set A)) {a : A} (ha : a ∈ I) (U : Set ℝ) : spectralProjection a U ∈ I :=
  TwoSidedIdeal.cfcₙ_mem_of_isClosed hI ha _

/-- A spectral projection vanishes exactly when `U` misses the quasispectrum. -/
theorem spectralProjection_eq_zero_iff {a : A} (ha : IsSelfAdjoint a) {U : Set ℝ}
    (hU : IsClopen (Subtype.val ⁻¹' U : Set (quasispectrum ℝ a))) (h0 : (0 : ℝ) ∉ U) :
    spectralProjection a U = 0 ↔ ∀ x ∈ quasispectrum ℝ a, x ∉ U := by
  have hcont : ContinuousOn (U.indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
    continuousOn_indicator_one_of_isClopen hU
  have hzero : (U.indicator (1 : ℝ → ℝ)) 0 = 0 := Set.indicator_of_notMem h0 _
  rw [spectralProjection, ← cfcₙ_zero ℝ a,
    cfcₙ_eq_cfcₙ_iff_eqOn (f := U.indicator (1 : ℝ → ℝ)) (g := 0) (a := a) ha hcont hzero]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · exact (Set.indicator_eq_zero_iff_notMem ℝ).mp (by simpa using h hx)
  · simpa using (Set.indicator_eq_zero_iff_notMem ℝ).mpr (h x hx)

/-- A spectral projection is nonzero as soon as `U` meets the quasispectrum. -/
theorem spectralProjection_ne_zero {a : A} (ha : IsSelfAdjoint a) {U : Set ℝ}
    (hU : IsClopen (Subtype.val ⁻¹' U : Set (quasispectrum ℝ a))) (h0 : (0 : ℝ) ∉ U)
    (hne : (U ∩ quasispectrum ℝ a).Nonempty) : spectralProjection a U ≠ 0 := by
  rw [Ne, spectralProjection_eq_zero_iff ha hU h0]
  push Not
  obtain ⟨x, hxU, hxσ⟩ := hne
  exact ⟨x, hxσ, hxU⟩

/-- When the quasispectrum of `a` is finite, the subspace topology on it is discrete, so *every*
subset of the reals is clopen in the quasispectrum. This is the mechanism by which finite-spectrum
C⋆-algebras (AF/UHF, matrix algebras) admit spectral projections onto arbitrary spectral values. -/
theorem isClopen_of_finite_quasispectrum {a : A} [Finite (quasispectrum ℝ a)] (U : Set ℝ) :
    IsClopen (Subtype.val ⁻¹' U : Set (quasispectrum ℝ a)) :=
  isClopen_discrete _

/-- **A nonzero selfadjoint element in a finite-quasispectrum C⋆-algebra admits a nonzero spectral
projection.** If `σₙ ℝ a` is finite and contains a nonzero point `μ`, then the projection onto
`{μ}` is nonzero (and, by `spectralProjection_mem`, lies in any closed two-sided ideal containing
`a`). Finiteness of the quasispectrum holds for matrix and AF/UHF C⋆-algebras; it is what upgrades
the mere existence of a nonzero spectral value to an *isolated* one. -/
theorem spectralProjection_singleton_ne_zero {a : A} (ha : IsSelfAdjoint a)
    [Finite (quasispectrum ℝ a)] {μ : ℝ} (hμ : μ ∈ quasispectrum ℝ a) (hμ0 : μ ≠ 0) :
    spectralProjection a {μ} ≠ 0 :=
  spectralProjection_ne_zero ha (isClopen_of_finite_quasispectrum {μ})
    (by simpa using hμ0.symm) ⟨μ, rfl, hμ⟩

end CStarAlgebra

-- Axiom audit (to be removed before upstreaming)
