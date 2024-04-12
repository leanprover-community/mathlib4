/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Yuyang Zhao
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

#align_import analysis.calculus.deriv.comp from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# One-dimensional derivatives of compositions of functions

In this file we prove the chain rule for the following cases:

* `HasDerivAt.comp` etc: `f : 𝕜' → 𝕜'` composed with `g : 𝕜 → 𝕜'`;
* `HasDerivAt.scomp` etc: `f : 𝕜' → E` composed with `g : 𝕜 → 𝕜'`;
* `HasFDerivAt.comp_hasDerivAt` etc: `f : E → F` composed with `g : 𝕜 → E`;

Here `𝕜` is the base normed field, `E` and `F` are normed spaces over `𝕜` and `𝕜'` is an algebra
over `𝕜` (e.g., `𝕜'=𝕜` or `𝕜=ℝ`, `𝕜'=ℂ`).

We also give versions with the `of_eq` suffix, which require an equality proof instead
of definitional equality of the different points used in the composition. These versions are
often more flexible to use.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative, chain rule
-/


universe u v w

open scoped Classical
open Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/


/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {h₁' : 𝕜} {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter 𝕜'} {y : 𝕜'} (x)

theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') x L := by
  simpa using ((hg.restrictScalars 𝕜).comp x hh hL).hasDerivAtFilter
#align has_deriv_at_filter.scomp HasDerivAtFilter.scomp

theorem HasDerivAtFilter.scomp_of_eq (hg : HasDerivAtFilter g₁ g₁' y L')
    (hh : HasDerivAtFilter h h' x L) (hy : y = h x) (hL : Tendsto h L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') x L := by
  rw [hy] at hg; exact hg.scomp x hh hL

theorem HasDerivWithinAt.scomp_hasDerivAt (hg : HasDerivWithinAt g₁ g₁' s' (h x))
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh <| tendsto_inf.2 ⟨hh.continuousAt, tendsto_principal.2 <| eventually_of_forall hs⟩
#align has_deriv_within_at.scomp_has_deriv_at HasDerivWithinAt.scomp_hasDerivAt

theorem HasDerivWithinAt.scomp_hasDerivAt_of_eq (hg : HasDerivWithinAt g₁ g₁' s' y)
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp_hasDerivAt x hh hs

nonrec theorem HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  hg.scomp x hh <| hh.continuousWithinAt.tendsto_nhdsWithin hst
#align has_deriv_within_at.scomp HasDerivWithinAt.scomp

theorem HasDerivWithinAt.scomp_of_eq (hg : HasDerivWithinAt g₁ g₁' t' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp x hh hst

/-- The chain rule. -/
nonrec theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh hh.continuousAt
#align has_deriv_at.scomp HasDerivAt.scomp

/-- The chain rule. -/
theorem HasDerivAt.scomp_of_eq
    (hg : HasDerivAt g₁ g₁' y) (hh : HasDerivAt h h' x) (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh

theorem HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  simpa using ((hg.restrictScalars 𝕜).comp x hh).hasStrictDerivAt
#align has_strict_deriv_at.scomp HasStrictDerivAt.scomp

theorem HasStrictDerivAt.scomp_of_eq
    (hg : HasStrictDerivAt g₁ g₁' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh

theorem HasDerivAt.scomp_hasDerivWithinAt (hg : HasDerivAt g₁ g₁' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh (mapsTo_univ _ _)
#align has_deriv_at.scomp_has_deriv_within_at HasDerivAt.scomp_hasDerivWithinAt

theorem HasDerivAt.scomp_hasDerivWithinAt_of_eq (hg : HasDerivAt g₁ g₁' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp_hasDerivWithinAt x hh

theorem derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) :=
  (HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh.hasDerivWithinAt hs).derivWithin hxs
#align deriv_within.scomp derivWithin.scomp

theorem derivWithin.scomp_of_eq (hg : DifferentiableWithinAt 𝕜' g₁ t' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hy : y = h x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) := by
  rw [hy] at hg; exact derivWithin.scomp x hg hh hs hxs

theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
  (HasDerivAt.scomp x hg.hasDerivAt hh.hasDerivAt).deriv
#align deriv.scomp deriv.scomp

theorem deriv.scomp_of_eq
    (hg : DifferentiableAt 𝕜' g₁ y) (hh : DifferentiableAt 𝕜 h x) (hy : y = h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) := by
  rw [hy] at hg; exact deriv.scomp x hg hh

/-! ### Derivative of the composition of a scalar and vector functions -/

theorem HasDerivAtFilter.comp_hasFDerivAtFilter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' (f x) L') (hf : HasFDerivAtFilter f f' x L'')
    (hL : Tendsto f L'' L') : HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') x L'' := by
  convert (hh₂.restrictScalars 𝕜).comp x hf hL
  ext x
  simp [mul_comm]
#align has_deriv_at_filter.comp_has_fderiv_at_filter HasDerivAtFilter.comp_hasFDerivAtFilter

theorem HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq
    {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' y L') (hf : HasFDerivAtFilter f f' x L'')
    (hL : Tendsto f L'' L') (hy : y = f x) : HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') x L'' := by
  rw [hy] at hh₂; exact hh₂.comp_hasFDerivAtFilter x hf hL

theorem HasStrictDerivAt.comp_hasStrictFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [HasStrictDerivAt] at hh
  convert (hh.restrictScalars 𝕜).comp x hf
  ext x
  simp [mul_comm]
#align has_strict_deriv_at.comp_has_strict_fderiv_at HasStrictDerivAt.comp_hasStrictFDerivAt

theorem HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' y) (hf : HasStrictFDerivAt f f' x) (hy : y = f x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasStrictFDerivAt x hf

theorem HasDerivAt.comp_hasFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.comp_hasFDerivAtFilter x hf hf.continuousAt
#align has_deriv_at.comp_has_fderiv_at HasDerivAt.comp_hasFDerivAt

theorem HasDerivAt.comp_hasFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivAt f f' x) (hy : y = f x) :
    HasFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasFDerivAt x hf

theorem HasDerivAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter x hf hf.continuousWithinAt
#align has_deriv_at.comp_has_fderiv_within_at HasDerivAt.comp_hasFDerivWithinAt

theorem HasDerivAt.comp_hasFDerivWithinAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivWithinAt f f' s x) (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf

theorem HasDerivWithinAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter x hf <| hf.continuousWithinAt.tendsto_nhdsWithin hst
#align has_deriv_within_at.comp_has_fderiv_within_at HasDerivWithinAt.comp_hasFDerivWithinAt

theorem HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t)
    (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf hst

/-! ### Derivative of the composition of two scalar functions -/

theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') x L := by
  rw [mul_comm]
  exact hh₂.scomp x hh hL
#align has_deriv_at_filter.comp HasDerivAtFilter.comp

theorem HasDerivAtFilter.comp_of_eq (hh₂ : HasDerivAtFilter h₂ h₂' y L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') (hy : y = h x) :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') x L := by
  rw [hy] at hh₂; exact hh₂.comp x hh hL

theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [mul_comm]
  exact hh₂.scomp x hh hst
#align has_deriv_within_at.comp HasDerivWithinAt.comp

theorem HasDerivWithinAt.comp_of_eq (hh₂ : HasDerivWithinAt h₂ h₂' s' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp x hh hst

/-- The chain rule.

Note that the function `h₂` is a function on an algebra. If you are looking for the chain rule
with `h₂` taking values in a vector space, use `HasDerivAt.scomp`. -/
nonrec theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  hh₂.comp x hh hh.continuousAt
#align has_deriv_at.comp HasDerivAt.comp

/-- The chain rule.

Note that the function `h₂` is a function on an algebra. If you are looking for the chain rule
with `h₂` taking values in a vector space, use `HasDerivAt.scomp_of_eq`. -/
theorem HasDerivAt.comp_of_eq
    (hh₂ : HasDerivAt h₂ h₂' y) (hh : HasDerivAt h h' x) (hy : y = h x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [hy] at hh₂; exact hh₂.comp x hh

theorem HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh
#align has_strict_deriv_at.comp HasStrictDerivAt.comp

theorem HasStrictDerivAt.comp_of_eq
    (hh₂ : HasStrictDerivAt h₂ h₂' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [hy] at hh₂; exact hh₂.comp x hh

theorem HasDerivAt.comp_hasDerivWithinAt (hh₂ : HasDerivAt h₂ h₂' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  hh₂.hasDerivWithinAt.comp x hh (mapsTo_univ _ _)
#align has_deriv_at.comp_has_deriv_within_at HasDerivAt.comp_hasDerivWithinAt

theorem HasDerivAt.comp_hasDerivWithinAt_of_eq (hh₂ : HasDerivAt h₂ h₂' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp_hasDerivWithinAt x hh

theorem derivWithin.comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x :=
  (hh₂.hasDerivWithinAt.comp x hh.hasDerivWithinAt hs).derivWithin hxs
#align deriv_within.comp derivWithin.comp

theorem derivWithin.comp_of_eq (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hy : y = h x) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x := by
  rw [hy] at hh₂; exact derivWithin.comp x hh₂ hh hs hxs

theorem deriv.comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  (hh₂.hasDerivAt.comp x hh.hasDerivAt).deriv
#align deriv.comp deriv.comp

theorem deriv.comp_of_eq (hh₂ : DifferentiableAt 𝕜' h₂ y) (hh : DifferentiableAt 𝕜 h x)
    (hy : y = h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x := by
  rw [hy] at hh₂; exact deriv.comp x hh₂ hh

protected nonrec theorem HasDerivAtFilter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasDerivAtFilter f f' x L) (hL : Tendsto f L L) (hx : f x = x) (n : ℕ) :
    HasDerivAtFilter f^[n] (f' ^ n) x L := by
  have := hf.iterate hL hx n
  rwa [ContinuousLinearMap.smulRight_one_pow] at this
#align has_deriv_at_filter.iterate HasDerivAtFilter.iterate

protected nonrec theorem HasDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasDerivAt f^[n] (f' ^ n) x :=
  hf.iterate _ (have := hf.tendsto_nhds le_rfl; by rwa [hx] at this) hx n
#align has_deriv_at.iterate HasDerivAt.iterate

protected theorem HasDerivWithinAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : HasDerivWithinAt f^[n] (f' ^ n) s x := by
  have := HasFDerivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.smulRight_one_pow] at this
#align has_deriv_within_at.iterate HasDerivWithinAt.iterate

protected nonrec theorem HasStrictDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictDerivAt f^[n] (f' ^ n) x := by
  have := hf.iterate hx n
  rwa [ContinuousLinearMap.smulRight_one_pow] at this
#align has_strict_deriv_at.iterate HasStrictDerivAt.iterate

end Composition

section CompositionVector

/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/

open ContinuousLinearMap

variable {l : F → E} {l' : F →L[𝕜] E} {y : F}
variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  simpa only [one_apply, one_smul, smulRight_apply, coe_comp', (· ∘ ·)] using
    (hl.comp x hf.hasFDerivWithinAt hst).hasDerivWithinAt
#align has_fderiv_within_at.comp_has_deriv_within_at HasFDerivWithinAt.comp_hasDerivWithinAt

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq {t : Set F}
    (hl : HasFDerivWithinAt l l' t y)
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf hst

theorem HasFDerivAt.comp_hasDerivWithinAt (hl : HasFDerivAt l l' (f x))
    (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (l ∘ f) (l' f') s x :=
  hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf (mapsTo_univ _ _)
#align has_fderiv_at.comp_has_deriv_within_at HasFDerivAt.comp_hasDerivWithinAt

theorem HasFDerivAt.comp_hasDerivWithinAt_of_eq (hl : HasFDerivAt l l' y)
    (hf : HasDerivWithinAt f f' s x) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x :=
  hasDerivWithinAt_univ.mp <| hl.comp_hasDerivWithinAt x hf.hasDerivWithinAt
#align has_fderiv_at.comp_has_deriv_at HasFDerivAt.comp_hasDerivAt

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivAt.comp_hasDerivAt_of_eq
    (hl : HasFDerivAt l l' y) (hf : HasDerivAt f f' x) (hy : y = f x) :
    HasDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasDerivAt x hf

theorem HasStrictFDerivAt.comp_hasStrictDerivAt (hl : HasStrictFDerivAt l l' (f x))
    (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (l ∘ f) (l' f') x := by
  simpa only [one_apply, one_smul, smulRight_apply, coe_comp', (· ∘ ·)] using
    (hl.comp x hf.hasStrictFDerivAt).hasStrictDerivAt
#align has_strict_fderiv_at.comp_has_strict_deriv_at HasStrictFDerivAt.comp_hasStrictDerivAt

theorem HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq (hl : HasStrictFDerivAt l l' y)
    (hf : HasStrictDerivAt f f' x) (hy : y = f x) :
    HasStrictDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasStrictDerivAt x hf

theorem fderivWithin.comp_derivWithin {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) :=
  (hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf.hasDerivWithinAt hs).derivWithin hxs
#align fderiv_within.comp_deriv_within fderivWithin.comp_derivWithin

theorem fderivWithin.comp_derivWithin_of_eq {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hy : y = f x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) := by
  rw [hy] at hl; exact fderivWithin.comp_derivWithin x hl hf hs hxs

theorem fderiv.comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
  (hl.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv
#align fderiv.comp_deriv fderiv.comp_deriv

theorem fderiv.comp_deriv_of_eq (hl : DifferentiableAt 𝕜 l y) (hf : DifferentiableAt 𝕜 f x)
    (hy : y = f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) := by
  rw [hy] at hl; exact fderiv.comp_deriv x hl hf

end CompositionVector
