/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Yuyang Zhao
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

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
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, chain rule
-/
set_option backward.defeqAttrib.useBackward true

public section


universe u v w

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector-valued and scalar-valued functions, and `comp`
in lemmas on composition of scalar-valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/


/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter (𝕜' × 𝕜')} {y : 𝕜'} (x)

theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' L')
    (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') L := by
  simpa using ((hg.hasFDerivAtFilter.restrictScalars 𝕜).comp hh hL).hasDerivAtFilter

@[deprecated HasDerivAtFilter.scomp (since := "2026-02-17")]
theorem HasDerivAtFilter.scomp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'}
    (hg : HasDerivAtFilter g₁ g₁' (L' ×ˢ pure y)) (hh : HasDerivAtFilter h h' (L ×ˢ pure x))
    (hy : y = h x) (hL : Tendsto h L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') (L ×ˢ pure x) :=
  hg.scomp hh <| .prodMap hL <| by simp [hy]

theorem HasDerivWithinAt.scomp_hasDerivAt (hg : HasDerivWithinAt g₁ g₁' s' (h x))
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp hh <| .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, .of_forall hs⟩)
    (tendsto_pure_pure _ _)

theorem HasDerivWithinAt.scomp_hasDerivAt_of_eq (hg : HasDerivWithinAt g₁ g₁' s' y)
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp_hasDerivAt x hh hs

theorem HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivAtFilter.scomp hg hh <| hh.continuousWithinAt.tendsto_nhdsWithin hst |>.prodMap <|
    tendsto_pure_pure ..

theorem HasDerivWithinAt.scomp_of_eq (hg : HasDerivWithinAt g₁ g₁' t' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp x hh hst

/-- The chain rule. -/
theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  HasDerivAtFilter.scomp hg hh <| hh.continuousAt.tendsto.prodMap <| tendsto_pure_pure _ _

/-- The chain rule. -/
theorem HasDerivAt.scomp_of_eq
    (hg : HasDerivAt g₁ g₁' y) (hh : HasDerivAt h h' x) (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh

theorem HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x :=
  HasDerivAtFilter.scomp hg hh <|
    hh.hasStrictFDerivAt.continuousAt.prodMap hh.hasStrictFDerivAt.continuousAt

theorem HasStrictDerivAt.scomp_of_eq
    (hg : HasStrictDerivAt g₁ g₁' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh

theorem HasDerivAt.scomp_hasDerivWithinAt (hg : HasDerivAt g₁ g₁' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh (mapsTo_univ _ _)

theorem HasDerivAt.scomp_hasDerivWithinAt_of_eq (hg : HasDerivAt g₁ g₁' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp_hasDerivWithinAt x hh

theorem derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin.scomp_of_eq (hg : DifferentiableWithinAt 𝕜' g₁ t' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t')
    (hy : y = h x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) := by
  rw [hy] at hg; exact derivWithin.scomp x hg hh hs

theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
  (HasDerivAt.scomp x hg.hasDerivAt hh.hasDerivAt).deriv

theorem deriv.scomp_of_eq
    (hg : DifferentiableAt 𝕜' g₁ y) (hh : DifferentiableAt 𝕜 h x) (hy : y = h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) := by
  rw [hy] at hg; exact deriv.scomp x hg hh

/-! ### Derivative of the composition of a scalar and vector functions -/

theorem HasDerivAtFilter.comp_hasFDerivAtFilter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'}
    {L'' : Filter (E × E)} (hh₂ : HasDerivAtFilter h₂ h₂' L') (hf : HasFDerivAtFilter f f' L'')
    (hL : Tendsto (Prod.map f f) L'' L') :
    HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') L'' := by
  convert (hh₂.restrictScalars 𝕜).comp hf hL
  ext x
  simp [mul_comm]

@[deprecated HasDerivAtFilter.comp_hasFDerivAtFilter (since := "2026-02-17")]
theorem HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq
    {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) {L' : Filter 𝕜'} {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y)) (hf : HasFDerivAtFilter f f' (L'' ×ˢ pure x))
    (hL : Tendsto f L'' L') (hy : y = f x) :
    HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') (L'' ×ˢ pure x) :=
  hh₂.comp_hasFDerivAtFilter hf <| hL.prodMap <| by simp [hy]

theorem HasStrictDerivAt.comp_hasStrictFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  HasDerivAtFilter.comp_hasFDerivAtFilter hh hf <| hf.continuousAt.prodMap hf.continuousAt

theorem HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' y) (hf : HasStrictFDerivAt f f' x) (hy : y = f x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasStrictFDerivAt x hf

theorem HasDerivAt.comp_hasFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.comp_hasFDerivAtFilter hf <| hf.continuousAt.tendsto.prodMap <| tendsto_pure_pure _ _

theorem HasDerivAt.comp_hasFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivAt f f' x) (hy : y = f x) :
    HasFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasFDerivAt x hf

theorem HasDerivAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter hf <| hf.continuousWithinAt.tendsto.prodMap <| tendsto_pure_pure _ _

theorem HasDerivAt.comp_hasFDerivWithinAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivWithinAt f f' s x) (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf

theorem HasDerivWithinAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter hf <| hf.continuousWithinAt.tendsto_nhdsWithin hst |>.prodMap <|
    tendsto_pure_pure _ _

theorem HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t)
    (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf hst

theorem HasDerivWithinAt.comp_hasFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) :
    HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.comp_hasFDerivAtFilter hf <| tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩ |>.prodMap <|
    tendsto_pure_pure _ _

theorem HasDerivWithinAt.comp_hasFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t)
    (hy : y = f x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  subst y; exact hh.comp_hasFDerivAt x hf ht

/-! ### Derivative of the composition of two scalar functions -/

theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' L')
    (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') L := by
  rw [mul_comm]
  exact hh₂.scomp hh hL

@[deprecated HasDerivAtFilter.comp (since := "2026-07-17")]
theorem HasDerivAtFilter.comp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'}
    (hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y))
    (hh : HasDerivAtFilter h h' (L ×ˢ pure x)) (hL : Tendsto h L L') (hy : y = h x) :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') (L ×ˢ pure x) :=
  hh₂.comp hh <| hL.prodMap <| by simp [hy]

theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [mul_comm]
  exact hh₂.scomp x hh hst

theorem HasDerivWithinAt.comp_of_eq (hh₂ : HasDerivWithinAt h₂ h₂' s' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp x hh hst

/-- The chain rule.

Note that the function `h₂` is a function on an algebra. If you are looking for the chain rule
with `h₂` taking values in a vector space, use `HasDerivAt.scomp`. -/
theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  HasDerivAtFilter.comp hh₂ hh <| hh.continuousAt.tendsto.prodMap <| tendsto_pure_pure _ _

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

theorem HasStrictDerivAt.comp_of_eq
    (hh₂ : HasStrictDerivAt h₂ h₂' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [hy] at hh₂; exact hh₂.comp x hh

theorem HasDerivAt.comp_hasDerivWithinAt (hh₂ : HasDerivAt h₂ h₂' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  hh₂.hasDerivWithinAt.comp x hh (mapsTo_univ _ _)

theorem HasDerivAt.comp_hasDerivWithinAt_of_eq (hh₂ : HasDerivAt h₂ h₂' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp_hasDerivWithinAt x hh

theorem HasDerivWithinAt.comp_hasDerivAt {t} (hh₂ : HasDerivWithinAt h₂ h₂' t (h x))
    (hh : HasDerivAt h h' x) (ht : ∀ᶠ x' in 𝓝 x, h x' ∈ t) : HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  HasDerivAtFilter.comp hh₂ hh <| tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, ht⟩ |>.prodMap <|
    tendsto_pure_pure _ _

theorem HasDerivWithinAt.comp_hasDerivAt_of_eq {t} (hh₂ : HasDerivWithinAt h₂ h₂' t y)
    (hh : HasDerivAt h h' x) (ht : ∀ᶠ x' in 𝓝 x, h x' ∈ t) (hy : y = h x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x := by
  subst y; exact hh₂.comp_hasDerivAt x hh ht

theorem derivWithin_comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hh₂.hasDerivWithinAt.comp x hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_comp_of_eq (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s')
    (hy : h x = y) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x := by
  subst hy; exact derivWithin_comp x hh₂ hh hs

theorem deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  (hh₂.hasDerivAt.comp x hh.hasDerivAt).deriv

theorem deriv_comp_of_eq (hh₂ : DifferentiableAt 𝕜' h₂ y) (hh : DifferentiableAt 𝕜 h x)
    (hy : h x = y) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x := by
  subst hy; exact deriv_comp x hh₂ hh

protected nonrec theorem HasDerivAtFilter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : ℕ) :
    HasDerivAtFilter f^[n] (f' ^ n) L := by
  have := hf.hasFDerivAtFilter.iterate hL n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

protected nonrec theorem HasDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasDerivAt f^[n] (f' ^ n) x :=
  hf.iterate (by simpa [hx] using hf.continuousAt.tendsto.prodMap <| tendsto_pure_pure f x) _

protected theorem HasDerivWithinAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : HasDerivWithinAt f^[n] (f' ^ n) s x := by
  have := HasFDerivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

protected theorem HasStrictDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictDerivAt f^[n] (f' ^ n) x := by
  have := hf.hasStrictFDerivAt.iterate hx n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

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
  simpa using (hl.comp x hf.hasFDerivWithinAt hst).hasDerivWithinAt

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq {t : Set F}
    (hl : HasFDerivWithinAt l l' t y)
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf hst

theorem HasFDerivWithinAt.comp_hasDerivAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
    (hf : HasDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) : HasDerivAt (l ∘ f) (l' f') x := by
  simpa using (hl.comp_hasFDerivAt x hf.hasFDerivAt ht).hasDerivAt

theorem HasFDerivWithinAt.comp_hasDerivAt_of_eq {t : Set F} (hl : HasFDerivWithinAt l l' t y)
    (hf : HasDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) (hy : y = f x) :
    HasDerivAt (l ∘ f) (l' f') x := by
  subst y; exact hl.comp_hasDerivAt x hf ht

theorem HasFDerivAt.comp_hasDerivWithinAt (hl : HasFDerivAt l l' (f x))
    (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (l ∘ f) (l' f') s x :=
  hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf (mapsTo_univ _ _)

theorem HasFDerivAt.comp_hasDerivWithinAt_of_eq (hl : HasFDerivAt l l' y)
    (hf : HasDerivWithinAt f f' s x) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x :=
  hasDerivWithinAt_univ.mp <| hl.comp_hasDerivWithinAt x hf.hasDerivWithinAt

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivAt.comp_hasDerivAt_of_eq
    (hl : HasFDerivAt l l' y) (hf : HasDerivAt f f' x) (hy : y = f x) :
    HasDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasDerivAt x hf

theorem HasStrictFDerivAt.comp_hasStrictDerivAt (hl : HasStrictFDerivAt l l' (f x))
    (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (l ∘ f) (l' f') x := by
  simpa using (hl.comp x hf.hasStrictFDerivAt).hasStrictDerivAt

theorem HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq (hl : HasStrictFDerivAt l l' y)
    (hf : HasStrictDerivAt f f' x) (hy : y = f x) :
    HasStrictDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasStrictDerivAt x hf

theorem fderivWithin_comp_derivWithin {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem fderivWithin_comp_derivWithin_of_eq {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hy : y = f x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) := by
  rw [hy] at hl; exact fderivWithin_comp_derivWithin x hl hf hs

theorem fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
  (hl.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv

theorem fderiv_comp_deriv_of_eq (hl : DifferentiableAt 𝕜 l y) (hf : DifferentiableAt 𝕜 f x)
    (hy : y = f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) := by
  rw [hy] at hl; exact fderiv_comp_deriv x hl hf

end CompositionVector
