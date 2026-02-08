/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.TangentCone.DimOne
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

- `HasDerivAtFilter f f' x L` states that the function `f` has the
  derivative `f'` at the point `x` as `x` goes along the filter `L`.

- `HasDerivWithinAt f f' s x` states that the function `f` has the
  derivative `f'` at the point `x` within the subset `s`.

- `HasDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x`.

- `HasStrictDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x` in the sense of strict differentiability, i.e.,
  `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

- `derivWithin f s x` is a derivative of `f` at `x` within `s`. If the
  derivative does not exist, then `derivWithin f s x` equals zero.

- `deriv f x` is a derivative of `f` at `x`. If the derivative does not
  exist, then `deriv f x` equals zero.

The theorems `fderivWithin_derivWithin` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps (in `Linear.lean`)
  - addition (in `Add.lean`)
  - sum of finitely many functions (in `Add.lean`)
  - negation (in `Add.lean`)
  - subtraction (in `Add.lean`)
  - star (in `Star.lean`)
  - multiplication of two functions in `𝕜 → 𝕜` (in `Mul.lean`)
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E` (in `Mul.lean`)
  - powers of a function (in `Pow.lean` and `ZPow.lean`)
  - inverse `x → x⁻¹` (in `Inv.lean`)
  - division (in `Inv.lean`)
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜` (in `Comp.lean`)
  - composition of a function in `F → E` with a function in `𝕜 → F` (in `Comp.lean`)
  - inverse function (assuming that it exists; the inverse function theorem is in `Inverse.lean`)
  - polynomials (in `Polynomial.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp; ring
```

The relationship between the derivative of a function and its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`
is developed in the file `Mathlib/Analysis/Calculus/Deriv/Slope.lean`.

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. See the explanations there.
-/

@[expose] public section

universe u v w

noncomputable section

open scoped Topology ENNReal NNReal
open Filter Asymptotics Set

open ContinuousLinearMap (smulRight toSpanSingleton_inj toSpanSingleton)

section TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

section
variable [ContinuousSMul 𝕜 F]

/-- `f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (L : Filter (𝕜 × 𝕜)) :=
  HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L

/-- `f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

/-- `f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 (x, x))

end
/-- Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasDerivWithinAt f f' s x`), then
`f x' = f x + (x' - x) • derivWithin f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1

/-- Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasDerivAt f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1

variable {f f₀ f₁ : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section
variable [ContinuousSMul 𝕜 F]
/-- Expressing `HasFDerivAtFilter f f' x L` in terms of `HasDerivAtFilter` -/
theorem hasFDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasFDerivAtFilter f f' L ↔ HasDerivAtFilter f (f' 1) L := by simp [HasDerivAtFilter]

alias ⟨HasFDerivAtFilter.hasDerivAtFilter, _⟩ := hasFDerivAtFilter_iff_hasDerivAtFilter

theorem hasDerivAtFilter_iff_hasFDerivAtFilter :
    HasDerivAtFilter f f' L ↔ HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L :=
  .rfl

alias ⟨HasDerivAtFilter.hasFDerivAtFilter, _⟩ := hasDerivAtFilter_iff_hasFDerivAtFilter

/-- Expressing `HasFDerivWithinAt f f' s x` in terms of `HasDerivWithinAt` -/
theorem hasFDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasFDerivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivWithinAt.hasDerivWithinAt, _⟩ := hasFDerivWithinAt_iff_hasDerivWithinAt

/-- Expressing `HasDerivWithinAt f f' s x` in terms of `HasFDerivWithinAt` -/
theorem hasDerivWithinAt_iff_hasFDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (toSpanSingleton 𝕜 f') s x :=
  Iff.rfl

alias ⟨HasDerivWithinAt.hasFDerivWithinAt, _⟩ :=
  hasDerivWithinAt_iff_hasFDerivWithinAt

/-- Expressing `HasFDerivAt f f' x` in terms of `HasDerivAt` -/
theorem hasFDerivAt_iff_hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivAt.hasDerivAt, _⟩ := hasFDerivAt_iff_hasDerivAt

/-- Expressing `HasDerivAt f f' x` in terms of `HasFDerivAt` -/
theorem hasDerivAt_iff_hasFDerivAt {f' : F} :
    HasDerivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x :=
  Iff.rfl

alias ⟨HasDerivAt.hasFDerivAt, _⟩ := hasDerivAt_iff_hasFDerivAt

theorem hasStrictFDerivAt_iff_hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictFDerivAt f f' x ↔ HasStrictDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

protected alias ⟨HasStrictFDerivAt.hasStrictDerivAt, _⟩ :=
  hasStrictFDerivAt_iff_hasStrictDerivAt

theorem hasStrictDerivAt_iff_hasStrictFDerivAt :
    HasStrictDerivAt f f' x ↔ HasStrictFDerivAt f (toSpanSingleton 𝕜 f') x :=
  Iff.rfl

alias ⟨HasStrictDerivAt.hasStrictFDerivAt, _⟩ := hasStrictDerivAt_iff_hasStrictFDerivAt

end

theorem derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [fderivWithin_zero_of_not_differentiableWithinAt h]
  simp

theorem differentiableWithinAt_of_derivWithin_ne_zero (h : derivWithin f s x ≠ 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h

end TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f f₀ f₁ : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter (𝕜 × 𝕜)}

theorem derivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) : derivWithin f s x = 0 := by
  rw [derivWithin, fderivWithin_zero_of_not_accPt h, ContinuousLinearMap.zero_apply]

theorem derivWithin_zero_of_not_uniqueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = 0 :=
  derivWithin_zero_of_not_accPt <| mt AccPt.uniqueDiffWithinAt h

theorem derivWithin_zero_of_notMem_closure (h : x ∉ closure s) : derivWithin f s x = 0 := by
  rw [derivWithin, fderivWithin_zero_of_notMem_closure h, ContinuousLinearMap.zero_apply]

theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt h]
  simp

theorem differentiableAt_of_deriv_ne_zero (h : deriv f x ≠ 0) : DifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiableAt h

theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  toSpanSingleton_inj.mp <| UniqueDiffWithinAt.eq H h h₁

theorem hasDerivAtFilter_iff_isLittleO :
    HasDerivAtFilter f f' L ↔
      (fun p => f p.1 - f p.2 - (p.1 - p.2) • f') =o[L] fun p => p.1 - p.2 :=
  hasFDerivAtFilter_iff_isLittleO ..

theorem hasDerivAtFilter_iff_tendsto :
    HasDerivAtFilter f f' L ↔
      Tendsto (fun p ↦ ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - (p.1 - p.2) • f'‖) L (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

theorem hasDerivWithinAt_iff_isLittleO :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  hasFDerivWithinAt_iff_isLittleO

alias ⟨HasDerivWithinAt.isLittleO, HasDerivWithinAt.of_isLittleO⟩ := hasDerivWithinAt_iff_isLittleO

theorem hasDerivWithinAt_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto

theorem hasDerivAt_iff_isLittleO :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  hasFDerivAt_iff_isLittleO ..

alias ⟨HasDerivAt.isLittleO, HasDerivAt.of_isLittleO⟩ := hasDerivAt_iff_isLittleO

theorem hasDerivAt_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAt_iff_tendsto

theorem HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2 :=
  HasFDerivAtFilter.isBigO_sub h

theorem HasDerivAt.isBigO_sub (h : HasDerivAt f f' x) : (f · - f x) =O[𝓝 x] (· - x) :=
  h.hasFDerivAt.isBigO_sub

/-- This theorem holds for any T2 TVS, see `isClosedEmbedding_smul_left`,
but this would require more imports.

The proof for a TVS is more complicated, and we wouldn't benefit from that form here,
so we prove a weaker version as a private lemma instead. -/
private lemma isInducing_toSpanSingleton (hf' : f' ≠ 0) :
    Topology.IsInducing (toSpanSingleton 𝕜 f') := by
  refine AntilipschitzWith.isInducing (K := ‖f'‖₊⁻¹) ?_ (map_continuous _)
  simp [antilipschitzWith_iff_le_mul_dist, dist_eq_norm, ← sub_smul, norm_smul, field]

theorem HasDerivAtFilter.isEquivalent_sub (hf : HasDerivAtFilter f f' L) (hf' : f' ≠ 0) :
    (fun p ↦ f p.1 - f p.2) ~[L] (fun p ↦ (p.1 - p.2) • f') :=
  HasFDerivAtFilter.isEquivalent_sub hf <| isInducing_toSpanSingleton hf'

theorem HasDerivAtFilter.isTheta_sub (hf : HasDerivAtFilter f f' L) (hf' : f' ≠ 0) :
    (fun p ↦ f p.1 - f p.2) =Θ[L] (fun p ↦ p.1 - p.2) :=
  HasFDerivAtFilter.isTheta_sub hf <| isInducing_toSpanSingleton hf'

@[deprecated HasDerivAtFilter.isTheta_sub (since := "2026-02-04")]
theorem HasDerivAtFilter.isBigO_sub_rev (hf : HasDerivAtFilter f f' L) (hf' : f' ≠ 0) :
    (fun p => p.1 - p.2) =O[L] fun p => f p.1 - f p.2 :=
  hf.isTheta_sub hf' |>.isBigO_symm

theorem HasStrictDerivAt.hasDerivAt (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.hasStrictFDerivAt.hasFDerivAt

theorem hasDerivWithinAt_congr_set' {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h

theorem hasDerivWithinAt_congr_set {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h

alias ⟨HasDerivWithinAt.congr_set, _⟩ := hasDerivWithinAt_congr_set

@[simp]
theorem hasDerivWithinAt_diff_singleton :
    HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_diff_singleton _

@[simp]
theorem hasDerivWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_diff_left, hasDerivWithinAt_diff_singleton]

alias ⟨HasDerivWithinAt.Ici_of_Ioi, HasDerivWithinAt.Ioi_of_Ici⟩ := hasDerivWithinAt_Ioi_iff_Ici

@[simp]
theorem hasDerivWithinAt_Iio_iff_Iic [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_diff_right, hasDerivWithinAt_diff_singleton]

alias ⟨HasDerivWithinAt.Iic_of_Iio, HasDerivWithinAt.Iio_of_Iic⟩ := hasDerivWithinAt_Iio_iff_Iic

theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
  hasFDerivWithinAt_inter <| Iio_mem_nhds h

alias ⟨HasDerivWithinAt.Ioi_of_Ioo, HasDerivWithinAt.Ioo_of_Ioi⟩ := HasDerivWithinAt.Ioi_iff_Ioo

theorem hasDerivAt_iff_isLittleO_nhds_zero :
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' L₂) (hst : L₁ ≤ L₂) :
    HasDerivAtFilter f f' L₁ :=
  HasFDerivAtFilter.mono h hst

theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono h hst

theorem HasDerivWithinAt.mono_of_mem_nhdsWithin (h : HasDerivWithinAt f f' t x) (hst : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono_of_mem_nhdsWithin h hst

theorem HasDerivAt.hasDerivAtFilter (h : HasDerivAt f f' x) (hL : L ≤ 𝓝 x ×ˢ pure x) :
    HasDerivAtFilter f f' L :=
  HasFDerivAt.hasFDerivAtFilter h hL

theorem HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFDerivAt.hasFDerivWithinAt h

theorem HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  HasFDerivWithinAt.differentiableWithinAt h

theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFDerivAt.differentiableAt h

@[simp]
theorem hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  hasFDerivWithinAt_univ

theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  toSpanSingleton_inj.mp <| h₀.hasFDerivAt.unique h₁

theorem hasDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter' h

theorem hasDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter h

theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s ∪ t) x :=
  hs.hasFDerivWithinAt.union ht.hasFDerivWithinAt

theorem HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasDerivAt f f' x :=
  HasFDerivWithinAt.hasFDerivAt h hs

theorem DifferentiableWithinAt.hasDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.hasFDerivWithinAt.hasDerivWithinAt

theorem DifferentiableAt.hasDerivAt (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.hasFDerivAt.hasDerivAt

@[simp]
theorem hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => h.differentiableAt, fun h => h.hasDerivAt⟩

@[simp]
theorem hasDerivWithinAt_derivWithin_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.differentiableWithinAt, fun h => h.hasDerivWithinAt⟩

theorem DifferentiableOn.hasDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasDerivAt f (deriv f x) x :=
  (h.hasFDerivAt hs).hasDerivAt

theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.differentiableAt.hasDerivAt.unique h

theorem deriv_eq {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv

theorem HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f' :=
  hxs.eq_deriv _ h.differentiableWithinAt.hasDerivWithinAt h

theorem fderivWithin_derivWithin : (fderivWithin 𝕜 f s x : 𝕜 → F) 1 = derivWithin f s x :=
  rfl

theorem toSpanSingleton_derivWithin :
    toSpanSingleton 𝕜 (derivWithin f s x) = fderivWithin 𝕜 f s x := by simp [derivWithin]

@[deprecated (since := "2025-12-18")] alias derivWithin_fderivWithin := toSpanSingleton_derivWithin

theorem norm_derivWithin_eq_norm_fderivWithin : ‖derivWithin f s x‖ = ‖fderivWithin 𝕜 f s x‖ := by
  simp [← toSpanSingleton_derivWithin]

theorem fderiv_apply_one_eq_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x := rfl

@[deprecated (since := "2025-12-18")] alias fderiv_deriv := fderiv_apply_one_eq_deriv

@[simp]
theorem fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 → F) y = y • deriv f x := by
  rw [← fderiv_apply_one_eq_deriv, ← map_smul]
  simp only [smul_eq_mul, mul_one]

theorem toSpanSingleton_deriv : toSpanSingleton 𝕜 (deriv f x) = fderiv 𝕜 f x := by
  simp only [deriv, ContinuousLinearMap.toSpanSingleton_apply_map_one]

@[deprecated (since := "2025-12-18")] alias deriv_fderiv := toSpanSingleton_deriv

lemma fderiv_eq_deriv_mul {f : 𝕜 → 𝕜} {x y : 𝕜} : (fderiv 𝕜 f x : 𝕜 → 𝕜) y = (deriv f x) * y := by
  simp [mul_comm]

theorem norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fderiv 𝕜 f x‖ := by
  simp [← toSpanSingleton_deriv]

theorem DifferentiableAt.derivWithin (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x := by
  unfold _root_.derivWithin deriv
  rw [h.fderivWithin hxs]

theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x)
    (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.hasDerivAt.hasDerivWithinAt hd

theorem derivWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono_of_mem_nhdsWithin st).derivWithin ht

theorem derivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht

theorem derivWithin_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    derivWithin f s x = derivWithin f t x := by simp only [derivWithin, fderivWithin_congr_set' y h]

theorem derivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : derivWithin f s x = derivWithin f t x := by
  simp only [derivWithin, fderivWithin_congr_set h]

@[simp]
theorem derivWithin_univ : derivWithin f univ = deriv f := by
  ext
  unfold derivWithin deriv
  rw [fderivWithin_univ]

theorem derivWithin_inter (ht : t ∈ 𝓝 x) : derivWithin f (s ∩ t) x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_inter ht]

theorem derivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : derivWithin f s x = deriv f x := by
  simp only [derivWithin, deriv, fderivWithin_of_mem_nhds h]

theorem derivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : derivWithin f s x = deriv f x :=
  derivWithin_of_mem_nhds (hs.mem_nhds hx)

lemma deriv_eqOn {f' : 𝕜 → F} (hs : IsOpen s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    s.EqOn (deriv f) f' := fun x hx ↦ by
  rw [← derivWithin_of_isOpen hs hx, (hf' _ hx).derivWithin <| hs.uniqueDiffWithinAt hx]

theorem deriv_mem_iff {f : 𝕜 → F} {s : Set F} {x : 𝕜} :
    deriv f x ∈ s ↔
      DifferentiableAt 𝕜 f x ∧ deriv f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) ∈ s := by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]

theorem derivWithin_mem_iff {f : 𝕜 → F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) ∈ s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]

theorem differentiableWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, fun h =>
    h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt⟩

-- Golfed while splitting the file
theorem derivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (x : ℝ) : derivWithin f (Ioi x) x = derivWithin f (Ici x) x := by
  by_cases H : DifferentiableWithinAt ℝ f (Ioi x) x
  · have A := H.hasDerivWithinAt.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).hasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).eq self_mem_Ici A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      derivWithin_zero_of_not_differentiableWithinAt]
    rwa [differentiableWithinAt_Ioi_iff_Ici] at H

section congr

/-! ### Congruence properties of derivatives -/

theorem Filter.EventuallyEq.hasDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
    (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' L ↔ HasDerivAtFilter f₁ f₁' L :=
  h₀.hasFDerivAtFilter_iff (by simp [h₁])

theorem HasDerivAtFilter.congr_of_eventuallyEq (h : HasDerivAtFilter f f' L)
    (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) :
    HasDerivAtFilter f₁ f' L := by
  rwa [hL.hasDerivAtFilter_iff rfl]

theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasDerivWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁

theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)

theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)

theorem HasDerivWithinAt.congr_of_eventuallyEq (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  HasDerivAtFilter.congr_of_eventuallyEq h <| h₁.prodMap hx

theorem Filter.EventuallyEq.hasDerivWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq h₁.symm hx.symm, fun h' ↦ h'.congr_of_eventuallyEq h₁ hx⟩

theorem HasDerivWithinAt.congr_of_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

theorem Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq_of_mem h₁.symm hx,
  fun h' ↦ h'.congr_of_eventuallyEq_of_mem h₁ hx⟩

theorem HasStrictDerivAt.congr_of_eventuallyEq (h : HasStrictDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasStrictDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h (h₁.prodMap_nhds h₁)

theorem HasStrictDerivAt.congr_deriv (h : HasStrictDerivAt f f' x) (h' : f' = g') :
    HasStrictDerivAt f g' x :=
  h.hasStrictFDerivAt.congr_fderiv <| congr_arg _ h'

theorem HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (h' : f' = g') : HasDerivAt f g' x :=
  HasFDerivAt.congr_fderiv h <| congr_arg _ h'

theorem HasDerivWithinAt.congr_deriv (h : HasDerivWithinAt f f' s x) (h' : f' = g') :
    HasDerivWithinAt f g' s x :=
  HasFDerivWithinAt.congr_fderiv h <| congr_arg _ h'

theorem HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h <| h₁.prodMap <| h₁.filter_mono <| pure_le_nhds _

theorem Filter.EventuallyEq.hasDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasDerivAt f₀ f' x ↔ HasDerivAt f₁ f' x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq h.symm, fun h' ↦ h'.congr_of_eventuallyEq h⟩

theorem Filter.EventuallyEq.derivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [hs.fderivWithin_eq hx]

theorem Filter.EventuallyEq.derivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    derivWithin f₁ s x = derivWithin f s x :=
  hs.derivWithin_eq <| hs.self_of_nhdsWithin hx

theorem Filter.EventuallyEq.derivWithin_eq_of_nhds (hs : f₁ =ᶠ[𝓝 x] f) :
    derivWithin f₁ s x = derivWithin f s x :=
  (hs.filter_mono nhdsWithin_le_nhds).derivWithin_eq hs.self_of_nhds

theorem derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_congr hs hx]

lemma Set.EqOn.deriv {f g : 𝕜 → F} {s : Set 𝕜} (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) (deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx, ← derivWithin_of_isOpen hs hx]
  exact derivWithin_congr hfg (hfg hx)

theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x := by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]

protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq

theorem Filter.EventuallyEq.nhdsNE_deriv (h : f₁ =ᶠ[𝓝[≠] x] f) : deriv f₁ =ᶠ[𝓝[≠] x] deriv f := by
  rw [Filter.EventuallyEq, ← eventually_nhdsNE_eventually_nhds_iff] at *
  filter_upwards [h] with y hy
  apply Filter.EventuallyEq.deriv hy

end congr

section id

/-! ### Derivative of the identity -/

variable (s x L)

theorem hasDerivAtFilter_id : HasDerivAtFilter id 1 L :=
  (hasFDerivAtFilter_id L).hasDerivAtFilter

theorem hasDerivWithinAt_id : HasDerivWithinAt id 1 s x :=
  hasDerivAtFilter_id _

theorem hasDerivAt_id : HasDerivAt id 1 x :=
  hasDerivAtFilter_id _

theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  hasDerivAtFilter_id _

theorem hasStrictDerivAt_id : HasStrictDerivAt id 1 x :=
  hasDerivAtFilter_id _

theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (hasDerivAt_id x)

@[simp]
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id

/-- Variant with `fun x => x` rather than `id` -/
@[simp]
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'

theorem derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (hasDerivWithinAt_id x s).derivWithin hxs

/-- Variant with `fun x => x` rather than `id` -/
theorem derivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => x) s x = 1 :=
  derivWithin_id x s hxs

end id

section Const

/-! ### Derivative of constant functions

This include the constant functions `0`, `1`, `Nat.cast n`, `Int.cast z`, and other numerals.
-/

variable (c : F) (s x L)

theorem hasDerivAtFilter_const : HasDerivAtFilter (fun _ => c) 0 L :=
  (hasFDerivAtFilter_const c L).hasDerivAtFilter

theorem hasDerivAtFilter_zero : HasDerivAtFilter (0 : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _

theorem hasDerivAtFilter_one [One F] : HasDerivAtFilter (1 : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _

theorem hasDerivAtFilter_natCast [NatCast F] (n : ℕ) : HasDerivAtFilter (n : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _

theorem hasDerivAtFilter_intCast [IntCast F] (z : ℤ) : HasDerivAtFilter (z : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _

theorem hasDerivAtFilter_ofNat (n : ℕ) [OfNat F n] : HasDerivAtFilter (ofNat(n) : 𝕜 → F) 0 L :=
  hasDerivAtFilter_const _ _

theorem hasStrictDerivAt_const : HasStrictDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _

theorem hasStrictDerivAt_zero : HasStrictDerivAt (0 : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _

theorem hasStrictDerivAt_one [One F] : HasStrictDerivAt (1 : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _

theorem hasStrictDerivAt_natCast [NatCast F] (n : ℕ) : HasStrictDerivAt (n : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _

theorem hasStrictDerivAt_intCast [IntCast F] (z : ℤ) : HasStrictDerivAt (z : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _

theorem HasStrictDerivAt_ofNat (n : ℕ) [OfNat F n] : HasStrictDerivAt (ofNat(n) : 𝕜 → F) 0 x :=
  hasStrictDerivAt_const _ _

theorem hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x :=
  hasDerivAtFilter_const _ _

theorem hasDerivWithinAt_zero : HasDerivWithinAt (0 : 𝕜 → F) 0 s x :=
  hasDerivAtFilter_zero _

theorem hasDerivWithinAt_one [One F] : HasDerivWithinAt (1 : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _

theorem hasDerivWithinAt_natCast [NatCast F] (n : ℕ) : HasDerivWithinAt (n : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _

theorem hasDerivWithinAt_intCast [IntCast F] (z : ℤ) : HasDerivWithinAt (z : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _

theorem hasDerivWithinAt_ofNat (n : ℕ) [OfNat F n] : HasDerivWithinAt (ofNat(n) : 𝕜 → F) 0 s x :=
  hasDerivWithinAt_const _ _ _

theorem hasDerivAt_const : HasDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _

theorem hasDerivAt_zero : HasDerivAt (0 : 𝕜 → F) 0 x :=
  hasDerivAtFilter_zero _

theorem hasDerivAt_one [One F] : HasDerivAt (1 : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _

theorem hasDerivAt_natCast [NatCast F] (n : ℕ) : HasDerivAt (n : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _

theorem hasDerivAt_intCast [IntCast F] (z : ℤ) : HasDerivAt (z : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _

theorem hasDerivAt_ofNat (n : ℕ) [OfNat F n] : HasDerivAt (ofNat(n) : 𝕜 → F) 0 x :=
  hasDerivAt_const _ _

theorem deriv_const : deriv (fun _ => c) x = 0 :=
  HasDerivAt.deriv (hasDerivAt_const x c)

@[simp]
theorem deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0 :=
  funext fun x => deriv_const x c

@[simp]
theorem deriv_zero : deriv (0 : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp]
theorem deriv_one [One F] : deriv (1 : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp]
theorem deriv_natCast [NatCast F] (n : ℕ) : deriv (n : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp]
theorem deriv_intCast [IntCast F] (z : ℤ) : deriv (z : 𝕜 → F) = 0 := funext fun _ => deriv_const _ _

@[simp low]
theorem deriv_ofNat (n : ℕ) [OfNat F n] : deriv (ofNat(n) : 𝕜 → F) = 0 :=
  funext fun _ => deriv_const _ _

@[simp]
theorem derivWithin_fun_const : derivWithin (fun _ => c) s = 0 := by
  ext; simp [derivWithin]

@[simp]
theorem derivWithin_const : derivWithin (Function.const 𝕜 c) s = 0 :=
  derivWithin_fun_const _ _

@[simp]
theorem derivWithin_zero : derivWithin (0 : 𝕜 → F) s = 0 := derivWithin_const _ _

@[simp]
theorem derivWithin_one [One F] : derivWithin (1 : 𝕜 → F) s = 0 := derivWithin_const _ _

@[simp]
theorem derivWithin_natCast [NatCast F] (n : ℕ) : derivWithin (n : 𝕜 → F) s = 0 :=
  derivWithin_const _ _

@[simp]
theorem derivWithin_intCast [IntCast F] (z : ℤ) : derivWithin (z : 𝕜 → F) s = 0 :=
  derivWithin_const _ _

@[simp low]
theorem derivWithin_ofNat (n : ℕ) [OfNat F n] : derivWithin (ofNat(n) : 𝕜 → F) s = 0 :=
  derivWithin_const _ _

end Const

section Continuous

/-! ### Continuity of a function admitting a derivative -/

theorem HasDerivAtFilter.tendsto_nhds {L : Filter 𝕜} (hL : L ≤ 𝓝 x)
    (h : HasDerivAtFilter f f' (L ×ˢ pure x)) :
    Tendsto f L (𝓝 (f x)) :=
  h.hasFDerivAtFilter.tendsto_nhds hL

theorem HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h

theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h

theorem HasDerivWithinAt.continuousOn {f f' : 𝕜 → F} (h : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    ContinuousOn f s := fun x hx => (h x hx).continuousWithinAt

protected theorem HasDerivAt.continuousOn {f f' : 𝕜 → F} (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) :
    ContinuousOn f s := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt

end Continuous

section MeanValue

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem HasDerivAt.le_of_lip' {f : 𝕜 → F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖f'‖ ≤ C := by
  simpa using HasFDerivAt.le_of_lip' hf.hasFDerivAt hC₀ hlip

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. -/
theorem HasDerivAt.le_of_lipschitzOn {f : 𝕜 → F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {s : Set 𝕜} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖f'‖ ≤ C := by
  simpa using HasFDerivAt.le_of_lipschitzOn hf.hasFDerivAt hs hlip

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
then its derivative at `x₀` has norm bounded by `C`. -/
theorem HasDerivAt.le_of_lipschitz {f : 𝕜 → F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖f'‖ ≤ C := by
  simpa using HasFDerivAt.le_of_lipschitz hf.hasFDerivAt hlip

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem norm_deriv_le_of_lip' {f : 𝕜 → F} {x₀ : 𝕜}
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lip' 𝕜 hC₀ hlip

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
Version using `deriv`. -/
theorem norm_deriv_le_of_lipschitzOn {f : 𝕜 → F} {x₀ : 𝕜} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitzOn 𝕜 hs hlip

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `deriv`. -/
theorem norm_deriv_le_of_lipschitz {f : 𝕜 → F} {x₀ : 𝕜}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitz 𝕜 hlip

end MeanValue

section Semilinear

variable {σ σ' : RingHom 𝕜 𝕜} [RingHomIsometric σ] [RingHomInvPair σ σ']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] (L : F →SL[σ] F')

variable (σ')

/-- If `L` is a `σ`-semilinear map, and `f` has Fréchet derivative `f'` at `x`, then `L ∘ f ∘ σ⁻¹`
has Fréchet derivative `L ∘ f'` at `σ x`. -/
lemma HasDerivAt.comp_semilinear (hf : HasDerivAt f f' x) :
    HasDerivAt (L ∘ f ∘ σ') (L f') (σ x) := by
  have : RingHomIsometric σ' := .inv σ
  let R : 𝕜 →SL[σ'] 𝕜 := ⟨σ'.toSemilinearMap, σ'.isometry.continuous⟩
  have hR (k : 𝕜) : R k = σ' k := rfl
  rw [hasDerivAt_iff_hasFDerivAt]
  convert HasFDerivAt.comp_semilinear L R (f' := toSpanSingleton 𝕜 f') ?_
  · ext
    simp [R]
  · rwa [← hasDerivAt_iff_hasFDerivAt, hR, RingHomInvPair.comp_apply_eq]

/-- If `f` is differentiable at `x`, and `L` is `σ`-semilinear, then `L ∘ f ∘ σ⁻¹` is
differentiable at `σ x`. -/
lemma DifferentiableAt.comp_semilinear₁ (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (L ∘ f ∘ σ') (σ x) :=
  (hf.hasDerivAt.comp_semilinear σ' L).differentiableAt

variable (σ) {f : 𝕜 → 𝕜} {f' : 𝕜}

/-- If `f` has derivative `f'` at `x`, and `σ, σ'` are mutually inverse normed-ring automorphisms,
then `σ ∘ f ∘ σ'` has derivative `σ f'` at `σ x`. -/
lemma HasDerivAt.comp_ringHom (hf : HasDerivAt f f' x) : HasDerivAt (σ ∘ f ∘ σ') (σ f') (σ x) :=
  hf.comp_semilinear σ' ⟨σ.toSemilinearMap, σ.isometry.continuous⟩

/-- If `f` is differentiable at `x`, and `L` is `σ`-semilinear, then `L ∘ f ∘ σ⁻¹` is
differentiable at `σ x`. -/
lemma DifferentiableAt.comp_ringHom (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (σ ∘ f ∘ σ') (σ x) :=
  (hf.hasDerivAt.comp_ringHom σ σ').differentiableAt

end Semilinear
