/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Additive operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
-/

public section


open Filter Asymptotics ContinuousLinearMap

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : E → F}
variable {f' g' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

section ConstSMul

variable {R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/

@[to_fun]
theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' L) (c : R) :
    HasFDerivAtFilter (c • f) (c • f') L :=
  (c • (1 : F →L[𝕜] F)).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (c • f) (c • f') s x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (c • f) s x :=
  (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (c • f) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (h x hx).const_smul c

@[to_fun (attr := fun_prop)]
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 (c • f) := fun x => (h x).const_smul c

theorem fderivWithin_fun_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs

theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x :=
  fderivWithin_fun_const_smul hxs h c

/-- If `c` is invertible, `c • f` is differentiable at `x` within `s` if and only if `f` is. -/
lemma differentiableWithinAt_smul_iff (c : R) [Invertible c] :
    DifferentiableWithinAt 𝕜 (c • f) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.const_smul c⟩
  apply (h.const_smul ⅟c).congr_of_eventuallyEq ?_ (by simp)
  filter_upwards with x using by simp

/-- A version of `fderivWithin_const_smul` without differentiability hypothesis:
in return, the constant `c` must be invertible, i.e. if `R` is a field. -/
theorem fderivWithin_const_smul_of_invertible (c : R) [Invertible c]
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact (h.hasFDerivWithinAt.const_smul c).fderivWithin hs
  · have : ¬DifferentiableWithinAt 𝕜 (c • f) s x := by
      contrapose h
      exact (differentiableWithinAt_smul_iff c).mp h
    simp [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this]

theorem fderiv_fun_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

/-- If `c` is invertible, `c • f` is differentiable at `x` if and only if `f` is. -/
lemma differentiableAt_smul_iff (c : R) [Invertible c] :
    DifferentiableAt 𝕜 (c • f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ, differentiableWithinAt_smul_iff, differentiableWithinAt_univ]

/-- A version of `fderiv_const_smul` without differentiability hypothesis: in return, the constant
`c` must be invertible, i.e. if `R` is a field. -/
theorem fderiv_const_smul_of_invertible (c : R) [Invertible c] :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x := by
  simp [← fderivWithin_univ, fderivWithin_const_smul_of_invertible c uniqueDiffWithinAt_univ]

end ConstSMul

section ConstSMulDivisionRing

variable {R : Type*} [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/-- Special case of `fderivWithin_const_smul_of_invertible` over a division semiring: any constant
is allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulActionWithZero`
typeclass. -/
lemma fderivWithin_const_smul_field (c : R) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  obtain (rfl | ha) := eq_or_ne c 0
  · simp
  · have : Invertible c := invertibleOfNonzero ha
    simp [fderivWithin_const_smul_of_invertible c hs]

lemma fderivWithin_const_smul_field' {s : Set 𝕜} {f : 𝕜 → F} {x : 𝕜} (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact fderivWithin_const_smul_field c hsx
  · simp [fderivWithin_zero_of_not_uniqueDiffWithinAt hsx]

omit [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] in
/-- Special case of `fderivWithin_neg` for functions `𝕜 → F`, i.e. when the domain `E` is the scalar
field `𝕜` itself. In this case no `UniqueDiffWithinAt 𝕜 s x` hypothesis is needed. -/
lemma fderivWithin_neg' {s : Set 𝕜} {f : 𝕜 → F} {x : 𝕜} :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x := by
  simpa only [neg_smul, one_smul] using fderivWithin_const_smul_field' (f := f) (-1 : 𝕜)

@[deprecated (since := "2026-01-11")] alias fderivWithin_const_smul_of_field :=
  fderivWithin_const_smul_field

/-- Special case of `fderiv_const_smul_of_invertible` over a division semiring: any constant is
allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulActionWithZero`
typeclass. -/
lemma fderiv_const_smul_field (c : R) : fderiv 𝕜 (c • f) = c • fderiv 𝕜 f := by
  simp_rw [← fderivWithin_univ]
  ext x
  simp [fderivWithin_const_smul_field c uniqueDiffWithinAt_univ]

@[deprecated (since := "2026-01-11")] alias fderiv_const_smul_of_field := fderiv_const_smul_field

end ConstSMulDivisionRing

section Add

/-! ### Derivative of the sum of two functions -/

@[to_fun]
theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' L)
    (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L :=
  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    grind [Pi.add_apply]

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f + g) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s := fun x hx => (hf x hx).add (hg x hx)

@[to_fun (attr := simp, fun_prop)]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) := fun x => (hf x).add (hg x)

-- TODO: `@[to_fun]` gives incorrect lemma name
theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f + g) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_fun_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  fderivWithin_add hxs hf hg

-- TODO: `@[to_fun]` gives incorrect lemma name
theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

theorem fderiv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  fderiv_add hf hg

@[simp]
theorem hasFDerivAtFilter_add_const_iff (c : F) :
    HasFDerivAtFilter (f · + c) f' L ↔ HasFDerivAtFilter f f' L := by
  simp [hasFDerivAtFilter_iff_isLittleOTVS]

alias ⟨_, HasFDerivAtFilter.add_const⟩ := hasFDerivAtFilter_add_const_iff

@[simp]
theorem hasStrictFDerivAt_add_const_iff (c : F) :
    HasStrictFDerivAt (f · + c) f' x ↔ HasStrictFDerivAt f f' x := by
  simp [hasStrictFDerivAt_iff_isLittleO]

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.add_const⟩ := hasStrictFDerivAt_add_const_iff

@[simp]
theorem hasFDerivWithinAt_add_const_iff (c : F) :
    HasFDerivWithinAt (f · + c) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.add_const⟩ := hasFDerivWithinAt_add_const_iff

@[simp]
theorem hasFDerivAt_add_const_iff (c : F) : HasFDerivAt (f · + c) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.add_const⟩ := hasFDerivAt_add_const_iff

@[simp]
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ ↦ hasFDerivWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.add_const⟩ := differentiableWithinAt_add_const_iff

@[simp]
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ ↦ hasFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.add_const⟩ := differentiableAt_add_const_iff

@[simp]
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ ↦ differentiableWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.add_const⟩ := differentiableOn_add_const_iff

@[simp]
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ ↦ differentiableAt_add_const_iff c

@[fun_prop]
alias ⟨_, Differentiable.add_const⟩ := differentiable_add_const_iff

@[simp]
theorem fderivWithin_add_const (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x := by
  classical simp [fderivWithin]

@[simp]
theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const]

@[simp]
theorem hasFDerivAtFilter_const_add_iff (c : F) :
    HasFDerivAtFilter (c + f ·) f' L ↔ HasFDerivAtFilter f f' L := by
  simpa only [add_comm] using hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasFDerivAtFilter.const_add⟩ := hasFDerivAtFilter_const_add_iff

@[simp]
theorem hasStrictFDerivAt_const_add_iff (c : F) :
    HasStrictFDerivAt (c + f ·) f' x ↔ HasStrictFDerivAt f f' x := by
  simpa only [add_comm] using hasStrictFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.const_add⟩ := hasStrictFDerivAt_const_add_iff

@[simp]
theorem hasFDerivWithinAt_const_add_iff (c : F) :
    HasFDerivWithinAt (c + f ·) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.const_add⟩ := hasFDerivWithinAt_const_add_iff

@[simp]
theorem hasFDerivAt_const_add_iff (c : F) : HasFDerivAt (c + f ·) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.const_add⟩ := hasFDerivAt_const_add_iff

@[simp]
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ ↦ hasFDerivWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.const_add⟩ := differentiableWithinAt_const_add_iff

@[simp]
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ ↦ hasFDerivAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.const_add⟩ := differentiableAt_const_add_iff

@[simp]
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ ↦ differentiableWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.const_add⟩ := differentiableOn_const_add_iff

@[simp]
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ ↦ differentiableAt_const_add_iff c

@[fun_prop]
alias ⟨_, Differentiable.const_add⟩ := differentiable_const_add_iff

@[simp]
theorem fderivWithin_const_add (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const c

@[simp]
theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


variable {ι : Type*} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

@[fun_prop]
theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [Finset.sum_sub_distrib, _root_.sum_apply]

@[fun_prop]
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x := by
  convert HasStrictFDerivAt.fun_sum h; simp

theorem HasFDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [_root_.sum_apply]

theorem HasFDerivAtFilter.sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (∑ i ∈ u, A i) (∑ i ∈ u, A' i) L := by
  convert HasFDerivAtFilter.fun_sum h; simp

@[fun_prop]
theorem HasFDerivWithinAt.fun_sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  HasFDerivAtFilter.fun_sum h

@[fun_prop]
theorem HasFDerivWithinAt.sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) s x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
theorem HasFDerivAt.fun_sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasFDerivAtFilter.fun_sum h

@[fun_prop]
theorem HasFDerivAt.sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
theorem DifferentiableWithinAt.fun_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i ∈ u, A i y) s x :=
  HasFDerivWithinAt.differentiableWithinAt <|
    HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt

@[fun_prop]
theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (∑ i ∈ u, A i) s x :=
  HasFDerivWithinAt.differentiableWithinAt <|
    HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i ∈ u, A i y) x :=
  HasFDerivAt.differentiableAt <| HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt

@[simp, fun_prop]
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (∑ i ∈ u, A i) x :=
  HasFDerivAt.differentiableAt <| HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt

@[fun_prop]
theorem DifferentiableOn.fun_sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i ∈ u, A i y) s := fun x hx =>
  DifferentiableWithinAt.fun_sum fun i hi => h i hi x hx

@[fun_prop]
theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (∑ i ∈ u, A i) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp, fun_prop]
theorem Differentiable.fun_sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i ∈ u, A i y :=
  fun x => DifferentiableAt.fun_sum fun i hi => h i hi x

@[simp, fun_prop]
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 (∑ i ∈ u, A i) := fun x => DifferentiableAt.sum fun i hi => h i hi x

theorem fderivWithin_fun_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i ∈ u, A i y) s x = ∑ i ∈ u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (∑ i ∈ u, A i) s x = ∑ i ∈ u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i ∈ u, A i y) x = ∑ i ∈ u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt).fderiv

theorem fderiv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (∑ i ∈ u, A i) x = ∑ i ∈ u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/


@[to_fun]
theorem HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter (-f) (-f') L :=
  (-1 : F →L[𝕜] F).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (-f) (-f') x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (-f) (-f') s x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (-f) (-f') x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (-f) s x :=
  h.hasFDerivWithinAt.neg.differentiableWithinAt

@[simp]
theorem differentiableWithinAt_fun_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (-f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (-f) x :=
  h.hasFDerivAt.neg.differentiableAt

@[simp]
theorem differentiableAt_fun_neg_iff :
    DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (-f) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (-f) s :=
  fun x hx => (h x hx).neg

@[simp]
theorem differentiableOn_fun_neg_iff :
    DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (-f) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 (-f) := fun x =>
  (h x).neg

@[simp]
theorem differentiable_fun_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
theorem differentiable_neg_iff : Differentiable 𝕜 (-f) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

theorem fderivWithin_fun_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
  · rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

/-- Version of `fderivWithin_fun_neg` where the function is written `-f` instead of `fun y ↦ -f y`.
For the special case `E = 𝕜` without a `UniqueDiffWithinAt 𝕜 s x` hypothesis, see
`fderivWithin_neg'`. -/
theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x :=
  fderivWithin_fun_neg hxs

@[simp]
theorem fderiv_fun_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_fun_neg uniqueDiffWithinAt_univ]

/-- Version of `fderiv_neg` where the function is written `-f` instead of `fun y ↦ - f y`. -/
theorem fderiv_neg : fderiv 𝕜 (-f) x = -fderiv 𝕜 f x :=
  fderiv_fun_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


@[to_fun]
theorem HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' L) (hg : HasFDerivAtFilter g g' L) :
    HasFDerivAtFilter (f - g) (f' - g') L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f - g) (f' - g') x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f - g) (f' - g') x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f - g) s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).differentiableAt

@[to_fun (attr := simp)]
lemma DifferentiableAt.add_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 f x := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
lemma DifferentiableAt.add_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
lemma DifferentiableAt.sub_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
lemma DifferentiableAt.sub_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [sub_eq_add_neg, hg, add_iff_right, differentiableAt_neg_iff]

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s := fun x hx => (hf x hx).sub (hg x hx)

@[to_fun (attr := simp)]
lemma DifferentiableOn.add_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
lemma DifferentiableOn.add_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
lemma DifferentiableOn.sub_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
lemma DifferentiableOn.sub_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_right]

@[to_fun (attr := simp, fun_prop)]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) := fun x => (hf x).sub (hg x)

@[to_fun (attr := simp)]
lemma Differentiable.add_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 f := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
lemma Differentiable.add_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 g := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
lemma Differentiable.sub_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
lemma Differentiable.sub_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 g := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_right]

theorem fderivWithin_fun_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f - g) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  fderivWithin_fun_sub hxs hf hg

theorem fderiv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv

theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f - g) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  fderiv_fun_sub hf hg

@[simp]
theorem hasFDerivAtFilter_sub_const_iff (c : F) :
    HasFDerivAtFilter (f · - c) f' L ↔ HasFDerivAtFilter f f' L := by
  simp only [sub_eq_add_neg, hasFDerivAtFilter_add_const_iff]

alias ⟨_, HasFDerivAtFilter.sub_const⟩ := hasFDerivAtFilter_sub_const_iff

@[simp]
theorem hasStrictFDerivAt_sub_const_iff (c : F) :
    HasStrictFDerivAt (f · - c) f' x ↔ HasStrictFDerivAt f f' x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.sub_const⟩ := hasStrictFDerivAt_sub_const_iff

@[simp]
theorem hasFDerivWithinAt_sub_const_iff (c : F) :
    HasFDerivWithinAt (f · - c) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.sub_const⟩ := hasFDerivWithinAt_sub_const_iff

@[simp]
theorem hasFDerivAt_sub_const_iff (c : F) : HasFDerivAt (f · - c) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.sub_const⟩ := hasFDerivAt_sub_const_iff

@[fun_prop]
theorem hasStrictFDerivAt_sub_const {x : F} (c : F) : HasStrictFDerivAt (· - c) (.id 𝕜 F) x :=
  (hasStrictFDerivAt_id x).sub_const c

@[fun_prop]
theorem hasFDerivAt_sub_const {x : F} (c : F) : HasFDerivAt (· - c) (.id 𝕜 F) x :=
  (hasFDerivAt_id x).sub_const c

@[fun_prop]
theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x :=
  (hf.hasFDerivWithinAt.sub_const c).differentiableWithinAt

@[simp]
theorem differentiableWithinAt_sub_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]

@[fun_prop]
theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x :=
  (hf.hasFDerivAt.sub_const c).differentiableAt

@[fun_prop]
theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s := fun x hx => (hf x hx).sub_const c

@[fun_prop]
theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y - c := fun x => (hf x).sub_const c

theorem fderivWithin_sub_const (c : F) :
    fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_add_const]

theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x := by
  simp only [sub_eq_add_neg, fderiv_add_const]

theorem HasFDerivAtFilter.const_sub (hf : HasFDerivAtFilter f f' L) (c : F) :
    HasFDerivAtFilter (fun x => c - f x) (-f') L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

@[fun_prop]
theorem HasStrictFDerivAt.const_sub (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => c - f x) (-f') x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
theorem HasFDerivWithinAt.const_sub (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun x => c - f x) (-f') s x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
theorem HasFDerivAt.const_sub (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => c - f x) (-f') x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
theorem DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x :=
  (hf.hasFDerivWithinAt.const_sub c).differentiableWithinAt

@[simp]
theorem differentiableWithinAt_const_sub_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp [sub_eq_add_neg]

@[fun_prop]
theorem DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x :=
  (hf.hasFDerivAt.const_sub c).differentiableAt

@[fun_prop]
theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s := fun x hx => (hf x hx).const_sub c

@[fun_prop]
theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c - f y := fun x => (hf x).const_sub c

theorem fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_fun_neg, hxs]

theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]

end Sub

section CompAdd

/-! ### Derivative of the composition with a translation -/

open scoped Pointwise Topology

theorem hasFDerivWithinAt_comp_add_left (a : E) :
    HasFDerivWithinAt (fun x ↦ f (a + x)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (a + x) := by
  have : map (a + ·) (𝓝[s] x) = 𝓝[a +ᵥ s] (a + x) := by
    simp only [nhdsWithin, Filter.map_inf (add_right_injective a)]
    simp [← Set.image_vadd]
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, ← this, Function.comp_def]

theorem differentiableWithinAt_comp_add_left (a : E) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f (a + x)) s x ↔
      DifferentiableWithinAt 𝕜 f (a +ᵥ s) (a + x) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_left]

theorem fderivWithin_comp_add_left (a : E) :
    fderivWithin 𝕜 (fun x ↦ f (a + x)) s x = fderivWithin 𝕜 f (a +ᵥ s) (a + x) := by
  classical
  simp only [fderivWithin, hasFDerivWithinAt_comp_add_left, differentiableWithinAt_comp_add_left]

theorem hasFDerivWithinAt_comp_add_right (a : E) :
    HasFDerivWithinAt (fun x ↦ f (x + a)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (x + a) := by
  simpa only [add_comm a] using hasFDerivWithinAt_comp_add_left a

theorem differentiableWithinAt_comp_add_right (a : E) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f (x + a)) s x ↔
      DifferentiableWithinAt 𝕜 f (a +ᵥ s) (x + a) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_right]

theorem fderivWithin_comp_add_right (a : E) :
    fderivWithin 𝕜 (fun x ↦ f (x + a)) s x = fderivWithin 𝕜 f (a +ᵥ s) (x + a) := by
  simp only [add_comm _ a, fderivWithin_comp_add_left]

theorem hasFDerivAt_comp_add_right (a : E) :
    HasFDerivAt (fun x ↦ f (x + a)) f' x ↔ HasFDerivAt f f' (x + a) := by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_add_right]

theorem differentiableAt_comp_add_right (a : E) :
    DifferentiableAt 𝕜 (fun x ↦ f (x + a)) x ↔ DifferentiableAt 𝕜 f (x + a) := by
  simp [DifferentiableAt, hasFDerivAt_comp_add_right]

theorem fderiv_comp_add_right (a : E) :
    fderiv 𝕜 (fun x ↦ f (x + a)) x = fderiv 𝕜 f (x + a) := by
  simp [← fderivWithin_univ, fderivWithin_comp_add_right]

theorem hasFDerivAt_comp_add_left (a : E) :
    HasFDerivAt (fun x ↦ f (a + x)) f' x ↔ HasFDerivAt f f' (a + x) := by
  simpa [add_comm a] using hasFDerivAt_comp_add_right a

theorem differentiableAt_comp_add_left (a : E) :
    DifferentiableAt 𝕜 (fun x ↦ f (a + x)) x ↔ DifferentiableAt 𝕜 f (a + x) := by
  simp [DifferentiableAt, hasFDerivAt_comp_add_left]

theorem fderiv_comp_add_left (a : E) :
    fderiv 𝕜 (fun x ↦ f (a + x)) x = fderiv 𝕜 f (a + x) := by
  simpa [add_comm a] using fderiv_comp_add_right a

theorem hasFDerivWithinAt_comp_sub (a : E) :
    HasFDerivWithinAt (fun x ↦ f (x - a)) f' s x ↔ HasFDerivWithinAt f f' (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using hasFDerivWithinAt_comp_add_right (-a)

theorem differentiableWithinAt_comp_sub (a : E) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f (x - a)) s x ↔
      DifferentiableWithinAt 𝕜 f (-a +ᵥ s) (x - a) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_sub]

theorem fderivWithin_comp_sub (a : E) :
    fderivWithin 𝕜 (fun x ↦ f (x - a)) s x = fderivWithin 𝕜 f (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using fderivWithin_comp_add_right (-a)

theorem hasFDerivAt_comp_sub (a : E) :
    HasFDerivAt (fun x ↦ f (x - a)) f' x ↔ HasFDerivAt f f' (x - a) := by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_sub]

theorem differentiableAt_comp_sub (a : E) :
    DifferentiableAt 𝕜 (fun x ↦ f (x - a)) x ↔ DifferentiableAt 𝕜 f (x - a) := by
  simp [DifferentiableAt, hasFDerivAt_comp_sub]

theorem fderiv_comp_sub (a : E) :
    fderiv 𝕜 (fun x ↦ f (x - a)) x = fderiv 𝕜 f (x - a) := by
  simp [← fderivWithin_univ, fderivWithin_comp_sub]

end CompAdd

end
