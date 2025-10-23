/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Additive operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
-/


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
variable {L : Filter E}

section ConstSMul

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/

@[fun_prop]
theorem HasStrictFDerivAt.fun_const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).hasStrictFDerivAt.comp x h

@[fun_prop]
theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (c • f) (c • f') x :=
  h.fun_const_smul c

theorem HasFDerivAtFilter.fun_const_smul (h : HasFDerivAtFilter f f' x L) (c : R) :
    HasFDerivAtFilter (fun x => c • f x) (c • f') x L :=
  (c • (1 : F →L[𝕜] F)).hasFDerivAtFilter.comp x h tendsto_map

theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' x L) (c : R) :
    HasFDerivAtFilter (c • f) (c • f') x L :=
  h.fun_const_smul c

@[fun_prop]
nonrec theorem HasFDerivWithinAt.fun_const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (fun x => c • f x) (c • f') s x :=
  h.const_smul c

@[fun_prop]
nonrec theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (c • f) (c • f') s x :=
  h.const_smul c

@[fun_prop]
nonrec theorem HasFDerivAt.fun_const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (fun x => c • f x) (c • f') x :=
  h.const_smul c

@[fun_prop]
nonrec theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (c • f) (c • f') x :=
  h.const_smul c

@[fun_prop]
theorem DifferentiableWithinAt.fun_const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[fun_prop]
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (c • f) s x :=
  h.fun_const_smul c

@[fun_prop]
theorem DifferentiableAt.fun_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[fun_prop]
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (c • f) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[fun_prop]
theorem DifferentiableOn.fun_const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (fun y => c • f y) s := fun x hx => (h x hx).const_smul c

@[fun_prop]
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (h x hx).const_smul c

@[fun_prop]
theorem Differentiable.fun_const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 fun y => c • f y := fun x => (h x).const_smul c

@[fun_prop]
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
  · obtain (rfl | hc) := eq_or_ne c 0
    · simp
    have : ¬DifferentiableWithinAt 𝕜 (c • f) s x := by
      contrapose! h
      exact (differentiableWithinAt_smul_iff c).mp h
    simp [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this]

/-- Special case of `fderivWithin_const_smul_of_invertible` over a field: any constant is allowed -/
lemma fderivWithin_const_smul_of_field (c : 𝕜) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  obtain (rfl | ha) := eq_or_ne c 0
  · simp
  · have : Invertible c := invertibleOfNonzero ha
    ext x
    simp [fderivWithin_const_smul_of_invertible c (f := f) hs]

@[deprecated (since := "2025-06-14")] alias fderivWithin_const_smul' := fderivWithin_const_smul

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

/-- Special case of `fderiv_const_smul_of_invertible` over a field: any constant is allowed -/
lemma fderiv_const_smul_of_field (c : 𝕜) : fderiv 𝕜 (c • f) = c • fderiv 𝕜 f := by
  simp_rw [← fderivWithin_univ]
  ext x
  simp [fderivWithin_const_smul_of_field c uniqueDiffWithinAt_univ]

@[deprecated (since := "2025-06-14")] alias fderiv_const_smul' := fderiv_const_smul

end ConstSMul

section Add

/-! ### Derivative of the sum of two functions -/


@[fun_prop]
nonrec theorem HasStrictFDerivAt.fun_add (hf : HasStrictFDerivAt f f' x)
    (hg : HasStrictFDerivAt g g' x) : HasStrictFDerivAt (fun y => f y + g y) (f' + g') x :=
  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun y => by
    simp only [map_sub, add_apply]
    abel

@[fun_prop]
nonrec theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x)
    (hg : HasStrictFDerivAt g g' x) : HasStrictFDerivAt (f + g) (f' + g') x :=
  hf.fun_add hg

theorem HasFDerivAtFilter.fun_add (hf : HasFDerivAtFilter f f' x L)
    (hg : HasFDerivAtFilter g g' x L) : HasFDerivAtFilter (fun y => f y + g y) (f' + g') x L :=
  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    simp only [map_sub, add_apply]
    abel

theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' x L)
    (hg : HasFDerivAtFilter g g' x L) : HasFDerivAtFilter (f + g) (f' + g') x L :=
  hf.fun_add hg

@[fun_prop]
nonrec theorem HasFDerivWithinAt.fun_add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg

@[fun_prop]
nonrec theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s x :=
  hf.add hg

@[fun_prop]
nonrec theorem HasFDerivAt.fun_add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg

@[fun_prop]
nonrec theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f + g) (f' + g') x :=
  hf.add hg

@[fun_prop]
theorem DifferentiableWithinAt.fun_add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y + g y) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f + g) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[simp, fun_prop]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[fun_prop]
theorem DifferentiableOn.fun_add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s := fun x hx => (hf x hx).add (hg x hx)

@[fun_prop]
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s := fun x hx => (hf x hx).add (hg x hx)

@[simp, fun_prop]
theorem Differentiable.fun_add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y + g y := fun x => (hf x).add (hg x)

@[simp, fun_prop]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) := fun x => (hf x).add (hg x)

theorem fderivWithin_fun_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f + g) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  fderivWithin_fun_add hxs hf hg

@[deprecated (since := "2025-06-14")] alias fderivWithin_add' := fderivWithin_add

theorem fderiv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  fderiv_fun_add hf hg

@[deprecated (since := "2025-06-14")] alias fderiv_add' := fderiv_add

@[simp]
theorem hasFDerivAtFilter_add_const_iff (c : F) :
    HasFDerivAtFilter (f · + c) f' x L ↔ HasFDerivAtFilter f f' x L := by
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
    HasFDerivAtFilter (c + f ·) f' x L ↔ HasFDerivAtFilter f f' x L := by
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
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]

@[fun_prop]
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x := by
  convert HasStrictFDerivAt.fun_sum h; simp

theorem HasFDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) x L) :
    HasFDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [ContinuousLinearMap.sum_apply]

theorem HasFDerivAtFilter.sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) x L) :
    HasFDerivAtFilter (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x L := by
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


@[fun_prop]
theorem HasStrictFDerivAt.fun_neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => -f x) (-f') x :=
  (-1 : F →L[𝕜] F).hasStrictFDerivAt.comp x h

@[fun_prop]
theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (-f) (-f') x :=
  (-1 : F →L[𝕜] F).hasStrictFDerivAt.comp x h

theorem HasFDerivAtFilter.fun_neg (h : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (fun x => -f x) (-f') x L :=
  (-1 : F →L[𝕜] F).hasFDerivAtFilter.comp x h tendsto_map

theorem HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (-f) (-f') x L :=
  (-1 : F →L[𝕜] F).hasFDerivAtFilter.comp x h tendsto_map

@[fun_prop]
nonrec theorem HasFDerivWithinAt.fun_neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg

@[fun_prop]
nonrec theorem HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (-f) (-f') s x :=
  h.neg

@[fun_prop]
nonrec theorem HasFDerivAt.fun_neg (h : HasFDerivAt f f' x) : HasFDerivAt (fun x => -f x) (-f') x :=
  h.neg

@[fun_prop]
nonrec theorem HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (-f) (-f') x :=
  h.neg

@[fun_prop]
theorem DifferentiableWithinAt.fun_neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.hasFDerivWithinAt.neg.differentiableWithinAt

@[fun_prop]
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

@[fun_prop]
theorem DifferentiableAt.fun_neg (h : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.hasFDerivAt.neg.differentiableAt

@[fun_prop]
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (-f) x :=
  h.hasFDerivAt.neg.differentiableAt

@[simp]
theorem differentiableAt_fun_neg_iff :
    DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (-f) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem DifferentiableOn.fun_neg (h : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg

@[fun_prop]
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (-f) s :=
  fun x hx => (h x hx).neg

@[simp]
theorem differentiableOn_fun_neg_iff :
    DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (-f) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem Differentiable.fun_neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y := fun x =>
  (h x).neg

@[fun_prop]
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
  classical
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
  · rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x :=
  fderivWithin_fun_neg hxs

@[deprecated (since := "2025-06-14")] alias fderivWithin_neg' := fderivWithin_neg

@[simp]
theorem fderiv_fun_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_fun_neg uniqueDiffWithinAt_univ]

/-- Version of `fderiv_neg` where the function is written `-f` instead of `fun y ↦ - f y`. -/
theorem fderiv_neg : fderiv 𝕜 (-f) x = -fderiv 𝕜 f x :=
  fderiv_fun_neg

@[deprecated (since := "2025-06-14")] alias fderiv_neg' := fderiv_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


@[fun_prop]
theorem HasStrictFDerivAt.fun_sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f - g) (f' - g') x :=
  hf.fun_sub hg

theorem HasFDerivAtFilter.fun_sub (hf : HasFDerivAtFilter f f' x L)
    (hg : HasFDerivAtFilter g g' x L) :
    HasFDerivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' x L) (hg : HasFDerivAtFilter g g' x L) :
    HasFDerivAtFilter (f - g) (f' - g') x L :=
  hf.fun_sub hg

@[fun_prop]
nonrec theorem HasFDerivWithinAt.fun_sub (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg

@[fun_prop]
nonrec theorem HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s x :=
  hf.sub hg

@[fun_prop]
nonrec theorem HasFDerivAt.fun_sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg

@[fun_prop]
nonrec theorem HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f - g) (f' - g') x :=
  hf.sub hg

@[fun_prop]
theorem DifferentiableWithinAt.fun_sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y - g y) s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]
theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f - g) s x :=
  hf.fun_sub hg

@[simp, fun_prop]
theorem DifferentiableAt.fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).differentiableAt

@[simp, fun_prop]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x :=
  hf.fun_sub hg

@[simp]
lemma DifferentiableAt.fun_add_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x ↔ DifferentiableAt 𝕜 f x := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.fun_sub hg

@[simp]
lemma DifferentiableAt.add_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 f x :=
  hg.fun_add_iff_left

@[simp]
lemma DifferentiableAt.fun_add_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [add_comm (f _), hg.fun_add_iff_left]

@[simp]
lemma DifferentiableAt.add_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 g x :=
  hg.fun_add_iff_right

@[simp]
lemma DifferentiableAt.fun_sub_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_fun_neg_iff, hg, fun_add_iff_left]

@[simp]
lemma DifferentiableAt.sub_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 f x :=
  hg.fun_sub_iff_left

@[simp]
lemma DifferentiableAt.fun_sub_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [sub_eq_add_neg, hg, fun_add_iff_right, differentiableAt_fun_neg_iff]

@[simp]
lemma DifferentiableAt.sub_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 g x :=
  hg.fun_sub_iff_right

@[fun_prop]
theorem DifferentiableOn.fun_sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s := fun x hx => (hf x hx).sub (hg x hx)

@[fun_prop]
theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s := fun x hx => (hf x hx).sub (hg x hx)

@[simp]
lemma DifferentiableOn.fun_add_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.fun_sub hg

@[simp]
lemma DifferentiableOn.add_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 f s :=
  hg.fun_add_iff_left

@[simp]
lemma DifferentiableOn.fun_add_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [add_comm (f _), hg.fun_add_iff_left]

@[simp]
lemma DifferentiableOn.add_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 g s :=
  hg.fun_add_iff_right

@[simp]
lemma DifferentiableOn.fun_sub_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_fun_neg_iff, hg, fun_add_iff_left]

@[simp]
lemma DifferentiableOn.sub_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 f s :=
  hg.fun_sub_iff_left

@[simp]
lemma DifferentiableOn.fun_sub_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [sub_eq_add_neg, differentiableOn_fun_neg_iff, hg, fun_add_iff_right]

@[simp]
lemma DifferentiableOn.sub_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 g s :=
  hg.fun_sub_iff_right

@[simp, fun_prop]
theorem Differentiable.fun_sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y - g y := fun x => (hf x).sub (hg x)

@[simp, fun_prop]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) := fun x => (hf x).sub (hg x)

@[simp]
lemma Differentiable.fun_add_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (fun y => f y + g y) ↔ Differentiable 𝕜 f := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.fun_sub hg

@[simp]
lemma Differentiable.add_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 f :=
  hg.fun_add_iff_left

@[simp]
lemma Differentiable.fun_add_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun y => f y + g y) ↔ Differentiable 𝕜 g := by
  simp only [add_comm (f _), hg.fun_add_iff_left]

@[simp]
lemma Differentiable.add_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 g :=
  hg.fun_add_iff_right

@[simp]
lemma Differentiable.fun_sub_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (fun y => f y - g y) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_fun_neg_iff, hg, fun_add_iff_left]

@[simp]
lemma Differentiable.sub_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 f :=
  hg.fun_sub_iff_left

@[simp]
lemma Differentiable.fun_sub_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun y => f y - g y) ↔ Differentiable 𝕜 g := by
  simp only [sub_eq_add_neg, differentiable_fun_neg_iff, hg, fun_add_iff_right]

@[simp]
lemma Differentiable.sub_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 g :=
  hg.fun_sub_iff_right

theorem fderivWithin_fun_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f - g) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  fderivWithin_fun_sub hxs hf hg

@[deprecated (since := "2025-06-14")] alias fderivWithin_sub' := fderivWithin_sub

theorem fderiv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv

theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f - g) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  fderiv_fun_sub hf hg

@[deprecated (since := "2025-06-14")] alias fderiv_sub' := fderiv_sub

@[simp]
theorem hasFDerivAtFilter_sub_const_iff (c : F) :
    HasFDerivAtFilter (f · - c) f' x L ↔ HasFDerivAtFilter f f' x L := by
  simp only [sub_eq_add_neg, hasFDerivAtFilter_add_const_iff]

alias ⟨_, HasFDerivAtFilter.sub_const⟩ := hasFDerivAtFilter_sub_const_iff

@[simp]
theorem hasStrictFDerivAt_sub_const_iff (c : F) :
    HasStrictFDerivAt (f · - c) f' x ↔ HasStrictFDerivAt f f' x := by
  simp only [sub_eq_add_neg, hasStrictFDerivAt_add_const_iff]

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

theorem HasFDerivAtFilter.const_sub (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

@[fun_prop]
nonrec theorem HasStrictFDerivAt.const_sub (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

@[fun_prop]
nonrec theorem HasFDerivWithinAt.const_sub (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c

@[fun_prop]
nonrec theorem HasFDerivAt.const_sub (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c

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
