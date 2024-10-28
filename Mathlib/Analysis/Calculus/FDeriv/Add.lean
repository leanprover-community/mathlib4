/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

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

open scoped Classical

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
theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).hasStrictFDerivAt.comp x h

theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' x L) (c : R) :
    HasFDerivAtFilter (fun x => c • f x) (c • f') x L :=
  (c • (1 : F →L[𝕜] F)).hasFDerivAtFilter.comp x h tendsto_map

@[fun_prop]
nonrec theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (fun x => c • f x) (c • f') s x :=
  h.const_smul c

@[fun_prop]
nonrec theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (fun x => c • f x) (c • f') x :=
  h.const_smul c

@[fun_prop]
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[fun_prop]
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (fun y => c • f y) s := fun x hx => (h x hx).const_smul c

@[fun_prop]
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 fun y => c • f y := fun x => (h x).const_smul c

theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs

theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

end ConstSMul

section Add

/-! ### Derivative of the sum of two functions -/


@[fun_prop]
nonrec theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x)
    (hg : HasStrictFDerivAt g g' x) : HasStrictFDerivAt (fun y => f y + g y) (f' + g') x :=
  (hf.add hg).congr_left fun y => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel

theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' x L)
    (hg : HasFDerivAtFilter g g' x L) : HasFDerivAtFilter (fun y => f y + g y) (f' + g') x L :=
  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel

@[fun_prop]
nonrec theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg

@[fun_prop]
nonrec theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg

@[fun_prop]
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y + g y) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[fun_prop]
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s := fun x hx => (hf x hx).add (hg x hx)

@[simp, fun_prop]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y + g y := fun x => (hf x).add (hg x)

theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

@[fun_prop]
theorem HasStrictFDerivAt.add_const (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun y => f y + c) f' x :=
  add_zero f' ▸ hf.add (hasStrictFDerivAt_const _ _)

theorem HasFDerivAtFilter.add_const (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun y => f y + c) f' x L :=
  add_zero f' ▸ hf.add (hasFDerivAtFilter_const _ _ _)

@[fun_prop]
nonrec theorem HasFDerivWithinAt.add_const (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun y => f y + c) f' s x :=
  hf.add_const c

@[fun_prop]
nonrec theorem HasFDerivAt.add_const (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => f x + c) f' x :=
  hf.add_const c

@[fun_prop]
theorem DifferentiableWithinAt.add_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x :=
  (hf.hasFDerivWithinAt.add_const c).differentiableWithinAt

@[simp]
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.add_const c⟩

@[fun_prop]
theorem DifferentiableAt.add_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x :=
  (hf.hasFDerivAt.add_const c).differentiableAt

@[simp]
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.add_const c⟩

@[fun_prop]
theorem DifferentiableOn.add_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s := fun x hx => (hf x hx).add_const c

@[simp]
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.add_const c⟩

@[fun_prop]
theorem Differentiable.add_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y + c := fun x => (hf x).add_const c

@[simp]
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.add_const c⟩

theorem fderivWithin_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x :=
  if hf : DifferentiableWithinAt 𝕜 f s x then (hf.hasFDerivWithinAt.add_const c).fderivWithin hxs
  else by
    rw [fderivWithin_zero_of_not_differentiableWithinAt hf,
      fderivWithin_zero_of_not_differentiableWithinAt]
    simpa

theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const uniqueDiffWithinAt_univ]

@[fun_prop]
theorem HasStrictFDerivAt.const_add (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun y => c + f y) f' x :=
  zero_add f' ▸ (hasStrictFDerivAt_const _ _).add hf

theorem HasFDerivAtFilter.const_add (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun y => c + f y) f' x L :=
  zero_add f' ▸ (hasFDerivAtFilter_const _ _ _).add hf

@[fun_prop]
nonrec theorem HasFDerivWithinAt.const_add (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c

@[fun_prop]
nonrec theorem HasFDerivAt.const_add (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => c + f x) f' x :=
  hf.const_add c

@[fun_prop]
theorem DifferentiableWithinAt.const_add (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x :=
  (hf.hasFDerivWithinAt.const_add c).differentiableWithinAt

@[simp]
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩

@[fun_prop]
theorem DifferentiableAt.const_add (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x :=
  (hf.hasFDerivAt.const_add c).differentiableAt

@[simp]
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩

@[fun_prop]
theorem DifferentiableOn.const_add (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s := fun x hx => (hf x hx).const_add c

@[simp]
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩

@[fun_prop]
theorem Differentiable.const_add (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c + f y := fun x => (hf x).const_add c

@[simp]
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩

theorem fderivWithin_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const hxs c

theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


variable {ι : Type*} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

@[fun_prop]
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  dsimp [HasStrictFDerivAt] at *
  convert IsLittleO.sum h
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]

theorem HasFDerivAtFilter.sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) x L) :
    HasFDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [ContinuousLinearMap.sum_apply]

@[fun_prop]
theorem HasFDerivWithinAt.sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
theorem HasFDerivAt.sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i ∈ u, A i y) s x :=
  HasFDerivWithinAt.differentiableWithinAt <|
    HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i ∈ u, A i y) x :=
  HasFDerivAt.differentiableAt <| HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt

@[fun_prop]
theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i ∈ u, A i y) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp, fun_prop]
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i ∈ u, A i y := fun x => DifferentiableAt.sum fun i hi => h i hi x

theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i ∈ u, A i y) s x = ∑ i ∈ u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i ∈ u, A i y) x = ∑ i ∈ u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/


@[fun_prop]
theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => -f x) (-f') x :=
  (-1 : F →L[𝕜] F).hasStrictFDerivAt.comp x h

theorem HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (fun x => -f x) (-f') x L :=
  (-1 : F →L[𝕜] F).hasFDerivAtFilter.comp x h tendsto_map

@[fun_prop]
nonrec theorem HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg

@[fun_prop]
nonrec theorem HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (fun x => -f x) (-f') x :=
  h.neg

@[fun_prop]
theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.hasFDerivWithinAt.neg.differentiableWithinAt

@[simp]
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.hasFDerivAt.neg.differentiableAt

@[simp]
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg

@[simp]
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y := fun x =>
  (h x).neg

@[simp]
theorem differentiable_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x :=
  if h : DifferentiableWithinAt 𝕜 f s x then h.hasFDerivWithinAt.neg.fderivWithin hxs
  else by
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

@[simp]
theorem fderiv_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_neg uniqueDiffWithinAt_univ]

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


@[fun_prop]
theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' x L) (hg : HasFDerivAtFilter g g' x L) :
    HasFDerivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
nonrec theorem HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg

@[fun_prop]
nonrec theorem HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg

@[fun_prop]
theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y - g y) s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).differentiableAt

@[simp]
lemma DifferentiableAt.add_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x ↔ DifferentiableAt 𝕜 f x := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[simp]
lemma DifferentiableAt.add_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [add_comm (f _), hg.add_iff_left]

@[simp]
lemma DifferentiableAt.sub_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_neg_iff, hg, add_iff_left]

@[simp]
lemma DifferentiableAt.sub_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [sub_eq_add_neg, hg, add_iff_right, differentiableAt_neg_iff]

@[fun_prop]
theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s := fun x hx => (hf x hx).sub (hg x hx)

@[simp]
lemma DifferentiableOn.add_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[simp]
lemma DifferentiableOn.add_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [add_comm (f _), hg.add_iff_left]

@[simp]
lemma DifferentiableOn.sub_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_left]

@[simp]
lemma DifferentiableOn.sub_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_right]

@[simp, fun_prop]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y - g y := fun x => (hf x).sub (hg x)

@[simp]
lemma Differentiable.add_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (fun y => f y + g y) ↔ Differentiable 𝕜 f := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[simp]
lemma Differentiable.add_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun y => f y + g y) ↔ Differentiable 𝕜 g := by
  simp only [add_comm (f _), hg.add_iff_left]

@[simp]
lemma Differentiable.sub_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (fun y => f y - g y) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_left]

@[simp]
lemma Differentiable.sub_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun y => f y - g y) ↔ Differentiable 𝕜 g := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_right]

theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv

@[fun_prop]
theorem HasStrictFDerivAt.sub_const (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => f x - c) f' x := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem HasFDerivAtFilter.sub_const (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun x => f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)

@[fun_prop]
nonrec theorem HasFDerivWithinAt.sub_const (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c

@[fun_prop]
nonrec theorem HasFDerivAt.sub_const (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => f x - c) f' x :=
  hf.sub_const c

@[fun_prop]
theorem hasStrictFDerivAt_sub_const {x : F} (c : F) : HasStrictFDerivAt (· - c) (id 𝕜 F) x :=
  (hasStrictFDerivAt_id x).sub_const c

@[fun_prop]
theorem hasFDerivAt_sub_const {x : F} (c : F) : HasFDerivAt (· - c) (id 𝕜 F) x :=
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

@[deprecated DifferentiableAt.sub_iff_left (since := "2024-07-11")]
theorem differentiableAt_sub_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x ↔ DifferentiableAt 𝕜 f x :=
  (differentiableAt_const _).sub_iff_left

@[fun_prop]
theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s := fun x hx => (hf x hx).sub_const c

@[deprecated DifferentiableOn.sub_iff_left (since := "2024-07-11")]
theorem differentiableOn_sub_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s ↔ DifferentiableOn 𝕜 f s :=
  (differentiableOn_const _).sub_iff_left

@[fun_prop]
theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y - c := fun x => (hf x).sub_const c

@[deprecated Differentiable.sub_iff_left (since := "2024-07-11")]
theorem differentiable_sub_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y - c) ↔ Differentiable 𝕜 f :=
  (differentiable_const _).sub_iff_left

theorem fderivWithin_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_add_const hxs]

theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x := by
  simp only [sub_eq_add_neg, fderiv_add_const]

@[fun_prop]
theorem HasStrictFDerivAt.const_sub (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem HasFDerivAtFilter.const_sub (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun x => c - f x) (-f') x L := by
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

@[deprecated DifferentiableAt.sub_iff_right (since := "2024-07-11")]
theorem differentiableAt_const_sub_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x ↔ DifferentiableAt 𝕜 f x :=
  (differentiableAt_const _).sub_iff_right

@[fun_prop]
theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s := fun x hx => (hf x hx).const_sub c

@[deprecated DifferentiableOn.sub_iff_right (since := "2024-07-11")]
theorem differentiableOn_const_sub_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s ↔ DifferentiableOn 𝕜 f s :=
  (differentiableOn_const _).sub_iff_right

@[fun_prop]
theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c - f y := fun x => (hf x).const_sub c

@[deprecated Differentiable.sub_iff_right (since := "2024-07-11")]
theorem differentiable_const_sub_iff (c : F) :
    (Differentiable 𝕜 fun y => c - f y) ↔ Differentiable 𝕜 f :=
  (differentiable_const _).sub_iff_right

theorem fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_neg, hxs]

theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]

end Sub

end
