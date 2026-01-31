/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Fréchet derivative of constant functions

This file contains the usual formulas (and existence assertions) for the derivative of constant
functions, including various special cases such as the functions `0`, `1`, `Nat.cast n`,
`Int.cast z`, and other numerals.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E → F} {x : E} {s : Set E}

section Const

@[fun_prop]
theorem hasStrictFDerivAt_const (c : F) (x : E) :
    HasStrictFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun _ => by
    simp only [zero_apply, sub_self, Pi.zero_apply]

@[fun_prop]
theorem hasStrictFDerivAt_zero (x : E) :
    HasStrictFDerivAt (0 : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
theorem hasStrictFDerivAt_one [One F] (x : E) :
    HasStrictFDerivAt (1 : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
theorem hasStrictFDerivAt_natCast [NatCast F] (n : ℕ) (x : E) :
    HasStrictFDerivAt (n : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
theorem hasStrictFDerivAt_intCast [IntCast F] (z : ℤ) (x : E) :
    HasStrictFDerivAt (z : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
theorem hasStrictFDerivAt_ofNat (n : ℕ) [OfNat F n] (x : E) :
    HasStrictFDerivAt (ofNat(n) : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

theorem hasFDerivAtFilter_const (c : F) (x : E) (L : Filter E) :
    HasFDerivAtFilter (fun _ => c) (0 : E →L[𝕜] F) x L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun _ => by
    simp only [zero_apply, sub_self, Pi.zero_apply]

theorem hasFDerivAtFilter_zero (x : E) (L : Filter E) :
    HasFDerivAtFilter (0 : E → F) (0 : E →L[𝕜] F) x L := hasFDerivAtFilter_const _ _ _

theorem hasFDerivAtFilter_one [One F] (x : E) (L : Filter E) :
    HasFDerivAtFilter (1 : E → F) (0 : E →L[𝕜] F) x L := hasFDerivAtFilter_const _ _ _

theorem hasFDerivAtFilter_natCast [NatCast F] (n : ℕ) (x : E) (L : Filter E) :
    HasFDerivAtFilter (n : E → F) (0 : E →L[𝕜] F) x L :=
  hasFDerivAtFilter_const _ _ _

theorem hasFDerivAtFilter_intCast [IntCast F] (z : ℤ) (x : E) (L : Filter E) :
    HasFDerivAtFilter (z : E → F) (0 : E →L[𝕜] F) x L :=
  hasFDerivAtFilter_const _ _ _

theorem hasFDerivAtFilter_ofNat (n : ℕ) [OfNat F n] (x : E) (L : Filter E) :
    HasFDerivAtFilter (ofNat(n) : E → F) (0 : E →L[𝕜] F) x L :=
  hasFDerivAtFilter_const _ _ _

@[fun_prop]
theorem hasFDerivWithinAt_const (c : F) (x : E) (s : Set E) :
    HasFDerivWithinAt (fun _ => c) (0 : E →L[𝕜] F) s x :=
  hasFDerivAtFilter_const _ _ _

@[fun_prop]
theorem hasFDerivWithinAt_zero (x : E) (s : Set E) :
    HasFDerivWithinAt (0 : E → F) (0 : E →L[𝕜] F) s x := hasFDerivWithinAt_const _ _ _

@[fun_prop]
theorem hasFDerivWithinAt_one [One F] (x : E) (s : Set E) :
    HasFDerivWithinAt (1 : E → F) (0 : E →L[𝕜] F) s x := hasFDerivWithinAt_const _ _ _

@[fun_prop]
theorem hasFDerivWithinAt_natCast [NatCast F] (n : ℕ) (x : E) (s : Set E) :
    HasFDerivWithinAt (n : E → F) (0 : E →L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
theorem hasFDerivWithinAt_intCast [IntCast F] (z : ℤ) (x : E) (s : Set E) :
    HasFDerivWithinAt (z : E → F) (0 : E →L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
theorem hasFDerivWithinAt_ofNat (n : ℕ) [OfNat F n] (x : E) (s : Set E) :
    HasFDerivWithinAt (ofNat(n) : E → F) (0 : E →L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  hasFDerivAtFilter_const _ _ _

@[fun_prop]
theorem hasFDerivAt_zero (x : E) :
    HasFDerivAt (0 : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
theorem hasFDerivAt_one [One F] (x : E) :
    HasFDerivAt (1 : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
theorem hasFDerivAt_natCast [NatCast F] (n : ℕ) (x : E) :
    HasFDerivAt (n : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
theorem hasFDerivAt_intCast [IntCast F] (z : ℤ) (x : E) :
    HasFDerivAt (z : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
theorem hasFDerivAt_ofNat (n : ℕ) [OfNat F n] (x : E) :
    HasFDerivAt (ofNat(n) : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[simp, fun_prop]
theorem differentiableAt_const (c : F) : DifferentiableAt 𝕜 (fun _ => c) x :=
  ⟨0, hasFDerivAt_const c x⟩

@[simp, fun_prop]
theorem differentiableAt_zero (x : E) :
    DifferentiableAt 𝕜 (0 : E → F) x := differentiableAt_const _

@[simp, fun_prop]
theorem differentiableAt_one [One F] (x : E) :
    DifferentiableAt 𝕜 (1 : E → F) x := differentiableAt_const _

@[simp, fun_prop]
theorem differentiableAt_natCast [NatCast F] (n : ℕ) (x : E) :
    DifferentiableAt 𝕜 (n : E → F) x := differentiableAt_const _

@[simp, fun_prop]
theorem differentiableAt_intCast [IntCast F] (z : ℤ) (x : E) :
    DifferentiableAt 𝕜 (z : E → F) x := differentiableAt_const _

@[simp low, fun_prop]
theorem differentiableAt_ofNat (n : ℕ) [OfNat F n] (x : E) :
    DifferentiableAt 𝕜 (ofNat(n) : E → F) x := differentiableAt_const _

@[fun_prop]
theorem differentiableWithinAt_const (c : F) : DifferentiableWithinAt 𝕜 (fun _ => c) s x :=
  DifferentiableAt.differentiableWithinAt (differentiableAt_const _)

@[fun_prop]
theorem differentiableWithinAt_zero :
    DifferentiableWithinAt 𝕜 (0 : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
theorem differentiableWithinAt_one [One F] :
    DifferentiableWithinAt 𝕜 (1 : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
theorem differentiableWithinAt_natCast [NatCast F] (n : ℕ) :
    DifferentiableWithinAt 𝕜 (n : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
theorem differentiableWithinAt_intCast [IntCast F] (z : ℤ) :
    DifferentiableWithinAt 𝕜 (z : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
theorem differentiableWithinAt_ofNat (n : ℕ) [OfNat F n] :
    DifferentiableWithinAt 𝕜 (ofNat(n) : E → F) s x := differentiableWithinAt_const _

theorem fderivWithin_const_apply (c : F) : fderivWithin 𝕜 (fun _ => c) s x = 0 := by
  rw [fderivWithin, if_pos]
  apply hasFDerivWithinAt_const

@[simp]
theorem fderivWithin_fun_const (c : F) : fderivWithin 𝕜 (fun _ ↦ c) s = 0 := by
  ext
  rw [fderivWithin_const_apply, Pi.zero_apply]

@[simp]
theorem fderivWithin_const (c : F) : fderivWithin 𝕜 (Function.const E c) s = 0 :=
  fderivWithin_fun_const c

@[simp]
theorem fderivWithin_zero : fderivWithin 𝕜 (0 : E → F) s = 0 := fderivWithin_const _

@[simp]
theorem fderivWithin_one [One F] : fderivWithin 𝕜 (1 : E → F) s = 0 := fderivWithin_const _

@[simp]
theorem fderivWithin_natCast [NatCast F] (n : ℕ) : fderivWithin 𝕜 (n : E → F) s = 0 :=
  fderivWithin_const _

@[simp]
theorem fderivWithin_intCast [IntCast F] (z : ℤ) : fderivWithin 𝕜 (z : E → F) s = 0 :=
  fderivWithin_const _

@[simp low]
theorem fderivWithin_ofNat (n : ℕ) [OfNat F n] : fderivWithin 𝕜 (ofNat(n) : E → F) s = 0 :=
  fderivWithin_const _

theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun _ => c) x = 0 :=
  (hasFDerivAt_const c x).fderiv

@[simp]
theorem fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) = 0 := by
  rw [← fderivWithin_univ, fderivWithin_fun_const]

@[simp]
theorem fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0 :=
  fderiv_fun_const c

@[simp]
theorem fderiv_zero : fderiv 𝕜 (0 : E → F) = 0 := fderiv_const _

@[simp]
theorem fderiv_one [One F] : fderiv 𝕜 (1 : E → F) = 0 := fderiv_const _

@[simp]
theorem fderiv_natCast [NatCast F] (n : ℕ) : fderiv 𝕜 (n : E → F) = 0 := fderiv_const _

@[simp]
theorem fderiv_intCast [IntCast F] (z : ℤ) : fderiv 𝕜 (z : E → F) = 0 := fderiv_const _

@[simp low]
theorem fderiv_ofNat (n : ℕ) [OfNat F n] : fderiv 𝕜 (ofNat(n) : E → F) = 0 := fderiv_const _

@[simp, fun_prop]
theorem differentiable_const (c : F) : Differentiable 𝕜 fun _ : E => c := fun _ =>
  differentiableAt_const _

@[simp, fun_prop]
theorem differentiable_zero :
    Differentiable 𝕜 (0 : E → F) := differentiable_const _

@[simp, fun_prop]
theorem differentiable_one [One F] :
    Differentiable 𝕜 (1 : E → F) := differentiable_const _

@[simp, fun_prop]
theorem differentiable_natCast [NatCast F] (n : ℕ) :
    Differentiable 𝕜 (n : E → F) := differentiable_const _

@[simp, fun_prop]
theorem differentiable_intCast [IntCast F] (z : ℤ) :
    Differentiable 𝕜 (z : E → F) := differentiable_const _

@[simp low, fun_prop]
theorem differentiable_ofNat (n : ℕ) [OfNat F n] :
    Differentiable 𝕜 (ofNat(n) : E → F) := differentiable_const _

@[simp, fun_prop]
theorem differentiableOn_const (c : F) : DifferentiableOn 𝕜 (fun _ => c) s :=
  (differentiable_const _).differentiableOn

@[simp, fun_prop]
theorem differentiableOn_zero :
    DifferentiableOn 𝕜 (0 : E → F) s := differentiableOn_const _

@[simp, fun_prop]
theorem differentiableOn_one [One F] :
    DifferentiableOn 𝕜 (1 : E → F) s := differentiableOn_const _

@[simp, fun_prop]
theorem differentiableOn_natCast [NatCast F] (n : ℕ) :
    DifferentiableOn 𝕜 (n : E → F) s := differentiableOn_const _

@[simp, fun_prop]
theorem differentiableOn_intCast [IntCast F] (z : ℤ) :
    DifferentiableOn 𝕜 (z : E → F) s := differentiableOn_const _

@[simp low, fun_prop]
theorem differentiableOn_ofNat (n : ℕ) [OfNat F n] :
    DifferentiableOn 𝕜 (ofNat(n) : E → F) s := differentiableOn_const _

@[fun_prop]
theorem hasFDerivWithinAt_singleton (f : E → F) (x : E) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) {x} x := by
  simp only [HasFDerivWithinAt, nhdsWithin_singleton, hasFDerivAtFilter_iff_isLittleO,
    isLittleO_pure, ContinuousLinearMap.zero_apply, sub_self]

@[fun_prop]
theorem hasFDerivAt_of_subsingleton [h : Subsingleton E] (f : E → F) (x : E) :
    HasFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [← hasFDerivWithinAt_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFDerivWithinAt_singleton f x

@[fun_prop]
theorem differentiableOn_singleton : DifferentiableOn 𝕜 f {x} :=
  forall_eq.2 (hasFDerivWithinAt_singleton f x).differentiableWithinAt

@[fun_prop]
theorem Set.Subsingleton.differentiableOn (hs : s.Subsingleton) : DifferentiableOn 𝕜 f s :=
  hs.induction_on differentiableOn_empty fun _ => differentiableOn_singleton

theorem hasFDerivAt_zero_of_eventually_const (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c) :
    HasFDerivAt f (0 : E →L[𝕜] F) x :=
  (hasFDerivAt_const _ _).congr_of_eventuallyEq hf

end Const

theorem differentiableWithinAt_of_isInvertible_fderivWithin
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) : DifferentiableWithinAt 𝕜 f s x := by
  contrapose hf
  rw [fderivWithin_zero_of_not_differentiableWithinAt hf]
  contrapose! hf
  rcases isInvertible_zero_iff.1 hf with ⟨hE, hF⟩
  exact (hasFDerivAt_of_subsingleton _ _).differentiableAt.differentiableWithinAt

theorem differentiableAt_of_isInvertible_fderiv
    (hf : (fderiv 𝕜 f x).IsInvertible) : DifferentiableAt 𝕜 f x := by
  simp only [← differentiableWithinAt_univ, ← fderivWithin_univ] at hf ⊢
  exact differentiableWithinAt_of_isInvertible_fderivWithin hf


/-! ### Support of derivatives -/

section Support

open Function

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}

theorem HasStrictFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) :
    HasStrictFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictFDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm

theorem HasFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) :
    HasFDerivAt f (0 : E →L[𝕜] F) x :=
  (HasStrictFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivAt

theorem HasFDerivWithinAt.of_notMem_tsupport {s : Set E} {x : E} (h : x ∉ tsupport f) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x :=
  (HasFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivWithinAt

theorem fderiv_of_notMem_tsupport (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0 :=
  (HasFDerivAt.of_notMem_tsupport 𝕜 h).fderiv

theorem support_fderiv_subset : support (fderiv 𝕜 f) ⊆ tsupport f := fun x ↦ by
  rw [← not_imp_not, notMem_support]
  exact fderiv_of_notMem_tsupport _

theorem tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) ⊆ tsupport f :=
  closure_minimal (support_fderiv_subset 𝕜) isClosed_closure

theorem tsupport_fderiv_apply_subset (v : E) : tsupport (fderiv 𝕜 f · v) ⊆ tsupport f :=
  (tsupport_comp_subset (g := fun L : E →L[𝕜] F ↦ L v) rfl _).trans (tsupport_fderiv_subset 𝕜)

protected theorem HasCompactSupport.fderiv (hf : HasCompactSupport f) :
    HasCompactSupport (fderiv 𝕜 f) :=
  hf.mono' <| support_fderiv_subset 𝕜

protected theorem HasCompactSupport.fderiv_apply (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (fderiv 𝕜 f · v) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset 𝕜 v)

end Support


end
