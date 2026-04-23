/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Metrizable.Basic

/-!
# Fréchet derivative of constant functions

This file contains the usual formulas (and existence assertions) for the derivative of constant
functions, including various special cases such as the functions `0`, `1`, `Nat.cast n`,
`Int.cast z`, and other numerals.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Asymptotics Function Filter Set Metric
open scoped Topology NNReal ENNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f : E → F} {x : E} {s : Set E}

section Const

theorem hasFDerivAtFilter_const (c : F) (L : Filter (E × E)) :
    HasFDerivAtFilter (fun _ => c) (0 : E →L[𝕜] F) L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun _ => by simp

theorem hasFDerivAtFilter_zero (L : Filter (E × E)) :
    HasFDerivAtFilter (0 : E → F) (0 : E →L[𝕜] F) L := hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_one [One F] (L : Filter (E × E)) :
    HasFDerivAtFilter (1 : E → F) (0 : E →L[𝕜] F) L := hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_natCast [NatCast F] (n : ℕ) (L : Filter (E × E)) :
    HasFDerivAtFilter (n : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_intCast [IntCast F] (z : ℤ) (L : Filter (E × E)) :
    HasFDerivAtFilter (z : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_ofNat (n : ℕ) [OfNat F n] (L : Filter (E × E)) :
    HasFDerivAtFilter (ofNat(n) : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
theorem hasStrictFDerivAt_const (c : F) (x : E) :
    HasStrictFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  hasFDerivAtFilter_const _ _

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

@[fun_prop]
theorem hasFDerivWithinAt_const (c : F) (x : E) (s : Set E) :
    HasFDerivWithinAt (fun _ => c) (0 : E →L[𝕜] F) s x :=
  hasFDerivAtFilter_const _ _

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
  hasFDerivAtFilter_const _ _

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

theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun _ => c) x = 0 := by
  rw [fderiv, fderivWithin_const_apply]

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
  refine .of_not_accPt ?_
  rw [accPt_iff_clusterPt, inf_principal]
  simp [ClusterPt]

@[fun_prop, nontriviality]
theorem hasFDerivWithinAt_of_subsingleton [h : Subsingleton E] (f : E → F) (s : Set E) (x : E) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x := by
  obtain rfl | ⟨a, rfl⟩ := s.eq_empty_or_singleton_of_subsingleton
  · simp
  · exact HasFDerivWithinAt.singleton

@[fun_prop, nontriviality]
theorem hasFDerivAt_of_subsingleton [h : Subsingleton E] (f : E → F) (x : E) :
    HasFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [← hasFDerivWithinAt_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFDerivWithinAt_singleton f x

@[nontriviality]
theorem differentiable_of_subsingleton [Subsingleton E] {f : E → F} : Differentiable 𝕜 f :=
  fun x ↦ (hasFDerivAt_of_subsingleton f x (𝕜 := 𝕜)).differentiableAt

@[nontriviality]
theorem differentiableWithinAt_of_subsingleton [Subsingleton E] :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiable_of_subsingleton x).differentiableWithinAt

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

/-- If `f : E → F` has injective differential within `s` at `x`,
it is differentiable within `s` at `x`. -/
lemma differentiableWithinAt_of_fderivWithin_injective (hf : Injective (fderivWithin 𝕜 f s x)) :
    DifferentiableWithinAt 𝕜 f s x := by
  nontriviality E
  contrapose hf
  rw [fderivWithin_zero_of_not_differentiableWithinAt hf]
  exact not_injective_const

/-- If `f : E → F` has injective differential at `x`, it is differentiable at `x`. -/
lemma differentiableAt_of_fderiv_injective (hf : Injective (fderiv 𝕜 f x)) :
    DifferentiableAt 𝕜 f x := by
  simp only [← differentiableWithinAt_univ, ← fderivWithin_univ] at hf ⊢
  exact differentiableWithinAt_of_fderivWithin_injective hf

theorem differentiableWithinAt_of_isInvertible_fderivWithin
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) : DifferentiableWithinAt 𝕜 f s x :=
  differentiableWithinAt_of_fderivWithin_injective hf.injective

theorem differentiableAt_of_isInvertible_fderiv
    (hf : (fderiv 𝕜 f x).IsInvertible) : DifferentiableAt 𝕜 f x :=
  differentiableAt_of_fderiv_injective hf.injective

/-! ### Support of derivatives -/

section Support
variable (𝕜)

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

theorem fderiv_of_notMem_tsupport (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.fderiv_eq]

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
