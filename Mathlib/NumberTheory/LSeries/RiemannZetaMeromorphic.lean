/-
Copyright (c) 2026 Chenguang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenguang
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic.FunProp

/-!
# Meromorphic continuation of the Riemann and Hurwitz zeta functions

We show that `riemannZeta` and `hurwitzZetaEven a` are meromorphic on `ℂ`, the only possible
pole being at `s = 1`. The proof is the same in both cases: if `g` denotes the value at `1` of
`s ↦ (s - 1) * f s` extended by its limit, then `g` is analytic (it is continuous at `1` and
differentiable away from `1`) and `s ↦ g s / (s - 1)` agrees with `f` away from `1`.
-/

open Topology HurwitzZeta

public theorem meromorphicAt_riemannZeta_one : MeromorphicAt riemannZeta 1 := by
  let g := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  suffices MeromorphicAt (fun s => g s / (s - 1)) 1 by
    apply this.congr
    exact eventually_nhdsWithin_of_forall fun x h => (by grind)
  refine MeromorphicAt.fun_div ?_ (by fun_prop)
  apply AnalyticAt.meromorphicAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · apply eventually_nhdsWithin_of_forall fun x h => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h
    suffices DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s) x by
      apply this.congr_of_eventuallyEq
      rw [Filter.EventuallyEq, eventually_nhds_iff]
      use {1}ᶜ
      simp +contextual [g, h]
    apply DifferentiableAt.mul (by fun_prop)
    apply differentiableAt_riemannZeta h
  · rw [continuousAt_iff_punctured_nhds]
    simp only [Function.update_self, g]
    apply riemannZeta_residue_one.congr'
    exact eventually_nhdsWithin_of_forall fun x h => (by grind)

public theorem meromorphicAt_hurwitzZetaEven_one (a : UnitAddCircle) :
    MeromorphicAt (hurwitzZetaEven a) 1 := by
  let g := Function.update (fun s => (s - 1) * hurwitzZetaEven a s) 1 1
  suffices MeromorphicAt (fun s => g s / (s - 1)) 1 by
    apply this.congr
    exact eventually_nhdsWithin_of_forall fun x h => (by grind)
  refine MeromorphicAt.fun_div ?_ (by fun_prop)
  apply AnalyticAt.meromorphicAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · apply eventually_nhdsWithin_of_forall fun x h => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h
    suffices DifferentiableAt ℂ (fun s => (s - 1) * hurwitzZetaEven a s) x by
      apply this.congr_of_eventuallyEq
      rw [Filter.EventuallyEq, eventually_nhds_iff]
      use {1}ᶜ
      simp +contextual [g, h]
    apply DifferentiableAt.mul (by fun_prop)
    exact differentiableAt_hurwitzZetaEven a h
  · rw [continuousAt_iff_punctured_nhds]
    simp only [Function.update_self, g]
    apply (hurwitzZetaEven_residue_one a).congr'
    exact eventually_nhdsWithin_of_forall fun x h => (by grind)

public theorem meromorphic_riemannZeta : Meromorphic riemannZeta := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact meromorphicAt_riemannZeta_one
  · have hdiff : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact ((hdiff.analyticOn isOpen_compl_singleton).analyticAt
      (isOpen_compl_singleton.mem_nhds hs)).meromorphicAt

public theorem meromorphic_hurwitzZetaEven (a : UnitAddCircle) :
    Meromorphic (hurwitzZetaEven a) := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact meromorphicAt_hurwitzZetaEven_one a
  · have hdiff : DifferentiableOn ℂ (hurwitzZetaEven a) {1}ᶜ :=
      fun z hz => (differentiableAt_hurwitzZetaEven a hz).differentiableWithinAt
    exact ((hdiff.analyticOn isOpen_compl_singleton).analyticAt
      (isOpen_compl_singleton.mem_nhds hs)).meromorphicAt
