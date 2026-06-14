/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Jon Bannon
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Exactness of sequences

In this file we provide some API for handling exact sequences.

## Main definitions / results:

* `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`: the Euler characteristic of a finite exact
  sequence is zero.

## TODO

Write a simproc to generate unrolled, universe-polymorphic versions of
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact` on the fly and so obviate the need for
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six`.

-/

universe u₀ u₁ u₂ u₃ u₄ u₅

namespace Module

open Function

variable {k : Type*} [DivisionRing k]

/-- The Euler characteristic of a finite exact sequence is zero. -/
public lemma sum_neg_one_pow_finrank_eq_zero_of_exact {n : ℕ} (V : Fin (n + 2) → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (f : (i : Fin (n + 1)) → V i.castSucc →ₗ[k] V i.succ)
    (inj : Injective (f 0))
    (h_exact : ∀ i : Fin n, Exact (f i.castSucc) (f i.succ))
    (surj : Surjective (f (Fin.last _))) :
    ∑ i, (-1) ^ i.val * (finrank k (V i) : ℤ) = 0 := by
  replace inj := LinearMap.finrank_range_of_inj inj
  replace surj := LinearMap.range_eq_top.mpr surj
  simp_rw [← smul_eq_mul]
  refine Fin.sum_neg_one_pow_eq_zero _ (fun i ↦ finrank k (f i).range) ?_ (fun i ↦ ?_) ?_
  · aesop
  · #adaptation_note /-- Prior to v4.31.0-rc1, this proof was
      ```
      grind [(h_exact i).linearMap_ker_eq, (f i.succ).finrank_range_add_finrank_ker]
      ```
      -/
    have hrn := (f i.succ).finrank_range_add_finrank_ker
    have hker : finrank k ↥(LinearMap.ker (f i.succ)) =
        finrank k ↥(LinearMap.range (f i.castSucc)) :=
      congrArg (fun S : Submodule k (V i.succ.castSucc) => finrank k ↥S)
        (h_exact i).linearMap_ker_eq
    omega
  · #adaptation_note /-- Prior to v4.31.0-rc1, this proof was
      ```
      grind [finrank_top]
      ```
      -/
    rw [surj, finrank_top, Fin.succ_last]

/- An unrolled version of `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`. This is an auxiliary
lemma en route to `Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six`. -/
private lemma sum_neg_one_pow_finrank_eq_zero_of_exact_six_aux {V₀ V₁ V₂ V₃ V₄ V₅ : Type u₀}
    [AddCommGroup V₀] [Module k V₀] [FiniteDimensional k V₀]
    [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
    [AddCommGroup V₄] [Module k V₄] [FiniteDimensional k V₄]
    [AddCommGroup V₅] [Module k V₅] [FiniteDimensional k V₅]
    (f₀ : V₀ →ₗ[k] V₁) (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj : Injective f₀)
    (exact₁ : Exact f₀ f₁)
    (exact₂ : Exact f₁ f₂)
    (exact₃ : Exact f₂ f₃)
    (exact₄ : Exact f₃ f₄)
    (surj : Surjective f₄) :
    (finrank k V₀ : ℤ) - finrank k V₁ + finrank k V₂ -
      finrank k V₃ + finrank k V₄ - finrank k V₅ = 0 := by
  letI Vs := ![V₀, V₁, V₂, V₃, V₄, V₅]
  letI (i : Fin 6) : AddCommGroup (Vs i) := match i with
  | 0 => ‹_› | 1 => ‹_› | 2 => ‹_› | 3 => ‹_› | 4 => ‹_› | 5 => ‹_›
  letI (i : Fin 6) : Module k (Vs i) := match i with
  | 0 => ‹_› | 1 => ‹_› | 2 => ‹_› | 3 => ‹_› | 4 => ‹_› | 5 => ‹_›
  have (i : Fin 6) : FiniteDimensional k (Vs i) := match i with
  | 0 => ‹_› | 1 => ‹_› | 2 => ‹_› | 3 => ‹_› | 4 => ‹_› | 5 => ‹_›
  letI fs (i : Fin 5) : Vs i.castSucc →ₗ[k] Vs i.succ := match i with
  | 0 => f₀ | 1 => f₁ | 2 => f₂ | 3 => f₃ | 4 => f₄
  simpa [Fin.sum_univ_six] using! Module.sum_neg_one_pow_finrank_eq_zero_of_exact Vs fs inj
    (fun i ↦ by fin_cases i; exacts [exact₁, exact₂, exact₃, exact₄]) surj

/-- This is an unrolled, universe-polymorphic version of
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact`. This special case exists because of the role that
this lemma plays in the proof of `LinearMap.index_comp`.

In theory one could write a `simproc` which conjured up this lemma for a sequence of any length and
then one would not need to have this special-case lemma at all. -/
public lemma sum_neg_one_pow_finrank_eq_zero_of_exact_six
    {V₀ : Type u₀} [AddCommGroup V₀] [Module k V₀] [FiniteDimensional k V₀]
    {V₁ : Type u₁} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    {V₂ : Type u₂} [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    {V₃ : Type u₃} [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
    {V₄ : Type u₄} [AddCommGroup V₄] [Module k V₄] [FiniteDimensional k V₄]
    {V₅ : Type u₅} [AddCommGroup V₅] [Module k V₅] [FiniteDimensional k V₅]
    (f₀ : V₀ →ₗ[k] V₁) (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj : Injective f₀)
    (exact₁ : Exact f₀ f₁)
    (exact₂ : Exact f₁ f₂)
    (exact₃ : Exact f₂ f₃)
    (exact₄ : Exact f₃ f₄)
    (surj : Surjective f₄) :
    (finrank k V₀ : ℤ) - finrank k V₁ + finrank k V₂ -
      finrank k V₃ + finrank k V₄ - finrank k V₅ = 0 := by
  let W₀ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₀
  let W₁ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₁
  let W₂ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₂
  let W₃ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₃
  let W₄ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₄
  let W₅ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₅
  let g₀ : W₀ →ₗ[k] W₁ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₀ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₁ : W₁ →ₗ[k] W₂ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₁ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₂ : W₂ →ₗ[k] W₃ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₂ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₃ : W₃ →ₗ[k] W₄ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₃ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₄ : W₄ →ₗ[k] W₅ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₄ ∘ₗ ULift.moduleEquiv.toLinearMap
  have := sum_neg_one_pow_finrank_eq_zero_of_exact_six_aux g₀ g₁ g₂ g₃ g₄
    (inj := by simpa [g₀]) (surj := by simpa [g₄])
  simp only [W₀, W₁, W₂, W₃, W₄, W₅, finrank_ulift] at this
  apply this <;>
  simpa only [g₀, g₁, g₂, g₃, g₄, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact, LinearEquiv.precomp_exact_iff_exact]

end Module
