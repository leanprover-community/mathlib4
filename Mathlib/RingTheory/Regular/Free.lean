/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop

/-!

# Freeness of QuotSMulTop by regular element

For finitely generated module `M` over Noetherian local ring `(R, m)`, if `x ∈ m` is `M`-regular,
`M/xM` is free over `R/(x)` iff `M` is free over `R`.

## Main Results

* `free_iff_quotSMulTop_free` : If `x ∈ m` is `M`-regular,
  `M/xM` is free over `R/(x)` iff `M` is free over `R`.

-/

public section

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing

private instance finite_QuotSMulTop (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  Module.Finite.of_restrictScalars_finite R _ _

lemma LinearMap.ker_mapRange_mkQ_eq_smul_top (ι : Type*) (I : Ideal R) :
    LinearMap.ker (Finsupp.mapRange.linearMap I.mkQ) = I • (⊤ : Submodule R (ι →₀ R)) := by
  ext y
  simp only [Finsupp.ker_mapRange, Submodule.ker_mkQ, Finsupp.mem_submodule_iff]
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · rw [← Finsupp.sum_single y]
    refine Submodule.sum_mem _ (fun i _ ↦ ?_)
    rw [← mul_one (y i), ← smul_eq_mul _ 1, ← Finsupp.smul_single]
    exact Submodule.smul_mem_smul (h i) trivial
  · induction h using Submodule.smul_induction_on' with
    | smul r hr m _ => simpa using I.mul_mem_right (m i) hr
    | add x _ y _ xmem ymem => simpa using add_mem xmem ymem

open Pointwise in
lemma free_iff_quotSMulTop_free [IsLocalRing R] [IsNoetherianRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] {x : R} (mem : x ∈ maximalIdeal R) (reg : IsSMulRegular M x) :
    Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Module.Free R M := by
  refine ⟨fun free ↦ ?_, fun free ↦ ?_⟩
  · let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
    let fin : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
    have : Module.Finite R (I →₀ R) := by simp [Fintype.finite fin]
    let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
    let b' : QuotSMulTop x M ≃ₗ[R] I →₀ R ⧸ Ideal.span {x} := b.1.restrictScalars R
    let f := b'.symm.toLinearMap.comp (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x})))
    rcases Module.projective_lifting_property (Submodule.mkQ (x • (⊤ : Submodule R M))) f
      (Submodule.mkQ_surjective _) with ⟨g, hg⟩
    have surjf : Function.Surjective f := by
      simpa [f] using Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective (Ideal.span {x}))
    have lejac : Ideal.span {x} ≤ (⊥ :Ideal R).jacobson :=
      ((Ideal.span_singleton_le_iff_mem _).mpr mem).trans (maximalIdeal_le_jacobson _)
    have surjg : Function.Surjective g := by
      rw [← LinearMap.range_eq_top, ← top_le_iff]
      apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) lejac
      rw [top_le_iff, sup_comm, ← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp,
        Submodule.ideal_span_singleton_smul x ⊤, hg]
      exact LinearMap.range_eq_top_of_surjective f surjf
    have kerf : LinearMap.ker f = x • (⊤ : Submodule R (I →₀ R)) := by
      simp [f, LinearMap.ker_mapRange_mkQ_eq_smul_top, Submodule.ideal_span_singleton_smul]
    have injg : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot]
      have fg : (LinearMap.ker g).FG := IsNoetherian.noetherian (LinearMap.ker g)
      apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _ fg _ lejac
      rw [Submodule.ideal_span_singleton_smul]
      intro y hy
      have : y ∈ x • (⊤ : Submodule R (I →₀ R)) := by simp [← kerf, ← hg, LinearMap.mem_ker.mp hy]
      rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp this with ⟨z, _, hz⟩
      simp only [← hz, LinearMap.mem_ker, map_smul] at hy
      have := LinearMap.mem_ker.mpr (IsSMulRegular.right_eq_zero_of_smul reg hy)
      simpa [hz] using Submodule.smul_mem_pointwise_smul z x _ this
    exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨injg, surjg⟩)
  · exact Module.Free.of_equiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective).symm
