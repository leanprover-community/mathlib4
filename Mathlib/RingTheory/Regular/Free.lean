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

@[expose] public section

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing

private instance finite_QuotSMulTop (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  Module.Finite.of_restrictScalars_finite R _ _

open Pointwise in
lemma LinearMap.ker_mapRange_eq_smul_top (I : Type*) [Finite I] (x : R) :
    LinearMap.ker (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x}))) =
    x • (⊤ : Submodule R (I →₀ R)) := by
  ext y
  simp only [Finsupp.ker_mapRange, Submodule.ker_mkQ, Finsupp.mem_submodule_iff]
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · let : Fintype I := Fintype.ofFinite I
    simp only [Ideal.mem_span_singleton', mul_comm] at h
    rw [← Finsupp.univ_sum_single y]
    refine Submodule.sum_mem _ (fun i _ ↦ ?_)
    rcases h i with ⟨z, hz⟩
    simpa only [← hz, ← Finsupp.smul_single'] using
      Submodule.smul_mem_pointwise_smul (Finsupp.single i z) x ⊤ trivial
  · rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨z, _, eq⟩
    simpa [← eq] using
      Ideal.IsTwoSided.mul_mem_of_left (z i) (Ideal.mem_span_singleton_self x)

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
      simpa only [LinearEquiv.ker_comp, f] using LinearMap.ker_mapRange_eq_smul_top R I x
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
  · let I := Module.Free.ChooseBasisIndex R M
    let fin : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
    have : Module.Finite R (I →₀ R) := by simp [Fintype.finite fin]
    let b := Module.Free.chooseBasis R M
    let f : M →ₗ[R] I →₀ (R ⧸ Ideal.span {x}) :=
      (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x}))).comp b.1.toLinearMap
    have surjf : Function.Surjective f := by
      simpa [f] using Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective _)
    have kerf : LinearMap.ker f = x • (⊤ : Submodule R M) := by
      simp only [f, LinearMap.ker_comp, LinearMap.ker_mapRange_eq_smul_top R I x,
        Submodule.map_top, Submodule.comap_equiv_eq_map_symm, Submodule.map_pointwise_smul,
        LinearMap.range_eq_top.mpr b.repr.symm.surjective]
    let e' := (Submodule.quotEquivOfEq _ _ kerf.symm).trans
      (LinearMap.quotKerEquivOfSurjective f surjf)
    let e : QuotSMulTop x M ≃ₗ[R ⧸ Ideal.span {x}] I →₀ R ⧸ Ideal.span {x} :=
      e'.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
    exact Module.Free.of_equiv e.symm
