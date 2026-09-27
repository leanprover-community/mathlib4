/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.NormNum

/-!

# Base change for linear independence

This file is a place to collect base change results for linear independence.

-/

public section

open Function Set TensorProduct

variable {ι ι' : Type*} [Finite ι']

/-- This is an auxiliary lemma dominated by `linearIndependent_algebraMap_comp_iff`. -/
private lemma LinearIndependent.linearIndependent_algebraMap_comp_aux {K : Type*} (L : Type*)
    [Field K] [Field L] [Algebra K L]
    {v : ι → ι' → K} (hv : LinearIndependent K v) :
    LinearIndependent L (fun i ↦ algebraMap K L ∘ v i) := by
  classical
  let : Fintype ι' := .ofFinite ι'
  let I : Set (ι' → K) := hv.linearIndepOn_id.extend (subset_univ _)
  let b : Module.Basis I K (ι' → K) := .extend hv.linearIndepOn_id
  let b' : Module.Basis I L (ι' → L) := (b.baseChange L).map (TensorProduct.piScalarRight K L L ι')
  let v' (i : ι) : I := ⟨v i, hv.linearIndepOn_id.subset_extend _ <| mem_range_self i⟩
  have hv' : b' ∘ v' = fun i ↦ algebraMap K L ∘ v i := by
    ext; simp [b', b, v', Module.Basis.extend, Algebra.algebraMap_eq_smul_one]
  have h_inj : Injective v' := fun i j hij ↦ by have : Injective v := hv.injective; aesop
  rw [← hv']
  exact b'.linearIndependent.comp _ h_inj

@[simp] lemma linearIndependent_algebraMap_comp_iff {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S] [IsDomain S]
    {v : ι → ι' → R} :
    LinearIndependent S (fun i ↦ algebraMap R S ∘ v i) ↔ LinearIndependent R v := by
  change LinearIndependent S (Pi.algebraMap ι' R S ∘ v) ↔ LinearIndependent R v
  refine ⟨fun h ↦ (h.restrict_scalars' R).of_comp, fun h ↦ ?_⟩
  have : IsDomain R := .of_faithfulSMul R S
  set K := FractionRing R
  set L := FractionRing S
  replace h : LinearIndependent K (Pi.algebraMap ι' R K ∘ v) := by
    rw [← LinearIndependent.iff_fractionRing (R := R)]
    have : Function.Injective (Pi.algebraMap ι' R K) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv; ext i; simpa [Pi.algebraMap] using congr($hv i)
    rwa [LinearMap.linearIndependent_iff_of_injOn _ this.injOn]
  let : Algebra K L := FractionRing.liftAlgebra R L
  suffices LinearIndependent L (Pi.algebraMap ι' R L ∘ v) by
    rw [← LinearIndependent.iff_fractionRing (R := S)] at this
    have aux : Pi.algebraMap ι' R L ∘ v = Pi.algebraMap ι' S L ∘ Pi.algebraMap ι' R S ∘ v := by
      ext; simp [Pi.algebraMap, ← IsScalarTower.algebraMap_apply]
    rw [aux] at this
    exact this.of_comp
  have aux : Pi.algebraMap ι' R L ∘ v = Pi.algebraMap ι' K L ∘ Pi.algebraMap ι' R K ∘ v := by
    ext; simp [Pi.algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [aux]
  replace h := h.linearIndependent_algebraMap_comp_aux L
  exact h
