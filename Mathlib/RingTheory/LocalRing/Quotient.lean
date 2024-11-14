/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/

import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Nakayama

/-!

We gather results about the quotients of local rings.

-/

open Submodule FiniteDimensional Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Module.Finite R S]

namespace IsLocalRing

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) p

theorem quotient_span_eq_top_iff_span_eq_top (s : Set S) :
    span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s) = ⊤ ↔ span R s = ⊤ := by
  have H : (span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
      (span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS)) := by
    rw [map_span, ← restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective,
      IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq]
  constructor
  · intro hs
    rw [← top_le_iff]
    apply le_of_le_smul_of_le_jacobson_bot
    · exact Module.finite_def.mp ‹_›
    · exact (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [Ideal.smul_top_eq_map]
      rintro x -
      have : LinearMap.ker (IsScalarTower.toAlgHom R S (S ⧸ pS)) =
          restrictScalars R pS := by
        ext; simp [Ideal.Quotient.eq_zero_iff_mem]
      rw [← this, ← comap_map_eq, mem_comap, ← H, hs, restrictScalars_top]
      exact mem_top
  · intro hs
    rwa [hs, Submodule.map_top, LinearMap.range_eq_top.mpr,
      restrictScalars_eq_top_iff] at H
    rw [IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective

attribute [local instance] Ideal.Quotient.field

variable [Module.Free R S] {ι : Type*}

theorem finrank_quotient_map :
    finrank (R ⧸ p) (S ⧸ pS) = finrank R S := by
  classical
  have : Module.Finite R (S ⧸ pS) := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom R S (S ⧸ pS)).toLinearMap (Ideal.Quotient.mk_surjective (I := pS))
  have : Module.Finite (R ⧸ p) (S ⧸ pS) := Module.Finite.of_restrictScalars_finite R _ _
  apply le_antisymm
  · let b := Module.Free.chooseBasis R S
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top
    rw [Set.range_comp]
    apply (quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq
  · let b := Module.Free.chooseBasis (R ⧸ p) (S ⧸ pS)
    choose b' hb' using fun i ↦ Ideal.Quotient.mk_surjective (b i)
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    refine finrank_le_of_span_eq_top (v := b') ?_
    apply (quotient_span_eq_top_iff_span_eq_top _).mp
    rw [← Set.range_comp, show Ideal.Quotient.mk pS ∘ b' = ⇑b from funext hb']
    exact b.span_eq

/-- Given a basis of `S`, the induced basis of `S / Ideal.map (algebraMap R S) p`. -/
noncomputable
def basisQuotient [Fintype ι] (b : Basis ι R S) : Basis ι (R ⧸ p) (S ⧸ pS) :=
  basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk pS ∘ b)
    (by
      rw [Set.range_comp]
      exact ((quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq).ge)
    (by rw [finrank_quotient_map, finrank_eq_card_basis b])

lemma basisQuotient_apply [Fintype ι] (b : Basis ι R S) (i) :
    (basisQuotient b) i = Ideal.Quotient.mk pS (b i) := by
  delta basisQuotient
  rw [coe_basisOfTopLeSpanOfCardEqFinrank, Function.comp_apply]

lemma basisQuotient_repr {ι} [Fintype ι] (b : Basis ι R S) (x) (i) :
    (basisQuotient b).repr (Ideal.Quotient.mk pS x) i =
    Ideal.Quotient.mk p (b.repr x i) := by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (basisQuotient b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply _ (R ⧸ p),
    Fintype.linearCombination_apply]
  simp only [Function.comp_apply, basisQuotient_apply,
    Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum, Basis.sum_repr b x]

end IsLocalRing

@[deprecated (since := "2024-11-11")]
alias LocalRing.quotient_span_eq_top_iff_span_eq_top :=
  IsLocalRing.quotient_span_eq_top_iff_span_eq_top

@[deprecated (since := "2024-11-11")]
alias LocalRing.finrank_quotient_map := IsLocalRing.finrank_quotient_map

@[deprecated (since := "2024-11-11")]
alias LocalRing.basisQuotient := IsLocalRing.basisQuotient

@[deprecated (since := "2024-11-11")]
alias LocalRing.basisQuotient_apply := IsLocalRing.basisQuotient_apply

@[deprecated (since := "2024-11-11")]
alias LocalRing.basisQuotient_repr := IsLocalRing.basisQuotient_repr
