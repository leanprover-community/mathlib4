/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.LinearCombination

/-!
# Class Field Theory

This is WIP towards the formalism of foundations in Artin-Tate.

-/

open MulAction Pointwise Subgroup

section Tate

variable (G : Type*) [Group G] (A : Type*) [AddMonoid A] [DistribMulAction G A]

def tateComplex (G : Type*) [Group G] (A : Type*) [AddMonoid A] [DistribMulAction G A] :
    CochainComplex AddCommGrp ℤ where
  X := sorry
  d := sorry

instance (n : ℤ) : (tateComplex G A).HasHomology n := sorry

noncomputable def tateCohomology (n : ℤ) :=
  HomologicalComplex.homology (tateComplex G A) n

end Tate

variable {G : Type*} [Group G] (S : Set (Subgroup G))
  (A : Type*) [AddMonoid A] [DistribMulAction G A]

class PreFormation : Prop where
  finiteIndex : ∀ H ∈ S, FiniteIndex H
  mem_of_le : ∀ H ∈ S, ∀ K, H ≤ K → K ∈ S
  inf_mem : ∀ H ∈ S, ∀ K ∈ S, H ⊓ K ∈ S
  conj_mem : ∀ H ∈ S, ∀ g : ConjAct G, g • H ∈ S
  inter_trivial : ∀ g, (∀ H ∈ S, g ∈ H) → g = 1

-- needs profinite assumption
instance {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    PreFormation (Set.range ((↑) : OpenSubgroup G → Subgroup G)) where
  finiteIndex := by
    rintro - ⟨U, rfl⟩
    exact finiteIndex_of_finite_quotient U.toSubgroup
  mem_of_le := by
    rintro - ⟨U, rfl⟩ V h
    exact ⟨⟨V, isOpen_of_openSubgroup V h⟩, rfl⟩
  inf_mem := by
    rintro - ⟨U, rfl⟩ - ⟨V, rfl⟩
    exact ⟨U ⊓ V, rfl⟩
  conj_mem := by
    rintro - ⟨U, rfl⟩ g
    rw [Subgroup.pointwise_smul_def]
    refine ⟨U.comap ((MulDistribMulAction.toMonoidEnd (ConjAct G) G) g⁻¹) ?_, ?_⟩
    · change Continuous (g.ofConjAct⁻¹ * · * g.ofConjAct⁻¹⁻¹)
      fun_prop
    · symm; apply map_eq_comap_of_inverse <;> intro <;> simp
  inter_trivial := by
    -- needs a hard theorem
    sorry

namespace PreFormation

variable [PreFormation S]

def galoisGroup (H K : Subgroup G) := H ⧸ K.subgroupOf H

end PreFormation

class Formation : Prop extends PreFormation S where
  smooth : ∀ a : A, ∃ H ∈ S, a ∈ fixedPoints H A

namespace Formation



end Formation


/-
: Prop extends Algebra.IsAlgebraic F K where
  splits' (x : K) : Splits (algebraMap F K) (minpoly F x)
-/
