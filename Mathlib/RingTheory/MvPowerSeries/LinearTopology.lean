/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernandez
-/

import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Data.Finsupp.Interval

/-! # Linear topology on the ring of multivariate power series

- `MvPowerSeries.basis`: the ideals of the ring of multivariate power series
all coefficients the exponent of which is smaller than some bound vanish.

- `MvPowerSeries.idealIsBasis`: it defines an `Ideal.IsBasis`

## Instances :

- `MvPowerSeries.linearTopology`

-/
namespace MvPowerSeries

open Set SetLike

variable (σ : Type*) (α : Type*) [Ring α]

section Ideal.IsBasis

/-- The underlying family for the `Ideal.IsBasis` in a multivariate power series ring. -/
def basis : (σ →₀ ℕ) → Ideal (MvPowerSeries σ α) := fun d =>
  { carrier   := {f | ∀ e ≤ d, coeff α e f = 0} -- monomial e 1 ∣ f
    zero_mem' := fun e _ => by rw [coeff_zero]
    add_mem'  := fun hf hg e he => by
      rw [map_add, hf e he, hg e he, add_zero]
    smul_mem' := fun f g hg e he => by
      classical
      rw [smul_eq_mul, coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.mul_zero (coeff α uv.fst f)
      exact hg  _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he) }

/-- A power series `f` belongs to the ideal `basis σ α d` if and only if `coeff α e f = 0` for all
  `e ≤ d`.  -/
theorem mem_basis (f : MvPowerSeries σ α) (d : σ →₀ ℕ) :
    f ∈ basis σ α d ↔ ∀ e ≤ d, coeff α e f = 0 := by
  simp only [basis, Submodule.mem_mk, AddSubmonoid.mem_mk, Set.mem_setOf_eq]
  rfl

/-- If `e ≤ d`, then we have the inclusion of ideals `basis σ α d ≤ basis σ α e`. -/
theorem basis_le {e d : σ →₀ ℕ} (hed : e ≤ d) : basis σ α d ≤ basis σ α e :=
  fun _ => forall_imp (fun _ h ha => h (le_trans ha hed))

/-- `basis σ α d ≤ basis σ α e` if and only if `e ≤ d`.-/
theorem basis_le_iff [Nontrivial α] {d e : σ →₀ ℕ} :
    basis σ α d ≤ basis σ α e ↔ e ≤ d := by
  refine ⟨?_, basis_le _ _⟩
  simp only [basis, Submodule.mk_le_mk, AddSubmonoid.mk_le_mk, setOf_subset_setOf]
  intro h
  rw [← inf_eq_right]
  apply le_antisymm inf_le_right
  by_contra h'
  simp only [AddSubsemigroup.mk_le_mk, setOf_subset_setOf] at h
  specialize h (monomial α e 1) _
  · intro e' he'
    apply coeff_monomial_ne
    intro hee'
    rw [hee'] at he'
    apply h'
    exact le_inf_iff.mpr ⟨he', le_rfl⟩
  · apply one_ne_zero' α
    convert h e le_rfl
    rw [coeff_monomial_same]

/-- The function `basis σ α` is antitone. -/
theorem basis_antitone : Antitone (basis σ α) := fun _ _ h => basis_le σ α h

/-- `MvPowerSeries.basis` is an `Ideal.IsBasis`. -/
theorem idealIsBasis : Ideal.IsBasis (basis σ α) where
  nonempty := inferInstance
  inter := fun d e ↦ ⟨d ⊔ e, Antitone.map_sup_le (basis_antitone σ α) d e ⟩
  mul_right := fun d f g ↦ by
    simp only [mem_basis]
    intro hf e he
    -- TODO : probably can be simplified using MvPowerSeries.order
    classical
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ h
    rw [hf i (le_trans ?_ he), zero_mul]
    simp only [← Finset.mem_antidiagonal.mp h, le_self_add]

/-- `MvPowerSeries.basis` is a `RingSubgroupsBasis`. -/
theorem ringSubgroupsBasis : RingSubgroupsBasis fun d => (basis σ α d).toAddSubgroup :=
  (idealIsBasis σ α).toRingSubgroupsBasis

end Ideal.IsBasis

section DiscreteTopology

-- We endow MvPowerSeries σ α with the product topology
open WithPiTopology

variable [TopologicalSpace α] [DiscreteTopology α]

/-- If the coefficient ring `α` is endowed with the discrete topology, then for every `d : σ →₀ ℕ`,
  `↑(basis σ α d) ∈ nhds (0 : MvPowerSeries σ α)`. -/
theorem basis_mem_nhds_zero (d : σ →₀ ℕ) :
    ↑(basis σ α d) ∈ nhds (0 : MvPowerSeries σ α) := by
  classical
  rw [nhds_pi, Filter.mem_pi]
  use Finset.Iic d, Finset.finite_toSet _, (fun e => if e ≤ d then {0} else univ)
  constructor
  · intro e
    split_ifs
    · simp only [nhds_discrete, Filter.mem_pure, mem_singleton_iff]
      rfl
    · simp only [Filter.univ_mem]
  · intro f
    simp only [Finset.coe_Iic, mem_pi, mem_Iic, mem_ite_univ_right, mem_singleton_iff, mem_coe]
    exact forall_imp (fun e h he => h he he)

lemma mem_nhds_zero_iff {U : Set (MvPowerSeries σ α)} :
    U ∈ nhds 0 ↔ ∃ d, {b | b ∈ basis σ α d} ⊆ U := by
  constructor
  · rw [nhds_pi, Filter.mem_pi]
    rintro ⟨D, hD, t, ht, ht'⟩
    use Finset.sup hD.toFinset id
    apply subset_trans _ ht'
    intros f hf e he
    rw [apply_eq_coeff f e, hf e]
    · exact mem_of_mem_nhds (ht e)
    · rw [← id_eq e]
      exact Finset.le_sup ((Set.Finite.mem_toFinset _).mpr he)
  · rintro ⟨d, hd⟩
    exact Filter.sets_of_superset _ (basis_mem_nhds_zero σ α d) hd

/-- If the coefficient ring `α` is endowed with the discrete topology, then the pointwise
  topology on `MvPowerSeries σ α)` agrees with the topology generated by `MvPowerSeries.basis`. -/
theorem topology_eq_ideals_basis_topology :
    MvPowerSeries.WithPiTopology.instTopologicalSpace α = (idealIsBasis σ α).topology := by
  rw [TopologicalAddGroup.ext_iff inferInstance inferInstance]
  ext s
  rw [mem_nhds_zero_iff, ((ringSubgroupsBasis σ α).hasBasis_nhds  0).mem_iff]
  simp only [sub_zero, Submodule.mem_toAddSubgroup, true_and]

/-- The topology on `MvPowerSeries` is a linear topology
  when the ring of coefficients has the discrete topology. -/
instance : LinearTopology (MvPowerSeries σ α) := {
  Ideal.IsBasis.toIdealBasis (idealIsBasis _ _) with
  isTopology := by
    rw [Ideal.IsBasis.ofIdealBasis_topology_eq]
    exact topology_eq_ideals_basis_topology σ α }

end DiscreteTopology

end MvPowerSeries
