/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Finsupp.Interval
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-! # Linear topology on the ring of multivariate power series

- `MvPowerSeries.basis`: the ideals of the ring of multivariate power series
all coefficients the exponent of which is smaller than some bound vanish.

## Instances :

- `MvPowerSeries.linearTopology`.

TODO. For the moment, this is restricted to commutative rings because of the similar
restriction for linear topologies. However, the definition below is already correct
in the general case, the issue is solely about the definition of a linear topology.

-/
namespace MvPowerSeries

namespace LinearTopology

open scoped Topology

open Set SetLike

/-- The underlying family for the basis of ideals in a multivariate power series ring. -/
def basis (σ : Type*) (α : Type*) [Ring α] :
    (σ →₀ ℕ) → TwoSidedIdeal (MvPowerSeries σ α) := fun d ↦ by
  apply TwoSidedIdeal.mk' {f | ∀ e ≤ d, coeff α e f = 0}
  · simp [coeff_zero]
  · exact fun hf hg e he ↦ by rw [map_add, hf e he, hg e he, add_zero]
  · exact fun {f} hf e he ↦ by simp only [map_neg, neg_eq_zero, hf e he]
  · exact fun {f g} hg e he ↦ by
      classical
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.mul_zero (coeff α uv.fst f)
      exact hg  _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he)
  · exact fun {f g} hf e he ↦ by
      classical
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.zero_mul (coeff α uv.snd g)
      exact hf _ (le_trans (le_iff_exists_add.mpr ⟨uv.2, (Finset.mem_antidiagonal.mp huv).symm⟩) he)

variable {σ : Type*} {α : Type*} [Ring α]

/-- A power series `f` belongs to the ideal `basis σ α d` if and only if `coeff α e f = 0` for all
`e ≤ d`. -/
theorem mem_basis_iff {f : MvPowerSeries σ α} {d : σ →₀ ℕ} :
    f ∈ basis σ α d ↔ ∀ e ≤ d, coeff α e f = 0 := by
  simp [basis]

/-- If `e ≤ d`, then we have the inclusion of ideals `basis σ α d ≤ basis σ α e`. -/
theorem basis_le {e d : σ →₀ ℕ} (hed : e ≤ d) : basis σ α d ≤ basis σ α e :=
  fun _ => forall_imp (fun _ h ha => h (le_trans ha hed))

/-- `basis σ α d ≤ basis σ α e` if and only if `e ≤ d`. -/
theorem basis_le_iff [Nontrivial α] {d e : σ →₀ ℕ} :
    basis σ α d ≤ basis σ α e ↔ e ≤ d := by
  refine ⟨?_, basis_le⟩
  simp only [basis]
  intro h
  rw [← inf_eq_right]
  apply le_antisymm inf_le_right
  by_contra h'
  simp only [TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', setOf_subset_setOf] at h
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
theorem basis_antitone : Antitone (basis σ α) := fun _ _ h => basis_le h

/-- The function `basis σ α` is strictly antitone. -/
theorem basis_strict_anti [Nontrivial α] : StrictAnti (basis σ α) :=
  strictAnti_of_le_iff_le (fun _ _ ↦ basis_le_iff.symm)

variable (σ α) in
theorem ringSubgroupsBasis :
    RingSubgroupsBasis (fun d ↦ (basis σ α d).asIdeal.toAddSubgroup) where
  inter d e := ⟨d ⊔ e, basis_antitone.map_sup_le d e⟩
  mul d := ⟨d, fun f ↦ by
    simp only [Submodule.coe_toAddSubgroup, mem_mul]
    rintro ⟨x, hx, y, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul f d := ⟨d, fun g hg ↦ (basis σ α d).mul_mem_left f g hg⟩
  rightMul f d := ⟨d, fun g hg ↦ by
    intro e he
    simp only [Submodule.coe_toAddSubgroup, TwoSidedIdeal.coe_asIdeal,
      mem_coe, sub_zero, mem_basis_iff] at hg ⊢
    classical
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ h
    rw [hg i (le_trans ?_ he), zero_mul]
    simp only [← Finset.mem_antidiagonal.mp h, le_self_add]⟩

section DiscreteTopology

-- We endow MvPowerSeries σ α with the product topology.
open WithPiTopology

variable [TopologicalSpace α] [DiscreteTopology α]

/-- If the coefficient ring `α` is endowed with the discrete topology, then for every `d : σ →₀ ℕ`,
`↑(basis σ α d) ∈ 𝓝 (0 : MvPowerSeries σ α)`. -/
theorem basis_mem_nhds_zero (d : σ →₀ ℕ) :
    (basis σ α d : Set (MvPowerSeries σ α)) ∈ 𝓝 0 := by
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
    rw [mem_basis_iff]
    exact forall_imp (fun e h he => h he he)

lemma mem_nhds_zero_iff {U : Set (MvPowerSeries σ α)} :
    U ∈ 𝓝 0 ↔ ∃ d, {b | b ∈ basis σ α d} ⊆ U := by
  refine ⟨?_ , fun ⟨d, hd⟩ ↦ Filter.sets_of_superset _ (basis_mem_nhds_zero d) hd⟩
  · rw [nhds_pi, Filter.mem_pi]
    rintro ⟨D, hD, t, ht, ht'⟩
    use Finset.sup hD.toFinset id
    apply subset_trans _ ht'
    intros f hf e he
    simp only [← coeff_apply α f e,
      sub_zero f ▸ hf e (id_eq e ▸ Finset.le_sup (hD.mem_toFinset.mpr he))]
    exact mem_of_mem_nhds (ht e)

/-- If the coefficient ring `α` is endowed with the discrete topology, then the pointwise
topology on `MvPowerSeries σ α)` agrees with the topology generated by `MvPowerSeries.basis`. -/
theorem topology_eq_ideals_basis_topology :
    MvPowerSeries.WithPiTopology.instTopologicalSpace α =
      (ringSubgroupsBasis σ α).toRingFilterBasis.topology := by
  rw [TopologicalAddGroup.ext_iff inferInstance inferInstance]
  ext s
  simp [mem_nhds_zero_iff, ((ringSubgroupsBasis σ α).hasBasis_nhds 0).mem_iff]

/-- The topology on `MvPowerSeries` is a linear topology when the ring of coefficients has
the discrete topology. -/
instance : IsLinearTopology (MvPowerSeries σ α) :=
  IsLinearTopology.mk_of_twoSidedIdeal (p := fun _ ↦ True) (s := fun d ↦ basis σ α d)
    (Filter.HasBasis.mk fun s ↦ by simp [mem_nhds_zero_iff])

end DiscreteTopology

end LinearTopology

end MvPowerSeries
