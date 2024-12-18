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

- `MvPowerSeries.idealIsBasis`: it defines an `Ideal.IsBasis`.

## Instances :

- `MvPowerSeries.linearTopology`.

TODO. For the moment, this is restricted to commutative rings because of the similar
restriction for linear topologies. However, the definition below is already correct
in the general case, the issue is solely about the definition of a linear topology.

-/
namespace MvPowerSeries

open scoped Topology

open Set SetLike

variable (σ : Type*) (α : Type*) [Ring α]

section Ideal.IsBasis

/-- The underlying family for the `Ideal.IsBasis` in a multivariate power series ring. -/
def basis : (σ →₀ ℕ) → Ideal (MvPowerSeries σ α) := fun d =>
  { carrier   := {f | ∀ e ≤ d, coeff α e f = 0} -- monomial e 1 ∣ f
    zero_mem' := fun _ _ => by rw [coeff_zero]
    add_mem'  := fun hf hg e he => by rw [map_add, hf e he, hg e he, add_zero]
    smul_mem' := fun f g hg e he => by
      classical
      rw [smul_eq_mul, coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.mul_zero (coeff α uv.fst f)
      exact hg  _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he) }

/-- The underlying family for the `Ideal.IsBasis` in a multivariate power series ring. -/
def basis₂ : (σ →₀ ℕ) → TwoSidedIdeal (MvPowerSeries σ α) := fun d ↦ by
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

/-- A power series `f` belongs to the ideal `basis σ α d` if and only if `coeff α e f = 0` for all
`e ≤ d`. -/
theorem mem_basis (f : MvPowerSeries σ α) (d : σ →₀ ℕ) :
    f ∈ basis σ α d ↔ ∀ e ≤ d, coeff α e f = 0 := by
  simp [basis]

/-- A power series `f` belongs to the ideal `basis σ α d` if and only if `coeff α e f = 0` for all
`e ≤ d`. -/
theorem mem_basis₂ (f : MvPowerSeries σ α) (d : σ →₀ ℕ) :
    f ∈ basis₂ σ α d ↔ ∀ e ≤ d, coeff α e f = 0 := by
  simp [basis₂]

/-- If `e ≤ d`, then we have the inclusion of ideals `basis σ α d ≤ basis σ α e`. -/
theorem basis_le {e d : σ →₀ ℕ} (hed : e ≤ d) : basis σ α d ≤ basis σ α e :=
  fun _ => forall_imp (fun _ h ha => h (le_trans ha hed))

/-- If `e ≤ d`, then we have the inclusion of ideals `basis σ α d ≤ basis σ α e`. -/
theorem basis₂_le {e d : σ →₀ ℕ} (hed : e ≤ d) : basis₂ σ α d ≤ basis₂ σ α e :=
  fun _ => forall_imp (fun _ h ha => h (le_trans ha hed))

/-- `basis σ α d ≤ basis σ α e` if and only if `e ≤ d`. -/
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

/-- `basis σ α d ≤ basis σ α e` if and only if `e ≤ d`. -/
theorem basis₂_le_iff [Nontrivial α] {d e : σ →₀ ℕ} :
    basis₂ σ α d ≤ basis₂ σ α e ↔ e ≤ d := by
  refine ⟨?_, basis₂_le _ _⟩
  simp only [basis₂]
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
theorem basis_antitone : Antitone (basis σ α) := fun _ _ h => basis_le σ α h

/-- The function `basis σ α` is strictly antitone. -/
theorem basis_strict_anti [Nontrivial α] : StrictAnti (basis σ α) :=
  strictAnti_of_le_iff_le (fun _ _ ↦ (basis_le_iff σ α).symm)

/-- The function `basis₂ σ α` is antitone. -/
theorem basis₂_antitone : Antitone (basis₂ σ α) := fun _ _ h => basis₂_le σ α h

/-- The function `basis₂ σ α` is strictly antitone. -/
theorem basis₂_strict_anti [Nontrivial α] : StrictAnti (basis₂ σ α) :=
  strictAnti_of_le_iff_le (fun _ _ ↦ (basis₂_le_iff σ α).symm)

theorem ringSubgroupsBasis : RingSubgroupsBasis (fun d ↦ (basis σ α d).toAddSubgroup) where
  inter d e := ⟨d ⊔ e, (basis_antitone σ α).map_sup_le d e⟩
  mul d := ⟨d, fun f ↦ by
    simp only [Submodule.coe_toAddSubgroup, mem_mul]
    rintro ⟨x, hx, y, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul f d := ⟨d, fun g hg ↦ (basis σ α d).mul_mem_left f hg⟩
  rightMul f d := ⟨d, fun g hg ↦ by
    simp only [Submodule.coe_toAddSubgroup, mem_preimage, mem_coe, mem_basis] at hg ⊢
    intro e he
    classical
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ h
    rw [hg i (le_trans ?_ he), zero_mul]
    simp only [← Finset.mem_antidiagonal.mp h, le_self_add]⟩

theorem ringSubgroupsBasis₂ :
    RingSubgroupsBasis (fun d ↦ (basis₂ σ α d).asIdeal.toAddSubgroup) where
  inter d e := ⟨d ⊔ e, (basis₂_antitone σ α).map_sup_le d e⟩
  mul d := ⟨d, fun f ↦ by
    simp only [Submodule.coe_toAddSubgroup, mem_mul]
    rintro ⟨x, hx, y, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul f d := ⟨d, fun g hg ↦ (basis₂ σ α d).mul_mem_left f g hg⟩
  rightMul f d := ⟨d, fun g hg ↦ by
    intro e he
    simp only [Submodule.coe_toAddSubgroup, TwoSidedIdeal.coe_asIdeal,
      mem_coe, sub_zero, mem_basis₂] at hg ⊢
    classical
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ h
    rw [hg i (le_trans ?_ he), zero_mul]
    simp only [← Finset.mem_antidiagonal.mp h, le_self_add]⟩

/- /-- `MvPowerSeries.basis` is an `Ideal.IsBasis`. -/
theorem idealIsBasis : Ideal.IsBasis (basis σ α) where
  nonempty := inferInstance
  inter := fun d e ↦ ⟨d ⊔ e, Antitone.map_sup_le (basis_antitone σ α) d e ⟩
  mul_right := fun d f g ↦ by
    simp only [mem_basis]
    intro hf e he
    classical
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ h
    rw [hf i (le_trans ?_ he), zero_mul]
    simp only [← Finset.mem_antidiagonal.mp h, le_self_add]

/-- `MvPowerSeries.basis` is a `RingSubgroupsBasis`. -/
theorem ringSubgroupsBasis : RingSubgroupsBasis fun d => (basis σ α d).toAddSubgroup :=
  (idealIsBasis σ α).toRingSubgroupsBasis -/

end Ideal.IsBasis

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
    exact forall_imp (fun e h he => h he he)

lemma mem_nhds_zero_iff {U : Set (MvPowerSeries σ α)} :
    U ∈ nhds 0 ↔ ∃ d, {b | b ∈ basis σ α d} ⊆ U := by
  refine ⟨?_ , fun ⟨d, hd⟩ ↦ Filter.sets_of_superset _ (basis_mem_nhds_zero σ α d) hd⟩
  · rw [nhds_pi, Filter.mem_pi]
    rintro ⟨D, hD, t, ht, ht'⟩
    use Finset.sup hD.toFinset id
    apply subset_trans _ ht'
    intros f hf e he
    rw [← coeff_apply α f e, hf e (id_eq e ▸ Finset.le_sup (hD.mem_toFinset.mpr he))]
    exact mem_of_mem_nhds (ht e)

/-- If the coefficient ring `α` is endowed with the discrete topology, then the pointwise
topology on `MvPowerSeries σ α)` agrees with the topology generated by `MvPowerSeries.basis`. -/
theorem topology_eq_ideals_basis_topology :
    MvPowerSeries.WithPiTopology.instTopologicalSpace α =
      (ringSubgroupsBasis σ α).toRingFilterBasis.topology := by
  rw [TopologicalAddGroup.ext_iff inferInstance inferInstance]
  ext s
  rw [mem_nhds_zero_iff, ((ringSubgroupsBasis σ α).hasBasis_nhds  0).mem_iff]
  simp only [sub_zero, Submodule.mem_toAddSubgroup, true_and]

example : (𝓝 (0 : MvPowerSeries σ α)).HasBasis (fun _ ↦ True) (fun d ↦ (basis σ α d)) := by
  apply Filter.HasBasis.mk
  intro s
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨t, hts, hopen, hmem⟩
    obtain ⟨d, hd⟩ := (mem_nhds_zero_iff σ α).mp
      (Filter.mem_of_superset  (IsOpen.mem_nhds hopen hmem) hts)
    refine ⟨d, ⟨by trivial, hd⟩⟩
  · rintro ⟨d, _, hd⟩
    use basis σ α d
    simp only [mem_coe, Submodule.zero_mem, and_true]
    exact ⟨hd, (basis σ α d).toAddSubgroup.isOpen_of_mem_nhds (basis_mem_nhds_zero σ α d)⟩

/-- If the coefficient ring `α` is endowed with the discrete topology, then for every `d : σ →₀ ℕ`,
`↑(basis₂ σ α d) ∈ 𝓝 (0 : MvPowerSeries σ α)`. -/
theorem basis₂_mem_nhds_zero (d : σ →₀ ℕ) :
    (basis₂ σ α d : Set (MvPowerSeries σ α)) ∈ 𝓝 0 := by
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
    rw [mem_basis₂]
    exact forall_imp (fun e h he => h he he)

lemma mem_nhds_zero_iff₂ {U : Set (MvPowerSeries σ α)} :
    U ∈ 𝓝 0 ↔ ∃ d, {b | b ∈ basis₂ σ α d} ⊆ U := by
  refine ⟨?_ , fun ⟨d, hd⟩ ↦ Filter.sets_of_superset _ (basis₂_mem_nhds_zero σ α d) hd⟩
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
theorem topology_eq_ideals_basis_topology₂ :
    MvPowerSeries.WithPiTopology.instTopologicalSpace α =
      (ringSubgroupsBasis₂ σ α).toRingFilterBasis.topology := by
  rw [TopologicalAddGroup.ext_iff inferInstance inferInstance]
  ext s
  simp [mem_nhds_zero_iff₂, ((ringSubgroupsBasis₂ σ α).hasBasis_nhds  0).mem_iff]

example : (𝓝 (0 : MvPowerSeries σ α)).HasBasis (fun _ ↦ True) (fun d ↦ (basis σ α d)) := by
  apply Filter.HasBasis.mk
  intro s
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨t, hts, hopen, hmem⟩
    obtain ⟨d, hd⟩ := (mem_nhds_zero_iff σ α).mp
      (Filter.mem_of_superset  (IsOpen.mem_nhds hopen hmem) hts)
    refine ⟨d, ⟨by trivial, hd⟩⟩
  · rintro ⟨d, _, hd⟩
    use basis σ α d
    simp only [mem_coe, Submodule.zero_mem, and_true]
    exact ⟨hd, (basis σ α d).toAddSubgroup.isOpen_of_mem_nhds (basis_mem_nhds_zero σ α d)⟩

theorem basis₂_hasBasis :
    (𝓝 (0 : MvPowerSeries σ α)).HasBasis (fun _ ↦ True) (fun d ↦ (basis₂ σ α d)) := by
  apply Filter.HasBasis.mk
  intro s
  simp [mem_nhds_zero_iff₂]

/-- The topology on `MvPowerSeries` is a linear topology when the ring of coefficients has
the discrete topology. -/
instance : LinearTopology (MvPowerSeries σ α) :=
  LinearTopology.mk_of_twoSidedIdeal (basis₂_hasBasis σ α)

end DiscreteTopology

end MvPowerSeries
