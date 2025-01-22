/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Finsupp.Interval
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! # Linear topology on the ring of multivariate power series

- `MvPowerSeries.basis`: the ideals of the ring of multivariate power series
all coefficients the exponent of which is smaller than some bound vanish.

## Instances :

- `MvPowerSeries.isLinearTopology` : if `R` has a linear topology,
then the product topology on `MvPowerSeries σ R` is a linear topology.
This applies in particular when `R` has a discrete topology.

-/

namespace MvPowerSeries

namespace LinearTopology

open scoped Topology

open Set SetLike

/-- The underlying family for the basis of ideals in a multivariate power series ring. -/
def basis (σ : Type*) (R : Type*) [Ring R] (Jd : TwoSidedIdeal R × (σ →₀ ℕ)) :
    TwoSidedIdeal (MvPowerSeries σ R) := by
  apply TwoSidedIdeal.mk' {f | ∀ e ≤ Jd.2, coeff R e f ∈ Jd.1}
  · simp [coeff_zero]
  · exact fun hf hg e he ↦ by rw [map_add]; exact add_mem (hf e he) (hg e he)
  · exact fun {f} hf e he ↦ by simp only [map_neg, neg_mem, hf e he]
  · exact fun {f g} hg e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      apply TwoSidedIdeal.mul_mem_left
      exact hg _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he)
  · exact fun {f g} hf e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      apply TwoSidedIdeal.mul_mem_right
      exact hf _ (le_trans (le_iff_exists_add.mpr ⟨uv.2, (Finset.mem_antidiagonal.mp huv).symm⟩) he)

variable {σ : Type*} {R : Type*} [Ring R]

/-- A power series `f` belongs to the twosided ideal `basis σ R ⟨J, d⟩`
if and only if `coeff R e f ∈ J` for all `e ≤ d`. -/
theorem mem_basis_iff {f : MvPowerSeries σ R} {Jd : TwoSidedIdeal R × (σ →₀ ℕ)} :
    f ∈ basis σ R Jd ↔ ∀ e ≤ Jd.2, coeff R e f ∈ Jd.1 := by
  simp [basis]

/-- If `J ≤ K` and `e ≤ d`, then we have the inclusion of twosided ideals
`basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e,>`. -/
theorem basis_le {Jd Ke : TwoSidedIdeal R × (σ →₀ ℕ)} (hJK : Jd.1 ≤ Ke.1) (hed : Ke.2 ≤ Jd.2) :
    basis σ R Jd ≤ basis σ R Ke :=
  fun _ ↦ forall_imp (fun _ h hue ↦ hJK (h (le_trans hue hed)))

/-- `basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e⟩` if and only if `J ≤ K` and `e ≤ d`. -/
theorem basis_le_iff {J K : TwoSidedIdeal R} {d e : σ →₀ ℕ} (hK : K ≠ ⊤) :
    basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e⟩ ↔ J ≤ K ∧ e ≤ d := by
  constructor
  · simp only [basis, TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', setOf_subset_setOf]
    intro h
    by_contra h'
    simp only [not_and_or] at h'
    rcases h' with h' | h'
    · simp only [← coe_subset_coe, Set.not_subset] at h'
      obtain ⟨a, haJ, haK⟩ := h'
      apply haK
      specialize h (monomial R e a) _ e (le_refl e)
      · intro e' he'
        classical
        rw [coeff_monomial]
        split_ifs
        · exact haJ
        · apply zero_mem
      rwa [coeff_monomial_same] at h
    · simp only [← inf_eq_right] at h'
      apply hK
      rw [eq_top_iff]
      intro a _
      specialize h (monomial R e a) _
      · intro e' he'
        convert zero_mem J
        apply coeff_monomial_ne
        rintro ⟨rfl⟩
        exact h' (right_eq_inf.mpr he').symm
      · specialize h e (le_refl e)
        rwa [coeff_monomial_same] at h
  · rintro ⟨hJK, hed⟩
    exact basis_le hJK hed

variable [TopologicalSpace R]

-- We endow MvPowerSeries σ R with the product topology.
open WithPiTopology

variable (σ R) in
theorem ringSubgroupsBasis :
    RingSubgroupsBasis (fun (Jd : {J : TwoSidedIdeal R | (J : Set R) ∈ 𝓝 0} × (σ →₀ ℕ))
        ↦ (basis σ R ⟨Jd.1, Jd.2⟩).asIdeal.toAddSubgroup) where
  inter Jd Ke := ⟨⟨⟨Jd.1 ⊓ Ke.1, Filter.inter_mem Jd.1.prop Ke.1.prop⟩, Jd.2 ⊔ Ke.2⟩, by
    simp only [le_inf_iff]
    exact ⟨basis_le inf_le_left le_sup_left, basis_le inf_le_right le_sup_right⟩⟩
  mul Jd := ⟨Jd, fun f ↦ by
    simp only [Submodule.coe_toAddSubgroup, mem_mul]
    rintro ⟨x, hx, y, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul f Jd := ⟨Jd, fun g hg ↦ (basis σ R ⟨Jd.1, Jd.2⟩).mul_mem_left f g hg⟩
  rightMul f Jd := ⟨Jd, fun g hg ↦ by
    intro e he
    simp only [Submodule.coe_toAddSubgroup, TwoSidedIdeal.coe_asIdeal,
      mem_coe, sub_zero, mem_basis_iff] at hg ⊢
    classical
    rw [coeff_mul]
    apply sum_mem
    rintro ⟨i, j⟩ h
    apply TwoSidedIdeal.mul_mem_right
    apply hg i (le_trans ?_ he)
    simp only [← Finset.mem_antidiagonal.mp h, le_self_add]⟩

/-- If the coefficient ring `R` is endowed with the discrete topology, then for every `d : σ →₀ ℕ`,
`↑(basis σ R d) ∈ 𝓝 (0 : MvPowerSeries σ R)`. -/
theorem basis_mem_nhds_zero (Jd : {J : TwoSidedIdeal R | (J : Set R) ∈ 𝓝 0} × (σ →₀ ℕ)) :
    (basis σ R ⟨Jd.1, Jd.2⟩ : Set (MvPowerSeries σ R)) ∈ 𝓝 0 := by
  classical
  rw [nhds_pi, Filter.mem_pi]
  use Finset.Iic Jd.2, Finset.finite_toSet _, (fun e => if e ≤ Jd.2 then Jd.1 else univ)
  constructor
  · intro e
    split_ifs
    · exact Jd.1.prop
    · simp only [Filter.univ_mem]
  · intro f
    simp only [Finset.coe_Iic, mem_pi, mem_Iic, mem_ite_univ_right, mem_singleton_iff, mem_coe]
    rw [mem_basis_iff]
    exact forall_imp (fun e h he => h he he)

lemma mem_nhds_zero_iff [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]
    {U : Set (MvPowerSeries σ R)} :
    U ∈ 𝓝 0 ↔ ∃ Jd, ((Jd.1 : Set R) ∈ 𝓝 0) ∧ (basis σ R Jd : Set (MvPowerSeries σ R)) ⊆ U := by
  constructor
  · rw [nhds_pi, Filter.mem_pi]
    rintro ⟨D, hD, t, ht, ht'⟩
    suffices ∃ J : TwoSidedIdeal R, (J : Set R) ∈ 𝓝 0 ∧ (J : Set R) ⊆ ⋂ i ∈ D, t i by
      obtain ⟨J, hJ, hJD⟩ := this
      use ⟨J, Finset.sup hD.toFinset id⟩
      constructor
      · exact hJ
      · apply subset_trans _ ht'
        intros f hf e he
        simp only [← coeff_apply R f e]
        apply biInter_subset_of_mem he
        apply hJD
        rw [mem_coe, mem_basis_iff] at hf
        exact hf e (Finset.le_sup (f := id) (hD.mem_toFinset.mpr he))
    set s := ⋂ i ∈ D, t i
    rw [← (IsLinearTopology.hasBasis_twoSidedIdeal (R := R)).mem_iff']
    exact (Filter.biInter_mem hD).mpr fun i a ↦ ht i
  · rintro ⟨Jd, hJd_mem_nhds, hJd⟩
    exact Filter.sets_of_superset _ (basis_mem_nhds_zero ⟨⟨Jd.1, hJd_mem_nhds⟩,Jd.2⟩) hJd

/-- The topology on `MvPowerSeries` is a (left and right) linear topology
  when the ring of coefficients has the discrete topology. -/
theorem hasBasis_twoSidedIdeal [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
  (𝓝 0).HasBasis (fun I : TwoSidedIdeal (MvPowerSeries σ R) ↦ (I : Set (MvPowerSeries σ R)) ∈ 𝓝 0)
    fun I : TwoSidedIdeal (MvPowerSeries σ R) ↦ (I : Set (MvPowerSeries σ R)) := by
  constructor
  intro U
  simp only [mem_nhds_zero_iff]
  constructor
  · rintro ⟨Jd, hJ, hd⟩
    exact ⟨basis σ R Jd, ⟨Jd, ⟨hJ, by simp⟩⟩, hd⟩
  · rintro ⟨J, ⟨⟨Id, hI, hJ⟩, hU⟩⟩
    exact ⟨Id, hI, fun ⦃a⦄ a_1 ↦ hU (hJ a_1)⟩

/-- The topology on `MvPowerSeries` is a left linear topology
  when the ring of coefficients has the discrete topology. -/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R) (MvPowerSeries σ R) :=
  (isLinearTopology_iff_hasBasis_twoSidedIdeal.mpr (hasBasis_twoSidedIdeal)).1

/-- The topology on `MvPowerSeries` is a right linear topology
  when the ring of coefficients has the discrete topology. -/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R)ᵐᵒᵖ (MvPowerSeries σ R) :=
  (isLinearTopology_iff_hasBasis_twoSidedIdeal.mpr (hasBasis_twoSidedIdeal)).2

end LinearTopology

end MvPowerSeries
