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

- `MvPowerSeries.LinearTopology.basis`: the ideals of the ring of multivariate power series
all coefficients the exponent of which is smaller than some bound vanish.

- `MvPowerSeries.LinearTopology.basis_mem_nhds_zero` :
  the two-sided ideals from `MvPowerSeries.LinearTopology.basis` are neighborhoods of `0`.

- `MvPowerSeries.LinearTopology.hasBasis_twoSidedIdeal` :
  the two-sided ideals from `MvPowerSeries.LinearTopology.basis` form a basis
  of neighborhoods of `0` if the topology of `R` is (left and right) linear.

## Instances :

If `R` has a linear topology, then the product topology on `MvPowerSeries σ R`
is a linear topology.

This applies in particular when `R` has the discrete topology.

-/

namespace MvPowerSeries

namespace LinearTopology

open scoped Topology

open Set SetLike

/-- The underlying family for the basis of ideals in a multivariate power series ring. -/
def basis (σ : Type*) (R : Type*) [Ring R] (Jd : TwoSidedIdeal R × (σ →₀ ℕ)) :
    TwoSidedIdeal (MvPowerSeries σ R) :=
  TwoSidedIdeal.mk' {f | ∀ e ≤ Jd.2, coeff R e f ∈ Jd.1}
    (by simp [coeff_zero])
    (fun hf hg e he ↦ by rw [map_add]; exact add_mem (hf e he) (hg e he))
    (fun {f} hf e he ↦ by simp only [map_neg, neg_mem, hf e he])
    (fun {f g} hg e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      apply TwoSidedIdeal.mul_mem_left
      exact hg _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he))
    (fun {f g} hf e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      exact TwoSidedIdeal.mul_mem_right Jd.1 _ _
        (hf _ (le_trans (le_iff_exists_add.mpr ⟨uv.2, (Finset.mem_antidiagonal.mp huv).symm⟩) he)))

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

/-- If the ring `R` is endowed with a linear topology, then the sets `↑basis σ R (J, d)`,
for `J : TwoSidedIdeal R` which are neighborhoods of `0 : R` and `d : σ →₀ ℕ`,
constitute a basis of neighborhoods of `0 : MvPowerSeries σ R` for the product topology. -/
lemma hasBasis_nhds_zero [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 0 : Filter (MvPowerSeries σ R)).HasBasis
      (fun Id : TwoSidedIdeal R × (σ →₀ ℕ) ↦ (Id.1 : Set R) ∈ 𝓝 0)
      (fun Id ↦ basis _ _ Id) := by
  rw [nhds_pi]
  refine IsLinearTopology.hasBasis_twoSidedIdeal.pi_self.to_hasBasis ?_ ?_
  · intro ⟨D, I⟩ ⟨hD, hI⟩
    refine ⟨⟨I, Finset.sup hD.toFinset id⟩, hI, fun f hf d hd ↦ ?_⟩
    rw [SetLike.mem_coe, mem_basis_iff] at hf
    convert hf _ <| Finset.le_sup (hD.mem_toFinset.mpr hd)
  · intro ⟨I, d⟩ hI
    refine ⟨⟨Iic d, I⟩, ⟨finite_Iic d, hI⟩, ?_⟩
    simpa [basis, coeff_apply, Iic, pi] using subset_rfl

/-- The product topology on `MvPowerSeries` is a (left and right) linear topology
  when the ring of coefficients has a linear topology.

  This weaker version of `MvPowerSeries.LinearTopology.hasBasis_nhds_zero`
  is useful in creating the instance below. -/
theorem hasBasis_nhds_zero' [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
  (𝓝 0).HasBasis (fun I : TwoSidedIdeal (MvPowerSeries σ R) ↦ (I : Set (MvPowerSeries σ R)) ∈ 𝓝 0)
    fun I : TwoSidedIdeal (MvPowerSeries σ R) ↦ (I : Set (MvPowerSeries σ R)) where
  mem_iff' := fun U ↦ by
    rw [hasBasis_nhds_zero.mem_iff]
    simp only [Prod.exists, exists_and_left]
    constructor
    · rintro ⟨J, hJ, d, hd⟩
      exact ⟨basis σ R (J, d), hasBasis_nhds_zero.mem_of_superset hJ fun ⦃a⦄ a ↦ a, hd⟩
    · rintro ⟨I, hI, hU⟩
      rw [hasBasis_nhds_zero.mem_iff] at hI
      obtain ⟨⟨J, d⟩, hJd, hI⟩ := hI
      exact ⟨J, hJd , d, fun ⦃_⦄ a ↦ hU (hI a)⟩

/-- The topology on `MvPowerSeries` is a left linear topology
  when the ring of coefficients has a linar topology. -/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R) (MvPowerSeries σ R) :=
  (isLinearTopology_iff_hasBasis_twoSidedIdeal.mpr (hasBasis_nhds_zero')).1

/-- The topology on `MvPowerSeries` is a right linear topology
  when the ring of coefficients has a linear topology. -/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R)ᵐᵒᵖ (MvPowerSeries σ R) :=
  (isLinearTopology_iff_hasBasis_twoSidedIdeal.mpr (hasBasis_nhds_zero')).2

end LinearTopology

end MvPowerSeries
