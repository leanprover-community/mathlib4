/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Finsupp.Interval
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! # Linear topology on the ring of multivariate power series

- `MvPowerSeries.LinearTopology.basis`: the ideals of the ring of multivariate power series
all coefficients the exponent of which is smaller than some bound vanish.

- `MvPowerSeries.LinearTopology.hasBasis_nhds_zero` :
  the two-sided ideals from `MvPowerSeries.LinearTopology.basis` form a basis
  of neighborhoods of `0` if the topology of `R` is (left and right) linear.

## Instances :

If `R` has a linear topology, then the product topology on `MvPowerSeries σ R`
is a linear topology.

This applies in particular when `R` has the discrete topology.

## Note

If we had an analogue of `PolynomialModule` for power series,
meaning that we could consider the `R⟦X⟧`-module `M⟦X⟧` when `M` is an `R`-module,
then one could prove that `M⟦X⟧` is linearly topologized over `R⟦X⟧`
whenever `M` is linearly topologized over `R`.
To recover the ring case, it would remain to show that the isomorphism between
`Rᵐᵒᵖ⟦X⟧` and `R⟦X⟧ᵐᵒᵖ` identifies their respective actions on `R⟦X⟧`.
(And likewise in the multivariate case.)

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
      exact TwoSidedIdeal.mul_mem_left _ _ _ (hg _ (le_trans (Finset.antidiagonal.snd_le huv) he)))
    (fun {f g} hf e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      exact TwoSidedIdeal.mul_mem_right _ _ _ (hf _ (le_trans (Finset.antidiagonal.fst_le huv) he)))

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
  classical
  constructor
  · simp only [basis, TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', setOf_subset_setOf]
    intro h
    constructor
    · intro x hx
      have (d') : coeff R d' (C σ R x) ∈ J := by
        rw [coeff_C]; split_ifs <;> [exact hx; exact J.zero_mem]
      simpa using h (C σ R x) (fun _ _ ↦ this _) _ (zero_le _)
    · by_contra h'
      apply hK
      rw [eq_top_iff]
      intro x _
      have (d') (hd'_le : d' ≤ d) : coeff R d' (monomial R e x) ∈ J := by
        rw [coeff_monomial]
        split_ifs with hd' <;> [exact (h' (hd' ▸ hd'_le)).elim; exact J.zero_mem]
      simpa using h (monomial R e x) this _ le_rfl
  · rintro ⟨hJK, hed⟩
    exact basis_le hJK hed

variable [TopologicalSpace R]

-- We endow MvPowerSeries σ R with the product topology.
open WithPiTopology

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

/-- The topology on `MvPowerSeries` is a left linear topology
  when the ring of coefficients has a linar topology. -/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R) (MvPowerSeries σ R) :=
  IsLinearTopology.mk_of_hasBasis'  _ hasBasis_nhds_zero TwoSidedIdeal.mul_mem_left

/-- The topology on `MvPowerSeries` is a right linear topology
  when the ring of coefficients has a linear topology. -/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R)ᵐᵒᵖ (MvPowerSeries σ R) :=
  IsLinearTopology.mk_of_hasBasis'  _ hasBasis_nhds_zero (fun J _ _ hg ↦ J.mul_mem_right _ _ hg)

end LinearTopology

end MvPowerSeries
