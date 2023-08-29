/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.RingTheory.Localization.Module

#align_import algebra.module.zlattice from "leanprover-community/mathlib"@"a3e83f0fa4391c8740f7d773a7a9b74e311ae2a3"

/-!
# ℤ-lattices

Let `E` be a finite dimensional vector space over a `NormedLinearOrderedField` `K` with a solid
norm that is also a `FloorRing`, e.g. `ℝ`. A (full) `ℤ`-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `K`.

A `ℤ`-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L = Submodule.span ℤ (Set.range b)` is a ℤ-lattice of `E`
* As an `AddSubgroup E` with the additional properties:
  * `DiscreteTopology L`, that is `L` is discrete
  * `Submodule.span ℝ (L : Set E) = ⊤`, that is `L` spans `E` over `K`.

Results about the first point of view are in the `Zspan` namespace and results about the second
point of view are in the `Zlattice` namespace.

## Main results

* `Zspan.isAddFundamentalDomain`: for a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that
the set defined by `Zspan.fundamentalDomain` is a fundamental domain.
* `Zlattice.module_free`: an AddSubgroup of `E` that is discrete and spans `E` over `K` is a free
`ℤ`-module
* `Zlattice.rank`:  an AddSubgroup of `E` that is discrete and spans `E` over `K` is a free
`ℤ`-module of `ℤ`-rank equal to the `K`-rank of `E`
-/


open scoped BigOperators

noncomputable section

namespace Zspan

open MeasureTheory MeasurableSet Submodule

variable {E ι : Type*}

section NormedLatticeField

variable {K : Type*} [NormedLinearOrderedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `Zspan.isAddFundamentalDomain`
for the proof that it is a fundamental domain. -/
def fundamentalDomain : Set E := {m | ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1}
#align zspan.fundamental_domain Zspan.fundamentalDomain

@[simp]
theorem mem_fundamentalDomain {m : E} :
    m ∈ fundamentalDomain b ↔ ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1 := Iff.rfl
#align zspan.mem_fundamental_domain Zspan.mem_fundamentalDomain

variable [FloorRing K]

section Fintype

variable [Fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def floor (m : E) : span ℤ (Set.range b) := ∑ i, ⌊b.repr m i⌋ • b.restrictScalars ℤ i
#align zspan.floor Zspan.floor

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding up its coordinates on the basis `b`. -/
def ceil (m : E) : span ℤ (Set.range b) := ∑ i, ⌈b.repr m i⌉ • b.restrictScalars ℤ i
#align zspan.ceil Zspan.ceil

@[simp]
theorem repr_floor_apply (m : E) (i : ι) : b.repr (floor b m) i = ⌊b.repr m i⌋ := by
  classical simp only [floor, zsmul_eq_smul_cast K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, LinearEquiv.map_sum]
#align zspan.repr_floor_apply Zspan.repr_floor_apply

@[simp]
theorem repr_ceil_apply (m : E) (i : ι) : b.repr (ceil b m) i = ⌈b.repr m i⌉ := by
  classical simp only [ceil, zsmul_eq_smul_cast K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, LinearEquiv.map_sum]
#align zspan.repr_ceil_apply Zspan.repr_ceil_apply

@[simp]
theorem floor_eq_self_of_mem (m : E) (h : m ∈ span ℤ (Set.range b)) : (floor b m : E) = m := by
  apply b.ext_elem
  -- ⊢ ∀ (i : ι), ↑(↑b.repr ↑(floor b m)) i = ↑(↑b.repr m) i
  simp_rw [repr_floor_apply b]
  -- ⊢ ∀ (i : ι), ↑⌊↑(↑b.repr m) i⌋ = ↑(↑b.repr m) i
  intro i
  -- ⊢ ↑⌊↑(↑b.repr m) i⌋ = ↑(↑b.repr m) i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  -- ⊢ ↑⌊↑(↑b.repr m) i⌋ = ↑(↑b.repr m) i
  rw [← hz]
  -- ⊢ ↑⌊↑(algebraMap ℤ K) z⌋ = ↑(algebraMap ℤ K) z
  exact congr_arg (Int.cast : ℤ → K) (Int.floor_intCast z)
  -- 🎉 no goals
#align zspan.floor_eq_self_of_mem Zspan.floor_eq_self_of_mem

@[simp]
theorem ceil_eq_self_of_mem (m : E) (h : m ∈ span ℤ (Set.range b)) : (ceil b m : E) = m := by
  apply b.ext_elem
  -- ⊢ ∀ (i : ι), ↑(↑b.repr ↑(ceil b m)) i = ↑(↑b.repr m) i
  simp_rw [repr_ceil_apply b]
  -- ⊢ ∀ (i : ι), ↑⌈↑(↑b.repr m) i⌉ = ↑(↑b.repr m) i
  intro i
  -- ⊢ ↑⌈↑(↑b.repr m) i⌉ = ↑(↑b.repr m) i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  -- ⊢ ↑⌈↑(↑b.repr m) i⌉ = ↑(↑b.repr m) i
  rw [← hz]
  -- ⊢ ↑⌈↑(algebraMap ℤ K) z⌉ = ↑(algebraMap ℤ K) z
  exact congr_arg (Int.cast : ℤ → K) (Int.ceil_intCast z)
  -- 🎉 no goals
#align zspan.ceil_eq_self_of_mem Zspan.ceil_eq_self_of_mem

/-- The map that sends a vector `E` to the `fundamentalDomain` of the lattice,
see `Zspan.fract_mem_fundamentalDomain`, and `fract_restrict` for the map with the codomain
restricted to `fundamentalDomain`. -/
def fract (m : E) : E := m - floor b m
#align zspan.fract Zspan.fract

theorem fract_apply (m : E) : fract b m = m - floor b m := rfl
#align zspan.fract_apply Zspan.fract_apply

@[simp]
theorem repr_fract_apply (m : E) (i : ι) : b.repr (fract b m) i = Int.fract (b.repr m i) := by
  rw [fract, LinearEquiv.map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_floor_apply, Int.fract]
  -- 🎉 no goals
#align zspan.repr_fract_apply Zspan.repr_fract_apply

@[simp]
theorem fract_fract (m : E) : fract b (fract b m) = fract b m :=
  Basis.ext_elem b fun _ => by classical simp only [repr_fract_apply, Int.fract_fract]
                               -- 🎉 no goals
#align zspan.fract_fract Zspan.fract_fract

@[simp]
theorem fract_zspan_add (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    fract b (v + m) = fract b m := by
  classical
  refine (Basis.ext_elem_iff b).mpr fun i => ?_
  simp_rw [repr_fract_apply, Int.fract_eq_fract]
  use (b.restrictScalars ℤ).repr ⟨v, h⟩ i
  rw [map_add, Finsupp.coe_add, Pi.add_apply, add_tsub_cancel_right,
    ← eq_intCast (algebraMap ℤ K) _, Basis.restrictScalars_repr_apply, coe_mk]
#align zspan.fract_zspan_add Zspan.fract_zspan_add

@[simp]
theorem fract_add_zspan (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    fract b (m + v) = fract b m := by rw [add_comm, fract_zspan_add b m h]
                                      -- 🎉 no goals
#align zspan.fract_add_zspan Zspan.fract_add_zspan

variable {b}

theorem fract_eq_self {x : E} : fract b x = x ↔ x ∈ fundamentalDomain b := by
  classical simp only [Basis.ext_elem_iff b, repr_fract_apply, Int.fract_eq_self,
    mem_fundamentalDomain, Set.mem_Ico]
#align zspan.fract_eq_self Zspan.fract_eq_self

variable (b)

theorem fract_mem_fundamentalDomain (x : E) : fract b x ∈ fundamentalDomain b :=
  fract_eq_self.mp (fract_fract b _)
#align zspan.fract_mem_fundamental_domain Zspan.fract_mem_fundamentalDomain

/-- The map `fract` with codomain restricted to `fundamentalDomain`. -/
def fract_restrict (x : E) : fundamentalDomain b := ⟨fract b x, fract_mem_fundamentalDomain b x⟩

theorem fract_restrict_surjective : Function.Surjective (fract_restrict b) :=
  fun x => ⟨↑x, Subtype.eq (fract_eq_self.mpr (Subtype.mem x))⟩

@[simp]
theorem fract_restrict_apply (x : E) : (fract_restrict b x : E) = fract b x := rfl

theorem fract_eq_fract (m n : E) : fract b m = fract b n ↔ -m + n ∈ span ℤ (Set.range b) := by
  classical
  rw [eq_comm, Basis.ext_elem_iff b]
  simp_rw [repr_fract_apply, Int.fract_eq_fract, eq_comm, Basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, LinearEquiv.map_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ← eq_intCast (algebraMap ℤ K) _, Set.mem_range]
#align zspan.fract_eq_fract Zspan.fract_eq_fract

theorem norm_fract_le [HasSolidNorm K] (m : E) : ‖fract b m‖ ≤ ∑ i, ‖b i‖ := by
  classical
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ := by rw [b.sum_repr]
    _ = ‖∑ i, Int.fract (b.repr m i) • b i‖ := by simp_rw [repr_fract_apply]
    _ ≤ ∑ i, ‖Int.fract (b.repr m i) • b i‖ := (norm_sum_le _ _)
    _ = ∑ i, ‖Int.fract (b.repr m i)‖ * ‖b i‖ := by simp_rw [norm_smul]
    _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => ?_
  suffices ‖Int.fract ((b.repr m) i)‖ ≤ 1 by
    convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i‖)
    exact (one_mul _).symm
  rw [(norm_one.symm : 1 = ‖(1 : K)‖)]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_one, Int.abs_fract]
  exact le_of_lt (Int.fract_lt_one _)
#align zspan.norm_fract_le Zspan.norm_fract_le

section Unique

variable [Unique ι]

@[simp]
theorem coe_floor_self (k : K) : (floor (Basis.singleton ι K) k : K) = ⌊k⌋ :=
  Basis.ext_elem _ fun _ => by rw [repr_floor_apply, Basis.singleton_repr, Basis.singleton_repr]
                               -- 🎉 no goals
#align zspan.coe_floor_self Zspan.coe_floor_self

@[simp]
theorem coe_fract_self (k : K) : (fract (Basis.singleton ι K) k : K) = Int.fract k :=
  Basis.ext_elem _ fun _ => by rw [repr_fract_apply, Basis.singleton_repr, Basis.singleton_repr]
                               -- 🎉 no goals
#align zspan.coe_fract_self Zspan.coe_fract_self

end Unique

end Fintype

theorem fundamentalDomain_bounded [Finite ι] [HasSolidNorm K] :
    Metric.Bounded (fundamentalDomain b) := by
  cases nonempty_fintype ι
  -- ⊢ Metric.Bounded (fundamentalDomain b)
  use 2 * ∑ j, ‖b j‖
  -- ⊢ ∀ (x : E), x ∈ fundamentalDomain b → ∀ (y : E), y ∈ fundamentalDomain b → di …
  intro x hx y hy
  -- ⊢ dist x y ≤ 2 * ∑ j : ι, ‖↑b j‖
  refine le_trans (dist_le_norm_add_norm x y) ?_
  -- ⊢ ‖x‖ + ‖y‖ ≤ 2 * ∑ j : ι, ‖↑b j‖
  rw [← fract_eq_self.mpr hx, ← fract_eq_self.mpr hy]
  -- ⊢ ‖fract b x‖ + ‖fract b y‖ ≤ 2 * ∑ j : ι, ‖↑b j‖
  refine (add_le_add (norm_fract_le b x) (norm_fract_le b y)).trans ?_
  -- ⊢ ∑ i : ι, ‖↑b i‖ + ∑ i : ι, ‖↑b i‖ ≤ 2 * ∑ j : ι, ‖↑b j‖
  rw [← two_mul]
  -- 🎉 no goals
#align zspan.fundamental_domain_bounded Zspan.fundamentalDomain_bounded

theorem vadd_mem_fundamentalDomain [Fintype ι] (y : span ℤ (Set.range b)) (x : E) :
    y +ᵥ x ∈ fundamentalDomain b ↔ y = -floor b x := by
  rw [Subtype.ext_iff, ← add_right_inj x, AddSubgroupClass.coe_neg, ← sub_eq_add_neg, ← fract_apply,
    ← fract_zspan_add b _ (Subtype.mem y), add_comm, ← vadd_eq_add, ← vadd_def, eq_comm, ←
    fract_eq_self]
#align zspan.vadd_mem_fundamental_domain Zspan.vadd_mem_fundamentalDomain

theorem exist_unique_vadd_mem_fundamentalDomain [Finite ι] (x : E) :
    ∃! v : span ℤ (Set.range b), v +ᵥ x ∈ fundamentalDomain b := by
  cases nonempty_fintype ι
  -- ⊢ ∃! v, v +ᵥ x ∈ fundamentalDomain b
  refine ⟨-floor b x, ?_, fun y h => ?_⟩
  -- ⊢ (fun v => v +ᵥ x ∈ fundamentalDomain b) (-floor b x)
  · exact (vadd_mem_fundamentalDomain b (-floor b x) x).mpr rfl
    -- 🎉 no goals
  · exact (vadd_mem_fundamentalDomain b y x).mp h
    -- 🎉 no goals
#align zspan.exist_unique_vadd_mem_fundamental_domain Zspan.exist_unique_vadd_mem_fundamentalDomain

/-- The map `Zspan.fract_restrict` defines an equiv map between `E ⧸ span ℤ (Set.range b)`
and `Zspan.fundamentalDomain b`. -/
def QuotientEquiv [Fintype ι] :
    E ⧸ span ℤ (Set.range b) ≃ (fundamentalDomain b) := by
  refine Equiv.ofBijective ?_ ⟨fun x y => ?_, fun x => ?_⟩
  · refine fun q => Quotient.liftOn q (fract_restrict b) (fun _ _ h => ?_)
    -- ⊢ fract_restrict b x✝¹ = fract_restrict b x✝
    rw [Subtype.mk.injEq, fract_restrict_apply, fract_restrict_apply, fract_eq_fract]
    -- ⊢ -x✝¹ + x✝ ∈ span ℤ (Set.range ↑b)
    exact QuotientAddGroup.leftRel_apply.mp h
    -- 🎉 no goals
  · refine Quotient.inductionOn₂ x y (fun _ _ hxy => ?_)
    -- ⊢ Quotient.mk (quotientRel (span ℤ (Set.range ↑b))) x✝¹ = Quotient.mk (quotien …
    rw [Quotient.liftOn_mk (s := quotientRel (span ℤ (Set.range b))), fract_restrict,
      Quotient.liftOn_mk (s := quotientRel (span ℤ (Set.range b))),  fract_restrict,
      Subtype.mk.injEq] at hxy
    apply Quotient.sound'
    -- ⊢ Setoid.r x✝¹ x✝
    rwa [QuotientAddGroup.leftRel_apply, mem_toAddSubgroup, ← fract_eq_fract]
    -- 🎉 no goals
  · obtain ⟨a, rfl⟩ := fract_restrict_surjective b x
    -- ⊢ ∃ a_1, Quotient.liftOn a_1 (fract_restrict b) (_ : ∀ (x x_1 : E), x ≈ x_1 →  …
    exact ⟨Quotient.mk'' a, rfl⟩
    -- 🎉 no goals

@[simp]
theorem quotientEquiv_apply_mk [Fintype ι] (x : E) :
    QuotientEquiv b (Submodule.Quotient.mk x) = fract_restrict b x := rfl

@[simp]
theorem quotientEquiv.symm_apply [Fintype ι] (x : fundamentalDomain b) :
    (QuotientEquiv b).symm x = Submodule.Quotient.mk ↑x := by
  rw [Equiv.symm_apply_eq, quotientEquiv_apply_mk b ↑x, Subtype.ext_iff, fract_restrict_apply]
  -- ⊢ ↑x = fract b ↑x
  exact (fract_eq_self.mpr x.prop).symm
  -- 🎉 no goals

end NormedLatticeField

section Real

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (b : Basis ι ℝ E)

@[measurability]
theorem fundamentalDomain_measurableSet [MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] :
    MeasurableSet (fundamentalDomain b) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis b
  -- ⊢ MeasurableSet (fundamentalDomain b)
  let f := (Finsupp.linearEquivFunOnFinite ℝ ℝ ι).toLinearMap.comp b.repr.toLinearMap
  -- ⊢ MeasurableSet (fundamentalDomain b)
  let D : Set (ι → ℝ) := Set.pi Set.univ fun _ : ι => Set.Ico (0 : ℝ) 1
  -- ⊢ MeasurableSet (fundamentalDomain b)
  rw [(_ : fundamentalDomain b = f ⁻¹' D)]
  -- ⊢ MeasurableSet (↑f ⁻¹' D)
  · refine measurableSet_preimage (LinearMap.continuous_of_finiteDimensional f).measurable ?_
    -- ⊢ MeasurableSet D
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
    -- 🎉 no goals
  · ext
    -- ⊢ x✝ ∈ fundamentalDomain b ↔ x✝ ∈ ↑f ⁻¹' D
    simp only [fundamentalDomain, Set.mem_setOf_eq, LinearMap.coe_comp,
      LinearEquiv.coe_toLinearMap, Set.mem_preimage, Function.comp_apply, Set.mem_univ_pi,
      Finsupp.linearEquivFunOnFinite_apply]
#align zspan.fundamental_domain_measurable_set Zspan.fundamentalDomain_measurableSet

/-- For a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that the set defined
by `Zspan.fundamentalDomain` is a fundamental domain. -/
protected theorem isAddFundamentalDomain [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup (fundamentalDomain b) μ := by
  cases nonempty_fintype ι
  -- ⊢ IsAddFundamentalDomain { x // x ∈ toAddSubgroup (span ℤ (Set.range ↑b)) } (f …
  exact IsAddFundamentalDomain.mk' (nullMeasurableSet (fundamentalDomain_measurableSet b))
    fun x => exist_unique_vadd_mem_fundamentalDomain b x
#align zspan.is_add_fundamental_domain Zspan.isAddFundamentalDomain

end Real

end Zspan

section Zlattice

open Submodule

variable (K : Type*) [NormedLinearOrderedField K] [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] {L : AddSubgroup E} [DiscreteTopology L]
variable (hs : span K (L : Set E) = ⊤)

theorem Zlattice.FG : AddSubgroup.FG L := by
  suffices (AddSubgroup.toIntSubmodule L).FG by exact (fg_iff_add_subgroup_fg _).mp this
  -- ⊢ Submodule.FG (↑AddSubgroup.toIntSubmodule L)
  obtain ⟨s, ⟨h_incl, ⟨h_span, h_lind⟩⟩⟩ := exists_linearIndependent K (L : Set E)
  -- ⊢ Submodule.FG (↑AddSubgroup.toIntSubmodule L)
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L ⧸ span ℤ s → 0` with `span ℤ s` and `L ⧸ span ℤ s` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (span ℤ s).mkQ ?_ ?_
  -- ⊢ Submodule.FG (map (mkQ (span ℤ s)) (↑AddSubgroup.toIntSubmodule L))
  · -- Let `b` be the `K`-basis of `E` formed by the vectors in `s`. The elements of
    -- `L ⧸ span ℤ s = L ⧸ span ℤ b` are in bijection with elements of `L ∩ fundamentalDomain b`
    -- so there are finitely many since `fundamentalDomain b` is bounded.
    refine fg_def.mpr ⟨map (span ℤ s).mkQ (AddSubgroup.toIntSubmodule L), ?_, span_eq _⟩
    -- ⊢ Set.Finite ↑(map (mkQ (span ℤ s)) (↑AddSubgroup.toIntSubmodule L))
    let b := Basis.mk h_lind (by
      rw [← hs, ← h_span]
      exact span_mono (by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq, subset_rfl]))
    rw [show span ℤ s = span ℤ (Set.range b) by simp [Basis.coe_mk, Subtype.range_coe_subtype]]
    -- ⊢ Set.Finite ↑(map (mkQ (span ℤ (Set.range ↑b))) (↑AddSubgroup.toIntSubmodule  …
    have : Fintype s := Set.Finite.fintype h_lind.finite
    -- ⊢ Set.Finite ↑(map (mkQ (span ℤ (Set.range ↑b))) (↑AddSubgroup.toIntSubmodule  …
    refine Set.Finite.of_finite_image (f := ((↑) : _ →  E) ∘ Zspan.QuotientEquiv b) ?_
      (Function.Injective.injOn (Subtype.coe_injective.comp (Zspan.QuotientEquiv b).injective) _)
    have : Set.Finite ((Zspan.fundamentalDomain b) ∩ L) :=
      Metric.Finite_bounded_inter_isClosed (Zspan.fundamentalDomain_bounded b) inferInstance
    refine Set.Finite.subset this ?_
    -- ⊢ Subtype.val ∘ ↑(Zspan.QuotientEquiv b) '' ↑(map (mkQ (span ℤ (Set.range ↑b)) …
    rintro _ ⟨_, ⟨⟨x, ⟨h_mem, rfl⟩⟩, rfl⟩⟩
    -- ⊢ (Subtype.val ∘ ↑(Zspan.QuotientEquiv b)) (↑(mkQ (span ℤ (Set.range ↑b))) x)  …
    rw [Function.comp_apply, mkQ_apply, Zspan.quotientEquiv_apply_mk, Zspan.fract_restrict_apply]
    -- ⊢ Zspan.fract b x ∈ Zspan.fundamentalDomain b ∩ ↑L
    refine ⟨?_, ?_⟩
    -- ⊢ Zspan.fract b x ∈ Zspan.fundamentalDomain b
    · exact Zspan.fract_mem_fundamentalDomain b x
      -- 🎉 no goals
    · rw [Zspan.fract, SetLike.mem_coe, sub_eq_add_neg]
      -- ⊢ x + -↑(Zspan.floor b x) ∈ L
      refine AddSubgroup.add_mem _ h_mem
        (neg_mem (Set.mem_of_subset_of_mem ?_ (Subtype.mem (Zspan.floor b x))))
      rw [show (L : Set E) = AddSubgroup.toIntSubmodule L by rfl]
      -- ⊢ ↑(span ℤ (Set.range ↑b)) ⊆ ↑(↑AddSubgroup.toIntSubmodule L)
      rw [SetLike.coe_subset_coe, Basis.coe_mk, Subtype.range_coe_subtype, Set.setOf_mem_eq]
      -- ⊢ span ℤ s ≤ ↑AddSubgroup.toIntSubmodule L
      exact span_le.mpr h_incl
      -- 🎉 no goals
  · -- `span ℤ s` is finitely generated because `s` is finite
    rw [ker_mkQ, inf_of_le_right (span_le.mpr h_incl)]
    -- ⊢ Submodule.FG (span ℤ s)
    exact fg_span (LinearIndependent.finite h_lind)
    -- 🎉 no goals

theorem Zlattice.module_finite : Module.Finite ℤ L :=
  Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg L).mpr (FG K hs))

theorem Zlattice.module_free : Module.Free ℤ L := by
  have : Module.Finite ℤ L := module_finite K hs
  -- ⊢ Module.Free ℤ { x // x ∈ L }
  have : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  -- ⊢ Module.Free ℤ { x // x ∈ L }
  have : NoZeroSMulDivisors ℤ E := RatModule.noZeroSMulDivisors
  -- ⊢ Module.Free ℤ { x // x ∈ L }
  have : NoZeroSMulDivisors ℤ L := by
    change NoZeroSMulDivisors ℤ (AddSubgroup.toIntSubmodule L)
    exact noZeroSMulDivisors _
  exact Module.free_of_finite_type_torsion_free'
  -- 🎉 no goals

open FiniteDimensional

theorem Zlattice.rank : finrank ℤ L = finrank K E := by
  classical
  have : Module.Finite ℤ L := module_finite K hs
  have : Module.Free ℤ L := module_free K hs
  have : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let b₀ := Module.Free.chooseBasis ℤ L
  -- Let `b` be a `ℤ`-basis of `L` formed of vectors of `E`
  let b := Subtype.val ∘ b₀
  have : LinearIndependent ℤ b :=
    LinearIndependent.map' b₀.linearIndependent (L.toIntSubmodule.subtype) (ker_subtype _)
  -- We prove some assertions that will be useful later on
  have h_spanL : span ℤ (Set.range b) = AddSubgroup.toIntSubmodule L := by
    convert congrArg (map (Submodule.subtype (AddSubgroup.toIntSubmodule L))) b₀.span_eq
    · rw [map_span, Set.range_comp]
      rfl
    · exact (map_subtype_top _).symm
  have h_spanE : span K (Set.range b) = ⊤ := by rwa [← span_span_of_tower (R := ℤ), h_spanL]
  have h_card : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) =
      (Set.range b).toFinset.card := by
    rw [Set.toFinset_range, Finset.univ.card_image_of_injective]
    rfl
    exact Subtype.coe_injective.comp (Basis.injective _)
  rw [finrank_eq_card_chooseBasisIndex]
    -- We prove that `finrank ℤ L ≤ finrank K E` and `finrank K E ≤ finrank ℤ L`
  refine le_antisymm ?_ ?_
  · -- To prove that `finrank ℤ L ≤ finrank K E`, we proceed by contradiction and prove that, in
    -- this case, there is a ℤ-relation between the vectors of `b`
    obtain ⟨t, ⟨ht_inc, ⟨ht_span, ht_lin⟩⟩⟩ := exists_linearIndependent K (Set.range b)
    -- `e` is a `K`-basis of `E` formed of vectors of `b`
    let e : Basis t K E := Basis.mk ht_lin (by simp [ht_span, h_spanE])
    have : Fintype t := Set.Finite.fintype ((Set.range b).toFinite.subset ht_inc)
    have h : LinearIndependent ℤ (fun x : (Set.range b) => (x : E)) := by
      rwa [linearIndependent_subtype_range (Subtype.coe_injective.comp b₀.injective)]
    contrapose! h
    -- Since `finrank ℤ L > finrank K E`, there exists a vector `v ∈ b` with `v ∉ e`
    obtain ⟨v, hv⟩ : (Set.range b \ Set.range e).Nonempty := by
      rw [Basis.coe_mk, Subtype.range_coe_subtype, Set.setOf_mem_eq, ← Set.toFinset_nonempty]
      contrapose h
      rw [Finset.not_nonempty_iff_eq_empty, Set.toFinset_diff,
        Finset.sdiff_eq_empty_iff_subset] at h
      replace h := Finset.card_le_of_subset h
      rwa [not_lt, h_card, ← topEquiv.finrank_eq, ← h_spanE, ← ht_span,
        finrank_span_set_eq_card _ ht_lin]
    -- Assume that `e ∪ {v}` is not `ℤ`-linear independent then we get the contradiction
    suffices ¬ LinearIndependent ℤ (fun x : ↥(insert v (Set.range e)) => (x : E)) by
      contrapose! this
      refine LinearIndependent.mono ?_ this
      exact Set.insert_subset (Set.mem_of_mem_diff hv) (by simp [ht_inc])
    -- We prove finally that `e ∪ {v}` is not ℤ-linear independent or, equivalently,
    -- not ℚ-linear independent by showing that `v ∈ span ℚ e`.
    rw [LinearIndependent.iff_fractionRing ℤ ℚ,
      (linearIndependent_insert (Set.not_mem_of_mem_diff hv)),  not_and, not_not]
    intro _
    -- But that follows from the fact that there exist `n, m : ℕ`, `n ≠ m`
    -- such that `(n - m) • v ∈ span ℤ e` which is true since `n ↦ Zspan.fract e (n • v)`
    -- takes value into the finite set `fundamentalDomain e ∩ L`
    have h_mapsto : Set.MapsTo (fun n : ℤ => Zspan.fract e (n • v)) Set.univ
        (Metric.closedBall 0 (∑ i, ‖e i‖) ∩ (L : Set E)) := by
      rw [Set.mapsTo_inter, Set.maps_univ_to, Set.maps_univ_to]
      refine ⟨fun _ =>  mem_closedBall_zero_iff.mpr (Zspan.norm_fract_le e _), fun _ => ?_⟩
      · change _ ∈ AddSubgroup.toIntSubmodule L
        rw [← h_spanL]
        refine sub_mem ?_ ?_
        · exact zsmul_mem (subset_span (Set.diff_subset _ _ hv)) _
        · exact span_mono (by simp [ht_inc]) (coe_mem _)
    have h_finite : Set.Finite (Metric.closedBall 0 (∑ i, ‖e i‖) ∩ (L : Set E)) :=
      Metric.Finite_bounded_inter_isClosed Metric.bounded_closedBall inferInstance
    obtain ⟨n, -, m, -, h_neq, h_eq⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo
      Set.infinite_univ h_mapsto h_finite
    have h_nz : (-n + m : ℚ) ≠ 0 := by
      rwa [Ne.def, add_eq_zero_iff_eq_neg.not, neg_inj, Rat.coe_int_inj, ← Ne.def]
    apply (smul_mem_iff _ h_nz).mp
    refine span_subset_span ℤ ℚ _ ?_
    rwa [add_smul, neg_smul, SetLike.mem_coe, ← Zspan.fract_eq_fract, ← zsmul_eq_smul_cast ℚ,
      ← zsmul_eq_smul_cast ℚ]
  · -- To prove that `finrank K E ≤ finrank ℤ L`, we use the fact `b` generates `E` over `K`
    -- and thus `finrank K E ≤ card b = finrank ℤ L`
    rw [← topEquiv.finrank_eq, ← h_spanE]
    convert finrank_span_le_card (K := K) (Set.range b)

end Zlattice
