/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Localization.Module

/-!
# ℤ-lattices

Let `E` be a finite-dimensional vector space over a `NormedLinearOrderedField` `K` with a solid
norm that is also a `FloorRing`, e.g. `ℝ`. A (full) `ℤ`-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `K`.

A `ℤ`-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L = Submodule.span ℤ (Set.range b)` is a ℤ-lattice of `E`
* As a `ℤ-submodule` of `E` with the additional properties:
  * `DiscreteTopology L`, that is `L` is discrete
  * `Submodule.span ℝ (L : Set E) = ⊤`, that is `L` spans `E` over `K`.

Results about the first point of view are in the `ZSpan` namespace and results about the second
point of view are in the `ZLattice` namespace.

## Main results and definitions

* `ZSpan.isAddFundamentalDomain`: for a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that
  the set defined by `ZSpan.fundamentalDomain` is a fundamental domain.
* `ZLattice.module_free`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is a free
  `ℤ`-module
* `ZLattice.rank`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is free
  of `ℤ`-rank equal to the `K`-rank of `E`
* `ZLattice.comap`: for `e : E → F` a linear map and `L : Submodule ℤ E`, define the pullback of
  `L` by `e`. If `L` is a `IsZLattice` and `e` is a continuous linear equiv, then it is also a
  `IsZLattice`, see `instIsZLatticeComap`.

## Note

There is also `Submodule.IsLattice` which has slightly different applications. There no
topology is needed and the discrete condition is replaced by finitely generated.

## Implementation Notes

A `ZLattice` could be defined either as a `AddSubgroup E` or a `Submodule ℤ E`. However, the module
aspect appears to be the more useful one (especially in computations involving basis) and is also
consistent with the `ZSpan` construction of `ℤ`-lattices.

-/

@[expose] public section


noncomputable section

namespace ZSpan

open MeasureTheory MeasurableSet Module Submodule Bornology

variable {E ι : Type*}

section NormedLatticeField

variable {K : Type*} [NormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable (b : Basis ι K E)

theorem span_top : span K (span ℤ (Set.range b) : Set E) = ⊤ := by simp [span_span_of_tower]

theorem map {F : Type*} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F) :
    Submodule.map (f.restrictScalars ℤ : E →ₗ[ℤ] F) (span ℤ (Set.range b)) =
      span ℤ (Set.range (b.map f)) := by
  simp_rw [Submodule.map_span, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Basis.coe_map, Set.range_comp]

open scoped Pointwise in
theorem smul {c : K} (hc : c ≠ 0) :
    c • span ℤ (Set.range b) = span ℤ (Set.range (b.isUnitSMul (fun _ ↦ hc.isUnit))) := by
  rw [smul_span, Set.smul_set_range]
  congr!
  rw [Basis.isUnitSMul_apply]

variable [LinearOrder K]

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `ZSpan.isAddFundamentalDomain`
for the proof that it is a fundamental domain. -/
def fundamentalDomain : Set E := {m | ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1}

@[simp]
theorem mem_fundamentalDomain {m : E} :
    m ∈ fundamentalDomain b ↔ ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1 := Iff.rfl

theorem map_fundamentalDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F) :
    f '' (fundamentalDomain b) = fundamentalDomain (b.map f) := by
  ext x
  rw [mem_fundamentalDomain, Basis.map_repr, LinearEquiv.trans_apply, ← mem_fundamentalDomain,
    show f.symm x = f.toEquiv.symm x by rfl, ← Set.mem_image_equiv]
  rfl

@[simp]
theorem fundamentalDomain_reindex {ι' : Type*} (e : ι ≃ ι') :
    fundamentalDomain (b.reindex e) = fundamentalDomain b := by
  ext
  simp [e.forall_congr_left]

variable [IsStrictOrderedRing K]

lemma fundamentalDomain_pi_basisFun [Fintype ι] :
    fundamentalDomain (Pi.basisFun ℝ ι) = Set.pi Set.univ fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
  ext; simp

variable [FloorRing K]

section Fintype

variable [Fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def floor (m : E) : span ℤ (Set.range b) := ∑ i, ⌊b.repr m i⌋ • b.restrictScalars ℤ i

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding up its coordinates on the basis `b`. -/
def ceil (m : E) : span ℤ (Set.range b) := ∑ i, ⌈b.repr m i⌉ • b.restrictScalars ℤ i

@[simp]
theorem repr_floor_apply (m : E) (i : ι) : b.repr (floor b m) i = ⌊b.repr m i⌋ := by
  classical simp only [floor, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]
theorem repr_ceil_apply (m : E) (i : ι) : b.repr (ceil b m) i = ⌈b.repr m i⌉ := by
  classical simp only [ceil, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]
theorem floor_eq_self_of_mem (m : E) (h : m ∈ span ℤ (Set.range b)) : (floor b m : E) = m := by
  apply b.ext_elem
  simp_rw [repr_floor_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : ℤ → K) (Int.floor_intCast z)

@[simp]
theorem ceil_eq_self_of_mem (m : E) (h : m ∈ span ℤ (Set.range b)) : (ceil b m : E) = m := by
  apply b.ext_elem
  simp_rw [repr_ceil_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : ℤ → K) (Int.ceil_intCast z)

/-- The map that sends a vector `E` to the `fundamentalDomain` of the lattice,
see `ZSpan.fract_mem_fundamentalDomain`, and `fractRestrict` for the map with the codomain
restricted to `fundamentalDomain`. -/
def fract (m : E) : E := m - floor b m

theorem fract_apply (m : E) : fract b m = m - floor b m := rfl

@[simp]
theorem repr_fract_apply (m : E) (i : ι) : b.repr (fract b m) i = Int.fract (b.repr m i) := by
  rw [fract, map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_floor_apply, Int.fract]

@[simp]
theorem fract_fract (m : E) : fract b (fract b m) = fract b m :=
  Basis.ext_elem b fun _ => by classical simp only [repr_fract_apply, Int.fract_fract]

@[simp]
theorem fract_zSpan_add (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    fract b (v + m) = fract b m := by
  classical
  refine (Basis.ext_elem_iff b).mpr fun i => ?_
  simp_rw [repr_fract_apply, Int.fract_eq_fract]
  use (b.restrictScalars ℤ).repr ⟨v, h⟩ i
  rw [map_add, Finsupp.coe_add, Pi.add_apply, add_tsub_cancel_right,
    ← eq_intCast (algebraMap ℤ K) _, Basis.restrictScalars_repr_apply, coe_mk]

@[simp]
theorem fract_add_ZSpan (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    fract b (m + v) = fract b m := by rw [add_comm, fract_zSpan_add b m h]

variable {b} in
theorem fract_eq_self {x : E} : fract b x = x ↔ x ∈ fundamentalDomain b := by
  classical simp only [Basis.ext_elem_iff b, repr_fract_apply, Int.fract_eq_self,
    mem_fundamentalDomain, Set.mem_Ico]

theorem fract_mem_fundamentalDomain (x : E) : fract b x ∈ fundamentalDomain b :=
  fract_eq_self.mp (fract_fract b _)

/-- The map `fract` with codomain restricted to `fundamentalDomain`. -/
def fractRestrict (x : E) : fundamentalDomain b := ⟨fract b x, fract_mem_fundamentalDomain b x⟩

theorem fractRestrict_surjective : Function.Surjective (fractRestrict b) :=
  fun x => ⟨↑x, Subtype.ext (fract_eq_self.mpr (Subtype.mem x))⟩

@[simp]
theorem fractRestrict_apply (x : E) : (fractRestrict b x : E) = fract b x := rfl

theorem fract_eq_fract (m n : E) : fract b m = fract b n ↔ -m + n ∈ span ℤ (Set.range b) := by
  classical
  rw [eq_comm, Basis.ext_elem_iff b]
  simp_rw [repr_fract_apply, Int.fract_eq_fract, eq_comm, Basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, map_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ← eq_intCast (algebraMap ℤ K) _, Set.mem_range]

theorem norm_fract_le [HasSolidNorm K] (m : E) : ‖fract b m‖ ≤ ∑ i, ‖b i‖ := by
  classical
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ := by rw [b.sum_repr]
    _ = ‖∑ i, Int.fract (b.repr m i) • b i‖ := by simp_rw [repr_fract_apply]
    _ ≤ ∑ i, ‖Int.fract (b.repr m i) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖Int.fract (b.repr m i)‖ * ‖b i‖ := by simp_rw [norm_smul]
    _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => ?_
  suffices ‖Int.fract ((b.repr m) i)‖ ≤ 1 by
    convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i‖)
    exact (one_mul _).symm
  rw [(norm_one.symm : 1 = ‖(1 : K)‖)]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_one, Int.abs_fract]
  exact le_of_lt (Int.fract_lt_one _)

section Unique

variable [Unique ι]

@[simp]
theorem coe_floor_self (k : K) : (floor (Basis.singleton ι K) k : K) = ⌊k⌋ :=
  Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_floor_apply, Basis.singleton_repr, Basis.singleton_repr]

@[simp]
theorem coe_fract_self (k : K) : (fract (Basis.singleton ι K) k : K) = Int.fract k :=
  Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_fract_apply, Basis.singleton_repr, Basis.singleton_repr]

end Unique

end Fintype

theorem fundamentalDomain_isBounded [Finite ι] [HasSolidNorm K] :
    IsBounded (fundamentalDomain b) := by
  cases nonempty_fintype ι
  refine isBounded_iff_forall_norm_le.2 ⟨∑ j, ‖b j‖, fun x hx ↦ ?_⟩
  rw [← fract_eq_self.mpr hx]
  apply norm_fract_le

theorem vadd_mem_fundamentalDomain [Fintype ι] (y : span ℤ (Set.range b)) (x : E) :
    y +ᵥ x ∈ fundamentalDomain b ↔ y = -floor b x := by
  rw [Subtype.ext_iff, ← add_right_inj x, NegMemClass.coe_neg, ← sub_eq_add_neg, ← fract_apply,
    ← fract_zSpan_add b _ (Subtype.mem y), add_comm, ← vadd_eq_add, ← vadd_def, eq_comm, ←
    fract_eq_self]

theorem exist_unique_vadd_mem_fundamentalDomain [Finite ι] (x : E) :
    ∃! v : span ℤ (Set.range b), v +ᵥ x ∈ fundamentalDomain b := by
  cases nonempty_fintype ι
  refine ⟨-floor b x, ?_, fun y h => ?_⟩
  · exact (vadd_mem_fundamentalDomain b (-floor b x) x).mpr rfl
  · exact (vadd_mem_fundamentalDomain b y x).mp h

set_option backward.isDefEq.respectTransparency false in
/-- The map `ZSpan.fractRestrict` defines an equiv map between `E ⧸ span ℤ (Set.range b)`
and `ZSpan.fundamentalDomain b`. -/
def quotientEquiv [Fintype ι] :
    E ⧸ span ℤ (Set.range b) ≃ (fundamentalDomain b) := by
  refine Equiv.ofBijective ?_ ⟨fun x y => ?_, fun x => ?_⟩
  · refine fun q => Quotient.liftOn q (fractRestrict b) (fun _ _ h => ?_)
    rw [Subtype.mk.injEq, fractRestrict_apply, fractRestrict_apply, fract_eq_fract]
    exact QuotientAddGroup.leftRel_apply.mp h
  · induction x, y using Quotient.inductionOn₂
    intro hxy
    rw [Quotient.liftOn_mk (s := quotientRel (span ℤ (Set.range b))), fractRestrict,
      Quotient.liftOn_mk (s := quotientRel (span ℤ (Set.range b))), fractRestrict,
      Subtype.mk.injEq] at hxy
    apply Quotient.sound'
    rwa [QuotientAddGroup.leftRel_apply, mem_toAddSubgroup, ← fract_eq_fract]
  · obtain ⟨a, rfl⟩ := fractRestrict_surjective b x
    exact ⟨Quotient.mk'' a, rfl⟩

@[simp]
theorem quotientEquiv_apply_mk [Fintype ι] (x : E) :
    quotientEquiv b (Submodule.Quotient.mk x) = fractRestrict b x := rfl

@[simp]
theorem quotientEquiv.symm_apply [Fintype ι] (x : fundamentalDomain b) :
    (quotientEquiv b).symm x = Submodule.Quotient.mk ↑x := by
  rw [Equiv.symm_apply_eq, quotientEquiv_apply_mk b ↑x, Subtype.ext_iff, fractRestrict_apply]
  exact (fract_eq_self.mpr x.prop).symm

end NormedLatticeField

section Real

theorem discreteTopology_pi_basisFun [Finite ι] :
    DiscreteTopology (span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  cases nonempty_fintype ι
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage, mem_ball_zero_iff, pi_norm_lt_iff zero_lt_one, Set.mem_singleton_iff]
  simp_rw [← coe_eq_zero, funext_iff, Pi.zero_apply, Real.norm_eq_abs]
  refine forall_congr' (fun i => ?_)
  rsuffices ⟨y, hy⟩ : ∃ (y : ℤ), (y : ℝ) = (x : ι → ℝ) i
  · rw [← hy, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff, Int.cast_eq_zero]
  exact ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x).mp (SetLike.coe_mem x) i

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem fundamentalDomain_subset_parallelepiped [Fintype ι] :
    fundamentalDomain b ⊆ parallelepiped b := by
  rw [fundamentalDomain, parallelepiped_basis_eq, Set.setOf_subset_setOf]
  exact fun _ h i ↦ Set.Ico_subset_Icc_self (h i)

instance [Finite ι] : DiscreteTopology (span ℤ (Set.range b)) := by
  have h : Set.MapsTo b.equivFun (span ℤ (Set.range b)) (span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
    intro _ hx
    rwa [SetLike.mem_coe, Basis.mem_span_iff_repr_mem] at hx ⊢
  convert DiscreteTopology.of_continuous_injective ((continuous_equivFun_basis b).restrict h) ?_
  · exact discreteTopology_pi_basisFun
  · refine Subtype.map_injective _ (Basis.equivFun b).injective

instance [Finite ι] : DiscreteTopology (span ℤ (Set.range b)).toAddSubgroup :=
  inferInstanceAs <| DiscreteTopology (span ℤ (Set.range b))

theorem setFinite_inter [ProperSpace E] [Finite ι] {s : Set E} (hs : Bornology.IsBounded s) :
    Set.Finite (s ∩ span ℤ (Set.range b)) := by
  have : DiscreteTopology (span ℤ (Set.range b)) := inferInstance
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

@[measurability]
theorem fundamentalDomain_measurableSet [MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] :
    MeasurableSet (fundamentalDomain b) := by
  cases nonempty_fintype ι
  haveI : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  let D : Set (ι → ℝ) := Set.pi Set.univ fun _ : ι => Set.Ico (0 : ℝ) 1
  rw [(_ : fundamentalDomain b = b.equivFun.toLinearMap ⁻¹' D)]
  · refine measurableSet_preimage (LinearMap.continuous_of_finiteDimensional _).measurable ?_
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
  · ext
    simp only [D, fundamentalDomain, Set.mem_Ico, Set.mem_setOf_eq, LinearEquiv.coe_coe,
      Set.mem_preimage, Basis.equivFun_apply, Set.mem_pi, Set.mem_univ, forall_true_left]

/-- For a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that the set defined
by `ZSpan.fundamentalDomain` is a fundamental domain. -/
protected theorem isAddFundamentalDomain [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)) (fundamentalDomain b) μ := by
  cases nonempty_fintype ι
  exact IsAddFundamentalDomain.mk' (nullMeasurableSet (fundamentalDomain_measurableSet b))
    fun x => exist_unique_vadd_mem_fundamentalDomain b x

/-- A version of `ZSpan.isAddFundamentalDomain` for `AddSubgroup`. -/
protected theorem isAddFundamentalDomain' [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup (fundamentalDomain b) μ :=
  ZSpan.isAddFundamentalDomain b μ

theorem measure_fundamentalDomain_ne_zero [Finite ι] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
    μ (fundamentalDomain b) ≠ 0 := by
  convert (ZSpan.isAddFundamentalDomain b μ).measure_ne_zero (NeZero.ne μ)
  exact inferInstanceAs <| VAddInvariantMeasure (span ℤ (Set.range b)).toAddSubgroup E μ

theorem measure_fundamentalDomain [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι ℝ E) :
    μ (fundamentalDomain b) = ENNReal.ofReal |b₀.det b| * μ (fundamentalDomain b₀) := by
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  convert μ.addHaar_preimage_linearEquiv (b.equiv b₀ (Equiv.refl ι)) (fundamentalDomain b₀)
  · rw [Set.eq_preimage_iff_image_eq (LinearEquiv.bijective _), map_fundamentalDomain,
      Basis.map_equiv, Equiv.refl_symm, Basis.reindex_refl]
  · simp

theorem measureReal_fundamentalDomain
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι ℝ E) :
    μ.real (fundamentalDomain b) = |b₀.det b| * μ.real (fundamentalDomain b₀) := by
  simp [measureReal_def, measure_fundamentalDomain b μ b₀]

@[simp]
theorem volume_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (ι → ℝ)) :
    volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).det| := by
  rw [measure_fundamentalDomain b volume (b₀ := Pi.basisFun ℝ ι), fundamentalDomain_pi_basisFun,
    volume_pi, Measure.pi_pi, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one,
    mul_one, ← Matrix.det_transpose]
  rfl

@[simp]
theorem volume_real_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (ι → ℝ)) :
    volume.real (fundamentalDomain b) = |(Matrix.of b).det| := by
  simp [measureReal_def]

theorem fundamentalDomain_ae_parallelepiped [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] :
    fundamentalDomain b =ᵐ[μ] parallelepiped b := by
  classical
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  rw [← measure_symmDiff_eq_zero_iff, symmDiff_of_le (fundamentalDomain_subset_parallelepiped b)]
  suffices (parallelepiped b \ fundamentalDomain b) ⊆ ⋃ i,
      AffineSubspace.mk' (b i) (span ℝ (b '' (Set.univ \ {i}))) by
    refine measure_mono_null this
      (measure_iUnion_null_iff.mpr fun i ↦ Measure.addHaar_affineSubspace μ _ ?_)
    refine (ne_of_mem_of_not_mem' (AffineSubspace.mem_top _ _ 0)
      (AffineSubspace.mem_mk'.not.mpr ?_)).symm
    simp_rw [vsub_eq_sub, zero_sub, neg_mem_iff]
    exact linearIndependent_iff_notMem_span.mp b.linearIndependent i
  intro x hx
  simp_rw [parallelepiped_basis_eq, Set.mem_Icc, Set.mem_diff, Set.mem_setOf_eq,
    mem_fundamentalDomain, Set.mem_Ico, not_forall, not_and, not_lt] at hx
  obtain ⟨i, hi⟩ := hx.2
  have : b.repr x i = 1 := le_antisymm (hx.1 i).2 (hi (hx.1 i).1)
  rw [← b.sum_repr x, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), this, one_smul, ← vadd_eq_add]
  refine Set.mem_iUnion.mpr ⟨i, AffineSubspace.vadd_mem_mk' _
    (sum_smul_mem _ _ (fun i hi ↦ Submodule.subset_span ?_))⟩
  exact ⟨i, Set.mem_diff_singleton.mpr ⟨trivial, Finset.ne_of_mem_erase hi⟩, rfl⟩

end Real

end ZSpan

section ZLattice

open Submodule Module ZSpan

-- TODO: generalize this class to other rings than `ℤ`
/-- `L : Submodule ℤ E` where `E` is a vector space over a normed field `K` is a `ℤ`-lattice if
it is discrete and spans `E` over `K`. -/
class IsZLattice (K : Type*) [NormedField K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Prop where
  /-- `L` spans the full space `E` over `K`. -/
  span_top : span K (L : Set E) = ⊤

instance instIsZLatticeRealSpan {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Finite ι] (b : Basis ι ℝ E) :
    IsZLattice ℝ (span ℤ (Set.range b)) where
  span_top := ZSpan.span_top b

section NormedLinearOrderedField

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

theorem ZLattice.FG [hs : IsZLattice K L] : L.FG := by
  obtain ⟨s, ⟨h_incl, ⟨h_span, h_lind⟩⟩⟩ := exists_linearIndependent K (L : Set E)
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L ⧸ span ℤ s → 0` with `span ℤ s` and `L ⧸ span ℤ s` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (span ℤ s).mkQ ?_ ?_
  · -- Let `b` be the `K`-basis of `E` formed by the vectors in `s`. The elements of
    -- `L ⧸ span ℤ s = L ⧸ span ℤ b` are in bijection with elements of `L ∩ fundamentalDomain b`
    -- so there are finitely many since `fundamentalDomain b` is bounded.
    refine fg_def.mpr ⟨map (span ℤ s).mkQ L, ?_, span_eq _⟩
    let b := Basis.mk h_lind (by
      rw [← hs.span_top, ← h_span]
      exact span_mono (by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq, subset_rfl]))
    rw [show span ℤ s = span ℤ (Set.range b) by simp [b, Basis.coe_mk, Subtype.range_coe_subtype]]
    have : Fintype s := h_lind.setFinite.fintype
    refine Set.Finite.of_finite_image (f := ((↑) : _ → E) ∘ quotientEquiv b) ?_
      (Function.Injective.injOn (Subtype.coe_injective.comp (quotientEquiv b).injective))
    have : ((fundamentalDomain b) ∩ L).Finite := by
      change ((fundamentalDomain b) ∩ L.toAddSubgroup).Finite
      have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed
        DiscreteTopology.isDiscrete (fundamentalDomain_isBounded b) inferInstance
    refine Set.Finite.subset this ?_
    rintro _ ⟨_, ⟨⟨x, ⟨h_mem, rfl⟩⟩, rfl⟩⟩
    rw [Function.comp_apply, mkQ_apply, quotientEquiv_apply_mk, fractRestrict_apply]
    refine ⟨?_, ?_⟩
    · exact fract_mem_fundamentalDomain b x
    · rw [fract, SetLike.mem_coe, sub_eq_add_neg]
      refine Submodule.add_mem _ h_mem
        (neg_mem (Set.mem_of_subset_of_mem ?_ (Subtype.mem (floor b x))))
      rw [SetLike.coe_subset_coe, Basis.coe_mk, Subtype.range_coe_subtype, Set.setOf_mem_eq]
      exact span_le.mpr h_incl
  · -- `span ℤ s` is finitely generated because `s` is finite
    rw [ker_mkQ, inf_of_le_right (span_le.mpr h_incl)]
    exact fg_span (LinearIndependent.setFinite h_lind)

theorem ZLattice.module_finite [IsZLattice K L] : Module.Finite ℤ L :=
  .of_fg (ZLattice.FG K L)

set_option backward.isDefEq.respectTransparency false in
instance instModuleFinite_of_discrete_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.Finite ℤ L := by
  let f := (span ℝ (L : Set E)).subtype
  let L₀ := L.comap (f.restrictScalars ℤ)
  have h_img : f '' L₀ = L := by
    rw [← LinearMap.coe_restrictScalars ℤ f, ← Submodule.map_coe (f.restrictScalars ℤ),
      Submodule.map_comap_eq_self]
    exact fun x hx ↦ LinearMap.mem_range.mpr ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
  suffices Module.Finite ℤ L₀ by
    have : L₀.map (f.restrictScalars ℤ) = L :=
      SetLike.ext'_iff.mpr h_img
    convert this ▸ Module.Finite.map L₀ (f.restrictScalars ℤ)
  have : DiscreteTopology L₀ := by
    refine DiscreteTopology.preimage_of_continuous_injective (L : Set E) ?_ (injective_subtype _)
    exact LinearMap.continuous_of_finiteDimensional f
  have : IsZLattice ℝ L₀ := ⟨by
    rw [← (Submodule.map_injective_of_injective (injective_subtype _)).eq_iff, Submodule.map_span,
      Submodule.map_top, range_subtype, h_img]⟩
  exact ZLattice.module_finite ℝ L₀

theorem ZLattice.module_free [IsZLattice K L] : Module.Free ℤ L := by
  have : Module.Finite ℤ L := module_finite K L
  have : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

instance instModuleFree_of_discrete_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.Free ℤ L := by
  have : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

theorem ZLattice.rank [hs : IsZLattice K L] : finrank ℤ L = finrank K E := by
  classical
  have : Module.Finite ℤ L := module_finite K L
  have : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  have : IsAddTorsionFree E := .of_module_rat _
  let b₀ := Module.Free.chooseBasis ℤ L
  -- Let `b` be a `ℤ`-basis of `L` formed of vectors of `E`
  let b := Subtype.val ∘ b₀
  have : LinearIndependent ℤ b :=
    LinearIndependent.map' b₀.linearIndependent (L.subtype) (ker_subtype _)
  -- We prove some assertions that will be useful later on
  have h_spanL : span ℤ (Set.range b) = L := by
    convert congrArg (map (Submodule.subtype L)) b₀.span_eq
    · rw [map_span, Set.range_comp]
      rfl
    · exact (map_subtype_top _).symm
  have h_spanE : span K (Set.range b) = ⊤ := by
    rw [← span_span_of_tower (R := ℤ), h_spanL]
    exact hs.span_top
  have h_card : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) =
      (Set.range b).toFinset.card := by
    rw [Set.toFinset_range, Finset.univ.card_image_of_injective]
    · rfl
    · exact Subtype.coe_injective.comp (Basis.injective _)
  rw [finrank_eq_card_chooseBasisIndex]
    -- We prove that `finrank ℤ L ≤ finrank K E` and `finrank K E ≤ finrank ℤ L`
  refine le_antisymm ?_ ?_
  · -- To prove that `finrank ℤ L ≤ finrank K E`, we proceed by contradiction and prove that, in
    -- this case, there is a ℤ-relation between the vectors of `b`
    obtain ⟨t, ⟨ht_inc, ⟨ht_span, ht_lin⟩⟩⟩ := exists_linearIndependent K (Set.range b)
    -- `e` is a `K`-basis of `E` formed of vectors of `b`
    let e : Basis t K E := Basis.mk ht_lin (by simp [ht_span, h_spanE])
    have : Fintype t := Set.Finite.fintype ((Set.range b).toFinite.subset ht_inc)
    have h : LinearIndepOn ℤ id (Set.range b) := by
      rwa [linearIndepOn_id_range_iff (Subtype.coe_injective.comp b₀.injective)]
    contrapose! h
    -- Since `finrank ℤ L > finrank K E`, there exists a vector `v ∈ b` with `v ∉ e`
    obtain ⟨v, hv⟩ : (Set.range b \ Set.range e).Nonempty := by
      rw [Basis.coe_mk, Subtype.range_coe_subtype, Set.setOf_mem_eq, ← Set.toFinset_nonempty]
      contrapose! h
      rw [Set.toFinset_diff, Finset.sdiff_eq_empty_iff_subset] at h
      replace h := Finset.card_le_card h
      rwa [h_card, ← topEquiv.finrank_eq, ← h_spanE, ← ht_span, finrank_span_set_eq_card ht_lin]
    -- Assume that `e ∪ {v}` is not `ℤ`-linear independent then we get the contradiction
    suffices ¬ LinearIndepOn ℤ id (insert v (Set.range e)) by
      contrapose! this
      refine this.mono ?_
      exact Set.insert_subset (Set.mem_of_mem_diff hv) (by simp [e, ht_inc])
    -- We prove finally that `e ∪ {v}` is not ℤ-linear independent or, equivalently,
    -- not ℚ-linear independent by showing that `v ∈ span ℚ e`.
    rw [LinearIndepOn, LinearIndependent.iff_fractionRing ℤ ℚ, ← LinearIndepOn,
      linearIndepOn_id_insert (Set.notMem_of_mem_diff hv), not_and, not_not]
    intro _
    -- But that follows from the fact that there exist `n, m : ℕ`, `n ≠ m`
    -- such that `(n - m) • v ∈ span ℤ e` which is true since `n ↦ ZSpan.fract e (n • v)`
    -- takes value into the finite set `fundamentalDomain e ∩ L`
    have h_mapsto : Set.MapsTo (fun n : ℤ => fract e (n • v)) Set.univ
        (Metric.closedBall 0 (∑ i, ‖e i‖) ∩ (L : Set E)) := by
      rw [Set.mapsTo_inter, Set.mapsTo_univ_iff, Set.mapsTo_univ_iff]
      refine ⟨fun _ ↦ mem_closedBall_zero_iff.mpr (norm_fract_le e _), fun _ => ?_⟩
      · rw [← h_spanL]
        refine sub_mem ?_ ?_
        · exact zsmul_mem (subset_span (Set.diff_subset hv)) _
        · exact span_mono (by simp [e, ht_inc]) (coe_mem _)
    have h_finite : Set.Finite (Metric.closedBall 0 (∑ i, ‖e i‖) ∩ (L : Set E)) := by
      change ((_ : Set E) ∩ L.toAddSubgroup).Finite
      have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall inferInstance
    obtain ⟨n, -, m, -, h_ne, h_eq⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo
      Set.infinite_univ h_mapsto h_finite
    have h_nz : (-n + m : ℚ) ≠ 0 := by
      rwa [Ne, add_eq_zero_iff_eq_neg.not, neg_inj, Rat.coe_int_inj, ← Ne]
    apply (smul_mem_iff _ h_nz).mp
    refine span_subset_span ℤ ℚ _ ?_
    rwa [add_smul, neg_smul, SetLike.mem_coe, ← fract_eq_fract, Int.cast_smul_eq_zsmul ℚ,
      Int.cast_smul_eq_zsmul ℚ]
  · -- To prove that `finrank K E ≤ finrank ℤ L`, we use the fact `b` generates `E` over `K`
    -- and thus `finrank K E ≤ card b = finrank ℤ L`
    rw [← topEquiv.finrank_eq, ← h_spanE]
    convert finrank_span_le_card (R := K) (Set.range b)

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι ℤ L)

namespace Module.Basis

/-- Any `ℤ`-basis of `L` is also a `K`-basis of `E`. -/
def ofZLatticeBasis : Basis ι K E := by
  have : Module.Finite ℤ L := ZLattice.module_finite K L
  have : Free ℤ L := ZLattice.module_free K L
  let e := (Free.chooseBasis ℤ L).indexEquiv b
  have : Fintype ι := Fintype.ofEquiv _ e
  refine basisOfTopLeSpanOfCardEqFinrank (L.subtype ∘ b) ?_ ?_
  · rw [← span_span_of_tower ℤ, Set.range_comp, ← map_span, Basis.span_eq, Submodule.map_top,
      range_subtype, top_le_iff, hs.span_top]
  · rw [← Fintype.card_congr e, ← finrank_eq_card_chooseBasisIndex, ZLattice.rank K L]

@[simp]
theorem ofZLatticeBasis_apply (i : ι) : b.ofZLatticeBasis K L i = b i := by
  simp [Basis.ofZLatticeBasis]

@[simp]
theorem ofZLatticeBasis_repr_apply (x : L) (i : ι) :
    (b.ofZLatticeBasis K L).repr x i = b.repr x i := by
  suffices ((b.ofZLatticeBasis K L).repr.toLinearMap.restrictScalars ℤ) ∘ₗ L.subtype
      = Finsupp.mapRange.linearMap (Algebra.linearMap ℤ K) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext b fun i ↦ ?_
  simp_rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, coe_subtype, ← b.ofZLatticeBasis_apply K, repr_self,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]

theorem ofZLatticeBasis_span : span ℤ (Set.range (b.ofZLatticeBasis K)) = L := by
  calc span ℤ (Set.range (b.ofZLatticeBasis K))
    _ = span ℤ (L.subtype '' Set.range b) := by congr; ext; simp
    _ = map L.subtype (span ℤ (Set.range b)) := by rw [Submodule.map_span]
    _ = L := by simp [b.span_eq]

end Module.Basis

open MeasureTheory in
theorem ZLattice.isAddFundamentalDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] [Finite ι]
    (b : Basis ι ℤ L) [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) :
    IsAddFundamentalDomain L (fundamentalDomain (b.ofZLatticeBasis ℝ)) μ := by
  convert ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis ℝ) μ
  all_goals exact (b.ofZLatticeBasis_span ℝ).symm

instance instCountable_of_discrete_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Countable L := by
  simp_rw [← (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Assume that the set `s` spans over `ℤ` a discrete set. Then its `ℝ`-rank is equal to its `ℤ`-rank.
-/
theorem Real.finrank_eq_int_finrank_of_discrete {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : DiscreteTopology (span ℤ s)) :
    Set.finrank ℝ s = Set.finrank ℤ s := by
  let F := span ℝ s
  let L : Submodule ℤ (span ℝ s) := comap (F.restrictScalars ℤ).subtype (span ℤ s)
  let f := Submodule.comapSubtypeEquivOfLe (span_le_restrictScalars ℤ ℝ s)
  have : DiscreteTopology L := by
    let e : span ℤ s ≃L[ℤ] L :=
      ⟨f.symm, continuous_of_discreteTopology, Isometry.continuous fun _ ↦ congrFun rfl⟩
    exact e.toHomeomorph.discreteTopology
  have : IsZLattice ℝ L := ⟨eq_top_iff.mpr <|
    span_span_coe_preimage.symm.le.trans (span_mono (Set.preimage_mono subset_span))⟩
  rw [Set.finrank, Set.finrank, ← f.finrank_eq]
  exact (ZLattice.rank ℝ L).symm

omit [DiscreteTopology L] [ProperSpace E] in
theorem Real.finrank_real_span_range_eq_finrank_int [hL : DiscreteTopology L] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {v : ι → L} :
    finrank ℝ (span ℝ <| .range (Subtype.val ∘ v)) =
      finrank ℤ (span ℤ <| .range (Subtype.val ∘ v)) := by
  have hd : DiscreteTopology (span ℤ (.range (Subtype.val ∘ v))) :=
    hL.of_subset (span_le.mpr <| Set.range_subset_iff.mpr fun j => (v j).prop)
  simpa only [Set.finrank] using Real.finrank_eq_int_finrank_of_discrete hd

end NormedLinearOrderedField

section Basis

variable {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]

/--
Return an arbitrary `ℤ`-basis of a lattice `L` of `ι → ℝ` indexed by `ι`.
-/
def IsZLattice.basis : Basis ι ℤ L :=
  (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq
    (by rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_fintype_fun_eq_card]))

end Basis

section comap

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

/-- Let `e : E → F` a linear map, the map that sends a `L : Submodule ℤ E` to the
`Submodule ℤ F` that is the pullback of `L` by `e`. If `IsZLattice L` and `e` is a continuous
linear equiv, then it is a `IsZLattice` of `E`, see `instIsZLatticeComap`. -/
protected def ZLattice.comap (e : F →ₗ[K] E) := L.comap (e.restrictScalars ℤ)

@[simp]
theorem ZLattice.coe_comap (e : F →ₗ[K] E) :
    (ZLattice.comap K L e : Set F) = e ⁻¹' L := rfl

theorem ZLattice.comap_refl :
    ZLattice.comap K L (1 : E →ₗ[K] E) = L := Submodule.comap_id L

theorem ZLattice.comap_discreteTopology [hL : DiscreteTopology L] {e : F →ₗ[K] E}
    (he₁ : Continuous e) (he₂ : Function.Injective e) :
    DiscreteTopology (ZLattice.comap K L e) := by
  exact DiscreteTopology.preimage_of_continuous_injective L he₁ he₂

instance [DiscreteTopology L] (e : F ≃L[K] E) :
    DiscreteTopology (ZLattice.comap K L e.toLinearMap) :=
  ZLattice.comap_discreteTopology K L e.continuous e.injective

theorem ZLattice.comap_span_top (hL : span K (L : Set E) = ⊤) {e : F →ₗ[K] E}
    (he : (L : Set E) ⊆ LinearMap.range e) :
    span K (ZLattice.comap K L e : Set F) = ⊤ := by
  rw [ZLattice.coe_comap, Submodule.span_preimage_eq (Submodule.nonempty L) he, hL, comap_top]

instance instIsZLatticeComap [DiscreteTopology L] [IsZLattice K L] (e : F ≃L[K] E) :
    IsZLattice K (ZLattice.comap K L e.toLinearMap) where
  span_top := by
    rw [ZLattice.coe_comap, LinearEquiv.coe_coe, e.coe_toLinearEquiv, ← e.image_symm_eq_preimage,
      ← ContinuousLinearEquiv.coe_toLinearEquiv, ← LinearEquiv.coe_coe, ← Submodule.map_span,
      IsZLattice.span_top, Submodule.map_top, e.symm.range]

@[simp]
theorem ZLattice.comap_toAddSubgroup (e : F →ₗ[K] E) :
    (ZLattice.comap K L e).toAddSubgroup = L.toAddSubgroup.comap e.toAddMonoidHom := rfl

theorem ZLattice.comap_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
    (e : F →ₗ[K] E) (e' : G →ₗ[K] F) :
    (ZLattice.comap K (ZLattice.comap K L e) e') = ZLattice.comap K L (e ∘ₗ e') :=
  (Submodule.comap_comp _ _ L).symm

/-- If `e` is a linear equivalence, it induces a `ℤ`-linear equivalence between
`L` and `ZLattice.comap K L e`. -/
def ZLattice.comap_equiv (e : F ≃ₗ[K] E) :
    L ≃ₗ[ℤ] (ZLattice.comap K L e.toLinearMap) :=
  LinearEquiv.ofBijective
    ((e.symm.toLinearMap.restrictScalars ℤ).restrict
      (fun _ h ↦ by simpa [← SetLike.mem_coe] using h))
    ⟨fun _ _ h ↦ Subtype.ext_iff.mpr (e.symm.injective (congr_arg Subtype.val h)),
    fun ⟨x, hx⟩ ↦ ⟨⟨e x, by rwa [← SetLike.mem_coe, ZLattice.coe_comap] at hx⟩,
      by simp [Subtype.ext_iff]⟩⟩

@[simp]
theorem ZLattice.comap_equiv_apply (e : F ≃ₗ[K] E) (x : L) :
    ZLattice.comap_equiv K L e x = e.symm x := rfl

namespace Module.Basis

/-- The basis of `ZLattice.comap K L e` given by the image of a basis `b` of `L` by `e.symm`. -/
def ofZLatticeComap (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι ℤ L) :
    Basis ι ℤ (ZLattice.comap K L e.toLinearMap) := b.map (ZLattice.comap_equiv K L e)

@[simp]
theorem ofZLatticeComap_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι ℤ L) (i : ι) :
    b.ofZLatticeComap K L e i = e.symm (b i) := by simp [Basis.ofZLatticeComap]

@[simp]
theorem ofZLatticeComap_repr_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    (b.ofZLatticeComap K L e).repr (ZLattice.comap_equiv K L e x) i = b.repr x i := by
  simp [Basis.ofZLatticeComap]

end Module.Basis
end comap

section NormedLinearOrderedField_comap

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K]
  [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
  [ProperSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
  [ProperSpace F]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L]

theorem Module.Basis.ofZLatticeBasis_comap (e : F ≃L[K] E) {ι : Type*} (b : Basis ι ℤ L) :
    (b.ofZLatticeComap K L e.toLinearEquiv).ofZLatticeBasis K (ZLattice.comap K L e.toLinearMap) =
    (b.ofZLatticeBasis K L).map e.symm.toLinearEquiv := by
  ext
  simp

end NormedLinearOrderedField_comap

/-- If `f` is periodic wrt a ℤ-lattice, then the range of `f` is compact. -/
lemma IsZLattice.isCompact_range_of_periodic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace F]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (f : E → F) (hf : Continuous f)
    (hf' : ∀ z w, w ∈ L → f (z + w) = f z) : IsCompact (Set.range f) := by
  have := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  convert (b.ofZLatticeBasis ℝ).parallelepiped.isCompact.image hf
  refine le_antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  let x' : L := b.repr.symm (Finsupp.equivFunOnFinite.symm
    fun i ↦ ⌊(b.ofZLatticeBasis ℝ).repr x i⌋)
  refine ⟨x + (- x'), ?_, hf' _ _ (- x').2⟩
  simp [parallelepiped_basis_eq, x', Int.floor_le, Int.lt_floor_add_one, le_of_lt, add_comm (1 : ℝ)]

end ZLattice
