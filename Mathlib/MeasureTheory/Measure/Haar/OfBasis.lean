/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Additive Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelepiped spanned by the basis.

## Main definitions

* `parallelepiped v` is the parallelepiped spanned by a finite family of vectors.
* `Basis.parallelepiped` is the parallelepiped associated to a basis, seen as a compact set with
  nonempty interior.
* `Basis.addHaar` is the Lebesgue measure associated to a basis, giving measure `1` to the
  corresponding parallelepiped.

In particular, we declare a `MeasureSpace` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/


open Set TopologicalSpace MeasureTheory MeasureTheory.Measure Module

open scoped Pointwise

noncomputable section

variable {ι ι' E F : Type*}

section Fintype

variable [Fintype ι] [Fintype ι']

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The closed parallelepiped spanned by a finite family of vectors. -/
def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Icc 0 1

theorem mem_parallelepiped_iff (v : ι → E) (x : E) :
    x ∈ parallelepiped v ↔ ∃ t ∈ Icc (0 : ι → ℝ) 1, x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]

theorem parallelepiped_basis_eq (b : Basis ι ℝ E) :
    parallelepiped b = {x | ∀ i, b.repr x i ∈ Set.Icc 0 1} := by
  classical
  ext x
  simp_rw [mem_parallelepiped_iff, mem_setOf_eq, b.ext_elem_iff, _root_.map_sum,
    map_smul, Finset.sum_apply', Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mem_Icc,
    Pi.le_def, Pi.zero_apply, Pi.one_apply, ← forall_and]
  aesop

theorem image_parallelepiped (f : E →ₗ[ℝ] F) (v : ι → E) :
    f '' parallelepiped v = parallelepiped (f ∘ v) := by
  simp only [parallelepiped, ← image_comp]
  congr 1 with t
  simp only [Function.comp_apply, _root_.map_sum, LinearMap.map_smulₛₗ, RingHom.id_apply]

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp]
theorem parallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    parallelepiped (v ∘ e) = parallelepiped v := by
  simp only [parallelepiped]
  let K : (ι' → ℝ) ≃ (ι → ℝ) := Equiv.piCongrLeft' (fun _a : ι' => ℝ) e
  have : Icc (0 : ι → ℝ) 1 = K '' Icc (0 : ι' → ℝ) 1 := by
    rw [← Equiv.preimage_eq_iff_eq_image]
    ext x
    simp only [K, mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply, Equiv.piCongrLeft'_apply,
      Pi.one_apply]
    refine
      ⟨fun h => ⟨fun i => ?_, fun i => ?_⟩, fun h =>
        ⟨fun i => h.1 (e.symm i), fun i => h.2 (e.symm i)⟩⟩
    · simpa only [Equiv.symm_apply_apply] using h.1 (e i)
    · simpa only [Equiv.symm_apply_apply] using h.2 (e i)
  rw [this, ← image_comp]
  congr 1 with x
  have := fun z : ι' → ℝ => e.symm.sum_comp fun i => z i • v (e i)
  simp_rw [Equiv.apply_symm_apply] at this
  simp_rw [Function.comp_apply, mem_image, mem_Icc, K, Equiv.piCongrLeft'_apply, this]

-- The parallelepiped associated to an orthonormal basis of `ℝ` is either `[0, 1]` or `[-1, 0]`.
theorem parallelepiped_orthonormalBasis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    parallelepiped b = Icc 0 1 ∨ parallelepiped b = Icc (-1) 0 := by
  have e : ι ≃ Fin 1 := by
    apply Fintype.equivFinOfCardEq
    simp only [← finrank_eq_card_basis b.toBasis, finrank_self]
  have B : parallelepiped (b.reindex e) = parallelepiped b := by
    convert parallelepiped_comp_equiv b e.symm
    ext i
    simp only [OrthonormalBasis.coe_reindex]
  rw [← B]
  let F : ℝ → Fin 1 → ℝ := fun t => fun _i => t
  have A : Icc (0 : Fin 1 → ℝ) 1 = F '' Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨x 0, ⟨hx.1 0, hx.2 0⟩, ?_⟩
      ext j
      simp only [F, Subsingleton.elim j 0]
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨fun _j => hy.1, fun _j => hy.2⟩
  rcases orthonormalBasis_one_dim (b.reindex e) with (H | H)
  · left
    simp_rw [parallelepiped, H, A, Algebra.id.smul_eq_mul, mul_one]
    simp only [F, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      ← image_comp, Function.comp_apply, image_id']
  · right
    simp_rw [H, parallelepiped, Algebra.id.smul_eq_mul, A]
    simp only [F, Finset.univ_unique, Fin.default_eq_zero, mul_neg, mul_one, Finset.sum_neg_distrib,
      Finset.sum_singleton, ← image_comp, Function.comp, image_neg_eq_neg, neg_Icc, neg_zero]

theorem parallelepiped_eq_sum_segment (v : ι → E) : parallelepiped v = ∑ i, segment ℝ 0 (v i) := by
  ext
  simp only [mem_parallelepiped_iff, Set.mem_finset_sum, Finset.mem_univ, forall_true_left,
    segment_eq_image, smul_zero, zero_add, ← Set.pi_univ_Icc, Set.mem_univ_pi]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t • v, fun {i} => ⟨t i, ht _, by simp⟩, rfl⟩
  rintro ⟨g, hg, rfl⟩
  choose t ht hg using @hg
  refine ⟨@t, @ht, ?_⟩
  simp_rw [hg]

theorem convex_parallelepiped (v : ι → E) : Convex ℝ (parallelepiped v) := by
  rw [parallelepiped_eq_sum_segment]
  exact convex_sum _ fun _i _hi => convex_segment _ _

/-- A `parallelepiped` is the convex hull of its vertices -/
theorem parallelepiped_eq_convexHull (v : ι → E) :
    parallelepiped v = convexHull ℝ (∑ i, {(0 : E), v i}) := by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]

/-- The axis aligned parallelepiped over `ι → ℝ` is a cuboid. -/
theorem parallelepiped_single [DecidableEq ι] (a : ι → ℝ) :
    (parallelepiped fun i => Pi.single i (a i)) = Set.uIcc 0 a := by
  ext x
  simp_rw [Set.uIcc, mem_parallelepiped_iff, Set.mem_Icc, Pi.le_def, ← forall_and, Pi.inf_apply,
    Pi.sup_apply, ← Pi.single_smul', Pi.one_apply, Pi.zero_apply, ← Pi.smul_apply',
    Finset.univ_sum_single (_ : ι → ℝ)]
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    specialize ht i
    simp_rw [smul_eq_mul, Pi.mul_apply]
    rcases le_total (a i) 0 with hai | hai
    · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai]
      exact ⟨le_mul_of_le_one_left hai ht.2, mul_nonpos_of_nonneg_of_nonpos ht.1 hai⟩
    · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai]
      exact ⟨mul_nonneg ht.1 hai, mul_le_of_le_one_left hai ht.2⟩
  · intro h
    refine ⟨fun i => x i / a i, fun i => ?_, funext fun i => ?_⟩
    · specialize h i
      rcases le_total (a i) 0 with hai | hai
      · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai] at h
        exact ⟨div_nonneg_of_nonpos h.2 hai, div_le_one_of_ge h.1 hai⟩
      · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai] at h
        exact ⟨div_nonneg h.1 hai, div_le_one_of_le₀ h.2 hai⟩
    · specialize h i
      simp only [smul_eq_mul, Pi.mul_apply]
      rcases eq_or_ne (a i) 0 with hai | hai
      · rw [hai, inf_idem, sup_idem, ← le_antisymm_iff] at h
        rw [hai, ← h, zero_div, zero_mul]
      · rw [div_mul_cancel₀ _ hai]

end AddCommGroup

section NormedSpace

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Module.Basis

/-- The parallelepiped spanned by a basis, as a compact set with nonempty interior. -/
def parallelepiped (b : Basis ι ℝ E) : PositiveCompacts E where
  carrier := _root_.parallelepiped b
  isCompact' := IsCompact.image isCompact_Icc
      (continuous_finset_sum Finset.univ fun (i : ι) (_H : i ∈ Finset.univ) =>
        (continuous_apply i).smul continuous_const)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equivFunL.symm.toHomeomorph '' Icc 0 1)) by
      dsimp only [_root_.parallelepiped]
      convert H
      exact (b.equivFun_symm_apply _).symm
    have A : Set.Nonempty (interior (Icc (0 : ι → ℝ) 1)) := by
      rw [← pi_univ_Icc, interior_pi_set (@finite_univ ι _)]
      simp only [univ_pi_nonempty_iff, Pi.zero_apply, Pi.one_apply, interior_Icc, nonempty_Ioo,
        zero_lt_one, imp_true_iff]
    rwa [← Homeomorph.image_interior, image_nonempty]

@[simp]
theorem coe_parallelepiped (b : Basis ι ℝ E) :
    (b.parallelepiped : Set E) = _root_.parallelepiped b := rfl

@[simp]
theorem parallelepiped_reindex (b : Basis ι ℝ E) (e : ι ≃ ι') :
    (b.reindex e).parallelepiped = b.parallelepiped :=
  PositiveCompacts.ext <|
    (congr_arg _root_.parallelepiped (b.coe_reindex e)).trans (parallelepiped_comp_equiv b e.symm)

theorem parallelepiped_map (b : Basis ι ℝ E) (e : E ≃ₗ[ℝ] F) :
    (b.map e).parallelepiped = b.parallelepiped.map e
    (haveI := FiniteDimensional.of_fintype_basis b
    LinearMap.continuous_of_finiteDimensional e.toLinearMap)
    (haveI := FiniteDimensional.of_fintype_basis (b.map e)
    LinearMap.isOpenMap_of_finiteDimensional _ e.surjective) :=
  PositiveCompacts.ext (image_parallelepiped e.toLinearMap _).symm

theorem prod_parallelepiped (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
    (v.prod w).parallelepiped = v.parallelepiped.prod w.parallelepiped := by
  ext x
  simp only [Basis.coe_parallelepiped, TopologicalSpace.PositiveCompacts.coe_prod, Set.mem_prod,
    mem_parallelepiped_iff]
  constructor
  · intro h
    rcases h with ⟨t, ht1, ht2⟩
    constructor
    · use t ∘ Sum.inl
      constructor
      · exact ⟨(ht1.1 <| Sum.inl ·), (ht1.2 <| Sum.inl ·)⟩
      simp [ht2, Prod.fst_sum]
    · use t ∘ Sum.inr
      constructor
      · exact ⟨(ht1.1 <| Sum.inr ·), (ht1.2 <| Sum.inr ·)⟩
      simp [ht2, Prod.snd_sum]
  intro h
  rcases h with ⟨⟨t, ht1, ht2⟩, ⟨s, hs1, hs2⟩⟩
  use Sum.elim t s
  constructor
  · constructor
    · change ∀ x : ι ⊕ ι', 0 ≤ Sum.elim t s x
      aesop
    · change ∀ x : ι ⊕ ι', Sum.elim t s x ≤ 1
      aesop
  ext
  · simp [ht2, Prod.fst_sum]
  · simp [hs2, Prod.snd_sum]

variable [MeasurableSpace E] [BorelSpace E]

/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
irreducible_def addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped

instance _root_.isAddHaarMeasure_basis_addHaar (b : Basis ι ℝ E) : IsAddHaarMeasure b.addHaar := by
  rw [Basis.addHaar]; exact Measure.isAddHaarMeasure_addHaarMeasure _

instance (b : Basis ι ℝ E) : SigmaFinite b.addHaar := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis b
  rw [Basis.addHaar_def]; exact sigmaFinite_addHaarMeasure

/-- Let `μ` be a σ-finite left invariant measure on `E`. Then `μ` is equal to the Haar measure
defined by `b` iff the parallelepiped defined by `b` has measure `1` for `μ`. -/
theorem addHaar_eq_iff [SecondCountableTopology E] (b : Basis ι ℝ E) (μ : Measure E)
    [SigmaFinite μ] [IsAddLeftInvariant μ] :
    b.addHaar = μ ↔ μ b.parallelepiped = 1 := by
  rw [Basis.addHaar_def]
  exact addHaarMeasure_eq_iff b.parallelepiped μ

@[simp]
theorem addHaar_reindex (b : Basis ι ℝ E) (e : ι ≃ ι') :
    (b.reindex e).addHaar = b.addHaar := by
  rw [Basis.addHaar, b.parallelepiped_reindex e, ← Basis.addHaar]

theorem addHaar_self (b : Basis ι ℝ E) : b.addHaar (_root_.parallelepiped b) = 1 := by
  rw [Basis.addHaar]; exact addHaarMeasure_self

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopologyEither E F]

theorem prod_addHaar (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
    (v.prod w).addHaar = v.addHaar.prod w.addHaar := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis v
  have : FiniteDimensional ℝ F := FiniteDimensional.of_fintype_basis w
  simp [(v.prod w).addHaar_eq_iff, Basis.prod_parallelepiped, Basis.addHaar_self]

end Module.Basis

end NormedSpace

end Fintype

/-- A finite dimensional inner product space has a canonical measure, the Lebesgue measure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orthonormal basis
is proved in `orthonormalBasis.volume_parallelepiped`.

This instance creates:

- a potential non-defeq diamond with the natural instance for `MeasureSpace (ULift E)`,
  which does not exist in Mathlib at the moment;

- a diamond with the existing instance `MeasureTheory.Measure.instMeasureSpacePUnit`.

However, we've decided not to refactor until one of these diamonds starts creating issues, see
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Hausdorff.20measure.20normalisation
-/
instance (priority := 100) measureSpaceOfInnerProductSpace [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    MeasureSpace E where volume := (stdOrthonormalBasis ℝ E).toBasis.addHaar

instance [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : IsAddHaarMeasure (volume : Measure E) :=
  isAddHaarMeasure_basis_addHaar _

/- This instance should not be necessary, but Lean has difficulties to find it in product
situations if we do not declare it explicitly. -/
instance Real.measureSpace : MeasureSpace ℝ := by infer_instance

/-! # Miscellaneous instances for `EuclideanSpace`

In combination with `measureSpaceOfInnerProductSpace`, these put a `MeasureSpace` structure
on `EuclideanSpace`. -/


namespace EuclideanSpace

variable (ι)

-- TODO: do we want these instances for `PiLp` too?
instance : MeasurableSpace (EuclideanSpace ℝ ι) := MeasurableSpace.pi

instance [Finite ι] : BorelSpace (EuclideanSpace ℝ ι) := Pi.borelSpace

/-- `WithLp.equiv` as a `MeasurableEquiv`. -/
@[simps toEquiv]
protected def measurableEquiv : EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ) where
  toEquiv := WithLp.equiv _ _
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id

theorem coe_measurableEquiv : ⇑(EuclideanSpace.measurableEquiv ι) = WithLp.ofLp := rfl

theorem coe_measurableEquiv_symm :
    ⇑(EuclideanSpace.measurableEquiv ι).symm = WithLp.toLp _ := rfl

end EuclideanSpace
