/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

#align_import measure_theory.measure.haar.of_basis from "leanprover-community/mathlib"@"92bd7b1ffeb306a89f450bee126ddd8a284c259d"

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

In particular, we declare a `measure_space` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/


open Set TopologicalSpace MeasureTheory MeasureTheory.Measure FiniteDimensional

open scoped BigOperators Pointwise

noncomputable section

variable {ι ι' E F : Type*} [Fintype ι] [Fintype ι']

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The closed parallelepiped spanned by a finite family of vectors. -/
def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Icc 0 1
#align parallelepiped parallelepiped

theorem mem_parallelepiped_iff (v : ι → E) (x : E) :
    x ∈ parallelepiped v ↔ ∃ (t : ι → ℝ) (_ht : t ∈ Icc (0 : ι → ℝ) 1), x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]
  -- 🎉 no goals
#align mem_parallelepiped_iff mem_parallelepiped_iff

theorem image_parallelepiped (f : E →ₗ[ℝ] F) (v : ι → E) :
    f '' parallelepiped v = parallelepiped (f ∘ v) := by
  simp only [parallelepiped, ← image_comp]
  -- ⊢ ((fun a => ↑f a) ∘ fun t => ∑ i : ι, t i • v i) '' Icc 0 1 = (fun a => ∑ x : …
  congr 1 with t
  -- ⊢ t ∈ ((fun a => ↑f a) ∘ fun t => ∑ i : ι, t i • v i) '' Icc 0 1 ↔ t ∈ (fun a  …
  simp only [Function.comp_apply, LinearMap.map_sum, LinearMap.map_smulₛₗ, RingHom.id_apply]
  -- 🎉 no goals
#align image_parallelepiped image_parallelepiped

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp]
theorem parallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    parallelepiped (v ∘ e) = parallelepiped v := by
  simp only [parallelepiped]
  -- ⊢ (fun a => ∑ x : ι', a x • (v ∘ ↑e) x) '' Icc 0 1 = (fun t => ∑ i : ι, t i •  …
  let K : (ι' → ℝ) ≃ (ι → ℝ) := Equiv.piCongrLeft' (fun _a : ι' => ℝ) e
  -- ⊢ (fun a => ∑ x : ι', a x • (v ∘ ↑e) x) '' Icc 0 1 = (fun t => ∑ i : ι, t i •  …
  have : Icc (0 : ι → ℝ) 1 = K '' Icc (0 : ι' → ℝ) 1 := by
    rw [← Equiv.preimage_eq_iff_eq_image]
    ext x
    simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply, Equiv.piCongrLeft'_apply,
      Pi.one_apply]
    refine'
      ⟨fun h => ⟨fun i => _, fun i => _⟩, fun h =>
        ⟨fun i => h.1 (e.symm i), fun i => h.2 (e.symm i)⟩⟩
    · simpa only [Equiv.symm_apply_apply] using h.1 (e i)
    · simpa only [Equiv.symm_apply_apply] using h.2 (e i)
  rw [this, ← image_comp]
  -- ⊢ (fun a => ∑ x : ι', a x • (v ∘ ↑e) x) '' Icc 0 1 = (fun t => ∑ i : ι, t i •  …
  congr 1 with x
  -- ⊢ x ∈ (fun a => ∑ x : ι', a x • (v ∘ ↑e) x) '' Icc 0 1 ↔ x ∈ (fun t => ∑ i : ι …
  have := fun z : ι' → ℝ => e.symm.sum_comp fun i => z i • v (e i)
  -- ⊢ x ∈ (fun a => ∑ x : ι', a x • (v ∘ ↑e) x) '' Icc 0 1 ↔ x ∈ (fun t => ∑ i : ι …
  simp_rw [Equiv.apply_symm_apply] at this
  -- ⊢ x ∈ (fun a => ∑ x : ι', a x • (v ∘ ↑e) x) '' Icc 0 1 ↔ x ∈ (fun t => ∑ i : ι …
  simp_rw [Function.comp_apply, mem_image, mem_Icc, Equiv.piCongrLeft'_apply, this]
  -- 🎉 no goals
#align parallelepiped_comp_equiv parallelepiped_comp_equiv

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
  -- ⊢ parallelepiped ↑(OrthonormalBasis.reindex b e) = Icc 0 1 ∨ parallelepiped ↑( …
  let F : ℝ → Fin 1 → ℝ := fun t => fun _i => t
  -- ⊢ parallelepiped ↑(OrthonormalBasis.reindex b e) = Icc 0 1 ∨ parallelepiped ↑( …
  have A : Icc (0 : Fin 1 → ℝ) 1 = F '' Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · intro x hx
      refine' ⟨x 0, ⟨hx.1 0, hx.2 0⟩, _⟩
      ext j
      simp only [Subsingleton.elim j 0]
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨fun _j => hy.1, fun _j => hy.2⟩
  rcases orthonormalBasis_one_dim (b.reindex e) with (H | H)
  -- ⊢ parallelepiped ↑(OrthonormalBasis.reindex b e) = Icc 0 1 ∨ parallelepiped ↑( …
  · left
    -- ⊢ parallelepiped ↑(OrthonormalBasis.reindex b e) = Icc 0 1
    simp_rw [parallelepiped, H, A, Algebra.id.smul_eq_mul, mul_one]
    -- ⊢ (fun a => ∑ x : Fin 1, a x) '' ((fun a _i => a) '' Icc 0 1) = Icc 0 1
    simp only [Finset.univ_unique, Fin.default_eq_zero, smul_eq_mul, mul_one, Finset.sum_singleton,
      ← image_comp, Function.comp_apply, image_id', ge_iff_le, zero_le_one, not_true, gt_iff_lt]
  · right
    -- ⊢ parallelepiped ↑(OrthonormalBasis.reindex b e) = Icc (-1) 0
    simp_rw [H, parallelepiped, Algebra.id.smul_eq_mul, A]
    -- ⊢ (fun a => ∑ x : Fin 1, a x * -1) '' ((fun a _i => a) '' Icc 0 1) = Icc (-1) 0
    simp only [Finset.univ_unique, Fin.default_eq_zero, mul_neg, mul_one, Finset.sum_neg_distrib,
      Finset.sum_singleton, ← image_comp, Function.comp, image_neg, preimage_neg_Icc, neg_zero]
#align parallelepiped_orthonormal_basis_one_dim parallelepiped_orthonormalBasis_one_dim

theorem parallelepiped_eq_sum_segment (v : ι → E) : parallelepiped v = ∑ i, segment ℝ 0 (v i) := by
  ext
  -- ⊢ x✝ ∈ parallelepiped v ↔ x✝ ∈ ∑ i : ι, segment ℝ 0 (v i)
  simp only [mem_parallelepiped_iff, Set.mem_finset_sum, Finset.mem_univ, forall_true_left,
    segment_eq_image, smul_zero, zero_add, ← Set.pi_univ_Icc, Set.mem_univ_pi]
  constructor
  -- ⊢ (∃ t h, x✝ = ∑ i : ι, t i • v i) → ∃ g h, ∑ i : ι, g i = x✝
  · rintro ⟨t, ht, rfl⟩
    -- ⊢ ∃ g h, ∑ i : ι, g i = ∑ i : ι, t i • v i
    exact ⟨t • v, fun {i} => ⟨t i, ht _, by simp⟩, rfl⟩
    -- 🎉 no goals
  rintro ⟨g, hg, rfl⟩
  -- ⊢ ∃ t h, ∑ i : ι, g i = ∑ i : ι, t i • v i
  choose t ht hg using @hg
  -- ⊢ ∃ t h, ∑ i : ι, g i = ∑ i : ι, t i • v i
  refine ⟨@t, @ht, ?_⟩
  -- ⊢ ∑ i : ι, g i = ∑ i : ι, t • v i
  simp_rw [hg]
  -- 🎉 no goals
#align parallelepiped_eq_sum_segment parallelepiped_eq_sum_segment

theorem convex_parallelepiped (v : ι → E) : Convex ℝ (parallelepiped v) := by
  rw [parallelepiped_eq_sum_segment]
  -- ⊢ Convex ℝ (∑ i : ι, segment ℝ 0 (v i))
  exact convex_sum _ fun _i _hi => convex_segment _ _
  -- 🎉 no goals
#align convex_parallelepiped convex_parallelepiped

/-- A `parallelepiped` is the convex hull of its vertices -/
theorem parallelepiped_eq_convexHull (v : ι → E) :
    parallelepiped v = convexHull ℝ (∑ i, {(0 : E), v i}) := by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]
  -- 🎉 no goals
#align parallelepiped_eq_convex_hull parallelepiped_eq_convexHull

/-- The axis aligned parallelepiped over `ι → ℝ` is a cuboid. -/
theorem parallelepiped_single [DecidableEq ι] (a : ι → ℝ) :
    (parallelepiped fun i => Pi.single i (a i)) = Set.uIcc 0 a := by
  ext x
  -- ⊢ (x ∈ parallelepiped fun i => Pi.single i (a i)) ↔ x ∈ uIcc 0 a
  simp_rw [Set.uIcc, mem_parallelepiped_iff, Set.mem_Icc, Pi.le_def, ← forall_and, Pi.inf_apply,
    Pi.sup_apply, ← Pi.single_smul', Pi.one_apply, Pi.zero_apply, ← Pi.smul_apply',
    Finset.univ_sum_single (_ : ι → ℝ)]
  constructor
  -- ⊢ (∃ t h, x = fun i => (t • a) i) → ∀ (x_1 : ι), 0 ⊓ a x_1 ≤ x x_1 ∧ x x_1 ≤ 0 …
  · rintro ⟨t, ht, rfl⟩ i
    -- ⊢ 0 ⊓ a i ≤ (fun i => (t • a) i) i ∧ (fun i => (t • a) i) i ≤ 0 ⊔ a i
    specialize ht i
    -- ⊢ 0 ⊓ a i ≤ (fun i => (t • a) i) i ∧ (fun i => (t • a) i) i ≤ 0 ⊔ a i
    simp_rw [smul_eq_mul, Pi.mul_apply]
    -- ⊢ 0 ⊓ a i ≤ t i * a i ∧ t i * a i ≤ 0 ⊔ a i
    cases' le_total (a i) 0 with hai hai
    -- ⊢ 0 ⊓ a i ≤ t i * a i ∧ t i * a i ≤ 0 ⊔ a i
    · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai]
      -- ⊢ a i ≤ t i * a i ∧ t i * a i ≤ 0
      exact ⟨le_mul_of_le_one_left hai ht.2, mul_nonpos_of_nonneg_of_nonpos ht.1 hai⟩
      -- 🎉 no goals
    · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai]
      -- ⊢ 0 ≤ t i * a i ∧ t i * a i ≤ a i
      exact ⟨mul_nonneg ht.1 hai, mul_le_of_le_one_left hai ht.2⟩
      -- 🎉 no goals
  · intro h
    -- ⊢ ∃ t h, x = fun i => (t • a) i
    refine' ⟨fun i => x i / a i, fun i => _, funext fun i => _⟩
    -- ⊢ 0 ≤ (fun i => x i / a i) i ∧ (fun i => x i / a i) i ≤ 1
    · specialize h i
      -- ⊢ 0 ≤ (fun i => x i / a i) i ∧ (fun i => x i / a i) i ≤ 1
      cases' le_total (a i) 0 with hai hai
      -- ⊢ 0 ≤ (fun i => x i / a i) i ∧ (fun i => x i / a i) i ≤ 1
      · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai] at h
        -- ⊢ 0 ≤ (fun i => x i / a i) i ∧ (fun i => x i / a i) i ≤ 1
        exact ⟨div_nonneg_of_nonpos h.2 hai, div_le_one_of_ge h.1 hai⟩
        -- 🎉 no goals
      · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai] at h
        -- ⊢ 0 ≤ (fun i => x i / a i) i ∧ (fun i => x i / a i) i ≤ 1
        exact ⟨div_nonneg h.1 hai, div_le_one_of_le h.2 hai⟩
        -- 🎉 no goals
    · specialize h i
      -- ⊢ x i = ((fun i => x i / a i) • a) i
      simp only [smul_eq_mul, Pi.mul_apply]
      -- ⊢ x i = x i / a i * a i
      cases' eq_or_ne (a i) 0 with hai hai
      -- ⊢ x i = x i / a i * a i
      · rw [hai, inf_idem, sup_idem, ← le_antisymm_iff] at h
        -- ⊢ x i = x i / a i * a i
        rw [hai, ← h, zero_div, zero_mul]
        -- 🎉 no goals
      · rw [div_mul_cancel _ hai]
        -- 🎉 no goals
#align parallelepiped_single parallelepiped_single

end AddCommGroup

section NormedSpace

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- The parallelepiped spanned by a basis, as a compact set with nonempty interior. -/
def Basis.parallelepiped (b : Basis ι ℝ E) : PositiveCompacts E where
  carrier := _root_.parallelepiped b
  isCompact' := IsCompact.image isCompact_Icc
      (continuous_finset_sum Finset.univ fun (i : ι) (_H : i ∈ Finset.univ) =>
        (continuous_apply i).smul continuous_const)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equivFunL.symm.toHomeomorph '' Icc 0 1))
    -- ⊢ Set.Nonempty (interior { carrier := _root_.parallelepiped ↑b, isCompact' :=  …
    · dsimp only [_root_.parallelepiped]
      -- ⊢ Set.Nonempty (interior ((fun t => ∑ i : ι, t i • ↑b i) '' Icc 0 1))
      convert H
      -- ⊢ ∑ i : ι, a✝¹ i • ↑b i = ↑(ContinuousLinearEquiv.toHomeomorph (ContinuousLine …
      exact (b.equivFun_symm_apply _).symm
      -- 🎉 no goals
    have A : Set.Nonempty (interior (Icc (0 : ι → ℝ) 1)) := by
      rw [← pi_univ_Icc, interior_pi_set (@finite_univ ι _)]
      simp only [univ_pi_nonempty_iff, Pi.zero_apply, Pi.one_apply, interior_Icc, nonempty_Ioo,
        zero_lt_one, imp_true_iff]
    rwa [← Homeomorph.image_interior, nonempty_image_iff]
    -- 🎉 no goals
#align basis.parallelepiped Basis.parallelepiped

@[simp]
theorem Basis.coe_parallelepiped (b : Basis ι ℝ E) :
   (b.parallelepiped : Set E) = _root_.parallelepiped b := rfl
#align basis.coe_parallelepiped Basis.coe_parallelepiped

@[simp]
theorem Basis.parallelepiped_reindex (b : Basis ι ℝ E) (e : ι ≃ ι') :
    (b.reindex e).parallelepiped = b.parallelepiped :=
  PositiveCompacts.ext <|
    (congr_arg _root_.parallelepiped (b.coe_reindex e)).trans (parallelepiped_comp_equiv b e.symm)
#align basis.parallelepiped_reindex Basis.parallelepiped_reindex

theorem Basis.parallelepiped_map (b : Basis ι ℝ E) (e : E ≃ₗ[ℝ] F) :
    (b.map e).parallelepiped = b.parallelepiped.map e
    (have := FiniteDimensional.of_fintype_basis b
    -- Porting note: Lean cannot infer the instance above
    @LinearMap.continuous_of_finiteDimensional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ this (e.toLinearMap))
    (have := FiniteDimensional.of_fintype_basis (b.map e)
    -- Porting note: Lean cannot infer the instance above
    @LinearMap.isOpenMap_of_finiteDimensional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ this _ e.surjective)
    := PositiveCompacts.ext (image_parallelepiped e.toLinearMap _).symm
#align basis.parallelepiped_map Basis.parallelepiped_map

variable [MeasurableSpace E] [BorelSpace E]

/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
irreducible_def Basis.addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped
#align basis.add_haar Basis.addHaar

instance IsAddHaarMeasure_basis_addHaar (b : Basis ι ℝ E) : IsAddHaarMeasure b.addHaar := by
  rw [Basis.addHaar]; exact Measure.isAddHaarMeasure_addHaarMeasure _
  -- ⊢ IsAddHaarMeasure (addHaarMeasure (Basis.parallelepiped b))
                      -- 🎉 no goals
#align is_add_haar_measure_basis_add_haar IsAddHaarMeasure_basis_addHaar

theorem Basis.addHaar_self (b : Basis ι ℝ E) : b.addHaar (_root_.parallelepiped b) = 1 := by
  rw [Basis.addHaar]; exact addHaarMeasure_self
  -- ⊢ ↑↑(addHaarMeasure (parallelepiped b)) (_root_.parallelepiped ↑b) = 1
                      -- 🎉 no goals
#align basis.add_haar_self Basis.addHaar_self

end NormedSpace

/-- A finite dimensional inner product space has a canonical measure, the Lebesgue measure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orthonormal basis
is proved in `orthonormalBasis.volume_parallelepiped`. -/
instance (priority := 100) measureSpaceOfInnerProductSpace [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    MeasureSpace E where volume := (stdOrthonormalBasis ℝ E).toBasis.addHaar
#align measure_space_of_inner_product_space measureSpaceOfInnerProductSpace

instance [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : IsAddHaarMeasure (volume : Measure E) :=
  IsAddHaarMeasure_basis_addHaar _

/- This instance should not be necessary, but Lean has difficulties to find it in product
situations if we do not declare it explicitly. -/
instance Real.measureSpace : MeasureSpace ℝ := by infer_instance
                                                  -- 🎉 no goals
#align real.measure_space Real.measureSpace

/-! # Miscellaneous instances for `EuclideanSpace`

In combination with `measureSpaceOfInnerProductSpace`, these put a `measure_space` structure
on `EuclideanSpace`. -/


namespace EuclideanSpace

variable (ι)

-- TODO: do we want these instances for `PiLp` too?
instance : MeasurableSpace (EuclideanSpace ℝ ι) := MeasurableSpace.pi

instance : BorelSpace (EuclideanSpace ℝ ι) := Pi.borelSpace

/-- `PiLp.equiv` as a `MeasurableEquiv`. -/
@[simps toEquiv]
protected def measurableEquiv : EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ) where
  toEquiv := PiLp.equiv _ _
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id
#align euclidean_space.measurable_equiv EuclideanSpace.measurableEquiv

theorem coe_measurableEquiv : ⇑(EuclideanSpace.measurableEquiv ι) = PiLp.equiv 2 _ := rfl
#align euclidean_space.coe_measurable_equiv EuclideanSpace.coe_measurableEquiv

end EuclideanSpace
