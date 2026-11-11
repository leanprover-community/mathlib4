/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anouk Brose, Xavier Roblot, Justus Springer
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Order.Interval.Set.Pi

/-!
# Parallelepipeds

Closed and half-open parallelepipeds spanned by a finite family of vectors in a module over a
linearly ordered field.

## Main definitions

* `parallelepiped K v`: the closed parallelepiped spanned by `v`, i.e. all combinations
  `∑ i, t i • v i` with `t i ∈ [0, 1]`.
* `halfOpenParallelepiped K v`: the half-open parallelepiped spanned by `v`, i.e. all combinations
  `∑ i, t i • v i` with `t i ∈ [0, 1)`.
* `Module.Basis.floor b m`, `Module.Basis.ceil b m`: for a basis `b` over a field with a floor
  function, the vector of the lattice `span ℤ (range b)` obtained by rounding the coordinates of `m`
  down, respectively up.
* `Module.Basis.fract b m`: the vector `m - b.floor m`, which lies in `halfOpenParallelepiped K b`.
* `Module.Basis.quotientEquiv b`: the bijection `E ⧸ span ℤ (range b) ≃ halfOpenParallelepiped K b`,
  i.e. the half-open parallelepiped spanned by `b` is a fundamental domain for `span ℤ (range b)`.
-/

@[expose] public section

open Set Module Submodule
open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K]
variable {ι ι' E F : Type*} [Fintype ι] [Fintype ι']
variable [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

section parallelepiped

variable (K) in
/-- The closed parallelepiped spanned by a finite family of vectors. -/
def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → K => ∑ i, t i • v i) '' Icc 0 1

theorem mem_parallelepiped_iff (v : ι → E) (x : E) :
    x ∈ parallelepiped K v ↔ ∃ t ∈ Icc (0 : ι → K) 1, x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]

@[simp]
theorem parallelepiped_of_isEmpty [IsEmpty ι] (v : ι → E) : parallelepiped K v = {0} := by
  simp [parallelepiped]

/-- For linearly independent `v`, a linear combination of `v` lies in the parallelepiped spanned
by `v` if and only if all its coefficients lie in `[0, 1]`. -/
theorem LinearIndependent.sum_smul_mem_parallelepiped_iff {v : ι → E}
    (hv : LinearIndependent K v) {t : ι → K} :
    ∑ i, t i • v i ∈ parallelepiped K v ↔ t ∈ Icc 0 1 := by
  refine ⟨fun h ↦ ?_, fun ht ↦ ⟨t, ht, rfl⟩⟩
  obtain ⟨t', ht', hsum⟩ := (mem_parallelepiped_iff v _).mp h
  exact funext (Fintype.linearIndependent_iffₛ.mp hv _ _ hsum) ▸ ht'

theorem parallelepiped_basis_eq (b : Basis ι K E) :
    parallelepiped K b = {x | ∀ i, b.repr x i ∈ Icc 0 1} := by
  rw [parallelepiped, ← funext b.equivFun_symm_apply, LinearEquiv.image_symm_eq_preimage]
  ext
  simp [Pi.le_def, forall_and]

theorem parallelepiped_basisFun : parallelepiped K (Pi.basisFun K ι) = Icc 0 1 := by
  ext
  simp [parallelepiped_basis_eq, Pi.le_def, forall_and]

theorem image_parallelepiped (f : E →ₗ[K] F) (v : ι → E) :
    f '' parallelepiped K v = parallelepiped K (f ∘ v) := by
  rw [parallelepiped, ← image_comp]
  congr 1 with t
  simp

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp]
theorem parallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    parallelepiped K (v ∘ e) = parallelepiped K v := by
  ext x
  refine (e.arrowCongr (.refl K)).exists_congr fun t ↦ ?_
  simp [Pi.le_def, ← e.sum_comp, e.forall_congr_left]

theorem parallelepiped_prod (v : ι → E) (w : ι' → F) :
    parallelepiped K (Sum.elim (LinearMap.inl K E F ∘ v) (LinearMap.inr K E F ∘ w)) =
      parallelepiped K v ×ˢ parallelepiped K w := by
  ext ⟨x, y⟩
  rw [mem_parallelepiped_iff, (Equiv.sumArrowEquivProdArrow ι ι' K).exists_congr_left]
  simp [mem_parallelepiped_iff, Pi.le_def, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum,
    and_and_and_comm]

variable [IsStrictOrderedRing K]

@[simp]
theorem zero_mem_parallelepiped (v : ι → E) : (0 : E) ∈ parallelepiped K v :=
  (mem_parallelepiped_iff v _).mpr ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩

theorem parallelepiped_subset_hull (v : ι → E) :
    parallelepiped K v ⊆ (PointedCone.hull K (range v) : Set E) := by
  rintro _ ⟨t, ht, rfl⟩
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have h : t i • v i = (⟨t i, ht.1 i⟩ : {c : K // 0 ≤ c}) • v i := rfl
  rw [h]
  exact Submodule.smul_mem _ _ (PointedCone.subset_hull ⟨i, rfl⟩)

theorem parallelepiped_eq_sum_segment (v : ι → E) :
    parallelepiped K v = ∑ i, segment K 0 (v i) := by
  simp_rw [parallelepiped, segment_eq_image, smul_zero, zero_add, ← image_fintype_sum_pi,
    ← piMap_image_univ_pi, ← image_comp, pi_univ_Icc, Function.comp_def, Pi.map_apply,
    ← Pi.zero_def, ← Pi.one_def]

/-- A parallelepiped spanned by a single vector is a segment. -/
theorem parallelepiped_unique [Unique ι] (v : ι → E) :
    parallelepiped K v = segment K 0 (v default) := by
  rw [parallelepiped_eq_sum_segment, Finset.univ_unique, Finset.sum_singleton]

theorem convex_parallelepiped (v : ι → E) : Convex K (parallelepiped K v) := by
  rw [parallelepiped_eq_sum_segment]
  exact convex_sum _ fun _ _ => convex_segment _ _

/-- A `parallelepiped` is the convex hull of its vertices -/
theorem parallelepiped_eq_convexHull (v : ι → E) :
    parallelepiped K v = convexHull K (∑ i, {(0 : E), v i}) := by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]

/-- The axis aligned parallelepiped over `ι → K` is a cuboid. -/
theorem parallelepiped_single [DecidableEq ι] (a : ι → K) :
    (parallelepiped K fun i => Pi.single i (a i)) = Set.uIcc 0 a := by
  have h : (fun t : ι → K ↦ ∑ i, t i • Pi.single i (a i)) = Pi.map fun i ↦ (· * a i) := by
    ext t j
    simp [Pi.single_apply]
  simp_rw [parallelepiped, h, ← pi_univ_Icc, piMap_image_univ_pi, ← pi_univ_uIcc, Pi.zero_apply,
    Pi.one_apply, ← uIcc_of_le zero_le_one, image_mul_const_uIcc, zero_mul, one_mul]

end parallelepiped

section halfOpenParallelepiped

variable (K) in
/-- The half-open parallelepiped spanned by a finite family of vectors. -/
def halfOpenParallelepiped (v : ι → E) : Set E :=
  (fun t : ι → K => ∑ i, t i • v i) '' univ.pi fun _ ↦ Ico 0 1

theorem mem_halfOpenParallelepiped_iff (v : ι → E) (x : E) :
    x ∈ halfOpenParallelepiped K v ↔
      ∃ t : ι → K, (∀ i, t i ∈ Ico (0 : K) 1) ∧ x = ∑ i, t i • v i := by
  simp [halfOpenParallelepiped, eq_comm]

@[simp]
theorem halfOpenParallelepiped_of_isEmpty [IsEmpty ι] (v : ι → E) :
    halfOpenParallelepiped K v = {0} := by
  simp [halfOpenParallelepiped, univ_eq_empty_iff.mpr]

theorem sum_smul_mem_halfOpenParallelepiped (v : ι → E) {t : ι → K}
    (ht : ∀ i, t i ∈ Ico (0 : K) 1) : ∑ i, t i • v i ∈ halfOpenParallelepiped K v :=
  (mem_halfOpenParallelepiped_iff v _).mpr ⟨t, ht, rfl⟩

/-- For linearly independent `v`, a linear combination of `v` lies in the half-open parallelepiped
spanned by `v` if and only if all its coefficients lie in `[0, 1)`. -/
theorem LinearIndependent.sum_smul_mem_halfOpenParallelepiped_iff {v : ι → E}
    (hv : LinearIndependent K v) {t : ι → K} :
    ∑ i, t i • v i ∈ halfOpenParallelepiped K v ↔ ∀ i, t i ∈ Ico (0 : K) 1 := by
  refine ⟨fun h ↦ ?_, sum_smul_mem_halfOpenParallelepiped v⟩
  obtain ⟨t', ht', hsum⟩ := (mem_halfOpenParallelepiped_iff v _).mp h
  exact fun i ↦ Fintype.linearIndependent_iffₛ.mp hv _ _ hsum i ▸ ht' i

theorem halfOpenParallelepiped_basis_eq (b : Basis ι K E) :
    halfOpenParallelepiped K b = {x | ∀ i, b.repr x i ∈ Ico 0 1} := by
  ext x
  conv_lhs => rw [← b.sum_repr x]
  exact b.linearIndependent.sum_smul_mem_halfOpenParallelepiped_iff

theorem halfOpenParallelepiped_basisFun :
    halfOpenParallelepiped K (Pi.basisFun K ι) = univ.pi fun _ ↦ Ico 0 1 := by
  ext
  simp [halfOpenParallelepiped_basis_eq]

theorem image_halfOpenParallelepiped (f : E →ₗ[K] F) (v : ι → E) :
    f '' halfOpenParallelepiped K v = halfOpenParallelepiped K (f ∘ v) := by
  rw [halfOpenParallelepiped, ← image_comp]
  congr 1 with t
  simp

/-- Reindexing a family of vectors does not change their half-open parallelepiped. -/
@[simp]
theorem halfOpenParallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    halfOpenParallelepiped K (v ∘ e) = halfOpenParallelepiped K v := by
  ext x
  refine (e.arrowCongr (.refl K)).exists_congr fun t ↦ ?_
  simp [← e.sum_comp, e.forall_congr_left]

theorem halfOpenParallelepiped_prod (v : ι → E) (w : ι' → F) :
    halfOpenParallelepiped K (Sum.elim (LinearMap.inl K E F ∘ v) (LinearMap.inr K E F ∘ w)) =
      halfOpenParallelepiped K v ×ˢ halfOpenParallelepiped K w := by
  ext ⟨x, y⟩
  rw [mem_halfOpenParallelepiped_iff, (Equiv.sumArrowEquivProdArrow ι ι' K).exists_congr_left]
  simp [mem_halfOpenParallelepiped_iff, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum,
    and_and_and_comm]

theorem halfOpenParallelepiped_subset_parallelepiped (v : ι → E) :
    halfOpenParallelepiped K v ⊆ parallelepiped K v :=
  image_mono fun _ ht ↦ ⟨fun i ↦ (ht i trivial).1, fun i ↦ (ht i trivial).2.le⟩

variable [IsStrictOrderedRing K]

@[simp]
theorem zero_mem_halfOpenParallelepiped (v : ι → E) : (0 : E) ∈ halfOpenParallelepiped K v :=
  (mem_halfOpenParallelepiped_iff v _).mpr ⟨0, by simp⟩

theorem halfOpenParallelepiped_subset_hull (v : ι → E) :
    halfOpenParallelepiped K v ⊆ (PointedCone.hull K (range v) : Set E) :=
  (halfOpenParallelepiped_subset_parallelepiped v).trans (parallelepiped_subset_hull v)

theorem smul_parallelepiped_subset_halfOpenParallelepiped {c : K} (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    (v : ι → E) : c • parallelepiped K v ⊆ halfOpenParallelepiped K v := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  refine ⟨c • t, fun i _ ↦ ⟨mul_nonneg hc₀ (ht.1 i), ?_⟩, by simp [Finset.smul_sum, smul_smul]⟩
  exact (mul_le_of_le_one_right hc₀ (ht.2 i)).trans_lt hc₁

theorem convex_halfOpenParallelepiped (v : ι → E) : Convex K (halfOpenParallelepiped K v) :=
  (convex_pi fun _ _ ↦ convex_Ico 0 1).linear_image (Fintype.linearCombination K v)

end halfOpenParallelepiped

noncomputable section FundamentalDomain

namespace Module.Basis

variable [IsStrictOrderedRing K] [FloorRing K] (b : Basis ι K E)

/-- The lattice vector obtained by rounding down the coordinates of `m` in the basis `b`. -/
def floor (m : E) : span ℤ (range b) := ∑ i, ⌊b.repr m i⌋ • b.restrictScalars ℤ i

/-- The lattice vector obtained by rounding up the coordinates of `m` in the basis `b`. -/
def ceil (m : E) : span ℤ (range b) := ∑ i, ⌈b.repr m i⌉ • b.restrictScalars ℤ i

@[simp]
theorem repr_floor_apply (m : E) (i : ι) : b.repr (b.floor m) i = ⌊b.repr m i⌋ := by
  simp only [floor, coe_sum, coe_smul_of_tower, restrictScalars_apply, ← Int.cast_smul_eq_zsmul K,
    repr_sum_self]

@[simp]
theorem repr_ceil_apply (m : E) (i : ι) : b.repr (b.ceil m) i = ⌈b.repr m i⌉ := by
  simp only [ceil, coe_sum, coe_smul_of_tower, restrictScalars_apply, ← Int.cast_smul_eq_zsmul K,
    repr_sum_self]

@[simp]
theorem floor_eq_self_of_mem (m : E) (h : m ∈ span ℤ (range b)) : (b.floor m : E) = m := by
  refine b.ext_elem fun i ↦ ?_
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  simp [← hz]

@[simp]
theorem ceil_eq_self_of_mem (m : E) (h : m ∈ span ℤ (range b)) : (b.ceil m : E) = m := by
  refine b.ext_elem fun i ↦ ?_
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  simp [← hz]

/-- The representative `m - b.floor m` of `m` in the half-open parallelepiped spanned by `b`, see
`Module.Basis.fract_mem_halfOpenParallelepiped`. -/
def fract (m : E) : E := m - b.floor m

theorem fract_apply (m : E) : b.fract m = m - b.floor m := rfl

@[simp]
theorem repr_fract_apply (m : E) (i : ι) : b.repr (b.fract m) i = Int.fract (b.repr m i) := by
  simp [fract]

@[simp]
theorem fract_fract (m : E) : b.fract (b.fract m) = b.fract m :=
  b.ext_elem fun _ ↦ by simp

@[simp]
theorem fract_span_add (m : E) {v : E} (h : v ∈ span ℤ (range b)) :
    b.fract (v + m) = b.fract m := by
  refine b.ext_elem fun i ↦ ?_
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  simp [← hz]

@[simp]
theorem fract_add_span (m : E) {v : E} (h : v ∈ span ℤ (range b)) :
    b.fract (m + v) = b.fract m := by
  rw [add_comm, fract_span_add b m h]

variable {b} in
theorem fract_eq_self {x : E} : b.fract x = x ↔ x ∈ halfOpenParallelepiped K b := by
  simp [halfOpenParallelepiped_basis_eq, b.ext_elem_iff]

theorem fract_mem_halfOpenParallelepiped (x : E) : b.fract x ∈ halfOpenParallelepiped K b :=
  fract_eq_self.mp (b.fract_fract x)

theorem fract_eq_fract (m n : E) : b.fract m = b.fract n ↔ -m + n ∈ span ℤ (range b) := by
  rw [← neg_mem_iff]
  simp [b.ext_elem_iff, Int.fract_eq_fract, mem_span_iff_repr_mem, @eq_comm K, neg_add_eq_sub]

/-- The map `Module.Basis.fract` with codomain restricted to the half-open parallelepiped. -/
def fractRestrict (x : E) : halfOpenParallelepiped K b :=
  ⟨b.fract x, b.fract_mem_halfOpenParallelepiped x⟩

@[simp]
theorem fractRestrict_apply (x : E) : (b.fractRestrict x : E) = b.fract x := rfl

theorem fractRestrict_surjective : Function.Surjective b.fractRestrict :=
  fun x ↦ ⟨x, Subtype.ext (fract_eq_self.mpr x.2)⟩

theorem vadd_mem_halfOpenParallelepiped (y : span ℤ (range b)) (x : E) :
    y +ᵥ x ∈ halfOpenParallelepiped K b ↔ y = -b.floor x := by
  rw [← fract_eq_self, vadd_def, vadd_eq_add, fract_span_add b x y.2, fract_apply, Subtype.ext_iff,
    NegMemClass.coe_neg]
  grind

theorem existsUnique_vadd_mem_halfOpenParallelepiped (x : E) :
    ∃! v : span ℤ (range b), v +ᵥ x ∈ halfOpenParallelepiped K b :=
  ⟨-b.floor x, (b.vadd_mem_halfOpenParallelepiped _ x).mpr rfl,
    fun y h ↦ (b.vadd_mem_halfOpenParallelepiped y x).mp h⟩

/-- The half-open parallelepiped spanned by `b` is in bijection with the quotient of `E` by the
lattice spanned by `b`, via `Module.Basis.fractRestrict`. -/
@[simps symm_apply]
def quotientEquiv : E ⧸ span ℤ (range b) ≃ halfOpenParallelepiped K b where
  toFun := Quotient.lift b.fractRestrict fun x y h ↦ by
    rw [Subtype.mk.injEq, b.fractRestrict_apply, b.fractRestrict_apply, b.fract_eq_fract]
    exact QuotientAddGroup.leftRel_apply.mp h
  invFun x := Submodule.Quotient.mk x
  left_inv := Quotient.ind fun x ↦ (Submodule.Quotient.eq _).mpr <| by simp [fract_apply]
  right_inv x := Subtype.ext (fract_eq_self.mpr x.2)

@[simp]
theorem quotientEquiv_apply_mk (x : E) :
    b.quotientEquiv (Submodule.Quotient.mk x) = b.fractRestrict x := rfl

section Unique

variable [Unique ι]

@[simp]
theorem coe_floor_singleton (k : K) : ((Basis.singleton ι K).floor k : K) = ⌊k⌋ :=
  (Basis.singleton ι K).ext_elem fun _ ↦ by simp

@[simp]
theorem fract_singleton (k : K) : (Basis.singleton ι K).fract k = Int.fract k :=
  (Basis.singleton ι K).ext_elem fun _ ↦ by simp

end Unique

end Module.Basis

end FundamentalDomain
