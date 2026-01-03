/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Transvections in a module

* When `f : Module.Dual R V` and `v : V`,
  `LinearMap.transvection f v` is the linear map given by `x ↦ x + f x • v`,

* If, moreover, `f v = 0`, then `LinearEquiv.transvection` shows that it is
  a linear equivalence.

* `LinearMap.transvections R V`: the set of transvections.

* `LinearEquiv.dilatransvections R V`: the set of linear equivalences
whose associated linear map is of the form `LinearMap.transvection f v`.

## Note on terminology

In the mathematical litterature, linear maps of the form `LinearMap.transvection f v`
are only called “transvections” when `f v = 0`. Otherwise, they are sometimes
called “dilations” (especially if `f v ≠ -1`).

The definition is almost the same as that of `Module.preReflection f v`,
up to a sign change, which are interesting when `f v = 2`, because they give “reflections”.

-/

@[expose] public section

namespace LinearMap

open Module

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- The transvection associated with a linear form `f` and a vector `v`.

NB. In mathematics, these linear maps are only called “transvections” when `f v = 0`.
See also `Module.preReflection` for a similar definition, up to a sign. -/
def transvection (f : Dual R V) (v : V) : V →ₗ[R] V where
  toFun x := x + f x • v
  map_add' x y := by simp [add_add_add_comm, add_smul]
  map_smul' r x := by simp [smul_eq_mul, smul_add, mul_smul]

namespace transvection

theorem apply (f : Dual R V) (v x : V) :
    transvection f v x = x + f x • v :=
  rfl

theorem comp_of_left_eq_apply {f : Dual R V} {v w : V} {x : V} (hw : f w = 0) :
    transvection f v (transvection f w x) = transvection f (v + w) x := by
  simp only [transvection, coe_mk, AddHom.coe_mk, map_add,
    map_smul, hw, smul_add, zero_smul, add_zero, add_assoc]

theorem comp_of_left_eq {f : Dual R V} {v w : V} (hw : f w = 0) :
    (transvection f v) ∘ₗ (transvection f w) = transvection f (v + w) := by
  ext; simp [comp_of_left_eq_apply hw]

theorem comp_of_right_eq_apply {f g : Dual R V} {v : V} {x : V} (hf : f v = 0) :
    (transvection f v) (transvection g v x) = transvection (f + g) v x := by
  simp only [transvection, coe_mk, AddHom.coe_mk, map_add, map_smul,
    hf, add_apply, zero_smul, add_zero, add_smul, add_assoc]

theorem comp_of_right_eq {f g : Dual R V} {v : V} (hf : f v = 0) :
    (transvection f v) ∘ₗ (transvection g v) = transvection (f + g) v := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
theorem of_left_eq_zero (v : V) :
    transvection (0 : Dual R V) v = LinearMap.id := by
  ext
  simp [transvection]

@[simp]
theorem of_right_eq_zero (f : Dual R V) :
    transvection f 0 = LinearMap.id := by
  ext
  simp [transvection]

theorem eq_id_of_finrank_le_one
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    [Free R V] [Module.Finite R V] [StrongRankCondition R]
    {f : Dual R V} {v : V} (hfv : f v = 0) (h1 : finrank R V ≤ 1) :
    transvection f v = LinearMap.id := by
  interval_cases h : finrank R V
  · have : Subsingleton V := (finrank_eq_zero_iff_of_free R V).mp h
    simp [Subsingleton.eq_zero v]
  · let b := finBasis R V
    ext x
    suffices f x • v = 0 by
      simp [apply, this]
    let i : Fin (finrank R V) := ⟨0, by simp [h]⟩
    suffices ∀ x, x = b.repr x i • (b i) by
      rw [this v, map_smul, smul_eq_mul, mul_comm] at hfv
      rw [this x, this v, map_smul, smul_eq_mul, ← mul_smul, mul_assoc, hfv, mul_zero, zero_smul]
    intro x
    have : x = ∑ i, b.repr x i • b i := (b.sum_equivFun x).symm
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by grind)] at this

theorem congr {W : Type*} [AddCommMonoid W] [Module R W]
    (f : Dual R V) (v : V) (e : V ≃ₗ[R] W) :
    e ∘ₗ (transvection f v) ∘ₗ e.symm = transvection (f ∘ₗ e.symm) (e v) := by
  ext; simp [transvection.apply]

end LinearMap.transvection

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

namespace LinearEquiv

open LinearMap LinearMap.transvection Module Submodule

/-- The transvection associated with a linear form `f` and a vector `v` such that `f v = 0`. -/
def transvection {f : Dual R V} {v : V} (h : f v = 0) :
    V ≃ₗ[R] V where
  toFun := LinearMap.transvection f v
  invFun := LinearMap.transvection f (-v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    simp [comp_of_left_eq_apply h]
  right_inv x := by
    have h' : f (-v) = 0 := by simp [h]
    simp [comp_of_left_eq_apply h']

namespace transvection

theorem apply {f : Dual R V} {v : V} (h : f v = 0) (x : V) :
    transvection h x = x + f x • v :=
  rfl

@[simp]
theorem coe_toLinearMap {f : Dual R V} {v : V} (h : f v = 0) :
    LinearEquiv.transvection h = LinearMap.transvection f v :=
  rfl

@[simp]
theorem coe_apply {f : Dual R V} {v x : V} {h : f v = 0} :
    LinearEquiv.transvection h x = LinearMap.transvection f v x :=
  rfl

theorem trans_of_left_eq {f : Dual R V} {v w : V}
    (hv : f v = 0) (hw : f w = 0) (hvw : f (v + w) = 0 := by simp [hv, hw]) :
    (transvection hw).trans (transvection hv) = transvection hvw := by
  ext; simp [comp_of_left_eq_apply hw]

theorem trans_of_right_eq {f g : Dual R V} {v : V}
    (hf : f v = 0) (hg : g v = 0) (hfg : (f + g) v = 0 := by simp [hf, hg]) :
    (transvection hg).trans (transvection hf) = transvection hfg := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
theorem of_left_eq_zero (v : V) (hv := LinearMap.zero_apply v) :
    transvection hv = LinearEquiv.refl R V := by
  ext; simp [transvection]

@[simp]
theorem of_right_eq_zero (f : Dual R V) (hf := f.map_zero) :
    transvection hf = LinearEquiv.refl R V := by
  ext; simp [transvection]

theorem symm_eq {f : Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv).symm = transvection hv' := by
  ext;
  simp [LinearEquiv.symm_apply_eq, comp_of_left_eq_apply hv']

theorem inv_eq {f : Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv)⁻¹ = transvection hv' :=
  symm_eq hv

theorem symm_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf).symm = transvection hf' := by
  ext; simp [LinearEquiv.symm_apply_eq, comp_of_right_eq_apply hf]

theorem inv_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf)⁻¹ = transvection hf' :=
  symm_eq' hf

end transvection

variable (R V) in
/-- The set of transvections in the group of linear equivalences -/
def transvections : Set (V ≃ₗ[R] V) :=
  { e | ∃ (f : Dual R V) (v : V) (hfv : f v = 0), e = transvection hfv }

theorem mem_transvections_iff {e : V ≃ₗ[R] V} :
    e ∈ transvections R V ↔
      ∃ (f : Dual R V) (v : V) (hfv : f v = 0), e = LinearEquiv.transvection hfv :=
  Iff.rfl

@[simp] theorem mem_transvections {f : Dual R V} {v : V} (hfv : f v = 0) :
    transvection hfv ∈ transvections R V :=
  ⟨f, v, hfv, rfl⟩

@[simp] theorem refl_mem_transvections :
    refl R V ∈ transvections R V :=
  ⟨0, 0, by simp, by aesop⟩

@[simp] theorem one_mem_transvections :
    1 ∈ transvections R V :=
  refl_mem_transvections

@[simp]
theorem symm_mem_transvections_iff {e : V ≃ₗ[R] V} :
    e.symm ∈ transvections R V ↔ e ∈ transvections R V := by
  suffices ∀ e ∈ transvections R V, e.symm ∈ transvections R V by
    refine ⟨fun h ↦ ?_, this e⟩
    rw [← symm_symm e]
    exact this _ h
  rintro _ ⟨f, v, hv, rfl⟩
  rw [transvection.symm_eq]
  apply mem_transvections

@[simp]
theorem inv_mem_transvections_iff {e : V ≃ₗ[R] V} :
    e.symm ∈ transvections R V ↔ e ∈ transvections R V :=
  symm_mem_transvections_iff

open Pointwise in
theorem transvections_pow_mono :
    Monotone (fun n : ℕ ↦ (transvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_transvections

variable (R V) in
/-- Dilatransvections are linear equivalences `V ≃ₗ[R] V` whose associated linear map are given by
`LinearMap.transvection`, ie, are of the form `x ↦ x + f x • v` for `f : Dual R V` and `v : V`.

Over a division ring, `LinearEquiv.mem_dilatransvections_iff_rank` shows that they correspond
to the linear equivalences which differ from the identity map by a linear map of rank at most 1. -/
def dilatransvections : Set (V ≃ₗ[R] V) :=
  { e : V ≃ₗ[R] V | ∃ (f : Dual R V) (v : V), e = LinearMap.transvection f v }

theorem transvections_subset_dilatransvections :
    transvections R V ⊆ dilatransvections R V := by
  rintro e ⟨f, v, hfv, rfl⟩
  exact ⟨f, v, by simp⟩

@[simp]
theorem refl_mem_dilatransvections : refl R V ∈ dilatransvections R V :=
  transvections_subset_dilatransvections one_mem_transvections

@[simp]
theorem one_mem_dilatransvections : 1 ∈ dilatransvections R V :=
  refl_mem_dilatransvections

@[simp]
theorem symm_mem_dilatransvections_iff {e : V ≃ₗ[R] V} :
    e.symm ∈ dilatransvections R V ↔ e ∈ dilatransvections R V := by
  suffices ∀ e ∈ dilatransvections R V, e.symm ∈ dilatransvections R V by
    refine ⟨by simpa using this e.symm, this e⟩
  rintro e ⟨f, v, he⟩
  use f, - e.symm v
  ext x
  simp only [coe_coe, LinearMap.transvection.apply, smul_neg, ← sub_eq_add_neg,
    symm_apply_eq, map_sub, _root_.map_smul, apply_symm_apply]
  rw [eq_comm, sub_eq_iff_eq_add, ← coe_coe, he, LinearMap.transvection.apply]

@[simp]
theorem inv_mem_dilatransvections_iff {e : V ≃ₗ[R] V} :
    e⁻¹ ∈ dilatransvections R V ↔ e ∈ dilatransvections R V :=
  symm_mem_dilatransvections_iff

open Pointwise in
theorem dilatransvections_pow_mono :
    Monotone (fun n : ℕ ↦ (dilatransvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_dilatransvections

/-- Over a division ring, `dilatransvections` correspond to linear
equivalences `e` such that the linear map `e - id` has rank at most 1.

See also `LinearEquiv.mem_dilatransvections_iff_finrank`. -/
theorem mem_dilatransvections_iff_rank {K : Type*} [DivisionRing K] [Module K V] {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔
      Module.rank K (range ((e : V →ₗ[K] V)- LinearMap.id (R := K))) ≤ 1 := by
  simp only [dilatransvections]
  constructor
  · simp only [Set.mem_setOf_eq]
    rintro ⟨f, v, he⟩
    apply le_trans (rank_mono (t := K ∙ v) ?_)
    · apply le_trans (rank_span_le _) (by simp)
    rintro _ ⟨x, rfl⟩
    simp [mem_span_singleton, he, LinearMap.transvection.apply]
  · intro he
    simp only at he
    simp only [Set.mem_setOf_eq]
    set u := (e : V →ₗ[K] V) - LinearMap.id with hu
    rw [eq_sub_iff_add_eq] at hu
    by_cases hr : Module.rank K (range u) = 0
    · use 0, 0
      ext x
      suffices u x = 0 by simp [← hu, this]
      rw [rank_zero_iff] at hr
      simpa [← Subtype.coe_inj] using Subsingleton.allEq (⟨u x , mem_range_self u x⟩ : range u) 0
    rw [← ne_eq, ← Cardinal.one_le_iff_ne_zero] at hr
    replace he : Module.rank K (range u) = 1 := le_antisymm he hr
    rw [rank_eq_one_iff_finrank_eq_one, finrank_eq_one_iff Unit] at he
    obtain ⟨b⟩ := he
    use (b.coord default) ∘ₗ u.rangeRestrict, b default
    ext x
    rw [← hu, LinearMap.transvection.apply, add_comm]
    suffices u x = b.repr (u.rangeRestrict x) default • b default by
      simp [this]
    suffices u.rangeRestrict x = u x by
      rw [← this, ← Submodule.coe_smul, Subtype.coe_inj]
      nth_rewrite 1 [← b.linearCombination_repr (u.rangeRestrict x)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_eq_single default] <;> simp
    exact codRestrict_apply (range u) u x

open Cardinal in
/-- Over a division ring, `dilatransvections` correspond to linear
equivalences `e` such that the linear map `e - id` has rank at most 1.

See also `LinearEquiv.mem_dilatransvections_iff_rank`. -/
theorem mem_dilatransvections_iff_finrank
    {K : Type*} [DivisionRing K] [Module K V] [Module.Finite K V]
    {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔
      finrank K (range ((e : V →ₗ[K] V)- LinearMap.id (R := K))) ≤ 1 := by
  rw [mem_dilatransvections_iff_rank, finrank, ← one_toNat,
    toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K _) one_lt_aleph0]

end LinearEquiv

section baseChange

open IsBaseChange LinearMap LinearEquiv Module

open scoped TensorProduct

section

variable
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    (A : Type*) [CommSemiring A] [Algebra R A]

theorem LinearMap.transvection.baseChange (f : Dual R V) (v : V) :
    (transvection f v).baseChange A = transvection (f.baseChange A) (1 ⊗ₜ[R] v) := by
  ext; simp [transvection, TensorProduct.tmul_add]

variable {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V →ₗ[R] W} (ibc : IsBaseChange A ε)

theorem IsBaseChange.transvection (f : Dual R V) (v : V) :
    ibc.endHom (transvection f v) = transvection (ibc.toDual f) (ε v) := by
  ext w
  induction w using ibc.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a w hw => simp [hw]
  | tmul x => simp [LinearMap.transvection.apply, endHom_comp_apply, toDual_comp_apply]

end

section

variable {R V A : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [CommRing A] [Algebra R A]
    {f : Module.Dual R V} {v : V} (h : f v = 0)
    {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V →ₗ[R] W} (ibc : IsBaseChange A ε)


theorem LinearEquiv.transvection.baseChange
    (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0 := by simp [Algebra.algebraMap_eq_smul_one]) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange,
    LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.baseChange]

theorem LinearEquiv.dilatransvection.baseChange (e : V ≃ₗ[R] V)
    (he : e ∈ LinearEquiv.dilatransvections R V) :
    e.baseChange R A V V ∈ LinearEquiv.dilatransvections A (A ⊗[R] V) := by
  obtain ⟨f, v, he⟩ := he
  use (f.baseChange A), (1 ⊗ₜ[R] v)
  simp [he, LinearMap.transvection.baseChange]

end

end baseChange

end
