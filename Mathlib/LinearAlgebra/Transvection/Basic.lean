/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Transvections in a module

* When `f : Module.Dual R V` and `v : V`,
  `LinearMap.transvection f v` is the linear map given by `x ↦ x + f x • v`,

* `LinearMap.transvection.det` shows that the determinant of
`LinearMap.transvection f v` is equal to `1 + f v`.

* If, moreover, `f v = 0`, then `LinearEquiv.transvection` shows that it is
  a linear equivalence.

* `LinearEquiv.transvection.det` shows that it has determinant `1`.


## Note on terminology

In the mathematical litterature, linear maps of the form `LinearMap.transvection f v`
are only called “transvections” when `f v = 0`. Otherwise, they are sometimes
called “dilations” (especially if `f v ≠ -1`).

The definition is almost the same as that of `Module.preReflection f v`,
up to a sign change, which are interesting when `f v = 2`, because they give “reflections”.

-/

@[expose] public section

namespace LinearEquiv

open Pointwise LinearMap Submodule MulAction

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)

theorem smul_submodule_def (W : Submodule R V) :
    e • W = map e.toLinearMap W := rfl

theorem mem_stabilizer_submodule_iff_map_eq
    (W : Submodule R V) :
    e ∈ stabilizer (V ≃ₗ[R] V) W ↔ map e.toLinearMap W = W := by
  simp [mem_stabilizer_iff, smul_submodule_def]

variable {P : Submodule R U} {Q : Submodule R V}

/-- The restriction of a linear equivalence to appropriate submodules. -/
def restrict (e : U ≃ₗ[R] V) (h : map e.toLinearMap P = Q) :
    P ≃ₗ[R] Q where
  toLinearMap := LinearMap.restrict e.toLinearMap (by aesop)
  invFun := LinearMap.restrict e.symm.toLinearMap (by aesop)
  left_inv x := by simp [← Subtype.coe_inj]
  right_inv x := by simp [← Subtype.coe_inj]

@[simp]
theorem coe_restrict (e : U ≃ₗ[R] V) (h : map e.toLinearMap P = Q) :
    (restrict e h).toLinearMap = LinearMap.restrict e.toLinearMap (by aesop) :=
  rfl

/-- The fixed submodule of a linear equivalence. -/
def fixedSubmodule (e : V ≃ₗ[R] V) : Submodule R V where
  carrier := { x | e x = x }
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp [map_add, hx, hy]
  zero_mem' := by simp
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at hx
    simp [hx]

@[simp]
theorem mem_fixedSubmodule_iff {e : V ≃ₗ[R] V} {v : V} :
    v ∈ e.fixedSubmodule ↔ e v = v := by
  simp [fixedSubmodule]

theorem fixedSubmodule_eq_ker {R : Type*} [Ring R]
    {V : Type*} [AddCommGroup V] [Module R V] (e : V ≃ₗ[R] V) :
    e.fixedSubmodule = LinearMap.ker ((e : V →ₗ[R] V) - id (R := R)) := by
  ext; simp [sub_eq_zero]

theorem fixedSubmodule_eq_top_iff {e : V ≃ₗ[R] V} :
    e.fixedSubmodule = ⊤ ↔ e = 1 := by
  simp [LinearEquiv.ext_iff, Submodule.ext_iff]

theorem mem_stabilizer_submodule_of_le_fixedSubmodule
    {e : V ≃ₗ[R] V} {W : Submodule R V} (hW : W ≤ e.fixedSubmodule) :
    e ∈ stabilizer (V ≃ₗ[R] V) W := by
  rw [mem_stabilizer_submodule_iff_map_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx : x ∈ W, rfl⟩
    suffices e x = x by simpa only [this, coe_coe]
    rw [← mem_fixedSubmodule_iff]
    exact hW hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    rw [coe_coe, ← mem_fixedSubmodule_iff]
    exact hW hx

theorem mem_stabilizer_fixedSubmodule (e : V ≃ₗ[R] V) :
    e ∈ stabilizer _ e.fixedSubmodule :=
  mem_stabilizer_submodule_of_le_fixedSubmodule (le_refl _)

theorem inf_fixedSubmodule_le_fixedSubmodule_mul (e f : V ≃ₗ[R] V) :
    e.fixedSubmodule ⊓ f.fixedSubmodule ≤ (e * f).fixedSubmodule := by
  intro; aesop

theorem fixedSubmodule_mul_inf_fixedSubmodule_le_fixedSubmodule (e f : V ≃ₗ[R] V) :
    (e * f).fixedSubmodule ⊓ f.fixedSubmodule ≤ e.fixedSubmodule := by
  intro; aesop

theorem fixedSubmodule_mul_inf_fixedSubmodule_le_fixedSubmodule' (e f : V ≃ₗ[R] V) :
    (e * f).fixedSubmodule ⊓ e.fixedSubmodule ≤ f.fixedSubmodule := by
  intro x
  simp only [mem_inf, mem_fixedSubmodule_iff, mul_apply, and_imp]
  intro hefx hex
  nth_rewrite 2 [← hex] at hefx
  simpa using hefx

theorem map_eq_of_mem_fixingSubgroup (W : Submodule R V)
    (he : e ∈ fixingSubgroup _ W.carrier) :
    map e.toLinearMap W = W := by
  ext v
  simp only [mem_fixingSubgroup_iff, carrier_eq_coe, SetLike.mem_coe, LinearEquiv.smul_def] at he
  refine ⟨fun ⟨w, hv, hv'⟩ ↦ ?_, fun hv ↦ ?_⟩
  · simp only [SetLike.mem_coe, coe_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

end LinearEquiv

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

open Submodule LinearMap

theorem apply (f : Dual R V) (v x : V) :
    transvection f v x = x + f x • v :=
  rfl

theorem comp_of_left_eq_apply {f : Dual R V} {v w : V} {x : V} (hw : f w = 0) :
    transvection f v (transvection f w x) = transvection f (v + w) x := by
  simp [transvection, hw, ← add_assoc, add_right_comm]

theorem comp_of_left_eq {f : Dual R V} {v w : V} (hw : f w = 0) :
    (transvection f v) ∘ₗ (transvection f w) = transvection f (v + w) := by
  ext; simp [comp_of_left_eq_apply hw]

theorem comp_smul_smul {f : Dual R V} {v : V} {r s : R} :
    transvection f (r • v) ∘ₗ transvection f (s • v) =
      transvection f ((r + s + s * f v * r) • v) := by
  ext x
  simp only [LinearMap.comp_apply, apply, map_add, map_smul, add_assoc]
  simp only [smul_add, ← mul_smul, ← add_smul, ← mul_add (f x), mul_assoc]

theorem comp_of_right_eq_apply {f g : Dual R V} {v : V} {x : V} (hf : f v = 0) :
    (transvection f v) (transvection g v x) = transvection (f + g) v x := by
  simp [transvection, hf, add_smul, ← add_assoc, add_right_comm]

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

theorem pow {f : Dual R V} {v : V} (hf : f v = 0) (n : ℕ) :
    (transvection f v) ^ n = transvection f (n • v) := by
  induction n with
  | zero => simp [End.one_eq_id]
  | succ n hind =>
    rw [pow_succ, hind, End.mul_eq_comp, comp_of_left_eq hf]
    simp [add_smul]

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

theorem pow {f : Dual R V} {v : V} (hf : f v = 0) (n : ℕ)
    (hfn : f (n • v) = 0 := by simp [map_smul, hf]) :
    (transvection hf) ^ n = transvection hfn := by
  rw [← toLinearMap_inj, ← automorphismGroup.toLinearMapMonoidHom_apply,
    map_pow, automorphismGroup.toLinearMapMonoidHom_apply]
  simp only [coe_toLinearMap, LinearMap.transvection.pow hf]

theorem zpow {f : Dual R V} {v : V} (hf : f v = 0) (n : ℤ)
    (hfn : f (n • v) = 0 := by simp [map_smul, hf]) :
    (transvection hf) ^ n = transvection hfn := by
  induction n using Int.negInduction with
  | nat n => simp only [zpow_natCast, natCast_zsmul, pow hf n]
  | neg hind n =>
    simp only [zpow_neg, zpow_natCast, neg_smul, natCast_zsmul,
      pow hf n]
    exact toLinearMap_inj.mp rfl

theorem symm_eq {f : Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv).symm = transvection hv' := by
  ext;
  simp [LinearEquiv.symm_apply_eq, comp_of_left_eq_apply hv']

theorem symm_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf).symm = transvection hf' := by
  ext; simp [LinearEquiv.symm_apply_eq, comp_of_right_eq_apply hf]

@[simp]
theorem symm_apply {f : Dual R V} {v : V}
    (hv : f v = 0) (x : V) :
    (transvection hv).symm x = x - f x • v := by
  rw [symm_eq, LinearEquiv.transvection.apply, smul_neg, ← sub_eq_add_neg]

theorem congr {W : Type*} [AddCommGroup W] [Module R W]
    {f : Dual R V} {v : V} (hfv : f v = 0) (e : V ≃ₗ[R] W) :
    e.symm ≪≫ₗ (transvection hfv) ≪≫ₗ e =
      transvection (f := f ∘ₗ e.symm) (v := e v) (by simp [hfv]) := by
  rw [← LinearEquiv.toLinearMap_inj]
  simp only [← LinearMap.transvection.congr, ← comp_coe, coe_toLinearMap]

end transvection

theorem mem_fixedSubmodule_transvection_iff {f : Dual R V} {v : V} {hfv : f v = 0} {x : V} :
    x ∈ fixedSubmodule (transvection hfv) ↔ f x • v = 0 := by
  simp only [mem_fixedSubmodule_iff, transvection.apply, add_eq_left]

theorem ker_le_fixedSubmodule_transvection {f : Dual R V} {v : V} (hfv : f v = 0) :
    LinearMap.ker f ≤ (transvection hfv).fixedSubmodule := by
  intro x hx
  rw [mem_ker] at hx
  rw [mem_fixedSubmodule_iff, transvection.apply]
  simp [hx]

section dilatransvections

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

@[simp] theorem one_mem_transvections :
    1 ∈ transvections R V :=
  ⟨0, 0, by simp, by aesop⟩

@[simp]
theorem inv_mem_transvections_iff {e : V ≃ₗ[R] V} :
    e⁻¹ ∈ transvections R V ↔ e ∈ transvections R V := by
  suffices ∀ e ∈ transvections R V, e⁻¹ ∈ transvections R V by
    refine ⟨fun h ↦ ?_, this e⟩
    rw [← inv_inv e]
    exact this _ h
  rintro _ ⟨f, v, hv, rfl⟩
  have : (LinearEquiv.transvection hv)⁻¹ = (LinearEquiv.transvection hv).symm := by
    rfl
  rw [this, LinearEquiv.transvection.symm_eq]
  apply mem_transvections

example (e : V ≃ₗ[R] V) (x : V) :
    e x = e.toLinearMap x := by
  rw [@coe_coe]

theorem toLinearMap_pow (e : V ≃ₗ[R] V) (n : ℕ) :
    (e ^ n) = (e.toLinearMap ^ n) := by
  induction n with
  | zero => simp
  | succ n hind => simp [pow_succ]

@[simp]
theorem coe_toLinearMap_pow (e : V ≃ₗ[R] V) (n : ℕ) :
    (e ^ n : V ≃ₗ[R] V) = (e ^ n : V →ₗ[R] V) := by
  induction n with
  | zero => simp [End.one_eq_id]
  | succ n hind => simp [pow_succ, hind]

theorem toLinearMap_pow_apply (e : V ≃ₗ[R] V) (n : ℕ) (x : V) :
    (e ^ n) x = (e.toLinearMap ^ n) x := by
  simp only [← coe_coe, coe_toLinearMap_pow]

theorem pow_mem_transvections {e : V ≃ₗ[R] V} {n : ℕ}
    (he : e ∈ transvections R V) :
    e ^ n ∈ transvections R V := by
  obtain ⟨f, v, hfv, rfl⟩ := he
  refine ⟨f, n • v, by simp [hfv], ?_⟩
  rw [← toLinearMap_inj, coe_toLinearMap_pow, transvection.coe_toLinearMap,
    transvection.coe_toLinearMap, pow hfv]

theorem zpow_mem_transvections {e : V ≃ₗ[R] V} {n : ℤ}
    (he : e ∈ transvections R V) :
    e ^ n ∈ transvections R V := by
  induction n using Int.negInduction with
  | nat n => exact pow_mem_transvections he
  | neg hind n =>
    simp only [zpow_neg, zpow_natCast, inv_mem_transvections_iff]
    exact hind n

open Pointwise in
theorem transvections_pow_mono :
    Monotone (fun n : ℕ ↦ (transvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_transvections

variable (R V) in
/-- Dilatransvections: linear equivalences which differ
from the identity by a linear map of rank at most 1. -/
def dilatransvections :=
  { e : V ≃ₗ[R] V | ∃ (f : Dual R V) (v : V), e = LinearMap.transvection f v }

theorem transvections_subset_dilatransvections :
    transvections R V ⊆ dilatransvections R V := by
  rintro e ⟨f, v, hfv, rfl⟩
  exact ⟨f, v, by rw [transvection.coe_toLinearMap]⟩

theorem one_mem_dilatransvections : 1 ∈ dilatransvections R V :=
  transvections_subset_dilatransvections one_mem_transvections

theorem transvection_mem_transvections {f : Dual R V} {v : V} {hfv : f v = 0} :
    transvection hfv ∈ transvections R V :=
  ⟨f, v, hfv, rfl⟩

theorem transvection_mem_dilatransvections {f : Dual R V} {v : V} (hfv : f v = 0) :
    transvection hfv ∈ dilatransvections R V :=
  transvections_subset_dilatransvections transvection_mem_transvections

theorem inv_mem_dilatransvections_iff (e : V ≃ₗ[R] V) :
    e⁻¹ ∈ dilatransvections R V ↔ e ∈ dilatransvections R V := by
  suffices ∀ e ∈ dilatransvections R V, e⁻¹ ∈ dilatransvections R V by
    refine ⟨by simpa using this e⁻¹, this e⟩
  rintro e ⟨f, v, he⟩
  use f, - e⁻¹ v
  ext x
  simp only [coe_coe, coe_inv, LinearMap.transvection.apply, smul_neg, ← sub_eq_add_neg,
    symm_apply_eq, map_sub, _root_.map_smul, apply_symm_apply]
  rw [eq_comm, sub_eq_iff_eq_add, ← coe_coe, he, LinearMap.transvection.apply]

/-- The dilatransvection associated with a linear form `f`
and a vector `v` such that `1 + f v` is a unit. -/
noncomputable def dilatransvection {f : Dual R V} {v : V} (h : IsUnit (1 + f v)) :
    V ≃ₗ[R] V where
  toFun := LinearMap.transvection f v
  invFun := LinearMap.transvection f (-h.unit⁻¹ • v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    -- Is this better than
    nth_rewrite 3 [← one_smul R v]
    rw [← LinearMap.comp_apply, Units.smul_def, LinearMap.transvection.comp_smul_smul]
    simp only [Units.val_neg, one_mul, mul_neg, ← sub_eq_add_neg]
    suffices (-h.unit⁻¹) + 1 - f v * (h.unit⁻¹) = 0 by simp [this]
    rw [sub_eq_zero, neg_add_eq_iff_eq_add]
    nth_rewrite 1 [← one_mul (h.unit⁻¹), Units.val_mul, ← add_mul]
    simp
    -- that other proof ?
/-    -- maybe one wants a general composition lemma
    simp only [LinearMap.transvection.apply, add_assoc, add_eq_left,
      Units.smul_def]
    rw [smul_smul, ← add_smul]
    convert zero_smul R v
    rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
    nth_rewrite 2 [← mul_one (f x)]
    rw [← mul_add]
    nth_rewrite 1 [← mul_one (f x), mul_assoc, ← mul_add]
    simp-/
  right_inv x := by
    simp only [LinearMap.transvection.apply, add_assoc, add_eq_left,
      Units.smul_def]
    rw [smul_smul, ← add_smul]
    convert zero_smul R v
    rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
    nth_rewrite 2 [← mul_one (f x)]
    rw [mul_assoc, ← mul_add, ← mul_add]
    convert mul_zero _
    rw [← add_assoc, add_comm _ 1, add_assoc]
    nth_rewrite 1 [← mul_one (-h.unit⁻¹), Units.val_mul, Units.val_one, ← mul_add]
    simp

@[simp]
theorem dilatransvection.coe_toLinearMap {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} :
    (dilatransvection h).toLinearMap = LinearMap.transvection f v :=
  rfl

theorem dilatransvection.apply {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} {x : V} :
    dilatransvection h x = x + f x • v := by
  simp [dilatransvection, LinearMap.transvection.apply]

@[simp]
theorem dilatransvection_mem_dilatransvections {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} :
    dilatransvection h ∈ dilatransvections R V := by
  simp only [dilatransvections, Set.mem_setOf_eq]
  refine ⟨f, v, by simp⟩

open Pointwise in
theorem dilatransvections_pow_mono :
    Monotone (fun n : ℕ ↦ (dilatransvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_dilatransvections

section divisionRing

variable {K : Type*} [DivisionRing K] [Module K V]

/-- Over a division ring, `dilatransvections` correspond to linear
equivalences `e` such that the linear map `e - id` has rank at most 1. -/
theorem mem_dilatransvections_iff_rank {e : V ≃ₗ[K] V} :
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
equivalences `e` such that the linear map `e - id` has rank at most 1. -/
theorem mem_dilatransvections_iff_finrank [Module.Finite K V] {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔
      finrank K (range ((e : V →ₗ[K] V)- LinearMap.id (R := K))) ≤ 1 := by
  rw [mem_dilatransvections_iff_rank, finrank, ← one_toNat,
    toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K _) one_lt_aleph0]

theorem mem_dilatransvections_iff_finrank_quotient [Module.Finite K V] {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔ finrank K (V ⧸ e.fixedSubmodule) ≤ 1 := by
  rw [mem_dilatransvections_iff_finrank, ← (quotKerEquivRange _).finrank_eq,
    ← fixedSubmodule_eq_ker]

theorem mem_dilatransvections_iff_rank_quotient {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔ Module.rank K (V ⧸ e.fixedSubmodule) ≤ 1 := by
  rw [mem_dilatransvections_iff_rank, ← (quotKerEquivRange _).rank_eq, ← fixedSubmodule_eq_ker]

variable (e f : V ≃ₗ[K] V)

open Pointwise MulAction

theorem mem_stabilizer_submodule {W : Submodule K V} {u : V ≃ₗ[K] V} :
    u ∈ stabilizer (V ≃ₗ[K] V) W ↔ map u.toLinearMap W = W := by
  rfl

/-- When `u : V ≃ₗ[K] V` maps a submodule `W` into itself,
this is the induced linear equivalence of `V ⧸ W`, as a group morphism. -/
def reduce (W : Submodule K V) : stabilizer (V ≃ₗ[K] V) W →* (V ⧸ W) ≃ₗ[K] (V ⧸ W) where
  toFun u := Quotient.equiv W W u.val u.prop
  map_mul' u v := by
    ext x
    obtain ⟨y, rfl⟩ := W.mkQ_surjective x
    simp
  map_one' := by aesop

@[simp]
theorem reduce_mk (W : Submodule K V) (u : stabilizer (V ≃ₗ[K] V) W) (x : V) :
    reduce W u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u.val x) :=
  rfl

theorem reduce_mkQ (W : Submodule K V) (u : stabilizer (V ≃ₗ[K] V) W) (x : V) :
    reduce W u (W.mkQ x) = W.mkQ (u.val x) :=
  rfl

/-- The linear equivalence deduced from `e : V ≃ₗ[K] V`
by passing to the quotient by `e.fixedSubmodule`. -/
def fixedReduce : (V ⧸ e.fixedSubmodule) ≃ₗ[K] V ⧸ e.fixedSubmodule :=
  reduce e.fixedSubmodule ⟨e, e.mem_stabilizer_fixedSubmodule⟩

@[simp]
theorem fixedReduce_mk (x : V) :
    fixedReduce e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) :=
  rfl

@[simp]
theorem fixedReduce_mkQ (x : V) :
    fixedReduce e (e.fixedSubmodule.mkQ x) = e.fixedSubmodule.mkQ (e x) :=
  rfl

theorem fixedReduce_eq_smul_iff (e : V ≃ₗ[K] V) (a : K) :
    (∀ x, e.fixedReduce x = a • x) ↔
      ∀ v, e v - a • v ∈ e.fixedSubmodule := by
  simp_rw [← e.fixedSubmodule.ker_mkQ, mem_ker, map_sub, ← fixedReduce_mkQ, sub_eq_zero]
  constructor
  · intro H x; simp [H]
  · intro H x
    have ⟨y, hy⟩ := e.fixedSubmodule.mkQ_surjective x
    rw [← hy]
    apply H

theorem fixedReduce_eq_one (e : V ≃ₗ[K] V) :
    e.fixedReduce = LinearEquiv.refl K _ ↔ ∀ v, e v - v ∈ e.fixedSubmodule := by
  simpa [LinearEquiv.ext_iff] using fixedReduce_eq_smul_iff e 1

/-- Characterization of transvections within dilatransvections. -/
theorem mem_transvections_iff' [Module.Finite K V] (e : V ≃ₗ[K] V) :
    e ∈ transvections K V ↔ e ∈ dilatransvections K V ∧ e.fixedReduce = 1 := by
  refine ⟨fun ⟨f, v, hfv, he⟩ ↦ ?_, fun ⟨he, he'⟩ ↦ ?_⟩
  · constructor
    · rw [he]
      exact transvection_mem_dilatransvections hfv
    · rw [one_eq_refl, fixedReduce_eq_one, he]
      intro x
      apply ker_le_fixedSubmodule_transvection hfv
      rw [transvection.apply]
      simp [hfv]
  · by_cases he_one : e = 1
    · use 0, 0, by simp, by aesop
    have hefixed_ne_top : e.fixedSubmodule ≠ ⊤ := by
      rwa [ne_eq, fixedSubmodule_eq_top_iff]
    obtain ⟨w : V, hw : w ∉ e.fixedSubmodule⟩ :=
      SetLike.exists_not_mem_of_ne_top e.fixedSubmodule hefixed_ne_top rfl
    obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
    rw [mem_dilatransvections_iff_finrank_quotient] at he
    have hf' : e.fixedSubmodule = LinearMap.ker f := by
      suffices finrank K (V ⧸ LinearMap.ker f) = 1 by
        apply Submodule.eq_of_le_of_finrank_le
        · intro x
          rw [mem_ker, ← Submodule.mem_bot K, ← hf]
          exact mem_map_of_mem
        rw [← Nat.add_le_add_iff_right, finrank_quotient_add_finrank] at he
        have := (LinearMap.ker f).finrank_quotient_add_finrank
        linarith
      rw [← Nat.add_left_inj, Submodule.finrank_quotient_add_finrank]
      rw [← f.finrank_ker_add_one_of_ne_zero, add_comm]
      aesop
    have eq_top : e.fixedSubmodule ⊔ Submodule.span K {w} = ⊤ :=
      Submodule.sup_span_eq_top he hw
    set v := (f w)⁻¹ • (e w - w)
    suffices hfv : f v = 0 by
      use f, v, hfv
      rw [← LinearEquiv.toLinearMap_inj,
        ← sub_eq_zero, ← LinearMap.ker_eq_top, eq_top_iff, ← eq_top]
      simp only [LinearEquiv.transvection.coe_toLinearMap,
        sup_le_iff, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro x hx
        suffices f x = 0 by
          simpa [this, LinearMap.transvection.apply, sub_eq_zero] using hx
        rwa [hf', LinearMap.mem_ker] at hx
      · simp only [v, LinearMap.transvection.apply]
        aesop
    suffices e w - w ∈ LinearMap.ker f by
      simp only [LinearMap.mem_ker, map_sub] at this
      simp only [v, LinearMap.map_smul, map_sub, this, smul_zero]
    rw [← hf', ← Submodule.ker_mkQ e.fixedSubmodule, LinearMap.mem_ker]
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_sub]
    simp only [← fixedReduce_mk, sub_eq_zero]
    simp [he']

theorem fixingSubgroup_le_stabilizer (W : Submodule K V) :
    fixingSubgroup (V ≃ₗ[K] V) (W : Set V) ≤ stabilizer _ W := by
  intro u
  rw [mem_stabilizer_iff, SetLike.ext'_iff, coe_pointwise_smul,
    ← mem_stabilizer_iff]
  apply MulAction.fixingSubgroup_le_stabilizer

end divisionRing

end LinearEquiv.dilatransvections

section baseChange

open IsBaseChange LinearMap LinearEquiv Module

open scoped TensorProduct

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

theorem LinearEquiv.transvection.baseChange
    {R V A : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [CommRing A] [Algebra R A]
    {f : Module.Dual R V} {v : V} (h : f v = 0)
    (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0 := by simp [Algebra.algebraMap_eq_smul_one]) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange,
    LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.baseChange]

end baseChange

section determinant

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

namespace LinearMap.transvection

open Polynomial

open scoped TensorProduct

section Field

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {f : Module.Dual K V} {v : V}

/-- In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v ≠ 0`,
there exists a basis `b` with an index `i`
such that `v = b i` and `f = (f v) • b.coord i`. -/
theorem exists_basis_of_pairing_ne_zero (hfv : f v ≠ 0) :
    ∃ (n : Set V) (b : Module.Basis n K V) (i : n),
      v = b i ∧ f = (f v) • b.coord i := by
  set b₁ := Module.Basis.ofVectorSpace K (LinearMap.ker f)
  set s : Set V := (LinearMap.ker f).subtype '' Set.range b₁
  have hs : Submodule.span K s = LinearMap.ker f := by
    simp only [s, Submodule.span_image]
    simp
  set n := insert v s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hfv]
  have H₂ : ⊤ ≤ Submodule.span K n := by
    rintro x -
    simp only [n, Submodule.mem_span_insert']
    use -f x / f v
    simp only [hs, mem_ker, map_add, map_smul, smul_eq_mul]
    field
  set b := Module.Basis.mk H₁ (by simpa using H₂)
  set i : n := ⟨v, s.mem_insert v⟩
  have hi : b i = v := by simp [b, i]
  refine ⟨n, b, i, by simp [b, i], ?_⟩
  rw [← hi]
  apply b.ext
  intro j
  by_cases h : i = j
  · simp [h]
  · suffices f (b j) = 0 by
      simp [Finsupp.single_eq_of_ne h, this]
    rw [← LinearMap.mem_ker, ← hs, Module.Basis.coe_mk]
    apply Submodule.subset_span
    apply Or.resolve_left (Set.mem_insert_iff.mpr j.prop)
    simp [← hi, b, Subtype.coe_inj, Ne.symm h]

/-- In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v = 0`,
there exists a basis `b` with two distinct indices `i`, `j`
such that `v = b i` and `f = b.coord j`. -/
theorem exists_basis_of_pairing_eq_zero
    (hfv : f v = 0) (hf : f ≠ 0) (hv : v ≠ 0) :
    ∃ (n : Set V) (b : Module.Basis n K V) (i j : n),
      i ≠ j ∧ v = b i ∧ f = b.coord j := by
  lift v to LinearMap.ker f using hfv
  have : LinearIndepOn K _root_.id {v} := by simpa using hv
  set b₁ : Module.Basis _ K (LinearMap.ker f) := .extend this
  obtain ⟨w, hw⟩ := (surjective_iff_ne_zero.mpr hf) 1
  set s : Set V := (LinearMap.ker f).subtype '' Set.range b₁
  have hs : Submodule.span K s = LinearMap.ker f := by
    simp only [s, Submodule.span_image]
    simp
  have hvs : ↑v ∈ s := by
    refine ⟨v, ?_, by simp⟩
    simp [b₁, this.subset_extend _ _]
  set n := insert w s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hw]
  have H₂ : ⊤ ≤ Submodule.span K n := by
    rintro x -
    simp only [n, Submodule.mem_span_insert']
    use -f x
    simp [hs, hw]
  set b := Module.Basis.mk H₁ (by simpa using H₂)
  refine ⟨n, b, ⟨v, by simp [n, hvs]⟩, ⟨w, by simp [n]⟩, ?_, by simp [b], ?_⟩
  · apply_fun (f ∘ (↑))
    simp [hw]
  · apply b.ext
    intro i
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    simp only [b, Module.Basis.mk_apply]
    rcases i with ⟨x, rfl | ⟨x, hx, rfl⟩⟩
    · simp [hw]
    · suffices x ≠ w by simp [this]
      apply_fun f
      simp [hw]

/-- Determinant of transvections, over a field.

See `LinearMap.Transvection.det` for the general result. -/
theorem det_ofField [FiniteDimensional K V] (f : Module.Dual K V) (v : V) :
    (LinearMap.transvection f v).det = 1 + f v := by
  classical
  by_cases hfv : f v = 0
  · by_cases hv : v = 0
    · simp [hv]
    by_cases hf : f = 0
    · simp [hf]
    obtain ⟨ι, b, i, j, hi, hj⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← LinearMap.det_toMatrix b]
    suffices LinearMap.toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
      rw [this, Matrix.det_transvection_of_ne i j hi 1, hfv, add_zero]
    ext x y
    rw [LinearMap.toMatrix_apply, LinearMap.transvection.apply, Matrix.transvection]
    simp only [hj.2, Module.Basis.coord_apply, Module.Basis.repr_self, hj.1, map_add, map_smul,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Matrix.add_apply]
    apply congr_arg₂
    · by_cases h : x = y
      · rw [h]; simp
      · rw [Finsupp.single_eq_of_ne h, Matrix.one_apply_ne h]
    · by_cases h : i = x ∧ j = y
      · rw [h.1, h.2]; simp
      · rcases not_and_or.mp h with h' | h' <;>
          simp [Finsupp.single_eq_of_ne' h',
            Finsupp.single_eq_of_ne h',
            Matrix.single_apply_of_ne (h := h)]
  · obtain ⟨ι, b, i, hv, hf⟩ := exists_basis_of_pairing_ne_zero hfv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← LinearMap.det_toMatrix b]
    suffices LinearMap.toMatrix b b (LinearMap.transvection f v) =
      Matrix.diagonal (Function.update 1 i (1 + f v)) by
      rw [this]
      simp only [Matrix.det_diagonal]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Function.update_of_ne hj]
      · simp
    ext x y
    rw [LinearMap.toMatrix_apply, LinearMap.transvection.apply, Matrix.diagonal]
    simp only [map_add, Module.Basis.repr_self, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hv, Function.update_apply, Module.Basis.repr_self, Pi.one_apply, hf]
    simp only [smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
    split_ifs with hxy hxi
    · simp [← hxy, hxi]
    · rw [Finsupp.single_eq_of_ne hxi]; simp [hxy]
    · rw [Finsupp.single_eq_of_ne hxy, zero_add, mul_assoc]
      convert mul_zero _
      by_cases hxi : x = i
      · simp [← hxi, Finsupp.single_eq_of_ne hxy]
      · simp [Finsupp.single_eq_of_ne hxi]

end Field

/-- Determinant of a transvection, over a domain.

See `LinearMap.transvection.det` for the general case. -/
theorem det_ofDomain [Module.Free R V] [Module.Finite R V] [IsDomain R]
    (f : Module.Dual R V) (v : V) :
    (transvection f v).det = 1 + f v := by
  let K := FractionRing R
  let : Field K := inferInstance
  apply FaithfulSMul.algebraMap_injective R K
  have := det_ofField (f.baseChange K) (1 ⊗ₜ[R] v)
  rw [← LinearMap.transvection.baseChange, LinearMap.det_baseChange,
    ← algebraMap.coe_one (R := R) (A := K)] at this
  simpa [Algebra.algebraMap_eq_smul_one, add_smul] using this

open IsBaseChange

theorem det [Module.Free R V] [Module.Finite R V]
    (f : Module.Dual R V) (v : V) :
    (LinearMap.transvection f v).det = 1 + f v := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · subsingleton
  let b := Module.finBasis R V
  set n := Module.finrank R V
  let S := MvPolynomial (Fin n ⊕ Fin n) ℤ
  let γ : S →+* R :=
    (MvPolynomial.aeval (Sum.elim (fun i ↦ f (b i)) (fun i ↦ b.coord i v)) :
      MvPolynomial (Fin n ⊕ Fin n) ℤ →ₐ[ℤ] R)
  have : IsDomain S := inferInstance
  let _ : Algebra S R := RingHom.toAlgebra γ
  let _ : Module S V := Module.compHom V γ
  have _ : IsScalarTower S R V := IsScalarTower.of_compHom S R V
  have ibc := IsBaseChange.of_fintype_basis S b
  set ε := Fintype.linearCombination S (fun i ↦ b i)
  set M := Fin n → S
  have hε (i) : ε (Pi.single i 1) = b i := by
    rw [Fintype.linearCombination_apply_single, one_smul]
  let fM : Module.Dual S M :=
    Fintype.linearCombination S fun i ↦ MvPolynomial.X (Sum.inl i)
  let vM : M := fun i ↦ MvPolynomial.X (Sum.inr i)
  have hf : ibc.toDual fM = f := by
    apply b.ext
    intro i
    rw [← hε, toDual_comp_apply, Fintype.linearCombination_apply_single,
      one_smul, RingHom.algebraMap_toAlgebra, hε]
    apply MvPolynomial.aeval_X
  have hv : ε vM = v := by
    rw [of_fintype_basis_eq]
    ext i
    rw [RingHom.algebraMap_toAlgebra]
    simp only [vM, γ, Function.comp_apply]
    apply MvPolynomial.aeval_X
  rw [← hf, ← hv, ← IsBaseChange.transvection, det_endHom, det_ofDomain]
  rw [map_add, map_one, add_right_inj, toDual_comp_apply]

/-- Determinant of a transvection.

It is not necessary to assume that the module is finite and free
because `LinearMap.det` is identically 1 otherwise. -/
theorem _root_.LinearEquiv.transvection.det_eq_one
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (LinearEquiv.transvection hfv).det = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det,
    LinearEquiv.transvection.coe_toLinearMap hfv, Units.val_one]
  by_contra! h
  have : Module.Free R V := Module.Free.of_det_ne_one h
  have : Module.Finite R V := finite_of_det_ne_one h
  apply h
  rw [LinearMap.transvection.det, hfv, add_zero]

end transvection

end LinearMap

end determinant

end
