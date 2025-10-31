/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Transvections

-/

universe u v

namespace LinearMap

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The transvection associated with a linear form `f` and a vector `v`.

NB. It is only a transvection when `f v = 0` -/
def transvection (f : Module.Dual R V) (v : V) : V →ₗ[R] V where
  toFun x := x + f x • v
  map_add' x y := by simp only [map_add]; module
  map_smul' r x := by simp only [map_smul, RingHom.id_apply, smul_eq_mul]; module

namespace transvection

theorem apply (f : Module.Dual R V) (v x : V) :
    transvection f v x = x + f x • v :=
  rfl

theorem comp_of_left_eq_apply {f : Module.Dual R V} {v w : V} {x : V} (hw : f w = 0) :
    transvection f v (transvection f w x) = transvection f (v + w) x := by
  simp only [transvection, coe_mk, AddHom.coe_mk, map_add, map_smul, hw, smul_add]
  module

theorem comp_of_left_eq {f : Module.Dual R V} {v w : V} (hw : f w = 0) :
    (transvection f v) ∘ₗ (transvection f w) = transvection f (v + w) := by
  ext; simp [comp_of_left_eq_apply hw]

theorem comp_of_right_eq_apply {f g : Module.Dual R V} {v : V} {x : V} (hf : f v = 0) :
    (transvection f v) (transvection g v x) = transvection (f + g) v x := by
  simp only [transvection, coe_mk, AddHom.coe_mk, map_add, map_smul, hf, add_apply]
  module

theorem comp_of_right_eq {f g : Module.Dual R V} {v : V} (hf : f v = 0) :
    (transvection f v) ∘ₗ (transvection g v) = transvection (f + g) v := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
theorem of_left_eq_zero (v : V) :
    transvection (0 : Module.Dual R V) v = LinearMap.id := by
  ext
  simp [transvection]

@[simp]
theorem of_right_eq_zero (f : Module.Dual R V) :
    transvection f 0 = LinearMap.id := by
  ext
  simp [transvection]

end LinearMap.transvection

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

namespace LinearEquiv

open LinearMap LinearMap.transvection

/-- The transvection associated with a linear form `f` and a vector `v` such that `f v = 0`. -/
def transvection {f : Module.Dual R V} {v : V} (h : f v = 0) :
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

theorem apply {f : Module.Dual R V} {v : V} (h : f v = 0) (x : V) :
    transvection h x = x + f x • v :=
  rfl

@[simp]
theorem coe_toLinearMap {f : Module.Dual R V} {v : V} (h : f v = 0) :
    LinearEquiv.transvection h = LinearMap.transvection f v :=
  rfl

@[simp]
theorem coe_apply {f : Module.Dual R V} {v x : V} {h : f v = 0} :
    LinearEquiv.transvection h x = LinearMap.transvection f v x :=
  rfl

theorem trans_of_left_eq {f : Module.Dual R V} {v w : V}
    (hv : f v = 0) (hw : f w = 0) (hvw : f (v + w) = 0 := by simp [hv, hw]) :
    (transvection hw).trans (transvection hv) = transvection hvw := by
  ext; simp [comp_of_left_eq_apply hw]

theorem trans_of_right_eq {f g : Module.Dual R V} {v : V}
    (hf : f v = 0) (hg : g v = 0) (hfg : (f + g) v = 0 := by simp [hf, hg]) :
    (transvection hg).trans (transvection hf) = transvection hfg := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
theorem of_left_eq_zero (v : V) (hv := LinearMap.zero_apply v) :
    transvection hv = LinearEquiv.refl R V := by
  ext; simp [transvection]

@[simp]
theorem of_right_eq_zero (f : Module.Dual R V) (hf := f.map_zero) :
    transvection hf = LinearEquiv.refl R V := by
  ext; simp [transvection]

theorem symm_eq {f : Module.Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv).symm = transvection hv' := by
  ext;
  simp [LinearEquiv.symm_apply_eq, comp_of_left_eq_apply hv']

theorem symm_eq' {f : Module.Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf).symm = transvection hf' := by
  ext; simp [LinearEquiv.symm_apply_eq, comp_of_right_eq_apply hf]


-- TODO: mv to somewhere
section Module.Dual.baseChange

open TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- `LinearMap.baseChange` for `Module.Dual`. -/
def _root_.Module.Dual.baseChange (f : Module.Dual R V) :
    Module.Dual A (A ⊗[R] V) :=
  (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap.comp (LinearMap.baseChange A f)

@[simp]
theorem _root_.Module.Dual.baseChange_apply_tmul (f : Module.Dual R V) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ v) = (f v) • a := by
  simp [Module.Dual.baseChange]

def _root_.Module.Dual.congr (e : V ≃ₗ[R] W) :
    Module.Dual R V ≃ₗ[R] Module.Dual R W := by
  exact congrLeft R R e

#check LinearEquiv.baseChange

def _root_.Module.Dual.baseChange_congr (e : V ≃ₗ[R] W) (f : Module.Dual R V) :
    Module.Dual A (A ⊗[R] W) :=
  -- Module.Dual.congr e (Module.Dual.baseChange A f)
  -- f.baseChange A : A ⊗[R] V →ₗ[A] A
  -- A ⊗[R] W ≃ₗ[A] A ⊗[R] V := e.symm.baseChange A
  (f.baseChange A).comp (e.symm.baseChange R A W V).toLinearMap

/-- `Module.Dual.baseChange` as a linear map. -/
def _root_.Module.Dual.baseChangeHom :
    Module.Dual R V →ₗ[R] Module.Dual A (A ⊗[R] V) where
  toFun := Module.Dual.baseChange A
  map_add' := by unfold Module.Dual.baseChange; aesop
  map_smul' r x := by
    ext
    unfold Module.Dual.baseChange
    simp [LinearMap.baseChange_smul, ← TensorProduct.tmul_smul, mul_smul]

@[simp]
theorem _root_.Module.Dual.baseChangeHom_apply (f : Module.Dual R V) :
    Module.Dual.baseChangeHom A f = f.baseChange A :=
  rfl

section group

variable {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (A : Type*) [CommRing A] [Algebra R A]

theorem _root_.Module.Dual.baseChange_sub (f g : Module.Dual R V) :
    Module.Dual.baseChange A (f - g) = Module.Dual.baseChange A f - Module.Dual.baseChange A g := by
  unfold Module.Dual.baseChange; aesop

theorem _root_.Module.Dual.baseChange_neg (f : Module.Dual R V) :
    Module.Dual.baseChange A (-f) = -(Module.Dual.baseChange A f) := by
  unfold Module.Dual.baseChange; aesop

end group

section comp

variable (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem _root_.Module.Dual.baseChange_comp (f : Module.Dual R V) :
    Module.Dual.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V)
      ((f.baseChange A).baseChange B) = f.baseChange B := by
  ext; simp [Module.Dual.congr, congrLeft]

end comp

end Module.Dual.baseChange

section transvection

variable (A : Type*) [CommRing A] [Algebra R A]

theorem _root_.LinearMap.transvection.baseChange (f : Module.Dual R V) (v : V) :
    (LinearMap.transvection f v).baseChange A
      = LinearMap.transvection (f.baseChange A) (1 ⊗ₜ[R] v) := by
  ext; simp [LinearMap.transvection, TensorProduct.tmul_add]

variable {W : Type*} [AddCommGroup W] [Module R W]

theorem baseChange {f : Module.Dual R V} {v : V}
    (h : f v = 0) (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0) :
    (transvection h).baseChange R A V V = transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange, coe_toLinearMap,
    LinearMap.transvection.baseChange]

end transvection

section determinant

open Polynomial

open scoped TensorProduct

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {f : Module.Dual K V} {v : V}

example {W : Type*} [AddCommGroup W] [Module K W] {φ : V →ₗ[K] W} :
    Function.Injective φ ↔ ker φ = ⊥ := by
  exact Iff.symm ker_eq_bot

omit [FiniteDimensional K V] in
theorem LinearIndependent.comp_of_injective
    {ι : Type*} {b : ι → V} (hb : LinearIndependent K b)
    {W : Type*} [AddCommGroup W] [Module K W] {φ : V →ₗ[K] W} (hφ : Function.Injective φ) :
    LinearIndependent K (φ ∘ b) := by
  rw [LinearMap.linearIndependent_iff_of_injOn]
  · exact hb
  · exact fun _ _ _ _ h ↦ hφ h

omit [FiniteDimensional K V] in
/-- In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v = 0`,
there exists a basis `b` with two distinct indices `i`, `j`
such that `v = b i` and `f = b.coord j`. -/
theorem exists_basis_of_pairing_eq_zero
    (hfv : f v = 0) (hf : f ≠ 0) (hv : v ≠ 0) :
    ∃ (n : Type v) (b : Module.Basis n K V) (i j : n),
      i ≠ j ∧ v = b i ∧ f = b.coord j := by
  have : ∃ u : V, f u ≠ 0 := by
    by_contra! hf'
    apply hf
    ext x
    simp [hf']
  obtain ⟨u' : V, hu'⟩ := this
  set u := (f u')⁻¹ • u'
  have hu : f u = 1 := by
    simp [u, inv_mul_cancel₀ hu']
  set W := LinearMap.ker f with W_def
  set w : W := ⟨v, by simp [W_def, hfv]⟩ with w_def
  have hw : LinearIndepOn K _root_.id {w} := by
    simp [linearIndepOn_singleton_iff, id_eq, ne_eq, ← Subtype.coe_inj, w_def, hv]
  set a := Module.Basis.extend hw
  generalize_proofs ha at a
  set n := {u} ∪ (ker f).subtype '' (hw.extend ha)
/-  have hn_disj : Disjoint {u} ((ker f).subtype '' (hw.extend ha)) := by
    simp only [Set.disjoint_right, Set.mem_singleton_iff]
    rintro _ ⟨⟨w, hw⟩, _, rfl⟩ hwu
    apply zero_ne_one (α := K)
    simp only [mem_ker] at hw
    simp only [Submodule.subtype_apply] at hwu
    rw [← hu, ← hw, hwu] -/
  have hn_disj' : u ∉ (ker f).subtype '' (hw.extend ha) := fun h ↦ by
    apply zero_ne_one (α := K)
    obtain ⟨⟨u', hu'⟩, _, rfl⟩ := h
    simp only [mem_ker] at hu'
    rw [← hu', hu]
  have hun : u ∈ n := by simp [n]
  let j : n := ⟨u, hun⟩
  have hj : ↑j = u := rfl
  have hvn : v ∈ n := by
    simp only [n]
    apply Set.mem_union_right
    use w
    refine ⟨?_, rfl⟩
    apply LinearIndepOn.subset_extend hw ha
    simp
  let i : n := ⟨v, hvn⟩
  have hi : ↑i = v := rfl

  have hn : LinearIndepOn K id n := by
    simp only [LinearIndepOn, linearIndependent_iff_injective_finsuppLinearCombination,
      ← ker_eq_bot, Submodule.eq_bot_iff, id_eq, mem_ker]
    intro x hx
    rw [Finsupp.linearCombination_apply] at hx
    let l : hw.extend ha ↪ n := {
      toFun x := ⟨(ker f).subtype x, by simp [n]⟩
      inj' x y h := by
        simpa only [Submodule.subtype_apply, Subtype.mk.injEq, SetLike.coe_eq_coe, Subtype.coe_inj] using h }
    let y : hw.extend ha →₀ K := {
      toFun i := x (l i)
      support := Finset.preimage x.support l l.injective.injOn
      mem_support_toFun i := by simp }
    have hxy : x = y.embDomain l + Finsupp.single j (x j) := by
      ext i
      simp only [Finsupp.coe_add, Pi.add_apply]
      rcases (Set.mem_union _ _ _).mpr i.prop with hi | hi
      · simp only [Set.mem_singleton_iff] at hi
        replace hi : i = j := by rw [← Subtype.coe_inj, hi]
        simp only [hi, Finsupp.single_eq_same, right_eq_add]
        apply Finsupp.embDomain_notin_range
        intro hj'
        apply hn_disj'
        obtain ⟨j', hj'⟩ := hj'
        use j', j'.prop
        simpa only [← Subtype.coe_inj] using hj'
      · obtain ⟨i', hi'_mem, hi'_eq⟩ := hi
        have hi' : i ≠ j := fun h ↦ hn_disj' (by
          rw [← Subtype.coe_inj, eq_comm, ← hi'_eq] at h
          rw [← hj, h]
          exact Set.mem_image_of_mem (⇑(ker f).subtype) hi'_mem)
        rw [Finsupp.single_eq_of_ne hi', add_zero]
        suffices i = l ⟨i', hi'_mem⟩ by
          rw [this, Finsupp.embDomain_apply]
          rfl
        rw [← Subtype.coe_inj, ← hi'_eq]
        rfl
    have hxy' : (ker f).subtype (y.sum fun i a ↦ a • (i : W)) + x j • u = 0 := by
      classical
      rw [← hx, map_finsuppSum]
      conv_rhs => rw [hxy]
      rw [Finsupp.sum_add_index (by simp) (by simp [add_smul]),
          Finsupp.sum_embDomain, Finsupp.sum_single_index] <;>
        simp [l]; rfl
    have hxj : x j = 0 := by
      have hx' := f.congr_arg hxy'
      rw [map_add, map_zero, _root_.map_smul, hu, smul_eq_mul, mul_one] at hx'
      rw [← hx']
      simp
    suffices y = 0 by simpa [this, hxj] using hxy
    simp only [hxj, Finsupp.single_zero, add_zero] at hxy
    simp only [hxy, Finsupp.sum_embDomain] at hx
    simp only [Submodule.subtype_apply, Function.Embedding.coeFn_mk, l] at hx
    have hm : LinearIndepOn K id (hw.extend ha) := LinearIndepOn.linearIndepOn_extend hw ha
    simp only [LinearIndepOn, linearIndependent_iff_injective_finsuppLinearCombination,
      ← ker_eq_bot, Submodule.eq_bot_iff, id_eq, mem_ker] at hm
    simp only [Finsupp.linearCombination, Finsupp.coe_lsum, coe_smulRight, id_coe, id_eq] at hm
    apply hm
    apply Submodule.injective_subtype (ker f)
    rw [map_finsuppSum]
    simpa using hx
  use n
  let b : Module.Basis n K V := Module.Basis.mk hn (by
    -- `n` spans `V`
    intro x _
    set y := x - f x • u with hxy
    have hy : f y = 0 := by simp [y, hu]
    rw [eq_sub_iff_add_eq] at hxy
    rw [← hxy]
    apply Submodule.add_mem
    · rw [← LinearMap.mem_ker] at hy
      let y' : W := ⟨y, hy⟩
      have : n = Set.range fun (x : n) ↦ _root_.id (x : V) := by simp
      rw [← this]
      have : (ker f).subtype '' (hw.extend ha) ⊆ n := by simp [n]
      apply Submodule.span_mono this
      rw [Submodule.span_image]
      rw [← Module.Basis.range_extend hw, Module.Basis.span_eq]
      simpa [this]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, by simpa⟩))
  use b, i, j
  refine ⟨fun h ↦ ?_, ?_, ?_⟩
  · simp only [← Subtype.coe_inj] at h
    apply zero_ne_one (α := K)
    rw [← hu, ← hfv, ← hi, ← hj, h]
  · rw [eq_comm]
    apply Module.Basis.mk_apply hn
  · apply b.ext
    intro k
    by_cases hk : k = j
    · rw [hk, Module.Basis.coord_apply, Module.Basis.repr_self]
      simp [b, hj, hu]
    · rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne' hk]
      suffices ↑k ∈ (ker f).subtype '' (hw.extend ha) by
        obtain ⟨_, _, hy⟩ := this
        simp [b, ← hy]
      apply Or.resolve_left (Set.mem_or_mem_of_mem_union k.prop)
      simp [Set.mem_singleton_iff, ← hj, Subtype.coe_inj, hk]

/-- Transvections have determinant `1`. -/
theorem det_eq_one_ofField {f : Module.Dual K V} {v : V} (hfv : f v = 0) :
    (LinearMap.transvection f v).det = 1 := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨ι, b, i, j, hi, hj⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have : DecidableEq ι := Classical.typeDecidableEq ι
  rw [← LinearMap.det_toMatrix b]
  suffices toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
    rw [this, Matrix.det_transvection_of_ne i j hi 1]
  ext x y
  rw [LinearMap.toMatrix_apply, LinearMap.transvection.apply]
  simp [Matrix.transvection]
  simp [hj.1, hj.2]
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


end Field

theorem _root_.LinearMap.transvection.det_eq_one
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (LinearMap.transvection f v).det = 1 :=
  sorry

theorem det_eq_one {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (transvection hfv).det = 1 := by
  rw [← Units.val_inj, coe_det, transvection.coe_toLinearMap hfv,
      LinearMap.transvection.det_eq_one hfv, Units.val_one]

end determinant

end transvection

end LinearEquiv

