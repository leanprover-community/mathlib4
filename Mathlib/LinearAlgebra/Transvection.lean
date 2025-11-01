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
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.IrrQuadratic
import Mathlib.LinearAlgebra.Dual.BaseChange

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

theorem congr {W : Type*} [AddCommMonoid W] [Module R W]
    (f : Module.Dual R V) (v : V) (e : V ≃ₗ[R] W) :
    e ∘ₗ (transvection f v) ∘ₗ e.symm = transvection (f ∘ₗ e.symm) (e v) := by
  ext; simp [transvection.apply]

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


end LinearEquiv.transvection

section transvection

namespace LinearMap.transvection

open LinearMap LinearEquiv

variable {A : Type*} [CommRing A] [Algebra R A]
variable {W : Type*} [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
  {ε : V →ₗ[R] W} (ibc_VW : IsBaseChange A ε)

theorem baseChange (f : Module.Dual R V) (v : V) :
    (transvection f v).baseChange A = transvection (f.baseChange A) (1 ⊗ₜ[R] v) := by
  ext; simp [transvection, TensorProduct.tmul_add]

variable {W : Type*} [AddCommGroup W] [Module R W]

theorem _root_.LinearEquiv.transvection.baseChange
    {f : Module.Dual R V} {v : V}
    (h : f v = 0) (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange, LinearEquiv.transvection.coe_toLinearMap,
    LinearMap.transvection.baseChange]

end transvection

section determinant

open Polynomial LinearMap

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

  have hn : LinearIndepOn K (id (R := K)) n := by
    simp only [LinearIndepOn, linearIndependent_iff_injective_finsuppLinearCombination,
      ← ker_eq_bot, Submodule.eq_bot_iff, mem_ker]
    intro x hx
    rw [Finsupp.linearCombination_apply] at hx
    let l : hw.extend ha ↪ n := {
      toFun x := ⟨(ker f).subtype x, by simp [n]⟩
      inj' x y h := by
        simpa only [Submodule.subtype_apply, Subtype.mk.injEq, Subtype.coe_inj] using h }
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
    have hm : LinearIndepOn K (id (R := K)) (hw.extend ha) :=
      LinearIndepOn.linearIndepOn_extend hw ha
    simp only [LinearIndepOn, linearIndependent_iff_injective_finsuppLinearCombination,
      ← ker_eq_bot, Submodule.eq_bot_iff, mem_ker] at hm
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
      have : n = Set.range fun (x : n) ↦ (id (R := K)) (x : V) := by simp
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
  suffices LinearMap.toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
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

variable [Module.Free R V] [Module.Finite R V]

theorem det_eq_one_ofDomain [IsDomain R]
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (transvection f v).det = 1 := by
  let K := FractionRing R
  let : Field K := inferInstance
  have : (transvection (f.baseChange K) (1 ⊗ₜ[R] v)).det = 1 :=
    det_eq_one_ofField (by simp [hfv])
  rw [← LinearMap.transvection.baseChange, LinearMap.det_baseChange,
    ← algebraMap.coe_one (R := R) (A := K)] at this
  simpa using this

example {f : Module.Dual R V} {v : V}
    (S : Type*) [CommRing S] [Algebra R S] :
    algebraMap R S (LinearMap.transvection f v).det
      = (LinearMap.transvection (f.baseChange S) (1 ⊗ₜ[R] v)).det := by
  rw [← LinearMap.transvection.baseChange, LinearMap.det_baseChange]

example {n : ℕ} (f : Fin n → R) : Module.Dual R (Fin n → R) := by
  exact Fintype.linearCombination R f

example {n : ℕ} (f : Fin n → R) (v : Fin n → R) :
    (Fin n → R) →ₗ[R] (Fin n → R) :=
  LinearMap.transvection (Fintype.linearCombination R f) v

end determinant

end LinearMap

section

namespace LinearMap.transvection

open scoped TensorProduct

open LinearMap

/- Unused
/-- Base change property of `n → R`, for finite `n`. -/
noncomputable def ibc {n : Type*} [Finite n]
    (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] :
    S ⊗[R] (n → R) ≃ₗ[S] n → S :=
  (IsBaseChange.pi
    (fun _ ↦ Algebra.linearMap R S)
    (fun i ↦ IsBaseChange.linearMap R ((fun _ ↦ S) i))).equiv
-/

variable [Module.Free R V] [Module.Finite R V]

theorem det_eq_one
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (LinearMap.transvection f v).det = 1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · subsingleton
  let b := Module.finBasis R V
  set n := Module.finrank R V
  by_cases hn0 : n = 0
  · suffices v = 0 by simp [this]
    rw [b.ext_elem_iff]
    intro i; exfalso; simpa [hn0] using i.prop
  by_cases hn1 : n = 1
  · suffices transvection f v = LinearMap.id by simp [this]
    ext x
    simp only [apply, id_coe, id_eq, add_eq_left]
    let i : Fin n := ⟨0, by simp [hn1]⟩
    suffices ∀ x, x = b.repr x i • (b i) by
      rw [this x, this v]
      rw [this v] at hfv
      rw [map_smul, smul_eq_mul, mul_comm] at hfv
      simp only [map_smul, smul_eq_mul, ← mul_smul]
      rw [mul_assoc, hfv, mul_zero, zero_smul]
    intro x
    have : x = ∑ i, b.repr x i • b i := (Module.Basis.sum_equivFun b x).symm
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)] at this
    intro j _ hj
    exfalso
    apply hj
    rw [Fin.eq_mk_iff_val_eq]
    simpa [hn1, Nat.lt_one_iff] using j.prop
  have hn2 : 2 ≤ n := by grind
  let e := b.equivFun
  let I := Fin n ⊕ Fin n
  let S := MvPolynomial I ℤ
  -- The correct ring is S ⧸ ⟨p⟩, where p says `fS vS = 0`
  let ε : I → R := Sum.elim (fun i ↦ f (b i)) (fun i ↦ b.coord i v)
  let M := Fin n → S
  let fS (i : Fin n) : S := MvPolynomial.X (Sum.inl i)
  let vS (i : Fin n) : S := MvPolynomial.X (Sum.inr i)
  let tS := LinearMap.transvection (Fintype.linearCombination S fS) vS

  let pS := (Fintype.linearCombination S fS) vS
  have hpS : pS = ∑ x, vS x * fS x := by
    simp [pS, Fintype.linearCombination_apply]
  have hpS' : Fintype.linearCombination S fS vS = MvPolynomial.sum_X_mul_Y (Fin n) ℤ := by
    simp only [MvPolynomial.sum_X_mul_Y]
    rw [Fintype.linearCombination_apply]
    simp_rw [smul_eq_mul, mul_comm, fS, vS]
  let T := S ⧸ Ideal.span {pS}
  let β : S →+* T := Ideal.Quotient.mk _
  let α : S →+* R := ↑(MvPolynomial.aeval ε : S →ₐ[ℤ] R)
  have hαfS (x : Fin n) : α (fS x) = f (b x) := by
    simp only [α, ε, fS, RingHom.coe_coe]
    rw [MvPolynomial.aeval_X]
    simp
  have hαvS (x : Fin n) : α (vS x) = b.repr v x := by
    simp only [α, ε, vS, RingHom.coe_coe]
    rw [MvPolynomial.aeval_X]
    simp
  have αpS : α pS = 0 := by
    simp only [pS, Fintype.linearCombination_apply]
    simp_rw [map_sum, smul_eq_mul, map_mul]
    simp_rw [hαvS, hαfS]
    rw [← hfv]
    conv_rhs => rw [← Module.Basis.sum_equivFun b v, map_sum]
    apply Finset.sum_congr rfl
    aesop
  let γ : T →+* R := Ideal.Quotient.lift _ α (fun p hp ↦ by
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp [map_mul, αpS])
  have hγβ : γ.comp β = α := Ideal.Quotient.lift_comp_mk ..
  let fT := β ∘ fS
  let vT := β ∘ vS
  have hfvT : (Fintype.linearCombination T fT) vT = 0 := by
    simp only [fT, vT]
    simp only [Fintype.linearCombination_apply]
    simp only [Function.comp_apply, smul_eq_mul, ← map_mul]
    rw [← map_sum, ← hpS]
    exact Ideal.Quotient.mk_singleton_self pS
  let tT := LinearMap.transvection (Fintype.linearCombination T fT) vT
  have : IsDomain T := by
    simp only [T, Ideal.Quotient.isDomain_iff_prime]
    suffices Irreducible pS by
      rw [Ideal.span_singleton_prime this.ne_zero, ← irreducible_iff_prime]
      exact this
    simp only [pS, hpS']
    apply MvPolynomial.irreducible_sum_X_mul_Y
    rw [Fin.nontrivial_iff_two_le]
    exact hn2
  let algTR : Algebra T R := RingHom.toAlgebra γ
  let fR := tT.baseChange R
  let j :=   (IsBaseChange.pi
    (fun _ ↦ Algebra.linearMap T R)
    (fun i ↦ IsBaseChange.linearMap T ((fun _ ↦ R) i))).equiv.trans e.symm
  have : LinearMap.transvection f v = j ∘ₗ fR ∘ₗ j.symm := by
    simp only [fR, tT, transvection.baseChange, LinearMap.transvection.congr]
    congr
    · ext x
      simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      set y := j.symm x with hy
      rw [LinearEquiv.eq_symm_apply] at hy
      rw [← hy]
      -- simp only [j, e]
      rw [← Module.Dual.baseChangeHom_apply]
      set lc1S := Fintype.linearCombination S (α := Fin n) (M := S)
      set lc2T := Fintype.linearCombination T (⇑β ∘ fun i ↦ MvPolynomial.X (Sum.inl i))
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, h, h']
      | tmul r t =>
        simp only [Module.Dual.baseChangeHom_apply, Module.Dual.baseChange_apply_tmul]
        simp only [lc2T, Fintype.linearCombination_apply, Finset.sum_smul]
        simp [j, e, IsBaseChange.equiv_tmul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
          map_mul, ← RingHom.comp_apply, hγβ, ← hαfS x]
        ring
    · simp only [LinearEquiv.trans_apply, j, LinearEquiv.eq_symm_apply]
      -- some API is missing
      ext i
      simp [IsBaseChange.equiv, vT, e, RingHom.algebraMap_toAlgebra]
      rw [← RingHom.comp_apply, hγβ]
      simp [α, ε]
      rw [MvPolynomial.aeval_X]
      simp
  rw [this, det_conj]
  simp only [fR, LinearMap.det_baseChange, tT]
  rw [det_eq_one_ofDomain hfvT, map_one]

theorem _root_.LinearEquiv.det_eq_one
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (LinearEquiv.transvection hfv).det = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det, LinearEquiv.transvection.coe_toLinearMap hfv,
      LinearMap.transvection.det_eq_one hfv, Units.val_one]

end transvection

end LinearMap

end

end transvection
