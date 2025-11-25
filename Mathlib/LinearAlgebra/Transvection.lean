/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Transvections in a module

* When `f : Module.Dual R V` and `v : V`,
  `LinearMap.transvection f v` is the linear map given by `x ↦ x + f x • v`,

* `LinearMap.transvection.det` shows that the determinant of
`LinearMap.transvection f v` is equal to `1 + f v`.


* If, moreover, `f v = 0`, then `LinearEquiv.transvection` shows that it is
  a linear equivalence.

* `LinearEquiv.transvection.det` shows that it has determinant `1`.

-/

@[expose] public section

namespace LinearMap

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The transvection associated with a linear form `f` and a vector `v`.

NB. It is only a transvection when `f v = 0`. See also `Module.preReflection`. -/
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

theorem eq_id_of_finrank_le_one
    [Module.Free R V] [Module.Finite R V] [StrongRankCondition R]
    {f : Module.Dual R V} {v : V}
    (hfv : f v = 0) (h1 : Module.finrank R V ≤ 1) :
    transvection f v = LinearMap.id := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton V := Module.subsingleton R V
    subsingleton
  let b := Module.finBasis R V
  rw [Nat.le_one_iff_eq_zero_or_eq_one] at h1
  rcases h1 with h0 | h1
  · suffices v = 0 by simp [this]
    rw [b.ext_elem_iff]
    intro i; exfalso; simpa [h0] using i.prop
  · ext x
    suffices f x • v = 0 by
      simp [apply, this]
    let i : Fin (Module.finrank R V) := ⟨0, by simp [h1]⟩
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
    simpa [h1, Nat.lt_one_iff] using j.prop

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

section baseChange

namespace LinearMap.transvection

open LinearMap LinearEquiv

open scoped TensorProduct

variable {A : Type*} [CommRing A] [Algebra R A]

variable (A) in
theorem baseChange (f : Module.Dual R V) (v : V) :
    (transvection f v).baseChange A = transvection (f.baseChange A) (1 ⊗ₜ[R] v) := by
  ext; simp [transvection, TensorProduct.tmul_add]

theorem _root_.LinearEquiv.transvection.baseChange
    {f : Module.Dual R V} {v : V} (h : f v = 0)
    (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0 := by simp [Algebra.algebraMap_eq_smul_one]) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange,
    LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.baseChange]

open IsBaseChange

variable {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V →ₗ[R] W} (ibc : IsBaseChange A ε)

theorem _root_.IsBaseChange.transvection (f : Module.Dual R V) (v : V) :
    ibc.endHom (transvection f v) = transvection (ibc.toDualHom f) (ε v) := by
  ext w
  induction w using ibc.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a w hw => simp [hw]
  | tmul x => simp [transvection.apply, endHom_comp_apply, toDualHom_comp_apply]

end LinearMap.transvection

end baseChange

section determinant

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
theorem exists_basis_of_pairing_ne_zero
    (hfv : f v ≠ 0) :
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
    grind

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
  obtain ⟨w, hw⟩ : ∃ w, f w = 1 := by
    simp only [ne_eq, DFunLike.ext_iff, not_forall] at hf
    rcases hf with ⟨w, hw⟩
    use (f w)⁻¹ • w
    simp_all
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
  by_cases hfv : f v = 0
  · by_cases hv : v = 0
    · simp [hv]
    by_cases hf : f = 0
    · simp [hf]
    obtain ⟨ι, b, i, j, hi, hj⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    have : DecidableEq ι := Classical.typeDecidableEq ι
    rw [← LinearMap.det_toMatrix b]
    suffices LinearMap.toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
      rw [this, Matrix.det_transvection_of_ne i j hi 1, hfv, add_zero]
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
  · obtain ⟨ι, b, i, hv, hf⟩ := exists_basis_of_pairing_ne_zero hfv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    have : DecidableEq ι := Classical.typeDecidableEq ι
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
    rw [LinearMap.toMatrix_apply, LinearMap.transvection.apply]
    simp [Matrix.diagonal]
    rw [hv, Function.update_apply, Module.Basis.repr_self, Pi.one_apply]
    rw [hf]
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

theorem Module.Free.of_det_ne_one {f : V →ₗ[R] V} (hf : f.det ≠ 1) :
    Module.Free R V := by
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s R V)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

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

-- [Mathlib.LinearAlgebra.Finsupp.LinearCombination]
theorem span_range_eq_top_iff_surjective_finsuppLinearCombination
    {ι : Type*} {v : ι → V} :
    Submodule.span R (Set.range v) = ⊤ ↔
      Function.Surjective (Finsupp.linearCombination R v) := by
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]

theorem span_range_eq_top_iff_surjective_fintypelinearCombination
    {ι : Type*} [Fintype ι] {v : ι → V} :
    Submodule.span R (Set.range v) = ⊤ ↔
      Function.Surjective (Fintype.linearCombination R v) := by
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
----

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
  have hf : ibc.toDualHom fM = f := by
    apply b.ext
    intro i
    rw [← hε, toDualHom_comp_apply, Fintype.linearCombination_apply_single,
      one_smul, RingHom.algebraMap_toAlgebra, hε]
    apply MvPolynomial.aeval_X
  have hv : ε vM = v := by
    rw [of_fintype_basis_eq]
    ext i
    rw [RingHom.algebraMap_toAlgebra]
    simp only [vM, γ, Function.comp_apply]
    apply MvPolynomial.aeval_X
  rw [← hf, ← hv, ← IsBaseChange.transvection, det_endHom, det_ofDomain]
  rw [map_add, map_one, add_right_inj, toDualHom_comp_apply]

variable {f : Module.Dual R V} {v : V} (hfv : f v = 0)
/-- Determinant of a transvection.

It is not necessary to assume that the module is finite and free
because `LinearMap.det` is identically 1 otherwise. -/
theorem _root_.LinearEquiv.det_eq_one
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (LinearEquiv.transvection hfv).det = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det,
    LinearEquiv.transvection.coe_toLinearMap hfv, Units.val_one]
  by_contra! h
  have : Module.Free R V := Module.Free.of_det_ne_one h
  have : Module.Finite R V := finite_of_det_ne_one h
  apply h
  rw [LinearMap.transvection.det, hfv, add_zero]

/-- Transvections in the special linear group. -/
def _root_.SpecialLinearGroup.transvection :
    SpecialLinearGroup R V :=
  ⟨LinearEquiv.transvection hfv, LinearEquiv.det_eq_one hfv⟩

theorem _root_.SpecialLinearGroup.coe_transvection :
    (SpecialLinearGroup.transvection hfv : V ≃ₗ[R] V) = .transvection hfv :=
  rfl

variable (R V) in
/-- The set of transvections in the special linear group -/
abbrev _root_.SpecialLinearGroup.transvections : Set (SpecialLinearGroup R V) :=
  { e | ∃ (f : Module.Dual R V) (v : V) (hfv : f v = 0),
      e = SpecialLinearGroup.transvection hfv }

end transvection

end LinearMap

end determinant

namespace SpecialLinearGroup

section action

open MulAction SubMulAction

instance : SMul (SpecialLinearGroup R V) V where
  smul e v := e v

@[simp] theorem smul_def (e : SpecialLinearGroup R V) (v : V) :
    e • v = (e : V ≃ₗ[R] V) v :=
  rfl

/-- The action of `SpecialLinearGroup R V` on `V`. -/
instance : DistribMulAction (SpecialLinearGroup R V) V where
  smul e v := e v
  one_smul := by simp
  mul_smul := by simp
  smul_zero := by simp
  smul_add := by simp

/-- The action of `SpecialLinearGroup R V` on `V` is `R`-linear. -/
instance : SMulCommClass (SpecialLinearGroup R V) R V where
  smul_comm := by simp

variable (R V) in
def subMulAction : SubMulAction (SpecialLinearGroup R V) V where
  carrier := {v | v ≠ 0}
  smul_mem' e v hv := by simpa using hv

instance :
    MulAction (SpecialLinearGroup R V) {v : V | v ≠ 0} :=
  (subMulAction R V).mulAction

variable (R) in
def subMulAction_fixingSubgroup (W : Submodule R V) :
    SubMulAction (fixingSubgroup (SpecialLinearGroup R V) W.carrier) V where
  carrier := {v | v ∉ W}
  smul_mem' e v hv := fun hev ↦ hv <| by
    rw [← inv_smul_smul e v]
    suffices e⁻¹ • e • v = e • v by rwa [this]
    exact (mem_fixingSubgroup_iff _).mp (inv_mem e.prop) (e • v) hev

instance (W : Submodule R V) :
    MulAction (fixingSubgroup (SpecialLinearGroup R V) W.carrier) {v : V | v ∉ W} :=
  (subMulAction_fixingSubgroup R W).mulAction

theorem smul_eq_iff (e : SpecialLinearGroup R V) (v w : { v : V | v ≠ 0}) :
    e • v = w ↔ e • v.val = w.val := by
  simp only [← Subtype.coe_inj]
  exact Eq.congr_right rfl

end action

section generation

open Module.End Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

/-- An element of the special linear group is exceptional if
  it is a nontrivial homothety modulo the eigenspace for eigenvalue 1. -/
abbrev IsExceptional (e : SpecialLinearGroup K V) : Prop :=
  e ≠ 1 ∧ ∃ a : K, a ≠ 1 ∧ ∀ v, e v - a • v ∈ eigenspace (e : End K V) (1 : K)


open scoped Pointwise

noncomputable def transvection_degree (e : SpecialLinearGroup K V) : ℕ∞ :=
  sInf (Nat.cast '' ({ n : ℕ | e ∈ (transvections K V) ^ n }))

omit [Module.Finite K V]
theorem transvection_degree_one :
    transvection_degree (1 : SpecialLinearGroup K V) = 0 := by
  rw [transvection_degree, ENat.sInf_eq_zero]
  use 0
  simp

theorem finrank_le_transvection_degree_add
    (e : SpecialLinearGroup K V) :
    finrank K V ≤ transvection_degree e +
      finrank K (eigenspace (e : End K V) (1 : K)) := sorry

theorem finrank_lt_transvection_degree_add_of_isExceptional
    (e : SpecialLinearGroup K V) (he : IsExceptional e) :
    finrank K V < transvection_degree e +
      finrank K (eigenspace (e : End K V) (1 : K)) := sorry

theorem _root_.Module.Basis.sumExtend_apply_left {ι K V : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] {v : ι → V}
    (hs : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  simp only [Basis.sumExtend, Equiv.trans_def, Basis.coe_reindex, Basis.coe_extend, Equiv.symm_symm,
    Equiv.coe_trans, Function.comp_apply]
  rfl

theorem exists_mem_transvections_apply_eq_of_indep {u v : V}
    (h : LinearIndependent K ![u, v]) :
    ∃ t ∈ transvections K V, v = t • u := by
  have : ∃ f : Dual K V, f (v - u) = 0 ∧ f u = 1 := by
    replace h : LinearIndepOn K ![u, v] ⊤ :=
      linearIndepOn_iff.mpr fun l a a_1 ↦ h a_1
    set ι := ↑(⊤ : Set (Fin 2)) ⊕ ↑(Basis.sumExtendIndex h)
    set b : Basis ι K V := Module.Basis.sumExtend h with hb
    let i : ι := Sum.inl (⟨0, Set.mem_univ 0⟩)
    let j : ι := Sum.inl (⟨1, Set.mem_univ 1⟩)
    have hi : b i = u := Module.Basis.sumExtend_apply_left h ⟨0, Set.mem_univ 0⟩
    have hj : b j = v := Basis.sumExtend_apply_left h ⟨1, Set.mem_univ 1⟩
    use b.coord i + b.coord j
    rw [← hi, ← hj]
    have hij : i ≠ j := by simp [ne_eq, i, j, Sum.inl_injective.eq_iff]
    simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  obtain ⟨f, hvu, hx⟩ := this
  refine ⟨SpecialLinearGroup.transvection hvu, ⟨f, v - u, hvu, rfl⟩, ?_⟩
  simp [transvection, LinearMap.transvection.apply, hx]

theorem exists_mem_transvections_apply_eq_of_indep'
    {W : Submodule K V} {u v : V}
    (hu : u ∉ W) (hv : u ∉ W)
    (h : LinearIndependent K ![u, v]) :
    ∃ t ∈ transvections K V, t ∈ fixingSubgroup _ W.carrier ∧ v = t • u := by
  sorry /-
  have : ∃ f : Dual K V, W ≤ LinearMap.ker f ∧ f (v - u) = 0 ∧ f u = 1 := by
    replace h : LinearIndepOn K ![u, v] ⊤ :=
      linearIndepOn_iff.mpr fun l a a_1 ↦ h a_1
    set ι := ↑(⊤ : Set (Fin 2)) ⊕ ↑(Basis.sumExtendIndex h)
    set b : Basis ι K V := Module.Basis.sumExtend h with hb
    let i : ι := Sum.inl (⟨0, Set.mem_univ 0⟩)
    let j : ι := Sum.inl (⟨1, Set.mem_univ 1⟩)
    have hi : b i = u := Module.Basis.sumExtend_apply_left h ⟨0, Set.mem_univ 0⟩
    have hj : b j = v := Basis.sumExtend_apply_left h ⟨1, Set.mem_univ 1⟩
    use b.coord i + b.coord j
    rw [← hi, ← hj]
    have hij : i ≠ j := by simp [ne_eq, i, j, Sum.inl_injective.eq_iff]
    simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  obtain ⟨f, hvu, hx⟩ := this
  refine ⟨SpecialLinearGroup.transvection hvu, ⟨f, v - u, hvu, rfl⟩, ?_⟩
  simp [transvection, LinearMap.transvection.apply, hx] -/

section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (W : Submodule R V)

theorem linearIndependent_sum (ι κ : Type*) (b : ι → W) (c : κ → V ⧸ W)
    (hb : LinearIndependent R b) (hc : LinearIndependent R c) :
    LinearIndependent R
      (Sum.elim (fun i ↦ (b i : V)) ((Function.surjInv W.mkQ_surjective) ∘ c)) := by
  rw [linearIndependent_iff]
  intro a ha
  set a' := Finsupp.sumFinsuppLEquivProdFinsupp R a with ha'
  rw [← LinearEquiv.symm_apply_eq] at ha'
  suffices a' = 0 by rw [← ha', this, map_zero]
  rw [Prod.ext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero]
  rw [← ha'] at ha
  -- nonterminal simp
  simp [Finsupp.linearCombination_apply, Finsupp.sum_sumElim] at ha
  suffices a'.2 = 0 by
    simp only [this, and_true]
    rw [linearIndependent_iff] at hb
    specialize hb a'.1
    apply hb
    rw [Finsupp.linearCombination_apply]
    rwa [this, Finsupp.sum_zero_index, add_zero,
      Finsupp.sum_congr (g2 := (fun i a ↦ W.subtype (a • (b i)))) (by simp),
      ← map_finsuppSum, LinearMap.map_eq_zero_iff _ W.subtype_injective] at ha
  replace ha := LinearMap.congr_arg (f := W.mkQ) ha
  simp only [map_add] at ha
  suffices W.mkQ _ = 0 by
    rw [linearIndependent_iff] at hc
    specialize hc a'.2
    apply hc
    rw [Finsupp.linearCombination_apply]
    rwa [this, zero_add, map_finsuppSum, map_zero,
      Finsupp.sum_congr (g2 := fun k a ↦ a • (c k))] at ha
    intro k _
    simp [Function.surjInv_eq W.mkQ_surjective (c k)]
  rw [map_finsuppSum]
  convert Finsupp.sum_zero with i r
  simp only [Function.comp_apply, Sum.elim_inl, map_smul, Submodule.mkQ_apply]
  convert smul_zero _
  simp


variable [Module.Free R W]
    [Module.Free R (V ⧸ W)] [Module.Finite R V]
    (f : V →ₗ[R] V) (hfW : W ≤ W.comap f)

example (hfW : W ≤ W.comap f) : V ⧸ W →ₗ[R] V ⧸ W :=
  Submodule.mapQ W W f hfW

example (hfW : W ≤ W.comap f) : W →ₗ[R] W :=
  f.restrict hfW

#synth Module.Finite R (V ⧸ W)





noncomputable example (ι κ : Type*) (b : Basis ι R W) (c : Basis κ R (V ⧸ W)) :
    Basis (ι ⊕ κ) R V := by
  have : Function.Surjective W.mkQ := by
    exact Submodule.mkQ_surjective W
  let w : V ⧸ W → V := Function.invFun W.mkQ
  let v : (ι ⊕ κ) → V := Sum.elim (fun i ↦ b i) (fun k ↦ Function.invFun W.mkQ (c k))
  apply Basis.mk (v := v)
  · sorry
  · sorry


example : (V ⧸ W) →ₗ[R] V := by
  have := Module.Free.of_basis (Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))


example : f.det = (f.restrict hfW).det * (Submodule.mapQ W W f hfW).det := by
  sorry

end
example (W : Submodule K V) :
    fixingSubgroup (SpecialLinearGroup K V) W.carrier →* SpecialLinearGroup K (V ⧸ W) where
  toFun e := sorry
  map_mul' := sorry
  map_one' := sorry

example {ι : Type*} [Fintype ι] (v : ι → V) :
    Fintype.card ι = finrank K (Submodule.span K (Set.range v)) ↔
      LinearIndependent K v := by
  simp [linearIndependent_iff_card_eq_finrank_span, Set.finrank]

lemma linearIndependent_of_not_mem_span {x y z : V} (hx : x ≠ 0)
    (hz : z ∉ Submodule.span K {x, y}) :
    LinearIndependent K ![x, z] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [and_comm]
  by_contra! h'
  apply hz
  by_cases ht : t = 0
  · exfalso
    apply h' ht
    simpa [ht, hx] using hst
  rw [Submodule.mem_span_insert]
  refine ⟨ -(s / t), 0, Submodule.zero_mem _, ?_⟩
  rw [add_zero, ← sub_eq_zero, neg_smul, sub_neg_eq_add,
    ← smul_eq_zero_iff_right ht, smul_add, smul_smul,
    add_comm, mul_div_cancel₀ s ht, hst]

theorem transvections_isPretransitive (h2 : 2 ≤ finrank K V) :
    MulAction.IsPretransitive (Subgroup.closure (transvections K V)) {v : V | v ≠ 0} where
  exists_smul_eq x y := by
    classical
    wlog h : LinearIndependent K ![x.val , y.val] with hyp
    · suffices ∃ z : V, z ∉ Submodule.span K {x.val, y.val} by
        obtain ⟨z, hz⟩ := this
        have hz0 : z ≠ 0 := fun h ↦ hz <| by
          rw [h]
          exact zero_mem _
        have hxz : LinearIndependent K ![x.val, z] := by
          exact linearIndependent_of_not_mem_span x.prop hz
        have hzy : LinearIndependent K ![z, y.val] := by
          rw [LinearIndependent.pair_symm_iff]
          apply linearIndependent_of_not_mem_span y.prop (y := x.val)
          convert hz using 3
          grind
        obtain ⟨g, hg⟩ := hyp h2 x ⟨z, hz0⟩ hxz
        obtain ⟨h, hh⟩ := hyp h2 ⟨z, hz0⟩ y hzy
        use h * g
        simp [mul_smul, hg, hh]
      suffices Submodule.span K {x.val, y.val} ≠ ⊤ by
        by_contra! hz
        apply this
        rw [eq_top_iff]
        exact fun z _ ↦ hz z
      intro h'
      have : Set.finrank K {x.val, y.val} < 2 := by
        apply Nat.lt_of_le_of_ne _ ?_
        · rw [← Finset.coe_pair]
          exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
        rw [eq_comm]
        simpa [linearIndependent_iff_card_eq_finrank_span, Set.pair_comm] using h
      rw [← not_le] at this
      apply this
      simp only [Set.finrank]
      rwa [h', finrank_top]
    obtain ⟨g, hg, hgxy⟩ := exists_mem_transvections_apply_eq_of_indep h
    use ⟨g, Subgroup.subset_closure hg⟩
    simp only [Subgroup.smul_def, ne_eq, Set.coe_setOf]
    rw [smul_eq_iff g x y, hgxy]

example (W : Submodule K V) :
    Set (fixingSubgroup (SpecialLinearGroup K V) W.carrier) := by
  exact (fixingSubgroup  _ _).subtype ⁻¹' (transvections K V)

open scoped Set.Notation in
theorem transvections_isPretransitive_fixingSubgroup
    (W : Submodule K V) (h2 : 2 ≤ finrank K V) :
    MulAction.IsPretransitive
      (Subgroup.closure
        ((fixingSubgroup (SpecialLinearGroup K V) W.carrier).subtype ⁻¹' (transvections K V)))
      {v : V | v ∉ W} where
  exists_smul_eq x y := by
    classical
    wlog h : LinearIndependent K ![x.val , y.val] with hyp
    · suffices ∃ z : V, z ∉ Submodule.span K {x.val, y.val} by
        obtain ⟨z, hz⟩ := this
        have hz0 : z ≠ 0 := fun h ↦ hz <| by
          rw [h]
          exact zero_mem _
        have hxz : LinearIndependent K ![x.val, z] := by
          exact linearIndependent_of_not_mem_span x.prop hz
        have hzy : LinearIndependent K ![z, y.val] := by
          rw [LinearIndependent.pair_symm_iff]
          apply linearIndependent_of_not_mem_span y.prop (y := x.val)
          convert hz using 3
          grind
        obtain ⟨g, hg⟩ := hyp h2 x ⟨z, hz0⟩ hxz
        obtain ⟨h, hh⟩ := hyp h2 ⟨z, hz0⟩ y hzy
        use h * g
        simp [mul_smul, hg, hh]
      suffices Submodule.span K {x.val, y.val} ≠ ⊤ by
        by_contra! hz
        apply this
        rw [eq_top_iff]
        exact fun z _ ↦ hz z
      intro h'
      have : Set.finrank K {x.val, y.val} < 2 := by
        apply Nat.lt_of_le_of_ne _ ?_
        · rw [← Finset.coe_pair]
          exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
        rw [eq_comm]
        simpa [linearIndependent_iff_card_eq_finrank_span, Set.pair_comm] using h
      rw [← not_le] at this
      apply this
      simp only [Set.finrank]
      rwa [h', finrank_top]
    obtain ⟨g, hg, hgxy⟩ := exists_mem_transvections_apply_eq_of_indep h
    use ⟨g, Subgroup.subset_closure hg⟩
    simp only [Subgroup.smul_def, ne_eq, Set.coe_setOf]
    rw [smul_eq_iff g x y, hgxy]

theorem closure_transvection [Module.Finite K V] :
    Subgroup.closure (transvections K V) = ⊤ := by
  rw [eq_top_iff]
  nontriviality V
  wlog h2 : 2 ≤ Module.finrank K V
  · suffices Subsingleton (SpecialLinearGroup K V) by simp
    rw [not_le, Nat.lt_succ_iff] at h2
    apply subsingleton_of_finrank_eq_one
    apply le_antisymm h2
    rwa [Nat.add_one_le_iff, finrank_pos_iff]
  suffices ∀ (n : ℕ) (e : SpecialLinearGroup K V)
    (hn : n = finrank K (eigenspace (e : End K V) (1 : K))),
      e ∈ Subgroup.closure (transvections K V) by
    intro e _
    apply this _ e rfl
  intro n
  induction n using Nat.strong_decreasing_induction with
  | base =>
    use finrank K V
    intro m hm e he
    rw [gt_iff_lt, he, ← not_le] at hm
    exact hm.elim (Submodule.finrank_le _)
  | step n hind=>
    intro e he
    set W := eigenspace (e : End K V) (1 : K) with hW
    by_cases H : W = ⊤
    · suffices e = 1 by
        rw [this]; exact one_mem _
      ext v
      change (e : End K V) v = v
      conv_rhs => rw [← one_smul K v]
      rw [← mem_eigenspace_iff, ← hW, H]
      exact Submodule.mem_top
    · obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top W H rfl
      have hv' := hv
      rw [hW, mem_eigenspace_iff, one_smul] at hv'
      have H' : finrank K W < finrank K V - 1 := sorry
      -- e' = t f u ∘ e
      -- f = 0 sur W, f u = 0
      -- e' v = (t f u) (e v) = e v + f (e v) • u = v
      -- u = v - e v, f (e v) = f (v) = 1
      have := transvections_isPretransitive h2
      have := this.exists_smul_eq
        ⟨(e : End K V) v, fun h ↦ hv' <| by rw [h, eq_comm];simpa using h⟩
        ⟨v, fun h ↦ hv' <| by rw [h, map_zero]⟩
      obtain ⟨⟨t, ht⟩, htv⟩ := this
      set e' := t * e with he'
      rw [← inv_mul_eq_iff_eq_mul] at he'
      rw [← he']
      apply Subgroup.mul_mem _ (Subgroup.inv_mem _ ht)
      apply hind _ _ e' rfl
      set W' := W ⊔ Submodule.span K {(e : End K V) v - v} with hW'
      rw [gt_iff_lt, he]
      apply Submodule.finrank_lt_finrank_of_lt
      rw [lt_iff_le_and_ne]
      constructor


      have hv' : v ∉ W' := fun h ↦ by
        rw [hW', Submodule.mem_sup] at h
        obtain ⟨w, hw, z, hz, hwz⟩ := h
        simp [Submodule.mem_span_singleton] at hz
        obtain ⟨a, rfl⟩ := hz
        have ha : a ≠ 0 := fun h ↦ by
          apply hv
          rwa [← hwz, h, zero_smul, add_zero]
        sorry
      sorry

end generation

end SpecialLinearGroup

