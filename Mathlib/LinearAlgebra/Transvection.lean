/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

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

namespace LinearMap

open Module

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- The transvection associated with a linear form `f` and a vector `v`.

NB. In mathematics, these linear maps are only called “transvections” when `f v = 0`.
See also `Module.preReflection` for a similar definition, up to a sign. -/
def transvection (f : Dual R V) (v : V) : V →ₗ[R] V where
  toFun x := x + f x • v
  map_add' x y := by simp only [map_add, add_smul]; abel
  map_smul' r x := by simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul, smul_add]

namespace transvection

theorem apply (f : Dual R V) (v x : V) :
    transvection f v x = x + f x • v :=
  rfl

theorem comp_of_left_eq_apply {f : Dual R V} {v w : V} {x : V} (hw : f w = 0) :
    transvection f v (transvection f w x) = transvection f (v + w) x := by
  simp only [transvection, coe_mk, AddHom.coe_mk, map_add, map_smul,
    hw, smul_add, zero_smul, smul_zero]
  abel

theorem comp_of_left_eq {f : Dual R V} {v w : V} (hw : f w = 0) :
    (transvection f v) ∘ₗ (transvection f w) = transvection f (v + w) := by
  ext; simp [comp_of_left_eq_apply hw]

theorem comp_of_right_eq_apply {f g : Dual R V} {v : V} {x : V} (hf : f v = 0) :
    (transvection f v) (transvection g v x) = transvection (f + g) v x := by
  simp only [transvection, coe_mk, AddHom.coe_mk, map_add, map_smul,
    hf, add_apply, zero_smul, add_smul, smul_add, smul_zero]
  abel

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
    have : x = ∑ i, b.repr x i • b i := (Basis.sum_equivFun b x).symm
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by grind)] at this

theorem congr {W : Type*} [AddCommMonoid W] [Module R W]
    (f : Dual R V) (v : V) (e : V ≃ₗ[R] W) :
    e ∘ₗ (transvection f v) ∘ₗ e.symm = transvection (f ∘ₗ e.symm) (e v) := by
  ext; simp [transvection.apply]

end LinearMap.transvection

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

namespace LinearEquiv

open LinearMap LinearMap.transvection Module

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

theorem symm_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf).symm = transvection hf' := by
  ext; simp [LinearEquiv.symm_apply_eq, comp_of_right_eq_apply hf]

end LinearEquiv.transvection

section baseChange

namespace LinearMap.transvection

open LinearMap LinearEquiv Module

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  {A : Type*} [CommRing A] [Algebra R A]

theorem baseChange (f : Dual R V) (v : V) :
    (transvection f v).baseChange A = transvection (f.baseChange A) (1 ⊗ₜ[R] v) := by
  ext; simp [transvection, TensorProduct.tmul_add]

theorem _root_.LinearEquiv.transvection.baseChange
    {f : Dual R V} {v : V} (h : f v = 0)
    (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0 := by simp [Algebra.algebraMap_eq_smul_one]) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, transvection.coe_toLinearMap, transvection.baseChange]

open IsBaseChange

variable {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V →ₗ[R] W} (ibc : IsBaseChange A ε)

@[simp]
theorem _root_.IsBaseChange.transvection (f : Dual R V) (v : V) :
    ibc.endHom (transvection f v) = transvection (ibc.toDual f) (ε v) := by
  ext w
  induction w using ibc.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a w hw => simp [hw]
  | tmul x => simp [transvection.apply, toDual_comp_apply, endHom_apply]

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

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

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

end transvection

end LinearMap

end determinant
