/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.MvPolynomial.IrrQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

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

section transvection

namespace LinearMap.transvection

open LinearMap LinearEquiv

open scoped TensorProduct

variable {A : Type*} [CommRing A] [Algebra R A]
variable {W : Type*} [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
  {ε : V →ₗ[R] W} (ibc_VW : IsBaseChange A ε)

theorem baseChange (f : Module.Dual R V) (v : V) :
    (transvection f v).baseChange A = transvection (f.baseChange A) (1 ⊗ₜ[R] v) := by
  ext; simp [transvection, TensorProduct.tmul_add]

theorem _root_.LinearEquiv.transvection.baseChange
    {f : Module.Dual R V} {v : V}
    (h : f v = 0) (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange, LinearEquiv.transvection.coe_toLinearMap,
    LinearMap.transvection.baseChange]

noncomputable def _root_.IsBaseChange.toDual (f : Module.Dual R V) :
    Module.Dual A W := (f.baseChange A).congr ibc_VW.equiv

noncomputable def _root_.IsBaseChange.toDualHom :
    Module.Dual R V →ₗ[R] Module.Dual A W where
  toFun f := (f.baseChange A).congr ibc_VW.equiv
  map_add' f g := by
    rw?
  map_smul' a f := by simp


example (f : Module.Dual R V) (v : V) : Module.Dual A W := by
  let fA := f.baseChange A
  let j := ibc_VW.equiv
  exact Module.Dual.congr j fA

example (f : Module.Dual R V) (v : V) :
    LinearMap.transvection (f.map ε) (ε v) =
  j ∘ₗ (transvection f v) ∘ₗ j.symm := sorry

noncomputable example : A ⊗[R] V ≃ₗ[A] W := by exact ibc_VW.equiv

end transvection

section determinant

open Polynomial LinearMap

open scoped TensorProduct

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

variable {f : Module.Dual K V} {v : V}

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

/-- Over a field, transvections have determinant `1`.

See `LinearMap.Transvection.det_eq_one` for the general result. -/
theorem det_eq_one_ofField {f : Module.Dual K V} {v : V} (hfv : f v = 0) :
    (LinearMap.transvection f v).det = 1 := by
  by_contra! h
  have := finite_of_det_ne_one h
  apply h
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

theorem Module.Free.of_det_ne_one {f : V →ₗ[R] V} (hf : f.det ≠ 1) : Module.Free R V := by
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s R V)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

/-- Over a domain, transvections have determinant 1.

See `LinearMap.transvection.det_eq_one` for the general case. -/
theorem det_eq_one_ofDomain [IsDomain R]
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (transvection f v).det = 1 := by
  by_contra! h
  have := LinearMap.free_of_det_ne_one h
  have := LinearMap.finite_of_det_ne_one h
  apply h
  let K := FractionRing R
  let : Field K := inferInstance
  have : (transvection (f.baseChange K) (1 ⊗ₜ[R] v)).det = 1 :=
    det_eq_one_ofField (by simp [hfv])
  rw [← LinearMap.transvection.baseChange, LinearMap.det_baseChange,
    ← algebraMap.coe_one (R := R) (A := K)] at this
  simpa using this

end determinant

end LinearMap

section

namespace LinearMap.transvection

open scoped TensorProduct

open LinearMap

theorem det_eq_one {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (LinearMap.transvection f v).det = 1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · subsingleton
  by_contra! h
  have := LinearMap.free_of_det_ne_one h
  have := LinearMap.finite_of_det_ne_one h
  apply h
  let b := Module.finBasis R V
  set n := Module.finrank R V
  by_cases hn2 : n < 2
  · simp [eq_id_of_finrank_le_one hfv (Nat.le_of_lt_succ hn2)]
  rw [not_lt] at hn2
  let I := Fin n ⊕ Fin n
  let S := MvPolynomial I ℤ

  let ε : I → R := Sum.elim (fun i ↦ f (b i)) (fun i ↦ b.coord i v)
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
    (fun i ↦ IsBaseChange.linearMap T ((fun _ ↦ R) i))).equiv.trans b.equivFun.symm
  have : LinearMap.transvection f v = j ∘ₗ fR ∘ₗ j.symm := by
    simp only [fR, tT, transvection.baseChange, LinearMap.transvection.congr]
    congr
    · ext x
      simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      set y := j.symm x with hy
      rw [LinearEquiv.eq_symm_apply] at hy
      rw [← hy]
      rw [← Module.Dual.baseChangeHom_apply]
      set lc1S := Fintype.linearCombination S (α := Fin n) (M := S)
      set lc2T := Fintype.linearCombination T (⇑β ∘ fun i ↦ MvPolynomial.X (Sum.inl i))
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, h, h']
      | tmul r t =>
        simp only [Module.Dual.baseChangeHom_apply, Module.Dual.baseChange_apply_tmul]
        simp only [lc2T, Fintype.linearCombination_apply, Finset.sum_smul]
        simp [j, IsBaseChange.equiv_tmul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
          map_mul, ← RingHom.comp_apply, hγβ, ← hαfS x]
        ring
    · simp only [LinearEquiv.trans_apply, j, LinearEquiv.eq_symm_apply]
      -- some API is missing
      ext i
      simp [IsBaseChange.equiv, vT, RingHom.algebraMap_toAlgebra]
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
#check Module.Finite
end transvection
