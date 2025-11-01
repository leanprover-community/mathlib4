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

/-!
# Transvections

-/

universe u v

section Polynomial

open Polynomial

theorem irreducible_smul_X_add_C {R : Type*} [CommRing R] [IsDomain R]
    {a b : R} (ha : a ≠ 0) (hab : IsRelPrime a b) :
    Irreducible (a • X + C b : Polynomial R) where
  not_isUnit h := by
    obtain ⟨u, hu, h⟩ := isUnit_iff.mp h
    apply ha
    simpa using congr_arg (fun f ↦ coeff f 1) h.symm
  isUnit_or_isUnit f g h := by
    wlog H : f.degree ≤ g.degree generalizing f g
    · rcases le_total f.degree g.degree with h' | h'
      · exact this f g h h'
      · rw [mul_comm] at h
        exact or_comm.mp (this g f h h')
    have hd := congr_arg degree h
    have ha' : (a • (X : R[X])).degree = 1 := by
      simp [smul_eq_C_mul a, degree_C ha]
    rw [degree_mul, degree_add_C (by simp [ha']), ha'] at hd
    rw [eq_comm, Nat.WithBot.add_eq_one_iff] at hd
    rcases hd with hd | hd
    · left
      have hf := f.eq_C_of_degree_eq_zero hd.1
      suffices IsUnit (f.coeff 0) by
        rw [isUnit_iff]
        exact ⟨f.coeff 0, this, hf.symm⟩
      rw [hf, ← smul_eq_C_mul] at h
      apply hab
      · use g.coeff 1
        simpa using congr_arg (fun f ↦ coeff f 1) h
      · use g.coeff 0
        simpa using congr_arg (fun f ↦ coeff f 0) h
    · exfalso
      rw [hd.1, hd.2, ← not_lt] at H
      apply H (zero_lt_one' (WithBot ℕ))

end Polynomial

-- TODO: exists? move elsewhere.
/-- The equivalence between a type and the `Option` type
of the type deprived of one given element. -/
noncomputable def equiv_option {n : Type*} [DecidableEq n] (i : n) :
    n ≃ Option {x : n // x ≠ i} where
  toFun x := if hx : x = i then none else some ⟨x, hx⟩
  invFun y := Option.elim y i (fun x ↦ ↑x)
  left_inv x := by
    by_cases hx : x = i <;> simp [hx]
  right_inv y :=  by
    cases y with
    | none => simp
    | some x => simp [x.prop]


namespace MvPolynomial

open scoped Polynomial

variable (n : Type*) [Fintype n] (R : Type*) [CommRing R] [IsDomain R]

/-- The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/
noncomputable def quad : MvPolynomial (n ⊕ n) R :=
  ∑ i : n, MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i)

noncomputable example (n : Type*) [DecidableEq n] (R : Type*) [CommRing R] (i : n) :
    MvPolynomial n R ≃ₐ[R] (MvPolynomial {x : n // x ≠ i} R)[X] :=
  (renameEquiv R (equiv_option i)).trans (MvPolynomial.optionEquivLeft R _)

variable {R} in
theorem totalDegree_le_of_dvd_of_isDomain
    {σ : Type*} {p q : MvPolynomial σ R} (hp : q ≠ 0) (h : p ∣ q) :
    p.totalDegree ≤ q.totalDegree := by
  obtain ⟨r, rfl⟩ := h
  rw [totalDegree_mul_of_isDomain]
  · exact Nat.le_add_right p.totalDegree r.totalDegree
  · exact fun h ↦ hp (by simp [h])
  · exact fun h ↦ hp (by simp [h])

theorem dvd_C_iff_exists
    {σ : Type*} {a : R} (ha : a ≠ 0) {p : MvPolynomial σ R} :
    p ∣ MvPolynomial.C a ↔ ∃ b, b ∣ a ∧ p = MvPolynomial.C b := by
  constructor
  · intro hp
    use MvPolynomial.coeff 0 p
    suffices p.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this, MvPolynomial.C_dvd_iff_dvd_coeff] at hp
      convert hp 0
      simp
    apply Nat.eq_zero_of_le_zero
    convert totalDegree_le_of_dvd_of_isDomain (by simp [ha]) hp
    simp
  · rintro ⟨b, hab, rfl⟩
    exact _root_.map_dvd MvPolynomial.C hab

theorem dvd_X_iff_exists
    {σ : Type*} {i : σ} {p : MvPolynomial σ R} :
    p ∣ X i ↔ ∃ r, IsUnit r ∧ (p = C r ∨ p = r • (X i)) := by
  constructor
  · rintro ⟨q, hq⟩
    have : totalDegree p + totalDegree q = 1 := by
      rw [← totalDegree_mul_of_isDomain, ← hq]
      · simp only [totalDegree_X]
      · intro h; simp [h] at hq
      · intro h; simp [h] at hq
    rw [Nat.add_eq_one_iff] at this
    rcases this with h01 | h10
    · rw [totalDegree_eq_zero_iff_eq_C] at h01
      refine ⟨coeff 0 p, ?_, Or.inl h01.1⟩
      rw [h01.1] at hq
      replace hq := congr_arg (fun f ↦ coeff (Finsupp.single i 1) f) hq
      simp only [coeff_X, coeff_C_mul] at hq
      exact isUnit_of_mul_eq_one _ _ hq.symm
    · rw [totalDegree_eq_zero_iff_eq_C] at h10
      have : IsUnit (coeff 0 q) := by
        replace hq := congr_arg (fun f ↦ coeff (Finsupp.single i 1) f) hq
        simp only at hq
        rw [h10.2, mul_comm] at hq
        simp only [coeff_X, coeff_C_mul] at hq
        exact isUnit_of_mul_eq_one _ _ hq.symm
      set u := this.unit
      have h : q = C (u : R) := by rw [h10.2]; simp [u]
      refine ⟨(u⁻¹ : Rˣ), Units.isUnit _, ?_⟩
      right
      rw [smul_eq_C_mul, hq, mul_comm p q, h, ← mul_assoc,
        ← map_mul]
      simp
  · rintro ⟨r, hr, hp⟩
    rcases hp with hp | hp
    · rw [hp, ← (hr.map _).unit_spec]
      exact Units.coe_dvd
    · rw [hp, smul_eq_C_mul, ← (hr.map _).unit_spec, Units.mul_left_dvd]

theorem dvd_monomial_iff {σ : Type*} {n : σ →₀ ℕ} {p : MvPolynomial σ R} :
    p ∣ monomial n 1 ↔
    ∃ (r : R) (m : σ →₀ ℕ), IsUnit r ∧ m ≤ n ∧ p = monomial m r := by
  constructor
  · rintro ⟨q, hq⟩


    sorry
  · rintro ⟨r, m, hr, hm, rfl⟩
    rw [monomial_dvd_monomial, ← isUnit_iff_dvd_one]
    simp [hm, hr]

theorem quad_irreducible (h : Nontrivial n) : Irreducible (quad n R) := by
  classical
  let p := ∑ x : n,
    MvPolynomial.X (R := MvPolynomial n R) x * MvPolynomial.C ( (MvPolynomial.X (R := R) x))
  let e := sumRingEquiv R n n
  have : e (quad n R) = p := by simp [e, p, quad, sumRingEquiv]
  rw [← MulEquiv.irreducible_iff e, this]
  obtain ⟨i, j, hij⟩ := h
  set S := MvPolynomial { x // x ≠ i } (MvPolynomial n R)
  let f : MvPolynomial n (MvPolynomial n R) ≃ₐ[R] S[X] :=
    ((renameEquiv (MvPolynomial n R) (equiv_option i)).trans
      (MvPolynomial.optionEquivLeft _ _)).restrictScalars R
  have hfXi : f (MvPolynomial.X i) = Polynomial.X := by
    simp only [f]
    rw [AlgEquiv.restrictScalars_apply]
    simp [equiv_option, optionEquivLeft_apply]
  have hfX (x : {x : n // x ≠ i}) : f (MvPolynomial.X x) =
      Polynomial.C (MvPolynomial.X x) := by
    simp only [f]
    rw [AlgEquiv.restrictScalars_apply]
    simp [equiv_option, optionEquivLeft_apply, dif_neg x.prop]
  have hfCX (x : n) : f (MvPolynomial.C (MvPolynomial.X x)) =
      Polynomial.C (MvPolynomial.C (MvPolynomial.X x)) := by
    simp only [f]
    rw [AlgEquiv.restrictScalars_apply]
    simp [equiv_option, optionEquivLeft_apply]
  rw [← MulEquiv.irreducible_iff f]
  let a : S := C (MvPolynomial.X (R := R) i)
  let b : S := ∑ x : { x : n // x ≠ i},
    (MvPolynomial.X (R := R) (x : n)) • X (R := MvPolynomial n R) x
  suffices f p = a • Polynomial.X + Polynomial.C b  by
    rw [this]
    refine irreducible_smul_X_add_C (fun ha ↦ ?_) (fun c hca hcb ↦ ?_)
    · simp only [ne_eq, a] at ha
      rw [MvPolynomial.C_eq_zero] at ha
      exact MvPolynomial.X_ne_zero i ha
    · simp only [a] at hca
      rw [dvd_C_iff_exists _ (MvPolynomial.X_ne_zero i)] at hca
      obtain ⟨c, hc, rfl⟩ := hca
      apply IsUnit.map
      rw [MvPolynomial.dvd_X_iff_exists] at hc
      obtain ⟨r, hr, hc | hc⟩ := hc <;>
        have hr' : IsUnit (MvPolynomial.C (σ := n) r) :=
            IsUnit.map MvPolynomial.C hr
      · simpa [hc] using hr'
      · exfalso
        apply hij
        rw [← MvPolynomial.X_dvd_X (σ := n) (R := R)]
        apply dvd_of_mul_left_dvd (a := MvPolynomial.C r)
        rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hcb
        specialize hcb (Finsupp.single ⟨j, Ne.symm hij⟩ 1)
        rw [hc, MvPolynomial.smul_eq_C_mul] at hcb
        simp only [b] at hcb
        rw [MvPolynomial.coeff_sum] at hcb
        simpa using hcb
  simp only [p]
  rw [map_sum, Fintype.sum_eq_add_sum_subtype_ne _ i]
  rw [map_sum]
  apply congr_arg₂
  · simp only [ne_eq, map_mul, a]
    rw [mul_comm, hfXi, hfCX, ← Polynomial.smul_eq_C_mul]
  · apply Fintype.sum_congr
    intro x
    simp [hfCX, hfX]
    rw [MvPolynomial.smul_eq_C_mul, map_mul, mul_comm]

end MvPolynomial



-- TODO: mv to somewhere
section

namespace Module.Dual

open TensorProduct LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- `LinearMap.baseChange` for `Module.Dual`. -/
def baseChange (f : Module.Dual R V) :
    Module.Dual A (A ⊗[R] V) :=
  (AlgebraTensorModule.rid R A A).toLinearMap.comp (LinearMap.baseChange A f)

@[simp]
theorem baseChange_apply_tmul (f : Module.Dual R V) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ v) = (f v) • a := by
  simp [baseChange]

/-- Equivalent modules have equivalent duals. -/
def congr (e : V ≃ₗ[R] W) :
    Module.Dual R V ≃ₗ[R] Module.Dual R W :=
  LinearEquiv.congrLeft R R e

/-- `Module.Dual.baseChange` as a linear map. -/
def baseChangeHom :
    Module.Dual R V →ₗ[R] Module.Dual A (A ⊗[R] V) where
  toFun := Module.Dual.baseChange A
  map_add' := by unfold Module.Dual.baseChange; aesop
  map_smul' r x := by
    ext
    unfold Module.Dual.baseChange
    simp [LinearMap.baseChange_smul, ← TensorProduct.tmul_smul, mul_smul]

@[simp]
theorem baseChangeHom_apply (f : Module.Dual R V) :
    Module.Dual.baseChangeHom A f = f.baseChange A :=
  rfl

section group

variable {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (A : Type*) [CommRing A] [Algebra R A]

theorem baseChange_sub (f g : Module.Dual R V) :
    Module.Dual.baseChange A (f - g) = Module.Dual.baseChange A f - Module.Dual.baseChange A g := by
  unfold Module.Dual.baseChange; aesop

theorem baseChange_neg (f : Module.Dual R V) :
    Module.Dual.baseChange A (-f) = -(Module.Dual.baseChange A f) := by
  unfold Module.Dual.baseChange; aesop

end group

section comp

variable (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem baseChange_comp (f : Module.Dual R V) :
    Module.Dual.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V)
      ((f.baseChange A).baseChange B) = f.baseChange B := by
  ext; simp [Module.Dual.congr, congrLeft]

end comp

variable {A}
variable {W : Type*} [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
  {ε : V →ₗ[R] W} (ibc_VW : IsBaseChange A ε)

/-- The map showing that the duals of modules related by base change
are also related by base change. -/
noncomputable def _root_.IsBaseChange.dualMap :
    (Module.Dual R V) →ₗ[R] Module.Dual A W where
  toFun f := ibc_VW.lift ((Algebra.linearMap R A).comp f)
  map_add' x y := by
    ext w
    simp [LinearMap.comp_add]
    induction w using ibc_VW.inductionOn with
    | zero => simp
    | add _ _ h h' => simp only [h, h', map_add]; module
    | smul _ _ h => simp only [_root_.map_smul, ← smul_add, h]
    | tmul => simp [ibc_VW.lift_eq]
  map_smul' r f := by
    ext w
    simp only [RingHom.id_apply, LinearMap.smul_apply]
    induction w using ibc_VW.inductionOn with
    | zero => simp
    | add _ _ h h' => simp only [h, h', map_add]; module
    | smul _ _ h => simp [_root_.map_smul, h]
    | tmul => simp [ibc_VW.lift_eq, Algebra.smul_def]

/-- Duals of modules related by base change are related by base change. -/
theorem isBaseChange : IsBaseChange A (ibc_VW.dualMap) := by
  sorry

end Module.Dual

end

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
  have hpS' : Fintype.linearCombination S fS vS =
    MvPolynomial.quad (Fin n) ℤ := by
    simp only [MvPolynomial.quad]
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
    refine MvPolynomial.quad_irreducible (Fin n) ℤ ?_
    rw [Fin.nontrivial_iff_two_le]
    exact hn2
  let algTR : Algebra T R := RingHom.toAlgebra γ
  let fR := tT.baseChange R
--  let j := (ibc T R (n := Fin n)).trans e.symm
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

example (S : Type*) [CommRing S] [Algebra R S] :
    V →ₗ[R] S ⊗[R] V :=
  ((TensorProduct.mk R S V) 1)

example (S : Type*) [CommRing S] [Algebra R S] :
    IsBaseChange S ((TensorProduct.mk R S V) 1) :=
  TensorProduct.isBaseChange R V S

theorem _root_.LinearEquiv.det_eq_one
    {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    (LinearEquiv.transvection hfv).det = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det, LinearEquiv.transvection.coe_toLinearMap hfv,
      LinearMap.transvection.det_eq_one hfv, Units.val_one]

end transvection

end LinearMap

end

end transvection
