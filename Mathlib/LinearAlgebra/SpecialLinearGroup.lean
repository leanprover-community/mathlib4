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

/-!
# The special linear group of a module

If `R` is a commutative ring and `V` is an `R`-module,
we define `SpecialLinearGroup R V` as the subtype of
linear equivalences `V ≃ₗ[R] V` with determinant 1.
When `V` doesn't have a finite basis, the determinant is defined by 1
and the definition gives `V ≃ₗ[R] V`.
The interest of this definition is that `SpecialLinearGroup R V`
has a group structure. (Starting from linear maps wouldn't have worked.)

The file is constructed parallel to the one defining `Matrix.SpecialLinearGroup`.

We provide `SpecialLinearGroup.toLinearEquiv`: the canonical map
from `SpecialLinearGroup R V` to `V ≃ₗ[R] V`, as a monoid hom.

When `V` is free and finite over `R`, we define
* `SpecialLinearGroup.dualMap`
* `SpecialLinearGroup.baseChange`

We define `Matrix.SpecialLinaerGroup.toLin'_equiv`: the mul equivalence
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R (n → R)`
and its variant
`Matrix.SpecialLinearGroup.toLin_equiv`,
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R V`,
associated with a finite basis of `V`.

-/
-- Two lemmas on  finrank
-- TODO : move elsewhere
theorem Module.finrank_eq_zero_iff_of_free {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R M = 0 ↔ Subsingleton M := by
  have := Module.rank_lt_aleph0 R M
  rw [← not_le] at this
  simp [Module.finrank, this, rank_zero_iff_of_free]

theorem Module.finrank_pos_iff_of_free {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    0 < Module.finrank R M ↔ Nontrivial M := by
  rw [← not_subsingleton_iff_nontrivial, ← iff_not_comm]
  simp [Module.finrank_eq_zero_iff_of_free]

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

variable (R V) in
/-- The special linear group of a module.

This is only meaningful when the module is finite and free,
for otherwise, it coincides with the group of linear equivalences. -/
abbrev SpecialLinearGroup := { u : V ≃ₗ[R] V // u.det = 1 }

namespace SpecialLinearGroup

lemma det_eq_one (u : SpecialLinearGroup R V) :
    LinearMap.det (u : V →ₗ[R] V) = 1 := by
  simp [← LinearEquiv.coe_det, u.prop]

/-- The coercion from `SpecialLinearGroup R V` to the function type `V → V` -/
instance : CoeFun (SpecialLinearGroup R V) (fun _ ↦ V → V) where
  coe u x := u.val x

lemma ext_iff (u v : SpecialLinearGroup R V) : u = v ↔ ∀ x : V, u x = v x := by
  simp only [← Subtype.coe_inj, LinearEquiv.ext_iff]

@[ext]
lemma ext (u v : SpecialLinearGroup R V) : (∀ x, u x = v x) → u = v :=
  (SpecialLinearGroup.ext_iff u v).mpr

section rankOne

/-- If a free module has `Module.finrank` equal to `1`, then its special linear group is trivial. -/
theorem subsingleton_of_finrank_eq_one [Module.Free R V] (d1 : Module.finrank R V = 1) :
    Subsingleton (SpecialLinearGroup R V) where
  allEq u v := by
    nontriviality R
    ext x
    by_cases hx : x = 0
    · simp [hx]
    suffices ∀ (u : SpecialLinearGroup R V), (u : V →ₗ[R] V) = LinearMap.id by
      simp only [LinearMap.ext_iff, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
      simp [this u, this v]
    intro u
    ext x
    set c := (LinearEquiv.smul_id_of_finrank_eq_one d1).symm u with hc
    rw [LinearEquiv.eq_symm_apply] at hc
    suffices c = 1 by
      simp [← hc, LinearEquiv.smul_id_of_finrank_eq_one, this]
    have hu := u.prop
    simpa [← Units.val_inj, LinearEquiv.coe_det, ← hc,
      LinearEquiv.smul_id_of_finrank_eq_one, d1] using hu

end rankOne

instance : Inv (SpecialLinearGroup R V) :=
  ⟨fun A => ⟨A⁻¹, by simp [A.prop]⟩⟩

instance : Mul (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A * B, by simp [A.prop, B.prop]⟩⟩

instance : Div (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A / B, by simp [A.prop, B.prop]⟩⟩

instance : One (SpecialLinearGroup R V) :=
  ⟨⟨1, by simp⟩⟩

instance : Pow (SpecialLinearGroup R V) ℕ where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩

instance : Pow (SpecialLinearGroup R V) ℤ where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩

instance : Inhabited (SpecialLinearGroup R V) :=
  ⟨1⟩

/-- The transpose of an element in `SpecialLinearGroup R V`. -/
def dualMap
    [Module.Free R V] [Module.Finite R V] (A : SpecialLinearGroup R V) :
    SpecialLinearGroup R (Module.Dual R V) :=
  ⟨LinearEquiv.dualMap (A : V ≃ₗ[R] V), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
      LinearEquiv.dualMap, LinearMap.det_dualMap]
    simp [← LinearEquiv.coe_det, A.prop]⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.dualMap

section CoeLemmas

variable (A B : SpecialLinearGroup R V)

lemma coe_mk (A : V ≃ₗ[R] V) (h : A.det = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup R V) = A :=
  rfl

@[simp]
lemma coe_mul : (A * B : SpecialLinearGroup R V) = (A * B  : V ≃ₗ[R] V) :=
  rfl

@[simp]
lemma coe_div : (A / B : SpecialLinearGroup R V) = (A / B  : V ≃ₗ[R] V) :=
  rfl

@[simp]
lemma coe_inv : (A : SpecialLinearGroup R V)⁻¹ = (A⁻¹ : V ≃ₗ[R] V) :=
  rfl

@[simp]
lemma coe_one : (1 : SpecialLinearGroup R V) = (1 : V ≃ₗ[R] V) :=
  rfl

@[simp]
lemma det_coe : LinearEquiv.det (A : V ≃ₗ[R] V) = 1 :=
  A.prop

@[simp]
lemma coe_pow (m : ℕ) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
lemma coe_zpow (m : ℤ) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
lemma coe_dualMap
    [Module.Free R V] [Module.Finite R V] :
    Aᵀ = (A : V ≃ₗ[R] V).dualMap :=
  rfl

end CoeLemmas

/-- The special linear group of a module is a group. -/
instance : Group (SpecialLinearGroup R V) := fast_instance%
  Function.Injective.group _ Subtype.coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/-- A version of `Matrix.toLin' A` that produces linear equivalences. -/
def toLinearEquiv : SpecialLinearGroup R V →* V ≃ₗ[R] V where
  toFun A := A.val
  map_one' := coe_one
  map_mul' := coe_mul

@[simp] lemma toLinearEquiv_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv v = A v :=
  rfl

@[simp]
theorem toLinearEquiv_to_linearMap (A : SpecialLinearGroup R V) :
    (SpecialLinearGroup.toLinearEquiv A) = (A : V →ₗ[R] V) :=
  rfl

@[simp]
theorem toLinearEquiv_symm_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv.symm v = A⁻¹ v :=
  rfl

@[simp]
theorem toLinearEquiv_symm_to_linearMap (A : SpecialLinearGroup R V) :
    A.toLinearEquiv.symm = ((A⁻¹ : SpecialLinearGroup R V) : V →ₗ[R] V) :=
  rfl

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : SpecialLinearGroup R V →* V ≃ₗ[R] V) :=
  Subtype.val_injective

/-- The canonical group morphism from the special linear group
to the general linear group. -/
def toGeneralLinearGroup : SpecialLinearGroup R V →* LinearMap.GeneralLinearGroup R V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm.toMonoidHom.comp toLinearEquiv

lemma toGeneralLinearGroup_toLinearEquiv_apply (u : SpecialLinearGroup R V) :
    u.toGeneralLinearGroup.toLinearEquiv = u.toLinearEquiv := rfl

lemma coe_toGeneralLinearGroup_apply (u : SpecialLinearGroup R V) :
    u.toGeneralLinearGroup.val = u.toLinearEquiv := rfl

lemma toGeneralLinearGroup_injective :
    Function.Injective ⇑(toGeneralLinearGroup (R := R) (V := V)) :=  by
  simp [toGeneralLinearGroup, toLinearEquiv_injective]

lemma mem_range_toGeneralLinearGroup_iff {u : LinearMap.GeneralLinearGroup R V} :
    u ∈ Set.range ⇑(toGeneralLinearGroup (R := R) (V := V)) ↔
      u.toLinearEquiv.det = 1 := by
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv, toGeneralLinearGroup_toLinearEquiv_apply]
    exact v.prop
  · intro hu
    refine ⟨⟨u.toLinearEquiv, hu⟩, rfl⟩

section baseChange

open TensorProduct

variable {S : Type*} [CommRing S] [Algebra R S]
  [Module.Free R V] [Module.Finite R V]

/-- By base change, an `R`-algebra `S` induces a group homomorphism from
`SpecialLinearGroup R V` to `SpecialLinearGroup S (S ⊗[R] V)`. -/
@[simps]
def baseChange : SpecialLinearGroup R V →* SpecialLinearGroup S (S ⊗[R] V) where
  toFun g := ⟨LinearEquiv.baseChange R S V V g, by
      rw [LinearEquiv.det_baseChange, g.prop, map_one]⟩
  map_one' := Subtype.ext <| by simp
  map_mul' x y := Subtype.ext <| by simp [LinearEquiv.baseChange_mul]

end baseChange

variable {W X : Type*} [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]

/-- The isomorphism between special linear groups of isomorphic modules. -/
def congr_linearEquiv (e : V ≃ₗ[R] W) :
    SpecialLinearGroup R V ≃* SpecialLinearGroup R W where
  toFun f := ⟨e.symm ≪≫ₗ f ≪≫ₗ e, by simp [f.prop]⟩
  invFun g := ⟨e ≪≫ₗ g ≪≫ₗ e.symm, by
    nth_rewrite 1 [← LinearEquiv.symm_symm e]
    rw [LinearEquiv.det_conj g e.symm, g.prop]⟩
  left_inv f := Subtype.coe_injective <| by aesop
  right_inv g := Subtype.coe_injective <| by aesop
  map_mul' f g := Subtype.coe_injective <| by aesop

@[simp]
lemma congr_linearEquiv_coe_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) :
    (congr_linearEquiv e f : W ≃ₗ[R] W) = e.symm ≪≫ₗ f ≪≫ₗ e :=
  rfl

@[simp]
lemma congr_linearEquiv_apply_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) (x : W) :
    congr_linearEquiv e f x = e (f (e.symm x)) :=
  rfl

lemma congr_linearEquiv_symm (e : V ≃ₗ[R] W) :
    (congr_linearEquiv e).symm = congr_linearEquiv e.symm :=
  rfl

lemma congr_linearEquiv_trans (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] X) :
    (congr_linearEquiv e).trans (congr_linearEquiv f) = congr_linearEquiv (e.trans f) := by
  rfl

lemma congr_linearEquiv_refl :
    congr_linearEquiv (LinearEquiv.refl R V) = MulEquiv.refl _ := by
  rfl


end SpecialLinearGroup

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n R V)

/-- The canonical isomorphism from `SL(n, R)` to the special linear group of the module `n → R`. -/
def _root_.Matrix.SpecialLinearGroup.toLin'_equiv :
    Matrix.SpecialLinearGroup n R ≃* SpecialLinearGroup R (n → R) where
  toFun A := ⟨Matrix.SpecialLinearGroup.toLin' A,
    by
      simp [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
        Matrix.SpecialLinearGroup.toLin'_to_linearMap]⟩
  invFun u := ⟨LinearMap.toMatrix' u,
      by simp [← LinearEquiv.coe_det, u.prop]⟩
  left_inv A := Subtype.coe_injective <| by
    rw [← LinearEquiv.eq_symm_apply, LinearMap.toMatrix'_symm,
      Matrix.SpecialLinearGroup.toLin'_to_linearMap]
  right_inv u := Subtype.coe_injective <| by
    simp [← LinearEquiv.toLinearMap_inj, Matrix.SpecialLinearGroup.toLin']
  map_mul' A B := Subtype.coe_injective (by simp)

/-- The isomorphism from `Matrix.SpecialLinearGroup n R`
to the special linear group of a module associated with a basis of that module. -/
noncomputable def _root_.Matrix.SpecialLinearGroup.toLin_equiv
    (b : Module.Basis n R V) :
    Matrix.SpecialLinearGroup n R ≃* SpecialLinearGroup R V :=
  Matrix.SpecialLinearGroup.toLin'_equiv.trans
    (SpecialLinearGroup.congr_linearEquiv
      (b.repr.trans (Finsupp.linearEquivFunOnFinite R R n)).symm)

end Matrix
