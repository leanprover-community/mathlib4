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

We define `Matrix.SpecialLinaerGruop.toLin'_equiv`: the mul equivalence
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R (n → R)`
and its variant
`Matrix.SpecialLinearGroup.toLin_equiv`,
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R V`,
associated with a finite basis of `V`.

-/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

variable (R V) in
/-- The special linear group of a module.

This is only meaningful when the module is finite and free,
for otherwise, it coincides with the group of linear equivalences. -/
abbrev SpecialLinearGroup := { u : V ≃ₗ[R] V // u.det = 1 }

namespace SpecialLinearGroup

theorem det_eq_one (u : SpecialLinearGroup R V) :
    LinearMap.det (u : V →ₗ[R] V) = 1 := by
  simp [← LinearEquiv.coe_det, u.prop]

instance : CoeFun (SpecialLinearGroup R V) (fun _ ↦ V → V) where
  coe u x := u.val x

theorem ext_iff (u v : SpecialLinearGroup R V) : u = v ↔ ∀ x : V, u x = v x := by
  simp only [← Subtype.coe_inj, LinearEquiv.ext_iff]

@[ext]
theorem ext (u v : SpecialLinearGroup R V) : (∀ x, u x = v x) → u = v :=
  (SpecialLinearGroup.ext_iff u v).mpr

section rankOne

variable [Nontrivial R] [Module.Free R V] [Module.Finite R V]

-- Move to other file ?
theorem _root_.exists_linearEquiv_of_finrank_eq_one (d1 : Module.finrank R V = 1) :
    Nonempty (R ≃ₗ[R] V) := by
  let ⟨ι, b⟩ := (Module.Free.exists_basis R V).some
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : DecidableEq ι := Classical.typeDecidableEq ι
  rw [Module.finrank_eq_card_basis b, Fintype.card_eq_one_iff] at d1
  obtain ⟨i, hi⟩ := d1
  exact ⟨{
    toFun r := r • (b i)
    invFun v := b.repr v i
    left_inv r := by simp
    right_inv v := b.repr.injective <| by ext j; simp [hi j]
    map_add' r s := by simp [add_smul]
    map_smul' r s := by simp [mul_smul] }⟩

theorem exists_unique_eq_smul_id_of_finrank_eq_one (d1 : Module.finrank R V = 1) (u : V →ₗ[R] V) :
    ∃! c : R, u = c • LinearMap.id := by
  let e := (exists_linearEquiv_of_finrank_eq_one d1).some
  set c := e.symm (u (e 1)) with hc
  suffices u = c • LinearMap.id by
    use c
    simp only [this, true_and]
    intro d hcd
    rw [LinearMap.ext_iff] at hcd
    specialize hcd (e 1)
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at hcd
    have hcd' := LinearEquiv.congr_arg (e := e.symm) hcd
    simp only [map_smul, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_one] at hcd'
    rw [hcd']
  ext x
  have (x : V) : x = (e.symm x) • (e 1) := by simp [← LinearEquiv.map_smul]
  rw [this x]
  simp only [hc, map_smul, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  rw [← this]

/-- Endomorphisms of a free module of rank one are homotheties. -/
noncomputable def LinearEquiv.smul_id_of_rank_one (d1 : Module.finrank R V = 1) :
    R ≃ₗ[R] (V →ₗ[R] V) where
  toFun := fun c ↦ c • LinearMap.id
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]
  invFun u := (exists_unique_eq_smul_id_of_finrank_eq_one d1 u).choose
  left_inv c := by
    simp [← (exists_unique_eq_smul_id_of_finrank_eq_one d1 (c • LinearMap.id)).choose_spec.2 c]
  right_inv u :=
    ((exists_unique_eq_smul_id_of_finrank_eq_one d1 u).choose_spec.1).symm

theorem subsingleton_of_subsingleton (d1 : Module.finrank R V = 1) :
    Subsingleton (SpecialLinearGroup R V) where
  allEq u v := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    suffices ∀ (u : SpecialLinearGroup R V), (u : V →ₗ[R] V) = LinearMap.id by
      simp only [LinearMap.ext_iff, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
      simp
      rw [this u, this v]
    intro u
    ext x
    set c := (LinearEquiv.smul_id_of_rank_one d1).symm u with hc
    rw [LinearEquiv.eq_symm_apply] at hc
    suffices c = 1 by
      simp [← hc, LinearEquiv.smul_id_of_rank_one, this]
    have hu := u.prop
    simpa [← Units.val_inj, LinearEquiv.coe_det, ← hc,
      LinearEquiv.smul_id_of_rank_one, d1] using hu

end rankOne

instance hasInv : Inv (SpecialLinearGroup R V) :=
  ⟨fun A => ⟨A⁻¹, by simp [A.prop]⟩⟩

instance hasMul : Mul (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A * B, by simp [A.prop, B.prop]⟩⟩

instance hasDiv : Div (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A / B, by simp [A.prop, B.prop]⟩⟩

instance hasOne : One (SpecialLinearGroup R V) :=
  ⟨⟨1, by simp⟩⟩

instance : Pow (SpecialLinearGroup R V) ℕ where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩

instance : Pow (SpecialLinearGroup R V) ℤ where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩

instance : Inhabited (SpecialLinearGroup R V) :=
  ⟨1⟩

-- TODO: move?
theorem _root_.LinearMap.det_dualMap
    [Module.Free R V] [Module.Finite R V] (f : V →ₗ[R] V) :
    f.dualMap.det = f.det := by
  set b := Module.Free.chooseBasis R V
  have : Fintype (Module.Free.ChooseBasisIndex R V) :=
    Module.Free.ChooseBasisIndex.fintype R V
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b.dualBasis]
  rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]
  simp only [Matrix.det_transpose, LinearMap.det_toMatrix]

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

-- Porting note: shouldn't be `@[simp]` because cast+mk gets reduced anyway
theorem coe_mk (A : V ≃ₗ[R] V) (h : A.det = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup R V) = A :=
  rfl

@[simp]
theorem coe_mul : (A * B : SpecialLinearGroup R V) = (A * B  : V ≃ₗ[R] V) :=
  rfl

@[simp]
theorem coe_div : (A / B : SpecialLinearGroup R V) = (A / B  : V ≃ₗ[R] V) :=
  rfl

@[simp]
theorem coe_inv : (A : SpecialLinearGroup R V)⁻¹ = (A⁻¹ : V ≃ₗ[R] V) :=
  rfl

@[simp]
theorem coe_one : (1 : SpecialLinearGroup R V) = (1 : V ≃ₗ[R] V) :=
  rfl

@[simp]
theorem det_coe : LinearEquiv.det (A : V ≃ₗ[R] V) = 1 :=
  A.prop

@[simp]
theorem coe_pow (m : ℕ) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
theorem coe_zpow (m : ℤ) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
theorem coe_dualMap
    [Module.Free R V] [Module.Finite R V] :
    Aᵀ = (A : V ≃ₗ[R] V).dualMap :=
  rfl

end CoeLemmas

instance : Group (SpecialLinearGroup R V) :=
  Function.Injective.group _ Subtype.coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/-- A version of `Matrix.toLin' A` that produces linear equivalences. -/
def toLinearEquiv : SpecialLinearGroup R V →* V ≃ₗ[R] V where
  toFun A := A.val
  map_one' := coe_one
  map_mul' := coe_mul

theorem toLinearEquiv_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv v = A v :=
  rfl

theorem toLinearEquiv_to_linearMap (A : SpecialLinearGroup R V) :
    (SpecialLinearGroup.toLinearEquiv A) = (A : V →ₗ[R] V) :=
  rfl

theorem toLinearEquiv_symm_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv.symm v = A⁻¹ v :=
  rfl

theorem toLinearEquiv_symm_to_linearMap (A : SpecialLinearGroup R V) :
    A.toLinearEquiv.symm = ((A⁻¹ : SpecialLinearGroup R V) : V →ₗ[R] V) :=
  rfl

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : SpecialLinearGroup R V →* V ≃ₗ[R] V) :=
  Subtype.val_injective

section baseChange

open TensorProduct

variable {S : Type*} [CommRing S] [Algebra R S]
  [Module.Free R V] [Module.Finite R V]

/-- By base change, an`R`-algebra `S` induces a group homomorphism from
`SpecialLinearGroup R V` to `SpecialLinearGroup S (S ⊗[R] V)`. -/
@[simps]
def baseChange : SpecialLinearGroup R V →* SpecialLinearGroup S (S ⊗[R] V) where
  toFun g := ⟨LinearEquiv.baseChange R S V V g, by
      rw [LinearEquiv.det_baseChange, g.prop, map_one]⟩
  map_one' := Subtype.ext <| by simp
  map_mul' x y := Subtype.ext <| by simp [LinearEquiv.baseChange_mul]

end baseChange

/-- The isomorphism between special linear groups of isomorphic modules. -/
def congr_linEquiv {W : Type*} [AddCommGroup W] [Module R W]
    (e : V ≃ₗ[R] W) :
    SpecialLinearGroup R V ≃* SpecialLinearGroup R W where
  toFun f := ⟨e.symm ≪≫ₗ f ≪≫ₗ e, by simp [f.prop]⟩
  invFun g := ⟨e ≪≫ₗ g ≪≫ₗ e.symm, by
    nth_rewrite 1 [← LinearEquiv.symm_symm e]
    rw [LinearEquiv.det_conj g e.symm, g.prop]⟩
  left_inv f := Subtype.coe_injective <| by aesop
  right_inv g := Subtype.coe_injective <| by aesop
  map_mul' f g := Subtype.coe_injective <| by aesop

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
    (SpecialLinearGroup.congr_linEquiv (b.repr.trans (Finsupp.linearEquivFunOnFinite R R n)).symm)

end Matrix

namespace SpecialLinearGroup

section center


theorem center_eq_bot_of_subsingleton [Subsingleton R] :
    Subgroup.center (SpecialLinearGroup R V) = ⊥ :=
  Subgroup.eq_bot_of_subsingleton _

variable [Module.Free R V] [Module.Finite R V] [Nontrivial R]

theorem center_eq_bot_of_finrank_le_one (h : Module.finrank R V ≤ 1) :
    Subgroup.center (SpecialLinearGroup R V) = ⊥ := by
  let b := Module.Free.chooseBasis R V
  haveI : Subsingleton (Module.Free.ChooseBasisIndex R V) := by
    rwa [← @Finite.card_le_one_iff_subsingleton,
      Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b]
  have : Subsingleton (Subgroup.center
    (Matrix.SpecialLinearGroup (Module.Free.ChooseBasisIndex R V) R)) := by
    infer_instance
  rw [Equiv.subsingleton_congr
    (Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).toEquiv] at this
  apply Subgroup.eq_bot_of_subsingleton

theorem mem_center_iff {g : SpecialLinearGroup R V} :
    g ∈ Subgroup.center (SpecialLinearGroup R V) ↔
      ∃ (r : R), r ^ (Module.finrank R V) = 1 ∧
        (g : V →ₗ[R] V) = r • LinearMap.id := by
  let b := Module.Free.chooseBasis R V
  letI _ := Module.Free.ChooseBasisIndex.fintype R V
  rw [Module.finrank_eq_card_basis b]
  let e := (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  rw [← show e g ∈ Subgroup.center _ ↔ g ∈ Subgroup.center _ from by
    exact MulEquivClass.apply_mem_center_iff e]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  apply exists_congr
  intro r
  apply and_congr
  · simp
  simp [e]
  suffices ((Matrix.SpecialLinearGroup.toLin_equiv b).symm g) =
    Matrix.of fun i j ↦ (b.repr (g (b j))) i by
    simp only [this]
    rw [← (LinearMap.toMatrix b b).injective.eq_iff]
    simp only [← Matrix.ext_iff, Matrix.of_apply]
    apply forall₂_congr
    intro i j
    simp [Matrix.diagonal, LinearMap.toMatrix_apply,
      Finsupp.single, Pi.single_apply, Iff.symm eq_comm]
  simp [Matrix.SpecialLinearGroup.toLin_equiv, Matrix.SpecialLinearGroup.toLin'_equiv,
    LinearMap.toMatrix', congr_linEquiv]

example (r : R) : LinearMap.det (r • LinearMap.id : V →ₗ[R] V) = r ^ (Module.finrank R V) := by
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one]
/-- The isomorphism between the roots of unity and the center of the special linear group. -/
noncomputable def center_equiv_rootsOfUnity :
    (Subgroup.center (SpecialLinearGroup R V)) ≃*
      ↥(rootsOfUnity (max (Module.finrank R V) 1) R) where
  toFun g := sorry
  invFun r := ⟨⟨LinearMap.equivOfIsUnitDet (M := V) (R := R)
      (f := ((r : Rˣ) : R) • LinearMap.id) (by
      simp [LinearMap.det_smul, IsUnit.pow]), by
      simp [← Units.val_inj, LinearEquiv.coe_det]
      have := r.prop
      rw [mem_rootsOfUnity, ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one] at this
      rcases max_cases (Module.finrank R V) 1 with ⟨h, h'⟩ |  ⟨h, h'⟩
      · simp_rw [h] at this
        exact this
      · simp_rw [h, pow_one] at this
        simp [this]⟩, sorry⟩
  left_inv g := sorry
  right_inv r := sorry
  map_mul' g h := sorry

end center

end SpecialLinearGroup


