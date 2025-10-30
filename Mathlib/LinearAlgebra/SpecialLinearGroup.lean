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

-- Four lemmas on rank, finrank
-- TODO : move elsewhere
theorem Module.rank_pos_iff_of_free {R M : Type*} [Ring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Free R M] :
    0 < Module.rank R M ↔ Nontrivial M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rank_pos_of_free⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro h'
  simp only [rank_subsingleton', lt_self_iff_false] at h

theorem Module.rank_zero_iff_of_free {R M : Type*} [Ring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Free R M] :
    Module.rank R M = 0 ↔ Subsingleton M := by
  rw [← not_nontrivial_iff_subsingleton, iff_not_comm,
    ← Module.rank_pos_iff_of_free (R := R), pos_iff_ne_zero]

theorem Module.finrank_eq_zero_iff_of_free {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R M = 0 ↔ Subsingleton M := by
  have := Module.rank_lt_aleph0 R M
  rw [← not_le] at this
  simp [Module.finrank, this, Module.rank_zero_iff_of_free]

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
theorem _root_.nonempty_linearEquiv_of_finrank_eq_one (d1 : Module.finrank R V = 1) :
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

theorem existsUnique_eq_smul_id_of_finrank_eq_one (d1 : Module.finrank R V = 1) (u : V →ₗ[R] V) :
    ∃! c : R, u = c • LinearMap.id := by
  let e := (nonempty_linearEquiv_of_finrank_eq_one d1).some
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
noncomputable def LinearEquiv.smul_id_of_finrank_eq_one (d1 : Module.finrank R V = 1) :
    R ≃ₗ[R] (V →ₗ[R] V) where
  toFun := fun c ↦ c • LinearMap.id
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]
  invFun u := (existsUnique_eq_smul_id_of_finrank_eq_one d1 u).choose
  left_inv c := by
    simp [← (existsUnique_eq_smul_id_of_finrank_eq_one d1 (c • LinearMap.id)).choose_spec.2 c]
  right_inv u :=
    ((existsUnique_eq_smul_id_of_finrank_eq_one d1 u).choose_spec.1).symm

theorem subsingleton_of_finrank_eq_one (d1 : Module.finrank R V = 1) :
    Subsingleton (SpecialLinearGroup R V) where
  allEq u v := by
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

/-- By base change, an `R`-algebra `S` induces a group homomorphism from
`SpecialLinearGroup R V` to `SpecialLinearGroup S (S ⊗[R] V)`. -/
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
theorem congr_linearEquiv_coe_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) :
    (congr_linearEquiv e f : W ≃ₗ[R] W) = e.symm ≪≫ₗ f ≪≫ₗ e :=
  rfl

@[simp]
theorem congr_linearEquiv_apply_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) (x : W) :
    congr_linearEquiv e f x = e (f (e.symm x)) :=
  rfl

theorem congr_linearEquiv_symm (e : V ≃ₗ[R] W) :
    (congr_linearEquiv e).symm = congr_linearEquiv e.symm :=
  rfl

theorem congr_linearEquiv_trans (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] X) :
    (congr_linearEquiv e).trans (congr_linearEquiv f) = congr_linearEquiv (e.trans f) := by
  aesop

theorem congr_linearEquiv_refl :
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

theorem _root_.Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq
    (b : Module.Basis n R V) (g : Matrix.SpecialLinearGroup n R) :
    (Matrix.SpecialLinearGroup.toLin_equiv b g : V →ₗ[R] V) =
        (Matrix.toLin b b g) :=
  rfl

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

theorem mem_center_iff_spec {g : SpecialLinearGroup R V}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup R V)) (x : V) :
    (g : V →ₗ[R] V) x = (mem_center_iff.mp hg).choose • x := by
  let H := (mem_center_iff.mp hg).choose_spec.2
  rw [LinearMap.ext_iff] at H
  simp [H]

example (r : R) : LinearMap.det (r • LinearMap.id : V →ₗ[R] V) = r ^ (Module.finrank R V) := by
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one]

/- TODO : delete this auxiliary definition
and put it in the definition of `center_equiv_rootsOfUnity.
How can one access to the definition of one already defined term in a structure
while one is still definining it? -/
/-- The inverse map for the equivalence `SpecialLinearGroup.center_equiv_rootsOfUnity`. -/
noncomputable def center_equiv_rootsOfUnity_invFun
    (r : rootsOfUnity (max (Module.finrank R V) 1) R) :
    Subgroup.center (SpecialLinearGroup R V) :=
  ⟨⟨LinearMap.equivOfIsUnitDet (M := V) (R := R) (f := ((r : Rˣ) : R) • LinearMap.id) (by
    simp [LinearMap.det_smul, IsUnit.pow]), by
    simp [← Units.val_inj, LinearEquiv.coe_det]
    have := r.prop
    rw [mem_rootsOfUnity, ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one] at this
    rcases max_cases (Module.finrank R V) 1 with ⟨h, h'⟩ |  ⟨h, h'⟩
    · simp_rw [h] at this
      exact this
    · simp_rw [h, pow_one] at this
      simp [this]⟩, by
    simp only [mem_center_iff, LinearMap.coe_equivOfIsUnitDet]
    use r.val
    simp only [and_true]
    by_cases hV : Module.finrank R V = 0
    · simp [hV]
    · let hr := (mem_rootsOfUnity _ _).mp r.prop
      rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one] at hr
      rw [← hr]
      congr
      refine (Nat.max_eq_left <| Nat.one_le_iff_ne_zero.mpr hV).symm⟩

/-- The isomorphism between the roots of unity and the center of the special linear group. -/
noncomputable def center_equiv_rootsOfUnity :
    (Subgroup.center (SpecialLinearGroup R V)) ≃*
      ↥(rootsOfUnity (max (Module.finrank R V) 1) R) where
  toFun g := by
    by_cases hV : Subsingleton V
    · exact 1
    · rw [not_subsingleton_iff_nontrivial, ← Module.finrank_pos_iff_of_free (R := R)] at hV
      replace hV : 1 ≤ Module.finrank R V := hV
      have hr := (mem_center_iff.mp g.prop).choose_spec.1
      set r := (mem_center_iff.mp g.prop).choose
      rw [← Nat.max_eq_left hV] at hr
      have : IsUnit r := by
        rw [← isUnit_pow_iff _, hr]
        · exact isUnit_one
        rw [Nat.max_eq_left hV]
        exact Nat.ne_zero_of_lt hV
      exact ⟨this.unit, by simp [mem_rootsOfUnity, ← Units.val_inj, hr]⟩
  invFun := center_equiv_rootsOfUnity_invFun
  left_inv g := by
    simp only [center_equiv_rootsOfUnity_invFun, ← Subtype.val_inj,
      ← LinearEquiv.toLinearMap_inj, LinearMap.coe_equivOfIsUnitDet]
    split_ifs with hV
    · simp [Subsingleton.eq_one g]
    simp only [IsUnit.unit_spec, ← (mem_center_iff.mp g.prop).choose_spec.2]
  right_inv r := by
    rw [← Subtype.val_inj, SetLike.coe_eq_coe]
    simp only
    split_ifs with hV
    · symm
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simpa [hV] using (mem_rootsOfUnity _ _).mp r.prop
    · rw [not_subsingleton_iff_nontrivial] at hV
      have := Module.Free.instFaithfulSMulOfNontrivial R V
      simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec]
      have H := mem_center_iff.mp (Subtype.prop (center_equiv_rootsOfUnity_invFun r))
      suffices (H.choose • LinearMap.id : V →ₗ[R] V) = (r.val : R) • LinearMap.id by
        apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
        intro x
        rw [LinearMap.ext_iff] at this
        simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at this
        rw [this x]
      rw [← H.choose_spec.2]
      simp [center_equiv_rootsOfUnity_invFun]
  map_mul' g h := by
    simp only [Subgroup.coe_mul, coe_mul, LinearEquiv.coe_toLinearMap_mul, mul_dite, mul_one,
      dite_mul, one_mul, MulMemClass.mk_mul_mk]
    split_ifs with hV
    · rfl
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    set Hg := (mem_center_iff.mp g.prop)
    set Hh := (mem_center_iff.mp h.prop)
    set Hgh := (mem_center_iff.mp (g * h).prop)
    simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec,
      Units.val_mul]
    change Hgh.choose = Hg.choose * Hh.choose
    suffices (Hgh.choose • LinearMap.id : V →ₗ[R] V)
      = (Hg.choose • LinearMap.id) * (Hh.choose • LinearMap.id) by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp  [mul_smul,
        ← mem_center_iff_spec (g * h).prop, ← mem_center_iff_spec h.prop,
        ← mem_center_iff_spec g.prop]
    simp [← Hgh.choose_spec.2, ← Hh.choose_spec.2, ← Hg.choose_spec.2]

theorem center_equiv_rootsOfUnity_apply
    (g : Subgroup.center (SpecialLinearGroup R V)) :
    (g : V →ₗ[R] V) = (center_equiv_rootsOfUnity g) • LinearMap.id := by
  have := (mem_center_iff.mp g.prop).choose_spec.2
  simp [center_equiv_rootsOfUnity]
  split_ifs with hV
  · apply Subsingleton.eq_one
  · rw [not_subsingleton_iff_nontrivial] at hV
    rw [← (mem_center_iff.mp g.prop).choose_spec.2]

theorem center_equiv_rootsOfUnity_apply_apply
    (g : Subgroup.center (SpecialLinearGroup R V)) (x : V) :
    (center_equiv_rootsOfUnity g) • x = (g : SpecialLinearGroup R V) x := by
  simp only
  rw [← LinearEquiv.coe_toLinearMap, center_equiv_rootsOfUnity_apply]
  simp

omit [Nontrivial R] in
theorem _root_.rootsOfUnity.eq_one {n : ℕ} {r : rootsOfUnity n R}
    (hn : n = 1) : r.val = 1 := by
  have h := r.prop
  simpa only [mem_rootsOfUnity, hn, pow_one] using h

theorem center_equiv_rootsOfUnity_apply_of_finrank_le_one
    (d1 : Module.finrank R V ≤ 1) (g : Subgroup.center (SpecialLinearGroup R V)) :
    center_equiv_rootsOfUnity g = 1 := by
  rw [← Subtype.coe_inj, OneMemClass.coe_one]
  apply rootsOfUnity.eq_one
  rw [Nat.max_eq_right d1]

theorem center_equiv_rootsOfUnity_symm_apply
    (r : rootsOfUnity (max (Module.finrank R V) 1) R) :
    (center_equiv_rootsOfUnity.symm r : V →ₗ[R] V) = r • LinearMap.id := by
  simp only [center_equiv_rootsOfUnity, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
    center_equiv_rootsOfUnity_invFun, LinearMap.coe_equivOfIsUnitDet]
  congr

section

open Subgroup Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

variable [Nontrivial R]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)

-- compare with `Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity`
-- TODO : golf!
example (g) : ((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).trans
    center_equiv_rootsOfUnity g).val =
    Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g := by
  by_cases hV : Subsingleton V
  · convert Eq.refl (1 : Rˣ) <;>
    · apply rootsOfUnity.eq_one
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simp only [hV, sup_eq_right, zero_le_one, ← Module.finrank_eq_card_basis b]
  · have hι : ¬ IsEmpty ι := fun hι ↦ hV (by
      rw [← Module.finrank_eq_zero_iff_of_free (R := R),
        Module.finrank_eq_card_basis b, Fintype.card_of_isEmpty])
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    suffices (((((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).trans
      center_equiv_rootsOfUnity g).val : R) • LinearMap.id) : V →ₗ[R] V) =
        ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g).val : R) • LinearMap.id by
      rw [← Units.val_inj]
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp only [MulEquiv.trans_apply, LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq] at this
      erw [this]
    simp only [MulEquiv.trans_apply]
    have hgg' := Subgroup.centerCongr_apply_coe (Matrix.SpecialLinearGroup.toLin_equiv b) g
    set g' := ((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)) g)
    ext x
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    erw [center_equiv_rootsOfUnity_apply_apply _ x]
    simp only
    rw [← Subtype.coe_inj, ← LinearEquiv.toLinearMap_inj, LinearMap.ext_iff] at hgg'
    erw [hgg' x]
    specialize hgg' x
    rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq,
      Matrix.SpecialLinearGroup.eq_scalar_center_equiv_rootsOfUnity g,
      Matrix.toLin_scalar]
    simp

end

end center

end SpecialLinearGroup
