/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Constructs the Hodge pairing on the exterior product
-/

@[expose] public section

open BigOperators Module

namespace exteriorPower

noncomputable section volume

variable {R M : Type*}
  [CommRing R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I] (b : Basis I R M)

abbrev _root_.Module.Basis.volSet : {a : Finset I // a.card = finrank R M} :=
    ⟨Finset.univ, by rw [finrank_eq_card_basis b, Finset.card_univ]⟩

/-- The induced element of maximal rank by the basis `b` on `M`. -/
abbrev _root_.Module.Basis.vol : ⋀[R]^(finrank R M) M :=
    ιMulti_family R (finrank R M) b b.volSet

@[simp]
lemma ιMulti_family_volSet_eq_vol :
    ιMulti_family R (finrank R M) b b.volSet = b.vol := rfl

lemma span_vol_eq_top : Submodule.span R {b.vol} = ⊤ := by
  rw [Submodule.eq_top_iff_forall_basis_mem (Basis.exteriorPower R (finrank R M) b)]
  rintro s
  suffices s = b.volSet by
    rw [this]
    apply Submodule.mem_span_of_mem
    rw [Set.mem_singleton_iff]
    exact basis_apply R (finrank R M) b b.volSet
  rw [Subtype.ext_iff]
  apply Finset.eq_of_subset_of_card_le (by simp)
  rw [s.2, b.volSet.2]

@[simp]
lemma volSet_repr_vol : ((Basis.exteriorPower R (finrank R M) b).repr b.vol) b.volSet = 1 := by
  simp only [basis_repr_self]

@[simp]
lemma volSet_repr (x : ⋀[R]^(finrank R M) M) :
    ((Basis.exteriorPower R (finrank R M) b).repr x) b.volSet • b.vol = x := by
  obtain ⟨r, rfl⟩ := (Submodule.span_singleton_eq_top_iff R b.vol).mp (span_vol_eq_top b) x
  simp

@[simp]
lemma volSet_coord (x : ⋀[R]^(finrank R M) M) :
    ((Basis.exteriorPower R (finrank R M) b).coord b.volSet x) • b.vol = x := by
  simp

def volEquiv : ⋀[R]^(finrank R M) M ≃ₗ[R] R where
  toFun := (Basis.exteriorPower R (finrank R M) b).coord b.volSet
  map_add' x y := by simp only [Basis.coord_apply, map_add]
  map_smul' r x := by simp only [map_smul, Basis.coord_apply, smul_eq_mul, RingHom.id_apply]
  invFun r := r • b.vol
  left_inv := by rw [Function.leftInverse_iff_comp]; ext; simp
  right_inv := by rw [Function.rightInverse_iff_comp]; ext; simp

variable (x : ⋀[R]^(finrank R M) M) (r : R)

lemma volEquiv_apply :
    volEquiv b x = (Basis.exteriorPower R (finrank R M) b).coord b.volSet x := rfl

@[simp]
lemma volEquiv_symm_apply : (volEquiv b).symm r = r • b.vol := rfl

@[simp]
lemma volEquiv_vol : volEquiv b b.vol = 1 := by
  rw [volEquiv_apply, Basis.coord_apply, basis_repr_self]

@[simp]
lemma volEquiv_smul : volEquiv b x • b.vol = x := by simp [volEquiv_apply]

lemma repr_volSet_eq_volEquiv :
    (Basis.exteriorPower R (finrank R M) b).repr x b.volSet = volEquiv b x := rfl

end volume

noncomputable section hodgePairing

variable {R M : Type*} {m n : ℕ}
  [Field R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I]

instance instHMul [h : Fact (m + n = finrank R M)] :
    HMul (⋀[R]^m M) (⋀[R]^n M) (⋀[R]^(finrank R M) M) where
  hMul x y := ⟨x.val * y.val, mul_mem_of_add_eq x y h.out⟩

variable [Fact (m + n = finrank R M)]

@[simp]
lemma hmul_val (x : ⋀[R]^m M) (y : ⋀[R]^n M) : (x * y).val = x.val * y.val := rfl

@[simp]
lemma hmul_add (x : ⋀[R]^m M) (y z : ⋀[R]^n M) : x * (y + z) = x * y + x * z := by
  ext
  simp [mul_add]

@[simp]
lemma add_hmul (x y : ⋀[R]^m M) (z : ⋀[R]^n M) : (x + y) * z = x * z + y * z := by
  ext
  simp [add_mul]

@[simp]
lemma smul_hmul (r : R) (x : ⋀[R]^m M) (y : ⋀[R]^n M) : (r • x) * y = r • (x * y) := by
  ext
  simp

@[simp]
lemma hmul_smul (r : R) (x : ⋀[R]^m M) (y : ⋀[R]^n M) : x * (r • y) = r • (x * y) := by
  ext
  simp

def mulLeft [Fact (m + n = finrank R M)] :
    (⋀[R]^m M) →ₗ[R] (⋀[R]^n M →ₗ[R] ⋀[R]^(finrank R M) M) where
  toFun x := {
    toFun y := x * y
    map_add' := by intros; rw [hmul_add]
    map_smul' := by intros; rw [RingHom.id_apply, hmul_smul] }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

lemma coe_mulLeft_eq_mulLeft (x : ⋀[R]^m M) (y : ⋀[R]^n M) :
    (mulLeft x y).val = LinearMap.mulLeft R x.val y.val := by rfl
 -- x = 0 iff coord i x = 0; coord i x = ιMulti_dual; ιMulti_dual = toDual
lemma mulLeft_injective [Fact (m + n = finrank R M)] :
    Function.Injective (mulLeft (m := m) (n := n) (R := R) (M := M)) := by
  intro x y h
  simp [LinearMap.ext_iff, Subtype.ext_iff, coe_mulLeft_eq_mulLeft] at h
  ext

  sorry


def mulRight [Fact (m + n = finrank R M)] :
    (⋀[R]^n M) →ₗ[R] (⋀[R]^m M →ₗ[R] ⋀[R]^(finrank R M) M) where
  toFun y := {
    toFun x := x * y
    map_add' := by intros; rw [add_hmul]
    map_smul' := by intros; rw [RingHom.id_apply, smul_hmul] }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

variable (b : Basis I R M) [FiniteDimensional R M]

def hodgePairing : ⋀[R]^m M →ₗ[R] ⋀[R]^n M →ₗ[R] R := mulLeft.compr₂ (volEquiv b)

lemma hodgePairing_flip :
    (hodgePairing (m := m) (n := n) b).flip = mulRight.compr₂ (volEquiv b) := by
  rw [hodgePairing]
  apply LinearMap.ext
  rintro x
  apply LinearMap.ext
  rintro y
  simp [mulLeft, mulRight]

/-
def hodgePairing : ⋀[R]^m M →ₗ[R] ⋀[R]^n M →ₗ[R] R where
  toFun x := {
    toFun y := volEquiv b (x * y)
    map_add' _ _ := by rw [← map_add]; congr; simp [mul_add]
    map_smul' _ _ := by rw [RingHom.id_apply, ← map_smul]; congr; simp}
  map_add' _ _ := by apply LinearMap.ext; intros; simp [← map_add, add_mul]
  map_smul' _ _ := by apply LinearMap.ext; intros; simp [- smul_eq_mul, ← map_smul]

def hodgePairing : ⋀[R]^m M →ₗ[R] ⋀[R]^n M →ₗ[R] R where
  toFun x := {
    toFun y := volEquiv b ⟨x * y, mul_mem_of_add_eq x y h⟩
    map_add' _ _ := by rw [← map_add]; congr; simp [mul_add]
    map_smul' _ _ := by rw [RingHom.id_apply, ← map_smul]; congr; simp}
  map_add' _ _ := by apply LinearMap.ext; intros; simp [← map_add, add_mul]
  map_smul' _ _ := by apply LinearMap.ext; intros; simp [- smul_eq_mul, ← map_smul]
-/

def hodgePairing_apply_apply (x : ⋀[R]^m M) (y : ⋀[R]^n M) :
    hodgePairing b x y = volEquiv b (x * y) := rfl

open LinearMap

lemma hodgePairing_injective : Function.Injective (hodgePairing (m := m) (n := n) b) := by
  rw [hodgePairing]
  apply LinearMap.injective_compr₂_of_injective
  · rw [← LinearMap.ker_eq_bot]
    sorry
  · exact (volEquiv b).injective

instance instPerfPair : LinearMap.IsPerfPair (hodgePairing (m := m) (n := n) b) := by
  apply IsPerfPair.of_injective
  ·
  ·
    sorry

end hodgePairing

end exteriorPower
