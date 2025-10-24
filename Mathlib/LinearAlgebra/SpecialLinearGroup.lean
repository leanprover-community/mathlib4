/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.Determinant

/-!
# The special linear group

see also `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`

-/

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

variable (F V) in
abbrev SpecialLinearGroup := { u : V ≃ₗ[F] V // u.det = 1 }

namespace SpecialLinearGroup

instance : CoeFun (SpecialLinearGroup F V) (fun _ ↦ V → V) where
  coe u x := u.val x

example (u : SpecialLinearGroup F V) : u 0 = 0 := by
  simp only [map_zero]

theorem ext_iff (u v : SpecialLinearGroup F V) : u = v ↔ ∀ x : V, u x = v x := by
  simp only [LinearMap.ext_iff, ← Subtype.coe_inj, LinearEquiv.ext_iff]

@[ext]
theorem ext (u v : SpecialLinearGroup F V) : (∀ x, u x = v x) → u = v :=
  (SpecialLinearGroup.ext_iff u v).mpr

example (c : F) : V →ₗ[F] V := c • LinearMap.id

example (n : ℕ) (hn : n ≠ 0) : n = n.pred.succ := by
  exact Eq.symm (Nat.succ_pred_eq_of_ne_zero hn)

theorem exists_ne_zero_of_finrank_ne_zero (d0 : Module.finrank F V ≠ 0) :
    ∃ v : V, v ≠ 0 := by
  have : FiniteDimensional F V := FiniteDimensional.of_finrank_pos (Nat.zero_lt_of_ne_zero d0)
  rw [← not_forall, ← finrank_zero_iff_forall_zero (K := F)]
  exact d0

theorem exists_eq_smul_id_of_finrank_eq_one
    (d1 : Module.finrank F V = 1) (u : V →ₗ[F] V) :
    ∃ c : F, u = c • LinearMap.id := by
  have : FiniteDimensional F V := Module.finite_of_finrank_eq_succ d1
  obtain ⟨v, hv⟩ := exists_ne_zero_of_finrank_ne_zero (ne_zero_of_eq_one d1)
  have := FiniteDimensional.basisSingleton Unit d1 v hv
  obtain ⟨c, hc : c • v = u v⟩ := exists_smul_eq_of_finrank_eq_one d1 hv (u v)
  use c
  ext x
  obtain ⟨d, rfl⟩ := exists_smul_eq_of_finrank_eq_one d1 hv x
  simp [hc]

example (c d : F) (v : V) (hv : v ≠ 0) :
      c = d ↔ c • v = d • v := by
  symm
  constructor
  · apply smul_left_injective _ hv
  · intro h
    exact congrFun (congrArg HSMul.hSMul h) v

example (d1 : Module.finrank F V = 1) : F ≃ₗ[F] (V →ₗ[F] V) where
  toFun := fun c ↦ c • LinearMap.id
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]
  invFun u := (exists_eq_smul_id_of_finrank_eq_one d1 u).choose
  left_inv c := by
    obtain ⟨v, hv⟩ := exists_ne_zero_of_finrank_ne_zero (ne_zero_of_eq_one d1)
    apply smul_left_injective _ hv
    exact (LinearMap.congr_fun
      (exists_eq_smul_id_of_finrank_eq_one d1 _).choose_spec v).symm
  right_inv u := by
    ext x
    obtain ⟨v, hv⟩ := exists_ne_zero_of_finrank_ne_zero (ne_zero_of_eq_one d1)
    sorry

instance subsingleton_of_subsingleton (d1 : Module.finrank F V = 1) :
    Subsingleton (SpecialLinearGroup F V) where
  allEq u v := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    have := FiniteDimensional.basisSingleton Unit d1
    obtain ⟨c, hc : c • x = u x⟩ := exists_smul_eq_of_finrank_eq_one d1 hx (u x)
    have (y : V) : u y = c • y := by
      obtain ⟨d, rfl⟩ := exists_smul_eq_of_finrank_eq_one d1 hx y



    sorry

instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩

instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B => ⟨A * B, by rw [det_mul, A.prop, B.prop, one_mul]⟩⟩

instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩

instance : Pow (SpecialLinearGroup n R) ℕ where
  pow x n := ⟨x ^ n, (det_pow _ _).trans <| x.prop.symm ▸ one_pow _⟩

instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩

instance [Fintype R] [DecidableEq R] : Fintype (SpecialLinearGroup n R) := Subtype.fintype _
instance [Finite R] : Finite (SpecialLinearGroup n R) := Subtype.finite

/-- The transpose of a matrix in `SL(n, R)` -/
def transpose (A : SpecialLinearGroup n R) : SpecialLinearGroup n R :=
  ⟨A.1.transpose, A.1.det_transpose ▸ A.2⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.transpose

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

-- Porting note: shouldn't be `@[simp]` because cast+mk gets reduced anyway
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl

@[simp]
theorem coe_inv : ↑ₘ(A⁻¹) = adjugate A :=
  rfl

@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB :=
  rfl

@[simp]
theorem coe_one : (1 : SpecialLinearGroup n R) = (1 : Matrix n n R) :=
  rfl

@[simp]
theorem det_coe : det ↑ₘA = 1 :=
  A.2

@[simp]
theorem coe_pow (m : ℕ) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl

@[simp]
lemma coe_transpose (A : SpecialLinearGroup n R) : ↑ₘAᵀ = (↑ₘA)ᵀ :=
  rfl

theorem det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg ≠ 0 := by
  rw [g.det_coe]
  norm_num

theorem row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : g i ≠ 0 := fun h =>
  g.det_ne_zero <| det_eq_zero_of_row_eq_zero i <| by simp [h]

end CoeLemmas

instance monoid : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid _ Subtype.coe_injective coe_one coe_mul coe_pow

instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    inv_mul_cancel := fun A => by
      ext1
      simp [adjugate_mul] }

/-- A version of `Matrix.toLin' A` that produces linear equivalences. -/
def toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R where
  toFun A :=
    LinearEquiv.ofLinear (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← toLin'_mul, ← coe_mul, mul_inv_cancel, coe_one, toLin'_one])
      (by rw [← toLin'_mul, ← coe_mul, inv_mul_cancel, coe_one, toLin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
  map_mul' A B := LinearEquiv.toLinearMap_injective <| Matrix.toLin'_mul ↑ₘA ↑ₘB

theorem toLin'_apply (A : SpecialLinearGroup n R) (v : n → R) :
    SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl

theorem toLin'_to_linearMap (A : SpecialLinearGroup n R) :
    ↑(SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA :=
  rfl

theorem toLin'_symm_apply (A : SpecialLinearGroup n R) (v : n → R) :
    A.toLin'.symm v = Matrix.toLin' (↑ₘA⁻¹) v :=
  rfl

theorem toLin'_symm_to_linearMap (A : SpecialLinearGroup n R) :
    ↑A.toLin'.symm = Matrix.toLin' ↑ₘA⁻¹ :=
  rfl

theorem toLin'_injective :
    Function.Injective ↑(toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R) := fun _ _ h =>
  Subtype.coe_injective <| Matrix.toLin'.injective <| LinearEquiv.toLinearMap_injective.eq_iff.mpr h

variable {S : Type*} [CommRing S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`SpecialLinearGroup n R` to `SpecialLinearGroup n S`. -/
@[simps]
def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S where
  toFun g :=
    ⟨f.mapMatrix ↑ₘg, by
      rw [← f.map_det]
      simp [g.prop]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' x y := Subtype.ext <| f.mapMatrix.map_mul ↑ₘx ↑ₘy

section center

open Subgroup

@[simp]
theorem center_eq_bot_of_subsingleton [Subsingleton n] :
    center (SpecialLinearGroup n R) = ⊥ :=
  eq_bot_iff.mpr fun x _ ↦ by rw [mem_bot, Subsingleton.elim x 1]

theorem scalar_eq_self_of_mem_center
    {A : SpecialLinearGroup n R} (hA : A ∈ center (SpecialLinearGroup n R)) (i : n) :
    scalar n (A i i) = A := by
  obtain ⟨r : R, hr : scalar n r = A⟩ := mem_range_scalar_of_commute_transvectionStruct fun t ↦
    Subtype.ext_iff.mp <| Subgroup.mem_center_iff.mp hA ⟨t.toMatrix, by simp⟩
  simp [← congr_fun₂ hr i i, ← hr]

theorem scalar_eq_coe_self_center
    (A : center (SpecialLinearGroup n R)) (i : n) :
    scalar n ((A : Matrix n n R) i i) = A :=
  scalar_eq_self_of_mem_center A.property i

/-- The center of a special linear group of degree `n` is the subgroup of scalar matrices, for which
the scalars are the `n`-th roots of unity. -/
theorem mem_center_iff {A : SpecialLinearGroup n R} :
    A ∈ center (SpecialLinearGroup n R) ↔ ∃ (r : R), r ^ (Fintype.card n) = 1 ∧ scalar n r = A := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩; · exact ⟨by aesop, by simp [Subsingleton.elim A 1]⟩
  refine ⟨fun h ↦ ⟨A i i, ?_, ?_⟩, fun ⟨r, _, hr⟩ ↦ Subgroup.mem_center_iff.mpr fun B ↦ ?_⟩
  · have : det ((scalar n) (A i i)) = 1 := (scalar_eq_self_of_mem_center h i).symm ▸ A.property
    simpa using this
  · exact scalar_eq_self_of_mem_center h i
  · suffices ↑ₘ(B * A) = ↑ₘ(A * B) from Subtype.val_injective this
    simpa only [coe_mul, ← hr] using (scalar_commute (n := n) r (Commute.all r) B).symm

/-- An equivalence of groups, from the center of the special linear group to the roots of unity. -/
-- replaced `(Fintype.card n).mkPNat'` by `Fintype.card n` (note `n` is nonempty here)
@[simps]
def center_equiv_rootsOfUnity' (i : n) :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (Fintype.card n) R where
  toFun A :=
    haveI : Nonempty n := ⟨i⟩
    rootsOfUnity.mkOfPowEq (↑ₘA i i) <| by
      obtain ⟨r, hr, hr'⟩ := mem_center_iff.mp A.property
      replace hr' : A.val i i = r := by simp only [← hr', scalar_apply, diagonal_apply_eq]
      simp only [hr', hr]
  invFun a := ⟨⟨a • (1 : Matrix n n R), by aesop⟩,
    Subgroup.mem_center_iff.mpr fun B ↦ Subtype.val_injective <| by simp [coe_mul]⟩
  left_inv A := by
    refine SetCoe.ext <| SetCoe.ext ?_
    obtain ⟨r, _, hr⟩ := mem_center_iff.mp A.property
    simpa [← hr, Submonoid.smul_def, Units.smul_def] using smul_one_eq_diagonal r
  right_inv a := by
    obtain ⟨⟨a, _⟩, ha⟩ := a
    exact SetCoe.ext <| Units.eq_iff.mp <| by simp
  map_mul' A B := by
    dsimp
    ext
    simp only [rootsOfUnity.val_mkOfPowEq_coe, Subgroup.coe_mul, Units.val_mul]
    rw [← scalar_eq_coe_self_center A i, ← scalar_eq_coe_self_center B i]
    simp

open scoped Classical in
/-- An equivalence of groups, from the center of the special linear group to the roots of unity.

See also `center_equiv_rootsOfUnity'`. -/
-- replaced `(Fintype.card n).mkPNat'` by what it means, avoiding `PNat`s.
noncomputable def center_equiv_rootsOfUnity :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (max (Fintype.card n) 1) R :=
  (isEmpty_or_nonempty n).by_cases
  (fun hn ↦ by
    rw [center_eq_bot_of_subsingleton, Fintype.card_eq_zero, max_eq_right_of_lt zero_lt_one,
      rootsOfUnity_one]
    exact MulEquiv.ofUnique)
  (fun _ ↦
    (max_eq_left (NeZero.one_le : 1 ≤ Fintype.card n)).symm ▸
      center_equiv_rootsOfUnity' (Classical.arbitrary n))

end center

