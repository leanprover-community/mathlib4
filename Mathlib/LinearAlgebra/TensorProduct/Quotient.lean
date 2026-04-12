/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!

# Interaction between Quotients and Tensor Products

This file contains constructions that relate quotients and tensor products. This file is also a home
for results whose proof depends on both tensor products and linear algebraic quotients.
Let `M, N` be `R`-modules, `m ≤ M` and `n ≤ N` be an `R`-submodules and `I ≤ R` an ideal. We prove
the following isomorphisms:

## Main results
- `TensorProduct.quotientTensorQuotientEquiv`:
  `(M ⧸ m) ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N ⊔ M ⊗ n)`
- `TensorProduct.quotientTensorEquiv`:
  `(M ⧸ m) ⊗[R] N ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N)`
- `TensorProduct.tensorQuotientEquiv`:
  `M ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (M ⊗ n)`
- `TensorProduct.quotTensorEquivQuotSMul`:
  `(R ⧸ I) ⊗[R] M ≃ₗ[R] M ⧸ (I • M)`
- `TensorProduct.tensorQuotEquivQuotSMul`:
  `M ⊗[R] (R ⧸ I) ≃ₗ[R] M ⧸ (I • M)`

## Tags

Quotient, Tensor Product

-/

@[expose] public section

assert_not_exists Cardinal

namespace TensorProduct

variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

attribute [local ext high] ext LinearMap.prod_ext

/--
Let `M, N` be `R`-modules, `m ≤ M` and `n ≤ N` be an `R`-submodules. Then we have a linear
isomorphism between tensor products of the quotients and the quotient of the tensor product:
`(M ⧸ m) ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N ⊔ M ⊗ n)`.
-/
noncomputable def quotientTensorQuotientEquiv (m : Submodule R M) (n : Submodule R N) :
    (M ⧸ (m : Submodule R M)) ⊗[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M ⊗[R] N) ⧸
      (LinearMap.range (map m.subtype LinearMap.id) ⊔
        LinearMap.range (map LinearMap.id n.subtype)) :=
  LinearEquiv.ofLinear
    (lift <| Submodule.liftQ _ (LinearMap.flip <| Submodule.liftQ _
      ((mk R (M := M) (N := N)).flip.compr₂ (Submodule.mkQ _)) fun x hx => by
      ext y
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, mk_apply, Submodule.mkQ_apply,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right ⟨y ⊗ₜ ⟨x, hx⟩, rfl⟩) fun x hx => by
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
        Submodule.liftQ_apply, LinearMap.compr₂_apply, mk_apply, LinearMap.zero_comp,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left ⟨⟨x, hx⟩ ⊗ₜ y, rfl⟩)
    (Submodule.liftQ _ (map (Submodule.mkQ _) (Submodule.mkQ _)) fun x hx => by
      rw [Submodule.mem_sup] at hx
      rcases hx with ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      simp only [LinearMap.mem_ker, map_add]
      set f := (map m.mkQ n.mkQ) ∘ₗ (map m.subtype LinearMap.id)
      set g := (map m.mkQ n.mkQ) ∘ₗ (map LinearMap.id n.subtype)
      have eq : LinearMap.coprod f g = 0 := by
        ext x y
        · simp [f, Submodule.Quotient.mk_eq_zero _ |>.2 x.2]
        · simp [g, Submodule.Quotient.mk_eq_zero _ |>.2 y.2]
      exact congr($eq (a, b)))
    (by ext; simp) (by ext; simp)

@[simp]
lemma quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    quotientTensorQuotientEquiv m n
      (Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ y) := rfl

@[simp]
lemma quotientTensorQuotientEquiv_symm_apply_mk_tmul
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    (quotientTensorQuotientEquiv m n).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
      Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y := rfl

variable (N) in
/--
Let `M, N` be `R`-modules, `m ≤ M` be an `R`-submodule. Then we have a linear isomorphism between
tensor products of the quotient and the quotient of the tensor product:
`(M ⧸ m) ⊗[R] N ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N)`.
-/
noncomputable def quotientTensorEquiv (m : Submodule R M) :
    (M ⧸ (m : Submodule R M)) ⊗[R] N ≃ₗ[R]
    (M ⊗[R] N) ⧸ (LinearMap.range (map m.subtype (LinearMap.id : N →ₗ[R] N))) :=
  congr (LinearEquiv.refl _ _) ((Submodule.quotEquivOfEqBot _ rfl).symm) ≪≫ₗ
  quotientTensorQuotientEquiv (N := N) m ⊥ ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp [Submodule.map_span, range_map_eq_span_tmul])

@[simp]
lemma quotientTensorEquiv_apply_tmul_mk (m : Submodule R M) (x : M) (y : N) :
    quotientTensorEquiv N m (Submodule.Quotient.mk x ⊗ₜ[R] y) =
    Submodule.Quotient.mk (x ⊗ₜ y) :=
  rfl

@[simp]
lemma quotientTensorEquiv_symm_apply_mk_tmul (m : Submodule R M) (x : M) (y : N) :
    (quotientTensorEquiv N m).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
    Submodule.Quotient.mk x ⊗ₜ[R] y :=
  rfl

variable (M) in
/--
Let `M, N` be `R`-modules, `n ≤ N` be an `R`-submodule. Then we have a linear isomorphism between
tensor products of the quotient and the quotient of the tensor product:
`M ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (M ⊗ n)`.
-/
noncomputable def tensorQuotientEquiv (n : Submodule R N) :
    M ⊗[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M ⊗[R] N) ⧸ (LinearMap.range (map (LinearMap.id : M →ₗ[R] M) n.subtype)) :=
  congr ((Submodule.quotEquivOfEqBot _ rfl).symm) (LinearEquiv.refl _ _) ≪≫ₗ
  quotientTensorQuotientEquiv (⊥ : Submodule R M) n ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp only [Submodule.map_sup]
    erw [Submodule.map_id, Submodule.map_id]
    simp only [sup_eq_right]
    rw [range_map_eq_span_tmul, range_map_eq_span_tmul]
    simp)

@[simp]
lemma tensorQuotientEquiv_apply_mk_tmul (n : Submodule R N) (x : M) (y : N) :
    tensorQuotientEquiv M n (x ⊗ₜ[R] Submodule.Quotient.mk y) =
    Submodule.Quotient.mk (x ⊗ₜ y) :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_tmul_mk (n : Submodule R N) (x : M) (y : N) :
    (tensorQuotientEquiv M n).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
    x ⊗ₜ[R] Submodule.Quotient.mk y :=
  rfl

variable (M) in
/-- Left tensoring a module with a quotient of the ring is the same as
quotienting that module by the corresponding submodule. -/
noncomputable def quotTensorEquivQuotSMul (I : Ideal R) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  quotientTensorEquiv M I ≪≫ₗ
  (Submodule.Quotient.equiv _ _ (TensorProduct.lid R M) <| by
    rw [← LinearMap.range_comp, ← (Submodule.topEquiv.lTensor I).range_comp, Submodule.smul_eq_map₂,
      map₂_eq_range_lift_comp_mapIncl]
    exact congr_arg _ (TensorProduct.ext' fun _ _ ↦ by simp))

variable (M) in
/-- Right tensoring a module with a quotient of the ring is the same as
quotienting that module by the corresponding submodule. -/
noncomputable def tensorQuotEquivQuotSMul (I : Ideal R) :
    (M ⊗[R] (R ⧸ I)) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  TensorProduct.comm _ _ _ ≪≫ₗ quotTensorEquivQuotSMul M I

@[simp]
lemma quotTensorEquivQuotSMul_mk_tmul (I : Ideal R) (r : R) (x : M) :
    quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I r ⊗ₜ[R] x) =
      Submodule.Quotient.mk (r • x) :=
  (quotTensorEquivQuotSMul M I).eq_symm_apply.mp <|
    Eq.trans (congrArg (· ⊗ₜ[R] x) <|
        Eq.trans (congrArg (Ideal.Quotient.mk I)
                    (Eq.trans (smul_eq_mul ..) (mul_one r))).symm <|
          Submodule.Quotient.mk_smul I r 1) <|
      smul_tmul r _ x

@[simp]
lemma quotTensorEquivQuotSMul_mk_one_tmul (I : Ideal R) (x : M) :
    quotTensorEquivQuotSMul M I (1 ⊗ₜ x) = Submodule.Quotient.mk x := by
  rw [← RingHom.map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  simp

lemma quotTensorEquivQuotSMul_comp_mkQ_rTensor (I : Ideal R) :
    quotTensorEquivQuotSMul M I ∘ₗ I.mkQ.rTensor M =
      (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.lid R M :=
  TensorProduct.ext' (quotTensorEquivQuotSMul_mk_tmul I)

@[simp]
lemma quotTensorEquivQuotSMul_symm_mk (I : Ideal R) (x : M) :
    (quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk x) = 1 ⊗ₜ[R] x :=
  rfl

lemma quotTensorEquivQuotSMul_symm_comp_mkQ (I : Ideal R) :
    (quotTensorEquivQuotSMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ =
      TensorProduct.mk R (R ⧸ I) M 1 :=
  LinearMap.ext (quotTensorEquivQuotSMul_symm_mk I)

lemma quotTensorEquivQuotSMul_comp_mk (I : Ideal R) :
    quotTensorEquivQuotSMul M I ∘ₗ TensorProduct.mk R (R ⧸ I) M 1 =
      Submodule.mkQ (I • ⊤) :=
  Eq.symm <| (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp <|
    quotTensorEquivQuotSMul_symm_comp_mkQ I

@[simp]
lemma tensorQuotEquivQuotSMul_tmul_mk (I : Ideal R) (x : M) (r : R) :
    tensorQuotEquivQuotSMul M I (x ⊗ₜ[R] Ideal.Quotient.mk I r) =
      Submodule.Quotient.mk (r • x) :=
  quotTensorEquivQuotSMul_mk_tmul I r x

lemma tensorQuotEquivQuotSMul_comp_mkQ_lTensor (I : Ideal R) :
    tensorQuotEquivQuotSMul M I ∘ₗ I.mkQ.lTensor M =
      (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.rid R M :=
  TensorProduct.ext' (tensorQuotEquivQuotSMul_tmul_mk I)

@[simp]
lemma tensorQuotEquivQuotSMul_symm_mk (I : Ideal R) (x : M) :
    (tensorQuotEquivQuotSMul M I).symm (Submodule.Quotient.mk x) = x ⊗ₜ[R] 1 :=
  rfl

lemma tensorQuotEquivQuotSMul_symm_comp_mkQ (I : Ideal R) :
    (tensorQuotEquivQuotSMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ =
      (TensorProduct.mk R M (R ⧸ I)).flip 1 :=
  LinearMap.ext (tensorQuotEquivQuotSMul_symm_mk I)

lemma tensorQuotEquivQuotSMul_comp_mk (I : Ideal R) :
    tensorQuotEquivQuotSMul M I ∘ₗ (TensorProduct.mk R M (R ⧸ I)).flip 1 =
      Submodule.mkQ (I • ⊤) :=
  Eq.symm <| (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp <|
    tensorQuotEquivQuotSMul_symm_comp_mkQ I

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `I` is be ideal of `R`, then `S ⧸ IS` is
  isomorphic to `S ⊗[R] (R ⧸ I)` as `S` modules. -/
noncomputable def _root_.Ideal.qoutMapEquivTensorQout {I : Ideal R} :
    (S ⧸ I.map (algebraMap R S)) ≃ₗ[S] S ⊗[R] (R ⧸ I) where
  __ := LinearEquiv.symm <| tensorQuotEquivQuotSMul S I ≪≫ₗ Submodule.quotEquivOfEq _ _ (by simp)
    ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _
  map_smul' := by
    rintro _ ⟨_⟩
    congr

variable (M) in
/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `I` is be ideal of `R`,
  then `S ⊗[R] M ⧸ I(S ⊗[R] M)` is isomorphic to `S ⊗[R] (M ⧸ IM)` as `S` modules. -/
noncomputable def tensorQuotMapSMulEquivTensorQuot (I : Ideal R) :
    ((S ⊗[R] M) ⧸ I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M))) ≃ₗ[S]
    S ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
  (tensorQuotEquivQuotSMul (S ⊗[R] M) (I.map (algebraMap R S))).symm ≪≫ₗ
    TensorProduct.comm S (S ⊗[R] M) _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S _ M ≪≫ₗ
      AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (LinearEquiv.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc R R S S _ M ≪≫ₗ (TensorProduct.comm R _ M).baseChange R S _ _ ≪≫ₗ
          (tensorQuotEquivQuotSMul M I).baseChange R S _ _

end TensorProduct

open TensorProduct

namespace TensorProduct.AlgebraTensorModule

variable {R : Type*} (A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

set_option backward.isDefEq.respectTransparency false in
/-- More linear version of `TensorProduct.tensorQuotientEquiv`. -/
noncomputable def tensorQuotientEquiv (n : Submodule B N) :
    M ⊗[R] (N ⧸ n) ≃ₗ[A]
      (M ⊗[R] N) ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) where
  __ := TensorProduct.tensorQuotientEquiv M (n.restrictScalars R)
  map_smul' m x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y =>
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [smul_tmul']
      rfl

@[simp]
lemma tensorQuotientEquiv_apply_tmul (n : Submodule B N) (x : M) (y : N) :
    tensorQuotientEquiv A B M n (x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_mk_tmul (n : Submodule B N) (x : M) (y : N) :
    (tensorQuotientEquiv A B M n).symm (Submodule.Quotient.mk (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] Submodule.Quotient.mk y :=
  rfl


variable [Module A N] [IsScalarTower R A N]

/- This lemma characterizes the kernel of `TensorProduct.mapOfCompatibleSMul`. Together with
`TensorProduct.mapOfCompatibleSMul_surjective` it gives an alternative characterization of
`M ⊗[A] N` as the quotient of `M ⊗[R] N` by the submodule `S` described below. -/
lemma ker_mapOfCompatibleSMul :
    (mapOfCompatibleSMul A R A M N).ker =
      Submodule.span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)} := by
  refine (Submodule.span_eq_of_le (mapOfCompatibleSMul A R A M N).ker ?_ ?_).symm
  · rintro - ⟨a, m, n, rfl⟩
    simp [smul_tmul]
  · let S := Submodule.span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)}
    let F : M ⊗[A] N →ₗ[A] (M ⊗[R] N) ⧸ S := TensorProduct.lift ({
      toFun m := {
        toFun n := S.mkQ (m ⊗ₜ[R] n)
        map_add' _ _ := by simp [tmul_add]
        map_smul' a n := by
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, eq_comm,
            Submodule.Quotient.eq, RingHom.id_apply]
          exact Submodule.subset_span ⟨a, m, n, rfl⟩ }
      map_add' _ _ := by ext _; simp [add_tmul]
      map_smul' _ _ := by simp; rfl })
    have h : F ∘ₗ mapOfCompatibleSMul A R A M N = S.mkQ := by ext; simp [S, F]
    change (mapOfCompatibleSMul A R A M N).ker ≤ S
    rw [← Submodule.ker_mkQ S, ← h]
    exact (mapOfCompatibleSMul A R A M N).ker_le_ker_comp F

end TensorProduct.AlgebraTensorModule
