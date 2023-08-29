/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin

#align_import linear_algebra.contraction from "leanprover-community/mathlib"@"657df4339ae6ceada048c8a2980fb10e393143ec"

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/

-- Porting note: universe metavariables behave oddly
universe w u v₁ v₂ v₃ v₄

variable {ι : Type w} (R : Type u) (M : Type v₁) (N : Type v₂)
  (P : Type v₃) (Q : Type v₄)

-- Porting note: we need high priority for this to fire first; not the case in ML3
attribute [local ext high] TensorProduct.ext

section Contraction

open TensorProduct LinearMap Matrix Module

open TensorProduct BigOperators

section CommSemiring

variable [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]

variable [Module R M] [Module R N] [Module R P] [Module R Q]

variable [DecidableEq ι] [Fintype ι] (b : Basis ι R M)

-- Porting note: doesn't like implicit ring in the tensor product
/-- The natural left-handed pairing between a module and its dual. -/
def contractLeft : Module.Dual R M ⊗[R] M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id
#align contract_left contractLeft

-- Porting note: doesn't like implicit ring in the tensor product
/-- The natural right-handed pairing between a module and its dual. -/
def contractRight : M ⊗[R] Module.Dual R M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)
#align contract_right contractRight

-- Porting note: doesn't like implicit ring in the tensor product
/-- The natural map associating a linear map to the tensor product of two modules. -/
def dualTensorHom : Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry R M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) LinearMap.smulRightₗ
#align dual_tensor_hom dualTensorHom

variable {R M N P Q}

@[simp]
theorem contractLeft_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f ⊗ₜ m) = f m :=
  rfl
#align contract_left_apply contractLeft_apply

@[simp]
theorem contractRight_apply (f : Module.Dual R M) (m : M) : contractRight R M (m ⊗ₜ f) = f m :=
  rfl
#align contract_right_apply contractRight_apply

@[simp]
theorem dualTensorHom_apply (f : Module.Dual R M) (m : M) (n : N) :
    dualTensorHom R M N (f ⊗ₜ n) m = f m • n :=
  rfl
#align dual_tensor_hom_apply dualTensorHom_apply

@[simp]
theorem transpose_dualTensorHom (f : Module.Dual R M) (m : M) :
    Dual.transpose (R := R) (dualTensorHom R M M (f ⊗ₜ m)) =
    dualTensorHom R _ _ (Dual.eval R M m ⊗ₜ f) := by
  ext f' m'
  -- ⊢ ↑(↑(↑Dual.transpose (↑(dualTensorHom R M M) (f ⊗ₜ[R] m))) f') m' = ↑(↑(↑(dua …
  simp only [Dual.transpose_apply, coe_comp, Function.comp_apply, dualTensorHom_apply,
    LinearMap.map_smulₛₗ, RingHom.id_apply, Algebra.id.smul_eq_mul, Dual.eval_apply,
    LinearMap.smul_apply]
  exact mul_comm _ _
  -- 🎉 no goals
#align transpose_dual_tensor_hom transpose_dualTensorHom

@[simp]
theorem dualTensorHom_prodMap_zero (f : Module.Dual R M) (p : P) :
    ((dualTensorHom R M P) (f ⊗ₜ[R] p)).prodMap (0 : N →ₗ[R] Q) =
      dualTensorHom R (M × N) (P × Q) ((f ∘ₗ fst R M N) ⊗ₜ inl R P Q p) := by
  ext <;>
    simp only [coe_comp, coe_inl, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      fst_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]
#align dual_tensor_hom_prod_map_zero dualTensorHom_prodMap_zero

@[simp]
theorem zero_prodMap_dualTensorHom (g : Module.Dual R N) (q : Q) :
    (0 : M →ₗ[R] P).prodMap ((dualTensorHom R N Q) (g ⊗ₜ[R] q)) =
      dualTensorHom R (M × N) (P × Q) ((g ∘ₗ snd R M N) ⊗ₜ inr R P Q q) := by
  ext <;>
    simp only [coe_comp, coe_inr, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      snd_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]
#align zero_prod_map_dual_tensor_hom zero_prodMap_dualTensorHom

theorem map_dualTensorHom (f : Module.Dual R M) (p : P) (g : Module.Dual R N) (q : Q) :
    TensorProduct.map (dualTensorHom R M P (f ⊗ₜ[R] p)) (dualTensorHom R N Q (g ⊗ₜ[R] q)) =
      dualTensorHom R (M ⊗[R] N) (P ⊗[R] Q) (dualDistrib R M N (f ⊗ₜ g) ⊗ₜ[R] p ⊗ₜ[R] q) := by
  ext m n
  -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R M N) (TensorProduct.map (↑(dualTensorHom R M  …
  simp only [compr₂_apply, mk_apply, map_tmul, dualTensorHom_apply, dualDistrib_apply, ←
    smul_tmul_smul]
#align map_dual_tensor_hom map_dualTensorHom

@[simp]
theorem comp_dualTensorHom (f : Module.Dual R M) (n : N) (g : Module.Dual R N) (p : P) :
    dualTensorHom R N P (g ⊗ₜ[R] p) ∘ₗ dualTensorHom R M N (f ⊗ₜ[R] n) =
      g n • dualTensorHom R M P (f ⊗ₜ p) := by
  ext m
  -- ⊢ ↑(comp (↑(dualTensorHom R N P) (g ⊗ₜ[R] p)) (↑(dualTensorHom R M N) (f ⊗ₜ[R] …
  simp only [coe_comp, Function.comp_apply, dualTensorHom_apply, LinearMap.map_smul,
    RingHom.id_apply, LinearMap.smul_apply]
  rw [smul_comm]
  -- 🎉 no goals
#align comp_dual_tensor_hom comp_dualTensorHom

/-- As a matrix, `dualTensorHom` evaluated on a basis element of `M* ⊗ N` is a matrix with a
single one and zeros elsewhere -/
theorem toMatrix_dualTensorHom {m : Type*} {n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (bM : Basis m R M) (bN : Basis n R N) (j : m) (i : n) :
    toMatrix bM bN (dualTensorHom R M N (bM.coord j ⊗ₜ bN i)) = stdBasisMatrix i j 1 := by
  ext i' j'
  -- ⊢ ↑(toMatrix bM bN) (↑(dualTensorHom R M N) (Basis.coord bM j ⊗ₜ[R] ↑bN i)) i' …
  by_cases hij : i = i' ∧ j = j' <;>
  -- ⊢ ↑(toMatrix bM bN) (↑(dualTensorHom R M N) (Basis.coord bM j ⊗ₜ[R] ↑bN i)) i' …
    simp [LinearMap.toMatrix_apply, Finsupp.single_eq_pi_single, hij]
    -- 🎉 no goals
    -- ⊢ Pi.single i (Pi.single j' 1 j) i' = 0
  rw [and_iff_not_or_not, Classical.not_not] at hij
  -- ⊢ Pi.single i (Pi.single j' 1 j) i' = 0
  cases' hij with hij hij <;> simp [hij]
  -- ⊢ Pi.single i (Pi.single j' 1 j) i' = 0
                              -- 🎉 no goals
                              -- 🎉 no goals
#align to_matrix_dual_tensor_hom toMatrix_dualTensorHom

end CommSemiring

section CommRing

variable [CommRing R]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]

variable [Module R M] [Module R N] [Module R P] [Module R Q]

variable [DecidableEq ι] [Fintype ι] (b : Basis ι R M)

variable {R M N P Q}

/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
-- @[simps! apply] -- Porting note: removed and created manually; malformed
noncomputable def dualTensorHomEquivOfBasis : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  LinearEquiv.ofLinear (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      -- ⊢ ↑(↑(comp (dualTensorHom R M N) (∑ i : ι, comp (↑(TensorProduct.mk R ((fun x  …
      simp only [applyₗ_apply_apply, coeFn_sum, dualTensorHom_apply, mk_apply, id_coe, id.def,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, (dualTensorHom R M N).map_sum, ← f.map_sum, b.sum_repr])
    (by
      ext f m
      -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R (Dual R M) N) (comp (∑ i : ι, comp (↑(TensorP …
      simp only [applyₗ_apply_apply, coeFn_sum, dualTensorHom_apply, mk_apply, id_coe, id.def,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])
#align dual_tensor_hom_equiv_of_basis dualTensorHomEquivOfBasis

@[simp]
theorem dualTensorHomEquivOfBasis_apply (x : Module.Dual R M ⊗[R] N) :
    (dualTensorHomEquivOfBasis (N := N) b :
    Module.Dual R M ⊗[R] N → (M →ₗ[R] N)) x = (dualTensorHom R M N) x := by
  ext; rfl
  -- ⊢ ↑(↑(dualTensorHomEquivOfBasis b) x) x✝ = ↑(↑(dualTensorHom R M N) x) x✝
       -- 🎉 no goals

@[simp]
theorem dualTensorHomEquivOfBasis_toLinearMap :
    (dualTensorHomEquivOfBasis b : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N).toLinearMap =
      dualTensorHom R M N :=
  rfl
#align dual_tensor_hom_equiv_of_basis_to_linear_map dualTensorHomEquivOfBasis_toLinearMap

-- Porting note: should N be explicit in dualTensorHomEquivOfBasis?
@[simp]
theorem dualTensorHomEquivOfBasis_symm_cancel_left (x : Module.Dual R M ⊗[R] N) :
    (dualTensorHomEquivOfBasis (N := N) b).symm (dualTensorHom R M N x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b,
    LinearEquiv.symm_apply_apply <| dualTensorHomEquivOfBasis (N := N) b]
#align dual_tensor_hom_equiv_of_basis_symm_cancel_left dualTensorHomEquivOfBasis_symm_cancel_left

@[simp]
theorem dualTensorHomEquivOfBasis_symm_cancel_right (x : M →ₗ[R] N) :
    dualTensorHom R M N ((dualTensorHomEquivOfBasis (N := N) b).symm x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b, LinearEquiv.apply_symm_apply]
  -- 🎉 no goals
#align dual_tensor_hom_equiv_of_basis_symm_cancel_right dualTensorHomEquivOfBasis_symm_cancel_right

variable (R M N P Q)

variable [Module.Free R M] [Module.Finite R M]

/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp]
noncomputable def dualTensorHomEquiv : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  dualTensorHomEquivOfBasis (Module.Free.chooseBasis R M)
#align dual_tensor_hom_equiv dualTensorHomEquiv

end CommRing

end Contraction

section HomTensorHom

open TensorProduct

open Module TensorProduct LinearMap

section CommRing

variable [CommRing R]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]

variable [Module R M] [Module R N] [Module R P] [Module R Q]

variable [Free R M] [Finite R M] [Free R N] [Finite R N] [Nontrivial R]

/-- When `M` is a finite free module, the map `lTensorHomToHomLTensor` is an equivalence. Note
that `lTensorHomEquivHomLTensor` is not defined directly in terms of
`lTensorHomToHomLTensor`, but the equivalence between the two is given by
`lTensorHomEquivHomLTensor_toLinearMap` and `lTensorHomEquivHomLTensor_apply`. -/
noncomputable def lTensorHomEquivHomLTensor : P ⊗[R] (M →ₗ[R] Q) ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q).symm ≪≫ₗ
      TensorProduct.leftComm R P _ Q ≪≫ₗ
    dualTensorHomEquiv R M _
#align ltensor_hom_equiv_hom_ltensor lTensorHomEquivHomLTensor

/-- When `M` is a finite free module, the map `rTensorHomToHomRTensor` is an equivalence. Note
that `rTensorHomEquivHomRTensor` is not defined directly in terms of
`rTensorHomToHomRTensor`, but the equivalence between the two is given by
`rTensorHomEquivHomRTensor_toLinearMap` and `rTensorHomEquivHomRTensor_apply`. -/
noncomputable def rTensorHomEquivHomRTensor : (M →ₗ[R] P) ⊗[R] Q ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (dualTensorHomEquiv R M P).symm (LinearEquiv.refl R Q) ≪≫ₗ TensorProduct.assoc R _ P Q ≪≫ₗ
    dualTensorHomEquiv R M _
#align rtensor_hom_equiv_hom_rtensor rTensorHomEquivHomRTensor

@[simp]
theorem lTensorHomEquivHomLTensor_toLinearMap :
    (lTensorHomEquivHomLTensor R M P Q).toLinearMap = lTensorHomToHomLTensor R M P Q := by
  classical -- Porting note: missing decidable for choosing basis
  let e := congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine' (cancel_right h).1 _
  ext f q m
  dsimp [lTensorHomEquivHomLTensor]
  simp only [lTensorHomEquivHomLTensor, dualTensorHomEquiv, compr₂_apply, mk_apply, coe_comp,
    LinearEquiv.coe_toLinearMap, Function.comp_apply, map_tmul, LinearEquiv.coe_coe,
    dualTensorHomEquivOfBasis_apply, LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply,
    dualTensorHomEquivOfBasis_symm_cancel_left, leftComm_tmul, dualTensorHom_apply, tmul_smul]
#align ltensor_hom_equiv_hom_ltensor_to_linear_map lTensorHomEquivHomLTensor_toLinearMap

@[simp]
theorem rTensorHomEquivHomRTensor_toLinearMap :
    (rTensorHomEquivHomRTensor R M P Q).toLinearMap = rTensorHomToHomRTensor R M P Q := by
  classical -- Porting note: missing decidable for choosing basis
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine' (cancel_right h).1 _
  ext f p q m
  simp only [rTensorHomEquivHomRTensor, dualTensorHomEquiv, compr₂_apply, mk_apply, coe_comp,
    LinearEquiv.coe_toLinearMap, Function.comp_apply, map_tmul, LinearEquiv.coe_coe,
    dualTensorHomEquivOfBasis_apply, LinearEquiv.trans_apply, congr_tmul,
    dualTensorHomEquivOfBasis_symm_cancel_left, LinearEquiv.refl_apply, assoc_tmul,
    dualTensorHom_apply, rTensorHomToHomRTensor_apply, smul_tmul']
#align rtensor_hom_equiv_hom_rtensor_to_linear_map rTensorHomEquivHomRTensor_toLinearMap

variable {R M N P Q}

@[simp]
theorem lTensorHomEquivHomLTensor_apply (x : P ⊗[R] (M →ₗ[R] Q)) :
    lTensorHomEquivHomLTensor R M P Q x = lTensorHomToHomLTensor R M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, lTensorHomEquivHomLTensor_toLinearMap]
  -- 🎉 no goals
#align ltensor_hom_equiv_hom_ltensor_apply lTensorHomEquivHomLTensor_apply

@[simp]
theorem rTensorHomEquivHomRTensor_apply (x : (M →ₗ[R] P) ⊗[R] Q) :
    rTensorHomEquivHomRTensor R M P Q x = rTensorHomToHomRTensor R M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, rTensorHomEquivHomRTensor_toLinearMap]
  -- 🎉 no goals
#align rtensor_hom_equiv_hom_rtensor_apply rTensorHomEquivHomRTensor_apply

variable (R M N P Q)

/-- When `M` and `N` are free `R` modules, the map `homTensorHomMap` is an equivalence. Note that
`homTensorHomEquiv` is not defined directly in terms of `homTensorHomMap`, but the equivalence
between the two is given by `homTensorHomEquiv_toLinearMap` and `homTensorHomEquiv_apply`.
-/
noncomputable def homTensorHomEquiv : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  rTensorHomEquivHomRTensor R M P _ ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr (lTensorHomEquivHomLTensor R N _ Q) ≪≫ₗ
    lift.equiv R M N _
#align hom_tensor_hom_equiv homTensorHomEquiv

@[simp]
theorem homTensorHomEquiv_toLinearMap :
    (homTensorHomEquiv R M N P Q).toLinearMap = homTensorHomMap R M N P Q := by
  ext m n
  -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R M N) (↑(↑(compr₂ (TensorProduct.mk R (M →ₗ[R] …
  simp only [homTensorHomEquiv, compr₂_apply, mk_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.trans_apply, lift.equiv_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, rTensorHomEquivHomRTensor_apply, lTensorHomEquivHomLTensor_apply,
    lTensorHomToHomLTensor_apply, rTensorHomToHomRTensor_apply, homTensorHomMap_apply,
    map_tmul]
#align hom_tensor_hom_equiv_to_linear_map homTensorHomEquiv_toLinearMap

variable {R M N P Q}

@[simp]
theorem homTensorHomEquiv_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
    homTensorHomEquiv R M N P Q x = homTensorHomMap R M N P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, homTensorHomEquiv_toLinearMap]
  -- 🎉 no goals
#align hom_tensor_hom_equiv_apply homTensorHomEquiv_apply

end CommRing

end HomTensorHom
