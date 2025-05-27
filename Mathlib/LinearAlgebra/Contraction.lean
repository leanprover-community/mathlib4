/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/


suppress_compilation

variable {ι : Type*} (R M N P Q : Type*)

-- Porting note: we need high priority for this to fire first; not the case in ML3
attribute [local ext high] TensorProduct.ext

section Contraction

open TensorProduct LinearMap Matrix Module

open TensorProduct

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable [DecidableEq ι] [Fintype ι] (b : Basis ι R M)

/-- The natural left-handed pairing between a module and its dual. -/
def contractLeft : Module.Dual R M ⊗[R] M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id

/-- The natural right-handed pairing between a module and its dual. -/
def contractRight : M ⊗[R] Module.Dual R M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
def dualTensorHom : Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry R M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) LinearMap.smulRightₗ

variable {R M N P Q}

@[simp]
theorem contractLeft_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f ⊗ₜ m) = f m :=
  rfl

@[simp]
theorem contractRight_apply (f : Module.Dual R M) (m : M) : contractRight R M (m ⊗ₜ f) = f m :=
  rfl

@[simp]
theorem dualTensorHom_apply (f : Module.Dual R M) (m : M) (n : N) :
    dualTensorHom R M N (f ⊗ₜ n) m = f m • n :=
  rfl

theorem dualTensorHom_comp_lTensor (f : N →ₗ[R] P) :
    dualTensorHom R M P ∘ₗ f.lTensor _ = f.compRight ∘ₗ dualTensorHom R M N := by
  ext; simp

theorem dualTensorHom_comp_rTensor_dualMap (f : M →ₗ[R] N) :
    dualTensorHom R M P ∘ₗ f.dualMap.rTensor _ = f.lcomp R P ∘ₗ dualTensorHom R N P := by
  ext; simp

@[simp]
theorem transpose_dualTensorHom (f : Module.Dual R M) (m : M) :
    Dual.transpose (R := R) (dualTensorHom R M M (f ⊗ₜ m)) =
    dualTensorHom R _ _ (Dual.eval R M m ⊗ₜ f) := by
  ext f' m'
  simp only [Dual.transpose_apply, coe_comp, Function.comp_apply, dualTensorHom_apply,
    LinearMap.map_smulₛₗ, RingHom.id_apply, Algebra.id.smul_eq_mul, Dual.eval_apply,
    LinearMap.smul_apply]
  exact mul_comm _ _

@[simp]
theorem dualTensorHom_prodMap_zero (f : Module.Dual R M) (p : P) :
    ((dualTensorHom R M P) (f ⊗ₜ[R] p)).prodMap (0 : N →ₗ[R] Q) =
      dualTensorHom R (M × N) (P × Q) ((f ∘ₗ fst R M N) ⊗ₜ inl R P Q p) := by
  ext <;>
    simp only [coe_comp, coe_inl, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      fst_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

@[simp]
theorem zero_prodMap_dualTensorHom (g : Module.Dual R N) (q : Q) :
    (0 : M →ₗ[R] P).prodMap ((dualTensorHom R N Q) (g ⊗ₜ[R] q)) =
      dualTensorHom R (M × N) (P × Q) ((g ∘ₗ snd R M N) ⊗ₜ inr R P Q q) := by
  ext <;>
    simp only [coe_comp, coe_inr, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      snd_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

theorem map_dualTensorHom (f : Module.Dual R M) (p : P) (g : Module.Dual R N) (q : Q) :
    TensorProduct.map (dualTensorHom R M P (f ⊗ₜ[R] p)) (dualTensorHom R N Q (g ⊗ₜ[R] q)) =
      dualTensorHom R (M ⊗[R] N) (P ⊗[R] Q) (dualDistrib R M N (f ⊗ₜ g) ⊗ₜ[R] p ⊗ₜ[R] q) := by
  ext m n
  simp only [compr₂_apply, mk_apply, map_tmul, dualTensorHom_apply, dualDistrib_apply, ←
    smul_tmul_smul]

@[simp]
theorem comp_dualTensorHom (f : Module.Dual R M) (n : N) (g : Module.Dual R N) (p : P) :
    dualTensorHom R N P (g ⊗ₜ[R] p) ∘ₗ dualTensorHom R M N (f ⊗ₜ[R] n) =
      g n • dualTensorHom R M P (f ⊗ₜ p) := by
  ext m
  simp only [coe_comp, Function.comp_apply, dualTensorHom_apply, LinearMap.map_smul,
    RingHom.id_apply, LinearMap.smul_apply]
  rw [smul_comm]

/-- As a matrix, `dualTensorHom` evaluated on a basis element of `M* ⊗ N` is a matrix with a
single one and zeros elsewhere -/
theorem toMatrix_dualTensorHom {m : Type*} {n : Type*} [Fintype m] [Finite n] [DecidableEq m]
    [DecidableEq n] (bM : Basis m R M) (bN : Basis n R N) (j : m) (i : n) :
    toMatrix bM bN (dualTensorHom R M N (bM.coord j ⊗ₜ bN i)) = single i j 1 := by
  ext i' j'
  by_cases hij : i = i' ∧ j = j' <;>
    simp [LinearMap.toMatrix_apply, Finsupp.single_eq_pi_single, hij]
  rw [and_iff_not_or_not, Classical.not_not] at hij
  rcases hij with hij | hij <;> simp [hij]

/-- If the identity linear map lies in the range of the canonical map `M* ⊗[R] M → Hom_R(M, M)`,
then `M` is a finite projective `R`-module. -/
theorem finite_projective_of_id_mem_range_dualTensorHom (h : .id ∈ range (dualTensorHom R M M)) :
    Module.Finite R M ∧ Projective R M := by
  have ⟨t, eq⟩ := h
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  let f : (s → R) →ₗ[R] M := Fintype.linearCombination R R (·.1.2)
  have : f ∘ₗ pi (·.1.1) = .id := by
    ext; simp [f, ← eq, Fintype.linearCombination_apply, ← s.sum_coe_sort]
  exact ⟨.of_surjective f (surjective_of_comp_eq_id _ _ this), .of_split _ f this⟩

/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
-- We manually create simp-lemmas because `@[simps]` generates a malformed lemma
noncomputable def dualTensorHomEquivOfBasis : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  LinearEquiv.ofLinear (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coeFn_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, _root_.map_sum (dualTensorHom R M N), ← _root_.map_sum f, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coeFn_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])

theorem coe_dualTensorHomEquivOfBasis :
    ⇑(dualTensorHomEquivOfBasis (N := N) b) = dualTensorHom R M N := rfl

@[simp]
theorem dualTensorHomEquivOfBasis_apply (x : Module.Dual R M ⊗[R] N) :
    dualTensorHomEquivOfBasis b x = dualTensorHom R M N x := by
  ext; rfl

@[simp]
theorem dualTensorHomEquivOfBasis_toLinearMap :
    (dualTensorHomEquivOfBasis b).toLinearMap = dualTensorHom R M N :=
  rfl

@[simp]
theorem dualTensorHomEquivOfBasis_symm_cancel_left (x : Module.Dual R M ⊗[R] N) :
    (dualTensorHomEquivOfBasis b).symm (dualTensorHom R M N x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b,
    LinearEquiv.symm_apply_apply <| dualTensorHomEquivOfBasis (N := N) b]

@[simp]
theorem dualTensorHomEquivOfBasis_symm_cancel_right (x : M →ₗ[R] N) :
    dualTensorHom R M N ((dualTensorHomEquivOfBasis b).symm x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b, LinearEquiv.apply_symm_apply]

theorem dualTensorHom_finsupp :
    dualTensorHom R M (ι →₀ N) = sorry ∘ₗ
      Finsupp.mapRange.linearMap (dualTensorHom R M N) ∘ₗ (finsuppRight R _ N ι).toLinearMap := by
  sorry

/-theorem dualTensorHom_bijective_of_finite_projective [Module.Finite R N] [Projective R N] :
    Function.Bijective (dualTensorHom R M N) := by
  have ⟨n, f, g⟩ := Finite.exists_comp_eq_id_of_projective R N
  have := dualTensorHomEquivOfBasis (M := M) (N := N) (Pi.basisFun R <| Fin n)
  constructor
  sorry
  sorry -/

theorem dualTensorHom_bijective [Projective R M] [Module.Finite R M] :
    Function.Bijective (dualTensorHom R M N) := by
  obtain ⟨n, f, g, -, -, eq⟩ := Finite.exists_comp_eq_id_of_projective R M
  let e := dualTensorHomEquivOfBasis (N := N) (Pi.basisFun R <| Fin n)
  constructor
  · refine .of_comp (f := f.lcomp R N) ?_
    rw [← coe_comp, ← dualTensorHom_comp_rTensor_dualMap, coe_comp,
      ← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (EquivLike.injective _).comp ?_
    refine injective_of_comp_eq_id _ (rTensor _ g.dualMap) ?_
    rw [← rTensor_comp, dualMap_comp_dualMap g f]
    sorry
  sorry

variable (R M N) in
/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp]
noncomputable def dualTensorHomEquiv [Free R M] [Module.Finite R M] :
    Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  dualTensorHomEquivOfBasis (Module.Free.chooseBasis R M)

end CommSemiring

end Contraction

section HomTensorHom

open TensorProduct

open Module TensorProduct LinearMap

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable [Free R M] [Module.Finite R M] [Free R N] [Module.Finite R N]

/-- When `M` is a finite free module, the map `lTensorHomToHomLTensor` is an equivalence. Note
that `lTensorHomEquivHomLTensor` is not defined directly in terms of
`lTensorHomToHomLTensor`, but the equivalence between the two is given by
`lTensorHomEquivHomLTensor_toLinearMap` and `lTensorHomEquivHomLTensor_apply`. -/
noncomputable def lTensorHomEquivHomLTensor : P ⊗[R] (M →ₗ[R] Q) ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q).symm ≪≫ₗ
      TensorProduct.leftComm R P _ Q ≪≫ₗ
    dualTensorHomEquiv R M _

/-- When `M` is a finite free module, the map `rTensorHomToHomRTensor` is an equivalence. Note
that `rTensorHomEquivHomRTensor` is not defined directly in terms of
`rTensorHomToHomRTensor`, but the equivalence between the two is given by
`rTensorHomEquivHomRTensor_toLinearMap` and `rTensorHomEquivHomRTensor_apply`. -/
noncomputable def rTensorHomEquivHomRTensor : (M →ₗ[R] P) ⊗[R] Q ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (dualTensorHomEquiv R M P).symm (LinearEquiv.refl R Q) ≪≫ₗ TensorProduct.assoc R _ P Q ≪≫ₗ
    dualTensorHomEquiv R M _

@[simp]
theorem lTensorHomEquivHomLTensor_toLinearMap :
    (lTensorHomEquivHomLTensor R M P Q).toLinearMap = lTensorHomToHomLTensor R M P Q := by
  let e := congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f q m
  simp only [e, lTensorHomEquivHomLTensor, dualTensorHomEquiv, LinearEquiv.comp_coe, compr₂_apply,
    mk_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply,
    dualTensorHomEquivOfBasis_apply, dualTensorHomEquivOfBasis_symm_cancel_left, leftComm_tmul,
    dualTensorHom_apply, coe_comp, Function.comp_apply, lTensorHomToHomLTensor_apply, tmul_smul]

@[simp]
theorem rTensorHomEquivHomRTensor_toLinearMap :
    (rTensorHomEquivHomRTensor R M P Q).toLinearMap = rTensorHomToHomRTensor R M P Q := by
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f p q m
  simp only [e, rTensorHomEquivHomRTensor, dualTensorHomEquiv, compr₂_apply, mk_apply, coe_comp,
    LinearEquiv.coe_toLinearMap, Function.comp_apply, map_tmul, LinearEquiv.coe_coe,
    dualTensorHomEquivOfBasis_apply, LinearEquiv.trans_apply, congr_tmul,
    dualTensorHomEquivOfBasis_symm_cancel_left, LinearEquiv.refl_apply, assoc_tmul,
    dualTensorHom_apply, rTensorHomToHomRTensor_apply, smul_tmul']

variable {R M N P Q}

@[simp]
theorem lTensorHomEquivHomLTensor_apply (x : P ⊗[R] (M →ₗ[R] Q)) :
    lTensorHomEquivHomLTensor R M P Q x = lTensorHomToHomLTensor R M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, lTensorHomEquivHomLTensor_toLinearMap]

@[simp]
theorem rTensorHomEquivHomRTensor_apply (x : (M →ₗ[R] P) ⊗[R] Q) :
    rTensorHomEquivHomRTensor R M P Q x = rTensorHomToHomRTensor R M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, rTensorHomEquivHomRTensor_toLinearMap]

variable (R M N P Q)

/-- When `M` and `N` are free `R` modules, the map `homTensorHomMap` is an equivalence. Note that
`homTensorHomEquiv` is not defined directly in terms of `homTensorHomMap`, but the equivalence
between the two is given by `homTensorHomEquiv_toLinearMap` and `homTensorHomEquiv_apply`.
-/
noncomputable def homTensorHomEquiv : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  rTensorHomEquivHomRTensor R M P _ ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr (lTensorHomEquivHomLTensor R N _ Q) ≪≫ₗ
    lift.equiv R M N _

@[simp]
theorem homTensorHomEquiv_toLinearMap :
    (homTensorHomEquiv R M N P Q).toLinearMap = homTensorHomMap R M N P Q := by
  ext m n
  simp only [homTensorHomEquiv, compr₂_apply, mk_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.trans_apply, lift.equiv_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, rTensorHomEquivHomRTensor_apply, lTensorHomEquivHomLTensor_apply,
    lTensorHomToHomLTensor_apply, rTensorHomToHomRTensor_apply, homTensorHomMap_apply,
    map_tmul]

variable {R M N P Q}

@[simp]
theorem homTensorHomEquiv_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
    homTensorHomEquiv R M N P Q x = homTensorHomMap R M N P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, homTensorHomEquiv_toLinearMap]

end CommSemiring

end HomTensorHom
