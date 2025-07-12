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
variable (b : Basis ι R M)

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
    LinearMap.smul_apply]
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
theorem finite_projective_of_one_mem_range_dualTensorHom (h : 1 ∈ range (dualTensorHom R M M)) :
    Module.Finite R M ∧ Projective R M := by
  have ⟨t, eq⟩ := h
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  let f : (s → R) →ₗ[R] M := Fintype.linearCombination R (·.1.2)
  have : f ∘ₗ pi (·.1.1) = 1 := by
    ext; simp [f, ← eq, Fintype.linearCombination_apply, ← s.sum_coe_sort]
  exact ⟨.of_surjective f (surjective_of_comp_eq_id _ _ this), .of_split _ f this⟩

section Fintype

variable [DecidableEq ι] [Fintype ι]

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
  rfl

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

end Fintype

theorem dualTensorHom_bijective [Module.Finite R M] [Projective R M] :
    Function.Bijective (dualTensorHom R M N) := by
  obtain ⟨n, f, g, -, -, eq⟩ := Finite.exists_comp_eq_id_of_projective R M
  constructor
  · refine .of_comp (f := f.lcomp R N) ?_
    rw [← coe_comp, ← dualTensorHom_comp_rTensor_dualMap, coe_comp,
      ← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (EquivLike.injective _).comp (injective_of_comp_eq_id _ (rTensor _ g.dualMap) ?_)
    simp [← rTensor_comp, dualMap_comp_dualMap g f, eq]
  · refine .of_comp (g := g.dualMap.rTensor N) ?_
    rw [← coe_comp, dualTensorHom_comp_rTensor_dualMap, coe_comp,
      ← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (surjective_of_comp_eq_id (f.lcomp R N) _ ?_).comp (EquivLike.surjective _)
    ext φ; exact congr(φ ($eq _))

theorem dualTensorHom_self_right : dualTensorHom R M R = TensorProduct.rid R (Dual R M) := by
  ext; simp

/- Subsumed by `dualTensorHom_bijective_of_finite_projective_right`. -/
private theorem dualTensorHom_self_right_bijective : Function.Bijective (dualTensorHom R M R) := by
  simpa only [dualTensorHom_self_right] using LinearEquiv.bijective _

theorem dualTensorHom_finsupp [DecidableEq ι] :
    dualTensorHom R M (ι →₀ N) = .finsuppLinearMap R ∘ₗ
      Finsupp.mapRange.linearMap (dualTensorHom R M N) ∘ₗ (finsuppRight R _ N ι).toLinearMap := by
  ext; simp [Finsupp.single_apply]

theorem dualTensorHom_finsupp_bijective (fin : Finite ι ∨ Module.Finite R M)
    (h : Function.Bijective (dualTensorHom R M N)) :
    Function.Bijective (dualTensorHom R M (ι →₀ N)) := by
  classical rw [dualTensorHom_finsupp, coe_comp]
  refine .comp ?_ ((Finsupp.mapRange_bijective _ (map_zero _) h).comp (LinearEquiv.bijective _))
  cases fin
  · apply finsuppLinearMap_bijective_of_finite
  · apply finsuppLinearMap_bijective_of_moduleFinite

theorem dualTensorHom_bijective_of_comp_eq_id_right (f : N →ₗ[R] P) (g : P →ₗ[R] N)
    (comp_eq_id : g ∘ₗ f = .id) (h : Function.Bijective (dualTensorHom R M P)) :
    Function.Bijective (dualTensorHom R M N) where
  left := .of_comp (f := f.compRight) <| by
    rw [← coe_comp, ← dualTensorHom_comp_lTensor]
    refine h.1.comp (injective_of_comp_eq_id _ (g.lTensor _) ?_)
    rw [← lTensor_comp, comp_eq_id, lTensor_id]
  right := .of_comp (g := g.lTensor _) <| by
    rw [← coe_comp, dualTensorHom_comp_lTensor, coe_comp]
    refine (surjective_of_comp_eq_id f.compRight _ ?_).comp h.2
    ext; exact congr($comp_eq_id _)

theorem dualTensorHom_fun_bijective [Finite ι] (h : Function.Bijective (dualTensorHom R M N)) :
    Function.Bijective (dualTensorHom R M (ι → N)) :=
  dualTensorHom_bijective_of_comp_eq_id_right
    (Finsupp.linearEquivFunOnFinite R N ι).symm
    (Finsupp.linearEquivFunOnFinite ..).toLinearMap (by ext; simp)
    (dualTensorHom_finsupp_bijective (.inl ‹_›) h)

theorem dualTensorHom_bijective_of_finite_projective_right [Module.Finite R N] [Projective R N] :
    Function.Bijective (dualTensorHom R M N) :=
  have ⟨_n, f, g, _, _, eq⟩ := Finite.exists_comp_eq_id_of_projective R N
  dualTensorHom_bijective_of_comp_eq_id_right g f eq <|
    dualTensorHom_fun_bijective dualTensorHom_self_right_bijective

theorem dualTensorHom_bijective_of_finite_left_projective_right [Module.Finite R M]
    [Projective R N] : Function.Bijective (dualTensorHom R M N) :=
  have ⟨f, eq⟩ := projective_def'.mp ‹Projective R N›
  dualTensorHom_bijective_of_comp_eq_id_right _ _ eq <|
    dualTensorHom_finsupp_bijective (.inr ‹_›) dualTensorHom_self_right_bijective

variable (R M N) in
/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp]
noncomputable def dualTensorHomEquiv [Module.Finite R M] [Projective R M] :
    Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  .ofBijective _ (dualTensorHom_bijective ..)

theorem dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis
    (b : Basis ι R M) [DecidableEq ι] [Fintype ι] :
    have := Module.Finite.of_basis b; have := Module.Free.of_basis b
    dualTensorHomEquiv R M N = dualTensorHomEquivOfBasis b := by
  ext; rfl

end CommSemiring

end Contraction

section HomTensorHom

open TensorProduct

open Module TensorProduct LinearMap

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable [Projective R M] [Module.Finite R M]

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
  simp [e, lTensorHomEquivHomLTensor]

@[simp]
theorem rTensorHomEquivHomRTensor_toLinearMap :
    (rTensorHomEquivHomRTensor R M P Q).toLinearMap = rTensorHomToHomRTensor R M P Q := by
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f p q m
  simp [e, rTensorHomEquivHomRTensor, smul_tmul']

variable {R M N P Q}

@[simp]
theorem lTensorHomEquivHomLTensor_apply (x : P ⊗[R] (M →ₗ[R] Q)) :
    lTensorHomEquivHomLTensor R M P Q x = lTensorHomToHomLTensor R M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, lTensorHomEquivHomLTensor_toLinearMap]

@[simp]
theorem rTensorHomEquivHomRTensor_apply (x : (M →ₗ[R] P) ⊗[R] Q) :
    rTensorHomEquivHomRTensor R M P Q x = rTensorHomToHomRTensor R M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, rTensorHomEquivHomRTensor_toLinearMap]

variable (R M N P Q) [Projective R N] [Module.Finite R N]

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
